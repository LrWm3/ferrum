//! Statement collection and variable analysis.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Statements.scala
//! Status: partial. Statement and variable queries are implemented; full traversal
//! and extension coverage depend on the remaining AST node/reconstruction work.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::ast::Metadata;
use crate::ast::statement::{Stmt, StmtKind};

pub fn empty_stmt() -> Stmt {
    Stmt::new(
        StmtKind::Seqn {
            statements: Vec::new(),
            declarations: Vec::new(),
        },
        Metadata::default(),
    )
}

/// Flatten sequences while retaining branch and loop statements themselves.
pub fn children(stmt: &Stmt) -> Vec<Stmt> {
    match stmt.kind() {
        StmtKind::While { body, .. } => std::iter::once(stmt.clone())
            .chain(children(body))
            .collect(),
        StmtKind::If {
            then_branch,
            else_branch,
            ..
        } => std::iter::once(stmt.clone())
            .chain(children(then_branch))
            .chain(children(else_branch))
            .collect(),
        StmtKind::Seqn { statements, .. } => statements.iter().flat_map(children).collect(),
        _ => vec![stmt.clone()],
    }
}

use super::nodes::{self, Node, TraversalError};
use crate::ast::expression::{ExpKind, LocalVar};
use crate::ast::program::{Declaration, LocalVarDecl};
use crate::ast::r#type::Type;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VariableAnalysisError {
    Traversal(TraversalError),
    DeclaredTypeMismatch {
        name: String,
        declared: Type,
        used: Type,
    },
    UsedWithDifferentTypes {
        name: String,
        first: Type,
        second: Type,
    },
}
impl From<TraversalError> for VariableAnalysisError {
    fn from(error: TraversalError) -> Self {
        Self::Traversal(error)
    }
}

pub fn undeclared_local_vars(stmt: &Stmt) -> Result<Vec<LocalVar>, VariableAnalysisError> {
    fn recurse(
        node: &Node,
        declarations: &[LocalVarDecl],
    ) -> Result<Vec<LocalVar>, VariableAnalysisError> {
        let mut nested = declarations.to_vec();
        match node {
            Node::Exp(e) => match e.kind() {
                ExpKind::Forall(vars, ..)
                | ExpKind::Exists(vars, ..)
                | ExpKind::ForPerm(vars, ..) => nested.extend(vars.iter().cloned()),
                ExpKind::Let(var, ..) => nested.push(var.clone()),
                _ => {}
            },
            Node::Stmt(s) => {
                if let StmtKind::Seqn { .. } = s.kind() {
                    nested.extend(s.scoped_declarations().into_iter().filter_map(|d| match d {
                        Declaration::Local(v) => Some(v),
                        _ => None,
                    }));
                }
            }
            _ => {}
        }
        let children = nodes::subnodes(node)?
            .iter()
            .map(|child| recurse(child, &nested))
            .collect::<Result<Vec<_>, _>>()?;
        let local = match node {
            Node::LocalVar(v) => Some(v),
            Node::Exp(e) => match e.kind() {
                ExpKind::LocalVar(v) => Some(v),
                _ => None,
            },
            _ => None,
        };
        let mut result = Vec::new();
        if let Some(v) = local {
            match declarations.iter().find(|d| d.name == v.name) {
                Some(d) if d.typ != v.typ => {
                    return Err(VariableAnalysisError::DeclaredTypeMismatch {
                        name: v.name.clone(),
                        declared: d.typ.clone(),
                        used: v.typ.clone(),
                    });
                }
                Some(_) => {}
                None => result.push(v.clone()),
            }
        }
        for child in children {
            for next in child {
                for previous in &result {
                    if previous.name == next.name && previous.typ != next.typ {
                        return Err(VariableAnalysisError::UsedWithDifferentTypes {
                            name: next.name.clone(),
                            first: previous.typ.clone(),
                            second: next.typ.clone(),
                        });
                    }
                }
                if !result.contains(&next) {
                    result.push(next);
                }
            }
        }
        Ok(result)
    }
    recurse(&Node::Stmt(stmt.clone()), &[])
}

pub fn written_vars(stmt: &Stmt) -> Result<Vec<LocalVar>, VariableAnalysisError> {
    fn visit(
        node: &Node,
        root: &Stmt,
        result: &mut Vec<LocalVar>,
    ) -> Result<(), VariableAnalysisError> {
        if let Node::Stmt(s) = node {
            match s.kind() {
                StmtKind::LocalVarAssign { lhs, .. } | StmtKind::NewStmt { lhs, .. } => {
                    result.insert(0, lhs.clone())
                }
                StmtKind::MethodCall { targets, .. } => result.extend(targets.iter().cloned()),
                StmtKind::While { body, .. } => {
                    let written = written_vars(body)?;
                    let root_free = undeclared_local_vars(root)?;
                    result.extend(written.into_iter().filter(|v| root_free.contains(v)));
                }
                _ => {}
            }
        }
        for child in nodes::subnodes(node)? {
            visit(&child, root, result)?;
        }
        Ok(())
    }
    let mut result = Vec::new();
    let root = Node::Stmt(stmt.clone());
    visit(&root, stmt, &mut result)?;
    let mut distinct = Vec::new();
    for value in result {
        if !distinct.contains(&value) {
            distinct.push(value);
        }
    }
    Ok(distinct)
}
