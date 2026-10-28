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

/// Expression-only substitution through statement products; extension statements
/// and declaration families requiring nested member reconstruction are explicit failures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementReplacementError {
    Expression(super::rewriter::strategy::ExpressionReplacementError),
    InvalidLocalVar,
    InvalidFieldAccess,
    InvalidPredicateAccess,
    InvalidAccessPredicate,
    InvalidMagicWand,
    InvalidStatement,
    InvalidDeclaration,
    InvalidField,
    Extension,
    NestedDeclaration,
}
impl From<super::rewriter::strategy::ExpressionReplacementError> for StatementReplacementError {
    fn from(e: super::rewriter::strategy::ExpressionReplacementError) -> Self {
        Self::Expression(e)
    }
}
pub fn replace_expressions(
    stmt: &Stmt,
    replacements: &[(crate::ast::expression::Exp, crate::ast::expression::Exp)],
) -> Result<Stmt, StatementReplacementError> {
    use super::rewriter::strategy::replace_expressions as replace;
    use crate::ast::expression::{Exp, ExpKind};
    use crate::ast::statement::{PredicateAccessPredicate, ResourceAccess};
    fn local(
        v: &LocalVar,
        replacements: &[(Exp, Exp)],
    ) -> Result<LocalVar, StatementReplacementError> {
        let e = Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone());
        let result = replace(&e, replacements)?;
        if let ExpKind::LocalVar(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidLocalVar)
        }
    }
    fn field(
        v: &crate::ast::expression::FieldAccess,
        replacements: &[(Exp, Exp)],
    ) -> Result<crate::ast::expression::FieldAccess, StatementReplacementError> {
        let e = Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone());
        let result = replace(&e, replacements)?;
        if let ExpKind::FieldAccess(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidFieldAccess)
        }
    }
    fn predicate(
        v: &crate::ast::expression::PredicateAccess,
        replacements: &[(Exp, Exp)],
    ) -> Result<crate::ast::expression::PredicateAccess, StatementReplacementError> {
        let e = Exp::new(ExpKind::PredicateAccess(v.clone()), v.meta.clone());
        let result = replace(&e, replacements)?;
        if let ExpKind::PredicateAccess(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidPredicateAccess)
        }
    }
    fn access(
        v: &PredicateAccessPredicate,
        replacements: &[(Exp, Exp)],
    ) -> Result<PredicateAccessPredicate, StatementReplacementError> {
        let e = Exp::new(ExpKind::PredicateAccessPredicate(v.clone()), v.meta.clone());
        let result = replace(&e, replacements)?;
        if let ExpKind::PredicateAccessPredicate(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidAccessPredicate)
        }
    }
    fn wand(v: &Exp, replacements: &[(Exp, Exp)]) -> Result<Exp, StatementReplacementError> {
        let result = replace(v, replacements)?;
        if matches!(result.kind(), ExpKind::MagicWand(..)) {
            Ok(result)
        } else {
            Err(StatementReplacementError::InvalidMagicWand)
        }
    }
    fn resource(
        v: &ResourceAccess,
        replacements: &[(Exp, Exp)],
    ) -> Result<ResourceAccess, StatementReplacementError> {
        Ok(match v {
            ResourceAccess::Field(v) => ResourceAccess::Field(field(v, replacements)?),
            ResourceAccess::Predicate(v) => ResourceAccess::Predicate(predicate(v, replacements)?),
            ResourceAccess::MagicWand(v) => ResourceAccess::MagicWand(wand(v, replacements)?),
        })
    }
    if replacements.is_empty() {
        return Ok(stmt.clone());
    }
    let exp = |e: &Exp| replace(e, replacements).map_err(StatementReplacementError::from);
    let exps = |es: &[Exp]| es.iter().map(exp).collect::<Result<Vec<_>, _>>();
    let kind = match stmt.kind() {
        StmtKind::NewStmt { lhs, fields } => StmtKind::NewStmt {
            lhs: local(lhs, replacements)?,
            fields: fields.clone(),
        },
        StmtKind::LocalVarAssign { lhs, rhs } => StmtKind::LocalVarAssign {
            lhs: local(lhs, replacements)?,
            rhs: exp(rhs)?,
        },
        StmtKind::FieldAssign { lhs, rhs } => StmtKind::FieldAssign {
            lhs: field(lhs, replacements)?,
            rhs: exp(rhs)?,
        },
        StmtKind::MethodCall {
            method_name,
            args,
            targets,
        } => StmtKind::MethodCall {
            method_name: method_name.clone(),
            args: exps(args)?,
            targets: targets
                .iter()
                .map(|v| local(v, replacements))
                .collect::<Result<_, _>>()?,
        },
        StmtKind::Exhale(e) => StmtKind::Exhale(exp(e)?),
        StmtKind::Inhale(e) => StmtKind::Inhale(exp(e)?),
        StmtKind::Assert(e) => StmtKind::Assert(exp(e)?),
        StmtKind::Assume(e) => StmtKind::Assume(exp(e)?),
        StmtKind::Fold(v) => StmtKind::Fold(access(v, replacements)?),
        StmtKind::Unfold(v) => StmtKind::Unfold(access(v, replacements)?),
        StmtKind::Package {
            wand: w,
            proof_script,
        } => StmtKind::Package {
            wand: wand(w, replacements)?,
            proof_script: replace_expressions(proof_script, replacements)?,
        },
        StmtKind::Apply(w) => StmtKind::Apply(wand(w, replacements)?),
        StmtKind::Seqn {
            statements,
            declarations,
        } => {
            if declarations
                .iter()
                .any(|d| !matches!(d, Declaration::Local(_) | Declaration::Label(_)))
            {
                return Err(StatementReplacementError::NestedDeclaration);
            }
            StmtKind::Seqn {
                statements: statements
                    .iter()
                    .map(|s| replace_expressions(s, replacements))
                    .collect::<Result<_, _>>()?,
                declarations: declarations
                    .iter()
                    .map(|d| match d {
                        Declaration::Local(v) => Ok(Declaration::Local(v.clone())),
                        Declaration::Label(v) => {
                            let invariants = exps(&v.invariants)?;
                            Ok(Declaration::Label(if invariants == v.invariants {
                                v.clone()
                            } else {
                                v.copy_with(|label| label.invariants = invariants)
                            }))
                        }
                        _ => Err(StatementReplacementError::NestedDeclaration),
                    })
                    .collect::<Result<_, _>>()?,
            }
        }
        StmtKind::If {
            condition,
            then_branch,
            else_branch,
        } => StmtKind::If {
            condition: exp(condition)?,
            then_branch: replace_expressions(then_branch, replacements)?,
            else_branch: replace_expressions(else_branch, replacements)?,
        },
        StmtKind::While {
            condition,
            invariants,
            body,
        } => StmtKind::While {
            condition: exp(condition)?,
            invariants: exps(invariants)?,
            body: replace_expressions(body, replacements)?,
        },
        StmtKind::Label(label) => {
            let invariants = exps(&label.invariants)?;
            StmtKind::Label(if invariants == label.invariants {
                label.clone()
            } else {
                label.copy_with(|d| d.invariants = invariants)
            })
        }
        StmtKind::Goto(name) => StmtKind::Goto(name.clone()),
        StmtKind::LocalVarDeclStmt(v) => StmtKind::LocalVarDeclStmt(v.clone()),
        StmtKind::Quasihavoc { guard, resource: r } => StmtKind::Quasihavoc {
            guard: guard.as_ref().map(exp).transpose()?,
            resource: resource(r, replacements)?,
        },
        StmtKind::Quasihavocall {
            variables,
            guard,
            resource: r,
        } => StmtKind::Quasihavocall {
            variables: variables.clone(),
            guard: guard.as_ref().map(exp).transpose()?,
            resource: resource(r, replacements)?,
        },
        StmtKind::Extension(_) => return Err(StatementReplacementError::Extension),
    };
    Ok(if &kind == stmt.kind() {
        stmt.clone()
    } else {
        Stmt::new(kind, stmt.metadata().clone())
    })
}

/// Maps each expression root in source statement order; the callback controls recursive expression traversal.
pub fn map_expression_roots<E: From<StatementReplacementError>>(
    stmt: &Stmt,
    replace: &dyn Fn(&crate::ast::expression::Exp) -> Result<crate::ast::expression::Exp, E>,
) -> Result<Stmt, E> {
    map_expression_roots_with_extensions(stmt, replace, &|_, _| {
        Err(StatementReplacementError::Extension.into())
    })
}

pub fn map_expression_roots_with_extensions<E: From<StatementReplacementError>>(
    stmt: &Stmt,
    replace: &dyn Fn(&crate::ast::expression::Exp) -> Result<crate::ast::expression::Exp, E>,
    extension: &dyn Fn(
        &crate::ast::statement::ExtensionStmtHandle,
        &dyn Fn(&crate::ast::expression::Exp) -> Result<crate::ast::expression::Exp, E>,
    ) -> Result<crate::ast::statement::ExtensionStmtHandle, E>,
) -> Result<Stmt, E> {
    use crate::ast::expression::{Exp, ExpKind};
    use crate::ast::statement::{PredicateAccessPredicate, ResourceAccess};
    fn local<E: From<StatementReplacementError>>(
        v: &LocalVar,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<LocalVar, E> {
        let e = Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone());
        let result = replace(&e)?;
        if let ExpKind::LocalVar(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidLocalVar.into())
        }
    }
    fn field<E: From<StatementReplacementError>>(
        v: &crate::ast::expression::FieldAccess,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<crate::ast::expression::FieldAccess, E> {
        let e = Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone());
        let result = replace(&e)?;
        if let ExpKind::FieldAccess(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidFieldAccess.into())
        }
    }
    fn predicate<E: From<StatementReplacementError>>(
        v: &crate::ast::expression::PredicateAccess,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<crate::ast::expression::PredicateAccess, E> {
        let e = Exp::new(ExpKind::PredicateAccess(v.clone()), v.meta.clone());
        let result = replace(&e)?;
        if let ExpKind::PredicateAccess(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidPredicateAccess.into())
        }
    }
    fn access<E: From<StatementReplacementError>>(
        v: &PredicateAccessPredicate,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<PredicateAccessPredicate, E> {
        let e = Exp::new(ExpKind::PredicateAccessPredicate(v.clone()), v.meta.clone());
        let result = replace(&e)?;
        if let ExpKind::PredicateAccessPredicate(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidAccessPredicate.into())
        }
    }
    fn wand<E: From<StatementReplacementError>>(
        v: &Exp,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<Exp, E> {
        let result = replace(v)?;
        if matches!(result.kind(), ExpKind::MagicWand(..)) {
            Ok(result)
        } else {
            Err(StatementReplacementError::InvalidMagicWand.into())
        }
    }
    fn resource<E: From<StatementReplacementError>>(
        v: &ResourceAccess,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<ResourceAccess, E> {
        Ok(match v {
            ResourceAccess::Field(v) => ResourceAccess::Field(field(v, replace)?),
            ResourceAccess::Predicate(v) => ResourceAccess::Predicate(predicate(v, replace)?),
            ResourceAccess::MagicWand(v) => ResourceAccess::MagicWand(wand(v, replace)?),
        })
    }
    let exp = |e: &Exp| replace(e);
    let exps = |es: &[Exp]| es.iter().map(exp).collect::<Result<Vec<_>, _>>();
    let kind = match stmt.kind() {
        StmtKind::NewStmt { lhs, fields } => StmtKind::NewStmt {
            lhs: local(lhs, replace)?,
            fields: fields.clone(),
        },
        StmtKind::LocalVarAssign { lhs, rhs } => StmtKind::LocalVarAssign {
            lhs: local(lhs, replace)?,
            rhs: exp(rhs)?,
        },
        StmtKind::FieldAssign { lhs, rhs } => StmtKind::FieldAssign {
            lhs: field(lhs, replace)?,
            rhs: exp(rhs)?,
        },
        StmtKind::MethodCall {
            method_name,
            args,
            targets,
        } => StmtKind::MethodCall {
            method_name: method_name.clone(),
            args: exps(args)?,
            targets: targets
                .iter()
                .map(|v| local(v, replace))
                .collect::<Result<_, _>>()?,
        },
        StmtKind::Exhale(e) => StmtKind::Exhale(exp(e)?),
        StmtKind::Inhale(e) => StmtKind::Inhale(exp(e)?),
        StmtKind::Assert(e) => StmtKind::Assert(exp(e)?),
        StmtKind::Assume(e) => StmtKind::Assume(exp(e)?),
        StmtKind::Fold(v) => StmtKind::Fold(access(v, replace)?),
        StmtKind::Unfold(v) => StmtKind::Unfold(access(v, replace)?),
        StmtKind::Package {
            wand: w,
            proof_script,
        } => StmtKind::Package {
            wand: wand(w, replace)?,
            proof_script: map_expression_roots_with_extensions(proof_script, replace, extension)?,
        },
        StmtKind::Apply(w) => StmtKind::Apply(wand(w, replace)?),
        StmtKind::Seqn {
            statements,
            declarations,
        } => {
            if declarations
                .iter()
                .any(|d| !matches!(d, Declaration::Local(_) | Declaration::Label(_)))
            {
                return Err(StatementReplacementError::NestedDeclaration.into());
            }
            StmtKind::Seqn {
                statements: statements
                    .iter()
                    .map(|s| map_expression_roots_with_extensions(s, replace, extension))
                    .collect::<Result<_, _>>()?,
                declarations: declarations
                    .iter()
                    .map(|d| -> Result<Declaration, E> {
                        match d {
                            Declaration::Local(v) => Ok(Declaration::Local(v.clone())),
                            Declaration::Label(v) => {
                                let invariants = exps(&v.invariants)?;
                                Ok(Declaration::Label(if invariants == v.invariants {
                                    v.clone()
                                } else {
                                    v.copy_with(|label| label.invariants = invariants)
                                }))
                            }
                            _ => Err(StatementReplacementError::NestedDeclaration.into()),
                        }
                    })
                    .collect::<Result<_, _>>()?,
            }
        }
        StmtKind::If {
            condition,
            then_branch,
            else_branch,
        } => StmtKind::If {
            condition: exp(condition)?,
            then_branch: map_expression_roots_with_extensions(then_branch, replace, extension)?,
            else_branch: map_expression_roots_with_extensions(else_branch, replace, extension)?,
        },
        StmtKind::While {
            condition,
            invariants,
            body,
        } => StmtKind::While {
            condition: exp(condition)?,
            invariants: exps(invariants)?,
            body: map_expression_roots_with_extensions(body, replace, extension)?,
        },
        StmtKind::Label(label) => {
            let invariants = exps(&label.invariants)?;
            StmtKind::Label(if invariants == label.invariants {
                label.clone()
            } else {
                label.copy_with(|d| d.invariants = invariants)
            })
        }
        StmtKind::Goto(name) => StmtKind::Goto(name.clone()),
        StmtKind::LocalVarDeclStmt(v) => StmtKind::LocalVarDeclStmt(v.clone()),
        StmtKind::Quasihavoc { guard, resource: r } => StmtKind::Quasihavoc {
            guard: guard.as_ref().map(exp).transpose()?,
            resource: resource(r, replace)?,
        },
        StmtKind::Quasihavocall {
            variables,
            guard,
            resource: r,
        } => StmtKind::Quasihavocall {
            variables: variables.clone(),
            guard: guard.as_ref().map(exp).transpose()?,
            resource: resource(r, replace)?,
        },
        StmtKind::Extension(value) => StmtKind::Extension(extension(value, replace)?),
    };
    Ok(if &kind == stmt.kind() {
        stmt.clone()
    } else {
        Stmt::new(kind, stmt.metadata().clone())
    })
}

/// Preorder statement/product-node rewriting with typed field and declaration slots.
pub fn map_statement_tree_with_extensions<E: From<StatementReplacementError>>(
    stmt: &Stmt,
    replace: &dyn Fn(&crate::ast::expression::Exp) -> Result<crate::ast::expression::Exp, E>,
    pre: &dyn Fn(&super::nodes::Node) -> Result<super::nodes::Node, E>,
    child: &dyn Fn(&super::nodes::Node) -> Result<super::nodes::Node, E>,
    extension: &dyn Fn(
        &crate::ast::statement::ExtensionStmtHandle,
        &dyn Fn(&crate::ast::expression::Exp) -> Result<crate::ast::expression::Exp, E>,
    ) -> Result<crate::ast::statement::ExtensionStmtHandle, E>,
) -> Result<Stmt, E> {
    map_statement_tree_with_post(stmt, replace, pre, child, extension, None, false)
}

pub fn map_statement_tree_with_post<E: From<StatementReplacementError>>(
    stmt: &Stmt,
    replace: &dyn Fn(&crate::ast::expression::Exp) -> Result<crate::ast::expression::Exp, E>,
    pre: &dyn Fn(&super::nodes::Node) -> Result<super::nodes::Node, E>,
    child: &dyn Fn(&super::nodes::Node) -> Result<super::nodes::Node, E>,
    extension: &dyn Fn(
        &crate::ast::statement::ExtensionStmtHandle,
        &dyn Fn(&crate::ast::expression::Exp) -> Result<crate::ast::expression::Exp, E>,
    ) -> Result<crate::ast::statement::ExtensionStmtHandle, E>,
    post: Option<&dyn Fn(&super::nodes::Node) -> Result<super::nodes::Node, E>>,
    force_copy: bool,
) -> Result<Stmt, E> {
    use crate::ast::expression::{Exp, ExpKind};
    use crate::ast::statement::{PredicateAccessPredicate, ResourceAccess};
    fn local<E: From<StatementReplacementError>>(
        v: &LocalVar,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<LocalVar, E> {
        let e = Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone());
        let result = replace(&e)?;
        if let ExpKind::LocalVar(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidLocalVar.into())
        }
    }
    fn field<E: From<StatementReplacementError>>(
        v: &crate::ast::expression::FieldAccess,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<crate::ast::expression::FieldAccess, E> {
        let e = Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone());
        let result = replace(&e)?;
        if let ExpKind::FieldAccess(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidFieldAccess.into())
        }
    }
    fn predicate<E: From<StatementReplacementError>>(
        v: &crate::ast::expression::PredicateAccess,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<crate::ast::expression::PredicateAccess, E> {
        let e = Exp::new(ExpKind::PredicateAccess(v.clone()), v.meta.clone());
        let result = replace(&e)?;
        if let ExpKind::PredicateAccess(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidPredicateAccess.into())
        }
    }
    fn access<E: From<StatementReplacementError>>(
        v: &PredicateAccessPredicate,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<PredicateAccessPredicate, E> {
        let e = Exp::new(ExpKind::PredicateAccessPredicate(v.clone()), v.meta.clone());
        let result = replace(&e)?;
        if let ExpKind::PredicateAccessPredicate(v) = result.kind() {
            Ok(v.clone())
        } else {
            Err(StatementReplacementError::InvalidAccessPredicate.into())
        }
    }
    fn wand<E: From<StatementReplacementError>>(
        v: &Exp,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<Exp, E> {
        let result = replace(v)?;
        if matches!(result.kind(), ExpKind::MagicWand(..)) {
            Ok(result)
        } else {
            Err(StatementReplacementError::InvalidMagicWand.into())
        }
    }
    fn resource<E: From<StatementReplacementError>>(
        v: &ResourceAccess,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<ResourceAccess, E> {
        Ok(match v {
            ResourceAccess::Field(v) => ResourceAccess::Field(field(v, replace)?),
            ResourceAccess::Predicate(v) => ResourceAccess::Predicate(predicate(v, replace)?),
            ResourceAccess::MagicWand(v) => ResourceAccess::MagicWand(wand(v, replace)?),
        })
    }
    use super::nodes::Node;
    use crate::ast::program::Member;
    let view = match stmt.kind() {
        StmtKind::Label(v) => Node::LabelDecl(v.clone()),
        _ => Node::Stmt(stmt.clone()),
    };
    let mapped = match pre(&view)? {
        Node::Stmt(stmt) => stmt,
        Node::LabelDecl(label) => Stmt::new(StmtKind::Label(label.clone()), label.meta.clone()),
        _ => return Err(StatementReplacementError::InvalidStatement.into()),
    };
    let stmt = &mapped;
    let map_local_decl = |v: &crate::ast::program::LocalVarDecl| -> Result<_, E> {
        match child(&Node::LocalDecl(v.clone()))? {
            Node::LocalDecl(v) => Ok(v),
            _ => Err(StatementReplacementError::InvalidDeclaration.into()),
        }
    };
    let map_label = |v: &crate::ast::program::LabelDeclaration| -> Result<_, E> {
        match child(&Node::LabelDecl(v.clone()))? {
            Node::LabelDecl(v) => Ok(v),
            Node::Stmt(s) => match s.kind() {
                StmtKind::Label(v) => Ok(v.clone()),
                _ => Err(StatementReplacementError::InvalidDeclaration.into()),
            },
            _ => Err(StatementReplacementError::InvalidDeclaration.into()),
        }
    };
    let exp = |e: &Exp| replace(e);
    let exps = |es: &[Exp]| es.iter().map(exp).collect::<Result<Vec<_>, _>>();
    let kind = match stmt.kind() {
        StmtKind::NewStmt { lhs, fields } => StmtKind::NewStmt {
            lhs: local(lhs, replace)?,
            fields: fields
                .iter()
                .map(|v| match child(&Node::Member(Member::Field(v.clone())))? {
                    Node::Member(Member::Field(v)) => Ok(v),
                    _ => Err(StatementReplacementError::InvalidField.into()),
                })
                .collect::<Result<Vec<_>, E>>()?,
        },
        StmtKind::LocalVarAssign { lhs, rhs } => StmtKind::LocalVarAssign {
            lhs: local(lhs, replace)?,
            rhs: exp(rhs)?,
        },
        StmtKind::FieldAssign { lhs, rhs } => StmtKind::FieldAssign {
            lhs: field(lhs, replace)?,
            rhs: exp(rhs)?,
        },
        StmtKind::MethodCall {
            method_name,
            args,
            targets,
        } => StmtKind::MethodCall {
            method_name: method_name.clone(),
            args: exps(args)?,
            targets: targets
                .iter()
                .map(|v| local(v, replace))
                .collect::<Result<_, _>>()?,
        },
        StmtKind::Exhale(e) => StmtKind::Exhale(exp(e)?),
        StmtKind::Inhale(e) => StmtKind::Inhale(exp(e)?),
        StmtKind::Assert(e) => StmtKind::Assert(exp(e)?),
        StmtKind::Assume(e) => StmtKind::Assume(exp(e)?),
        StmtKind::Fold(v) => StmtKind::Fold(access(v, replace)?),
        StmtKind::Unfold(v) => StmtKind::Unfold(access(v, replace)?),
        StmtKind::Package {
            wand: w,
            proof_script,
        } => StmtKind::Package {
            wand: wand(w, replace)?,
            proof_script: map_statement_tree_with_post(
                proof_script,
                replace,
                pre,
                child,
                extension,
                post,
                force_copy,
            )?,
        },
        StmtKind::Apply(w) => StmtKind::Apply(wand(w, replace)?),
        StmtKind::Seqn {
            statements,
            declarations,
        } => StmtKind::Seqn {
            statements: statements
                .iter()
                .map(|s| {
                    map_statement_tree_with_post(
                        s, replace, pre, child, extension, post, force_copy,
                    )
                })
                .collect::<Result<_, _>>()?,
            declarations: declarations
                .iter()
                .map(|d| -> Result<Declaration, E> {
                    match d {
                        Declaration::Local(v) => Ok(Declaration::Local(map_local_decl(v)?)),
                        Declaration::Label(v) => Ok(Declaration::Label(map_label(v)?)),
                        Declaration::Field(v) => {
                            match child(&Node::Member(Member::Field(v.clone())))? {
                                Node::Member(Member::Field(v)) => Ok(Declaration::Field(v)),
                                _ => Err(StatementReplacementError::InvalidDeclaration.into()),
                            }
                        }
                        Declaration::Predicate(v) => {
                            match child(&Node::Member(Member::Predicate(v.clone())))? {
                                Node::Member(Member::Predicate(v)) => Ok(Declaration::Predicate(v)),
                                _ => Err(StatementReplacementError::InvalidDeclaration.into()),
                            }
                        }
                        Declaration::Method(v) => {
                            match child(&Node::Member(Member::Method(v.clone())))? {
                                Node::Member(Member::Method(v)) => Ok(Declaration::Method(v)),
                                _ => Err(StatementReplacementError::InvalidDeclaration.into()),
                            }
                        }
                        Declaration::Function(v) => {
                            match child(&Node::Member(Member::Function(v.clone())))? {
                                Node::Member(Member::Function(v)) => Ok(Declaration::Function(v)),
                                _ => Err(StatementReplacementError::InvalidDeclaration.into()),
                            }
                        }
                        Declaration::Domain(v) => {
                            match child(&Node::Member(Member::Domain(v.clone())))? {
                                Node::Member(Member::Domain(v)) => Ok(Declaration::Domain(v)),
                                _ => Err(StatementReplacementError::InvalidDeclaration.into()),
                            }
                        }
                        Declaration::DomainFunc(v) => match child(&Node::DomainFunc(v.clone()))? {
                            Node::DomainFunc(v) => Ok(Declaration::DomainFunc(v)),
                            _ => Err(StatementReplacementError::InvalidDeclaration.into()),
                        },
                        Declaration::NamedDomainAxiom(v) => {
                            match child(&Node::DomainAxiom(v.clone()))? {
                                Node::DomainAxiom(v)
                                    if matches!(
                                        v.kind(),
                                        crate::ast::program::DomainAxiomKind::Named { .. }
                                    ) =>
                                {
                                    Ok(Declaration::NamedDomainAxiom(v))
                                }
                                _ => Err(StatementReplacementError::InvalidDeclaration.into()),
                            }
                        }
                        Declaration::Extension(_) => {
                            Err(StatementReplacementError::NestedDeclaration.into())
                        }
                    }
                })
                .collect::<Result<_, _>>()?,
        },
        StmtKind::If {
            condition,
            then_branch,
            else_branch,
        } => StmtKind::If {
            condition: exp(condition)?,
            then_branch: map_statement_tree_with_post(
                then_branch,
                replace,
                pre,
                child,
                extension,
                post,
                force_copy,
            )?,
            else_branch: map_statement_tree_with_post(
                else_branch,
                replace,
                pre,
                child,
                extension,
                post,
                force_copy,
            )?,
        },
        StmtKind::While {
            condition,
            invariants,
            body,
        } => StmtKind::While {
            condition: exp(condition)?,
            invariants: exps(invariants)?,
            body: map_statement_tree_with_post(
                body, replace, pre, child, extension, post, force_copy,
            )?,
        },
        StmtKind::Label(label) => {
            let invariants = exps(&label.invariants)?;
            StmtKind::Label(if !force_copy && invariants == label.invariants {
                label.clone()
            } else {
                label.copy_with(|d| d.invariants = invariants)
            })
        }
        StmtKind::Goto(name) => StmtKind::Goto(name.clone()),
        StmtKind::LocalVarDeclStmt(v) => StmtKind::LocalVarDeclStmt(map_local_decl(v)?),
        StmtKind::Quasihavoc { guard, resource: r } => StmtKind::Quasihavoc {
            guard: guard.as_ref().map(exp).transpose()?,
            resource: resource(r, replace)?,
        },
        StmtKind::Quasihavocall {
            variables,
            guard,
            resource: r,
        } => StmtKind::Quasihavocall {
            variables: variables
                .iter()
                .map(map_local_decl)
                .collect::<Result<Vec<_>, _>>()?,
            guard: guard.as_ref().map(exp).transpose()?,
            resource: resource(r, replace)?,
        },
        StmtKind::Extension(value) => StmtKind::Extension(extension(value, replace)?),
    };
    let rebuilt = if !force_copy && &kind == stmt.kind() {
        stmt.clone()
    } else {
        Stmt::new(kind, stmt.metadata().clone())
    };
    if let Some(post) = post {
        let view = match rebuilt.kind() {
            StmtKind::Label(label) => Node::LabelDecl(label.clone()),
            _ => Node::Stmt(rebuilt.clone()),
        };
        match post(&view)? {
            Node::Stmt(stmt) => Ok(stmt),
            Node::LabelDecl(label) => Ok(Stmt::new(
                StmtKind::Label(label.clone()),
                label.meta.clone(),
            )),
            _ => Err(StatementReplacementError::InvalidStatement.into()),
        }
    } else {
        Ok(rebuilt)
    }
}

#[cfg(test)]
mod replacement_tests {
    use super::*;
    use crate::ast::{expression::Exp, program::LabelDeclaration};
    #[test]
    fn replaces_inside_statement_and_scoped_label() {
        let m = Metadata::default();
        let yes = Exp::new(ExpKind::TrueLit, m.clone());
        let no = Exp::new(ExpKind::FalseLit, m.clone());
        let s = Stmt::new(
            StmtKind::Seqn {
                statements: vec![Stmt::new(StmtKind::Assert(yes.clone()), m.clone())],
                declarations: vec![Declaration::Label(LabelDeclaration::new(
                    crate::ast::program::LabelDeclarationData {
                        name: "l".into(),
                        invariants: vec![yes.clone()],
                        meta: m.clone(),
                    },
                ))],
            },
            m,
        );
        let updated = replace_expressions(&s, &[(yes, no.clone())]).unwrap();
        let StmtKind::Seqn {
            statements,
            declarations,
        } = updated.kind()
        else {
            panic!("sequence")
        };
        assert!(matches!(statements[0].kind(),StmtKind::Assert(e) if e==&no));
        assert!(matches!(&declarations[0],Declaration::Label(l) if l.invariants==vec![no]));
    }
}
