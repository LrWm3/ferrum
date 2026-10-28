//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/sif/SIFAstExtensions.scala
//!
//! Purpose:
//! Define relational expressions and frontend control-flow extensions used by the SIF product
//! transformation.
//!
//! Planned Rust structure:
//! Port SIFLowExp, SIFLowEventExp, SIFRelExp, SIFLowExitExp and SIFTerminatesExp;
//! return/break/continue/raise, exception handler/try-catch, declassify, inlined-call and
//! assert-no-exception statements; SIFInfo and SIFDynCheckInfo.
//!
//! Behavior to preserve:
//! Preserve expression types and purity, optional low comparator/type map, execution index and all
//! subnodes/metadata. Control-flow extensions beyond low/rel have no parser in SIFPlugin. Direct
//! verification of relational expression extensions is unimplemented and requires transformation.
//! Preserve try-catch subnode traversal as written.
//!
//! Integration:
//! sif_plugin, sifp_ast_extensions and sif_extended_transformer; ast::{expression,statement,ast} metadata and pretty printer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for metadata, node identity and extension dispatch.
//!
//! Open decisions:
//! Agree on frontend-created extension ownership, comparator signatures and direct-verification
//! failure with AST and verifier.
//!
//! Status: partial; SIF expression, statement and metadata variants are represented with ordered
//! children. Nested statement reconstruction and SIF transformations remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2025 ETH Zurich.

use crate::ast::ast::{ExtensionInfo, Metadata};
use crate::ast::expression::{Exp, ExpKind, ExtensionExp, ExtensionExpHandle};
use crate::ast::r#type::{Type, TypeSubstitution};
use crate::ast::utility::nodes::{Node, TraversalError};
use crate::verifier::verification_result::DiagnosticError;
use std::{any::Any, sync::Arc};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SifExpressionKind {
    Low {
        exp: Exp,
        comparator: Option<String>,
        type_variables: TypeSubstitution,
    },
    LowEvent,
    Rel {
        exp: Exp,
        index: Exp,
    },
    LowExit,
    Terminates {
        condition: Exp,
    },
}
#[derive(Clone, Debug)]
pub struct SifExpression {
    pub kind: SifExpressionKind,
    pub meta: Metadata,
}
impl SifExpression {
    pub fn expression(self) -> Result<Exp, DiagnosticError> {
        if let SifExpressionKind::Rel { index, .. } = &self.kind {
            if !matches!(index.kind(), ExpKind::IntLit(_)) {
                return Err(DiagnosticError::InvalidNode(
                    "SIF rel index must be an integer literal",
                ));
            }
        }
        let meta = self.meta.clone();
        Ok(Exp::new(
            ExpKind::Extension(ExtensionExpHandle(Arc::new(self))),
            meta,
        ))
    }
    pub fn pretty(&self, render: &impl Fn(&Exp) -> String) -> String {
        match &self.kind {
            SifExpressionKind::Low {
                exp, comparator, ..
            } => format!(
                "{}({})",
                if comparator.is_some() {
                    "lowVal"
                } else {
                    "low"
                },
                render(exp)
            ),
            SifExpressionKind::LowEvent => "lowEvent".into(),
            SifExpressionKind::Rel { exp, index } => {
                format!("rel({}, {})", render(exp), render(index))
            }
            SifExpressionKind::LowExit => "lowExit".into(),
            SifExpressionKind::Terminates { condition } => {
                format!("terminates under condition {}", render(condition))
            }
        }
    }
    pub fn verify_unlowered(&self) -> Result<(), &'static str> {
        Err(match self.kind {
            SifExpressionKind::Low { .. } => "SIFLowExp: verifyExtExp has not been implemented.",
            SifExpressionKind::LowEvent => "SIFLowEventExp: verifyExtExp has not been implemented.",
            SifExpressionKind::Rel { .. } => "SIFRelExp: verifyExtExp has not been implemented.",
            SifExpressionKind::LowExit => "SIFLowExitExp: verifyExtExp has not been implemented.",
            SifExpressionKind::Terminates { .. } => {
                "SIFTerminatesExp: verifyExtExp has not been implemented."
            }
        })
    }
}
impl ExtensionExp for SifExpression {
    fn metadata(&self) -> &Metadata {
        &self.meta
    }
    fn with_metadata(&self, meta: Metadata) -> ExtensionExpHandle {
        let mut copy = self.clone();
        copy.meta = meta;
        ExtensionExpHandle(Arc::new(copy))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionExp) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|o| self.kind == o.kind)
    }
    fn typ(&self) -> Type {
        match &self.kind {
            SifExpressionKind::Rel { exp, .. } => exp.typ().expect("typed SIF rel expression"),
            _ => Type::Bool,
        }
    }
    fn is_pure(&self) -> bool {
        match &self.kind {
            SifExpressionKind::Low { exp, .. } | SifExpressionKind::Rel { exp, .. } => {
                exp.is_pure()
            }
            SifExpressionKind::Terminates { condition } => condition.is_pure(),
            SifExpressionKind::LowEvent => true,
            SifExpressionKind::LowExit => false,
        }
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        Ok(match &self.kind {
            SifExpressionKind::Low { exp, .. } => vec![Node::Exp(exp.clone())],
            SifExpressionKind::Rel { exp, index } => {
                vec![Node::Exp(exp.clone()), Node::Exp(index.clone())]
            }
            SifExpressionKind::Terminates { condition } => vec![Node::Exp(condition.clone())],
            _ => vec![],
        })
    }
    fn map_expressions(
        &self,
        map: &dyn Fn(&Exp) -> Result<Exp, DiagnosticError>,
    ) -> Result<ExtensionExpHandle, DiagnosticError> {
        let kind = match &self.kind {
            SifExpressionKind::Low {
                exp,
                comparator,
                type_variables,
            } => SifExpressionKind::Low {
                exp: map(exp)?,
                comparator: comparator.clone(),
                type_variables: type_variables.clone(),
            },
            SifExpressionKind::Rel { exp, index } => {
                let exp = map(exp)?;
                let index = map(index)?;
                if !matches!(index.kind(), ExpKind::IntLit(_)) {
                    return Err(DiagnosticError::InvalidNode(
                        "SIF rel index must be an integer literal",
                    ));
                }
                SifExpressionKind::Rel { exp, index }
            }
            SifExpressionKind::Terminates { condition } => SifExpressionKind::Terminates {
                condition: map(condition)?,
            },
            kind => kind.clone(),
        };
        Ok(ExtensionExpHandle(Arc::new(Self {
            kind,
            meta: self.meta.clone(),
        })))
    }
}
#[derive(Clone, Debug)]
pub struct SifInfo {
    pub comments: Vec<String>,
    pub continue_unaware: bool,
    pub obligation_var: bool,
}
impl ExtensionInfo for SifInfo {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn comments(&self) -> Vec<String> {
        self.comments.clone()
    }
}
#[derive(Clone, Debug)]
pub struct SifDynCheckInfo {
    pub comments: Vec<String>,
    pub dyn_check: Exp,
    pub only_dyn_version: bool,
}
impl ExtensionInfo for SifDynCheckInfo {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn comments(&self) -> Vec<String> {
        self.comments.clone()
    }
}

#[derive(Clone, Debug)]
pub struct SifExceptionHandler {
    pub error_var: crate::ast::expression::LocalVar,
    pub exception: Exp,
    pub body: crate::ast::statement::Stmt,
    pub meta: Metadata,
}
impl PartialEq for SifExceptionHandler {
    fn eq(&self, other: &Self) -> bool {
        self.error_var == other.error_var
            && self.exception == other.exception
            && self.body == other.body
    }
}
impl Eq for SifExceptionHandler {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SifStatementKind {
    Return {
        exp: Option<Exp>,
        result_var: Option<crate::ast::expression::LocalVar>,
    },
    Break,
    Continue,
    Raise {
        assignment: Option<crate::ast::statement::Stmt>,
    },
    ExceptionHandler(SifExceptionHandler),
    TryCatch {
        body: crate::ast::statement::Stmt,
        handlers: Vec<SifExceptionHandler>,
        else_block: Option<crate::ast::statement::Stmt>,
        finally_block: Option<crate::ast::statement::Stmt>,
    },
    Declassify(Exp),
    InlinedCall(crate::ast::statement::Stmt),
    AssertNoException,
}
#[derive(Clone, Debug)]
pub struct SifStatement {
    pub kind: SifStatementKind,
    pub meta: Metadata,
}
impl SifStatement {
    pub fn statement(self) -> Result<crate::ast::statement::Stmt, DiagnosticError> {
        use crate::ast::statement::{ExtensionStmtHandle, Stmt, StmtKind};
        let is_seq = |s: &Stmt| matches!(s.kind(), StmtKind::Seqn { .. });
        match &self.kind {
            SifStatementKind::Raise {
                assignment: Some(s),
            } if !matches!(s.kind(), StmtKind::LocalVarAssign { .. }) => {
                return Err(DiagnosticError::InvalidNode("SIF raise assignment"));
            }
            SifStatementKind::ExceptionHandler(h) if !is_seq(&h.body) => {
                return Err(DiagnosticError::InvalidNode("SIF handler body"));
            }
            SifStatementKind::TryCatch {
                body,
                handlers,
                else_block,
                finally_block,
            } if !is_seq(body)
                || handlers.iter().any(|h| !is_seq(&h.body))
                || else_block.as_ref().is_some_and(|s| !is_seq(s))
                || finally_block.as_ref().is_some_and(|s| !is_seq(s)) =>
            {
                return Err(DiagnosticError::InvalidNode("SIF try/catch block"));
            }
            SifStatementKind::InlinedCall(s) if !is_seq(s) => {
                return Err(DiagnosticError::InvalidNode("SIF inlined call block"));
            }
            _ => {}
        }
        let meta = self.meta.clone();
        Ok(Stmt::new(
            StmtKind::Extension(ExtensionStmtHandle(Arc::new(self))),
            meta,
        ))
    }
    pub fn verify_unlowered(&self) -> Result<(), &'static str> {
        Err("SIF statement must be transformed before verification")
    }
}
impl crate::ast::statement::ExtensionStmt for SifStatement {
    fn metadata(&self) -> &Metadata {
        &self.meta
    }
    fn with_metadata(&self, meta: Metadata) -> crate::ast::statement::ExtensionStmtHandle {
        let mut copy = self.clone();
        copy.meta = meta;
        crate::ast::statement::ExtensionStmtHandle(Arc::new(copy))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn crate::ast::statement::ExtensionStmt) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|o| self.kind == o.kind)
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        use SifStatementKind::*;
        let handler = |h: &SifExceptionHandler| {
            vec![
                Node::LocalVar(h.error_var.clone()),
                Node::Exp(h.exception.clone()),
                Node::Stmt(h.body.clone()),
            ]
        };
        Ok(match &self.kind {
            Return { exp, result_var } => exp
                .iter()
                .cloned()
                .map(Node::Exp)
                .chain(result_var.iter().cloned().map(Node::LocalVar))
                .collect(),
            Raise { assignment } => assignment.iter().cloned().map(Node::Stmt).collect(),
            ExceptionHandler(h) => handler(h),
            TryCatch {
                body,
                handlers,
                else_block,
                finally_block,
            } => std::iter::once(Node::Stmt(body.clone()))
                .chain(else_block.iter().cloned().map(Node::Stmt))
                .chain(finally_block.iter().cloned().map(Node::Stmt))
                .chain(handlers.iter().flat_map(handler))
                .collect(),
            Declassify(exp) => vec![Node::Exp(exp.clone())],
            InlinedCall(body) => vec![Node::Stmt(body.clone())],
            Break | Continue | AssertNoException => vec![],
        })
    }
    fn map_expressions(
        &self,
        map: &dyn Fn(&Exp) -> Result<Exp, DiagnosticError>,
    ) -> Result<crate::ast::statement::ExtensionStmtHandle, DiagnosticError> {
        use SifStatementKind::*;
        let kind = match &self.kind {
            Return { exp, result_var } => {
                let exp = exp.as_ref().map(map).transpose()?;
                let result_var = result_var
                    .as_ref()
                    .map(|v| {
                        let e = Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone());
                        let e = map(&e)?;
                        match e.kind() {
                            ExpKind::LocalVar(v) => Ok(v.clone()),
                            _ => Err(DiagnosticError::InvalidNode("SIF return result variable")),
                        }
                    })
                    .transpose()?;
                Return { exp, result_var }
            }
            Declassify(exp) => Declassify(map(exp)?),
            Break => Break,
            Continue => Continue,
            AssertNoException => AssertNoException,
            _ => {
                return Err(DiagnosticError::Unsupported(
                    "SIF nested statement reconstruction",
                ));
            }
        };
        Ok(crate::ast::statement::ExtensionStmtHandle(Arc::new(Self {
            kind,
            meta: self.meta.clone(),
        })))
    }
}
