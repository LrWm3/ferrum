//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/refute/RefuteASTExtension.scala
//!
//! Purpose:
//! Represent refute statements and mark their lowered assertions.
//!
//! Planned Rust structure:
//! Port Refute extension statement and RefuteInfo failure-expected metadata; provide pretty
//! printing and expression subnode.
//!
//! Behavior to preserve:
//! Keep positions, info and error transformation on Refute; RefuteInfo associates each lowered
//! assertion with its source statement.
//!
//! Integration:
//! plugin::standard::refute::refute_plugin, refute_errors and parser extension; ast statement,
//! info and pretty printer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for AST handles and metadata.
//!
//! Open decisions:
//! Agree on metadata identity and source node lifetime with refute_plugin and ast.
//!
//! Status: partial; refute statement and metadata extension implemented. Source printer
//! and failure-expected marker integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use crate::ast::ast::{ExtensionInfo, Metadata};
use crate::ast::expression::Exp;
use crate::ast::statement::{ExtensionStmt, ExtensionStmtHandle, Stmt, StmtKind};
use crate::ast::utility::nodes::{Node, TraversalError};
use std::any::Any;
use std::sync::Arc;

/// Refute's case-class equality compares the expression, excluding metadata.
#[derive(Clone, Debug)]
pub struct Refute {
    pub exp: Exp,
    pub meta: Metadata,
}
impl Refute {
    pub fn new(exp: Exp, meta: Metadata) -> Self {
        Self { exp, meta }
    }
    pub fn statement(self) -> Stmt {
        let meta = self.meta.clone();
        Stmt::new(
            StmtKind::Extension(ExtensionStmtHandle(Arc::new(self))),
            meta,
        )
    }
    /// The callback must use the pretty printer's expression-parenthesization rules.
    pub fn pretty(&self, print_parenthesized_exp: impl FnOnce(&Exp) -> String) -> String {
        format!("refute {}", print_parenthesized_exp(&self.exp))
    }
}
impl ExtensionStmt for Refute {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionStmt) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|other| self.exp == other.exp)
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        Ok(vec![Node::Exp(self.exp.clone())])
    }
}
#[derive(Clone, Debug)]
pub struct RefuteInfo {
    pub refute: Refute,
}
impl ExtensionInfo for RefuteInfo {
    fn as_any(&self) -> &dyn Any {
        self
    }
}
