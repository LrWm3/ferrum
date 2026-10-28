//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/smoke/UnreachableASTExtension.scala
//!
//! Purpose:
//! Represent the smoke-detection unreachable marker in the verification AST.
//!
//! Planned Rust structure:
//! Port Unreachable extension statement, metadata and pretty printer; it has no subnodes.
//!
//! Behavior to preserve:
//! Preserve source position and marker until smoke preprocessing removes it.
//!
//! Integration:
//! smoke_detection_plugin and unreachable_past_extension; ast statement/metadata and pretty
//! printer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for extension node and position ownership.
//!
//! Open decisions:
//! Agree on extension elimination before verification with smoke_detection_plugin.
//!
//! Status: partial; typed extension and translation adapter implemented. Parser and
//! smoke plugin integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use crate::ast::ast::Metadata;
use crate::ast::statement::{ExtensionStmt, ExtensionStmtHandle, Stmt, StmtKind};
use crate::ast::utility::nodes::{Node, TraversalError};
use std::any::Any;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct Unreachable {
    pub meta: Metadata,
}
impl Unreachable {
    pub fn statement(self) -> Stmt {
        let meta = self.meta.clone();
        Stmt::new(
            StmtKind::Extension(ExtensionStmtHandle(Arc::new(self))),
            meta,
        )
    }
    pub fn pretty(&self) -> &'static str {
        "unreachable"
    }
}
impl ExtensionStmt for Unreachable {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionStmt) -> bool {
        other.as_any().is::<Self>()
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        Ok(Vec::new())
    }
}
