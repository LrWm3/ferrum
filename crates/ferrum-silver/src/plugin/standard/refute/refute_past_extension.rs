//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/refute/RefutePASTExtension.scala
//!
//! Purpose:
//! Parse-tree representation of refute statements.
//!
//! Planned Rust structure:
//! Represent PRefuteKeyword and PRefute with typecheck and translateStmt hooks.
//!
//! Behavior to preserve:
//! Typecheck expression as Bool and translate to Refute preserving source position.
//!
//! Integration:
//! parser::fast_parser, resolver and translator; plugin::standard::refute::refute_ast_extension
//! and refute_plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser extension and position conversion.
//!
//! Open decisions:
//! Reconcile extension registration and parse-tree ownership with parser and refute_plugin.
//!
//! Status: partial; source keyword/node, Bool-check and translation adapters are implemented.
//! Parser registration and concrete typechecker/translator callbacks remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use super::refute_ast_extension::Refute;
use crate::ast::ast::Metadata;
use crate::ast::expression::Exp;
use crate::ast::statement::Stmt;
use crate::parser::parse_ast::{
    PExpHandle, PExtender, PNodeHandle, PStatement, PStatementKind, PStmtHandle,
};
use crate::parser::parse_ast_keyword::{
    PExtensionKeyword, PExtensionKeywordCategory, PReserved, Span,
};
use std::sync::Arc;

pub fn refute_keyword(pos: Span) -> PReserved<PExtensionKeyword> {
    PReserved::new(
        PExtensionKeyword {
            spelling: "refute".into(),
            category: PExtensionKeywordCategory::Statement,
        },
        pos,
    )
}
#[derive(Clone, Debug)]
pub struct PRefute {
    pub keyword: PReserved<PExtensionKeyword>,
    pub expression: PExpHandle,
    pub pos: Span,
}
impl PExtender for PRefute {
    fn subnodes(&self) -> Vec<PNodeHandle> {
        vec![self.keyword.node().clone(), self.expression.node().clone()]
    }
}
impl PRefute {
    pub fn statement(self) -> PStmtHandle {
        let pos = self.pos.clone();
        PStmtHandle::new(
            PStatement {
                kind: PStatementKind::Extension(Arc::new(self)),
            },
            pos,
        )
    }
    /// The typechecker callback must perform its ordinary Bool check and report failures.
    pub fn typecheck<E>(
        &self,
        check_bool: impl FnOnce(&PExpHandle) -> Result<(), E>,
    ) -> Result<(), E> {
        check_bool(&self.expression)
    }
    pub fn translate<E>(
        &self,
        translate: impl FnOnce(&PExpHandle) -> Result<Exp, E>,
        lift_metadata: impl FnOnce(&Span) -> Metadata,
    ) -> Result<Stmt, E> {
        Ok(Refute::new(translate(&self.expression)?, lift_metadata(&self.pos)).statement())
    }
}
