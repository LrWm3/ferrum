//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/smoke/UnreachablePASTExtension.scala
//!
//! Purpose:
//! Represent the unreachable marker in the parse AST.
//!
//! Planned Rust structure:
//! Port PUnreachableKeyword and PUnreachable typecheck and translateStmt hooks.
//!
//! Behavior to preserve:
//! Typechecking adds no diagnostics; translation retains source position in Unreachable.
//!
//! Integration:
//! parser::fast_parser, resolver and translator; smoke::unreachable_ast_extension and
//! smoke_detection_plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser extensions and positions.
//!
//! Open decisions:
//! Agree on native parser registration with fast_parser.
//!
//! Status: partial; typed extension and translation adapter implemented. Parser and
//! smoke plugin integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use super::unreachable_ast_extension::Unreachable;
use crate::ast::ast::Metadata;
use crate::ast::statement::Stmt;
use crate::parser::parse_ast::{PExtender, PNodeHandle, PStatement, PStatementKind, PStmtHandle};
use crate::parser::parse_ast_keyword::{
    PExtensionKeyword, PExtensionKeywordCategory, PReserved, Span,
};
use std::sync::Arc;

pub fn unreachable_keyword(pos: Span) -> PReserved<PExtensionKeyword> {
    PReserved::new(
        PExtensionKeyword {
            spelling: "unreachable".into(),
            category: PExtensionKeywordCategory::Statement,
        },
        pos,
    )
}
#[derive(Clone, Debug)]
pub struct PUnreachable {
    pub keyword: PReserved<PExtensionKeyword>,
    pub pos: Span,
}
impl PExtender for PUnreachable {
    fn reformat_as_product(&self) -> bool {
        true
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        vec![self.keyword.node().clone()]
    }
}
impl PUnreachable {
    pub fn statement(self) -> PStmtHandle {
        let pos = self.pos.clone();
        PStmtHandle::new(
            PStatement {
                kind: PStatementKind::Extension(Arc::new(self)),
            },
            pos,
        )
    }
    /// The source node contributes no type errors.
    pub fn typecheck(&self) {}
    pub fn translate(&self, lift_metadata: impl FnOnce(&Span) -> Metadata) -> Stmt {
        Unreachable {
            meta: lift_metadata(&self.pos),
        }
        .statement()
    }
}
