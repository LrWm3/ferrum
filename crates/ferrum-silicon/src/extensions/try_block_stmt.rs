//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/extensions/TryBlockStmt.scala
//!
//! Purpose:
//! Represent try blocks in parse and verification ASTs.
//!
//! Planned Rust structure:
//! Port PTryKeyword, PTryBlock typecheck/translateStmt and TryBlock extension statement with child
//! and pretty printing.
//!
//! Behavior to preserve:
//! Typecheck body, translate it retaining position, and expose body as sole extension subnode.
//!
//! Integration:
//! extensions::try_block_parser_plugin, Silicon executor and Silver parser/AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for AST extension and position handling.
//!
//! Open decisions:
//! Agree on execution failure semantics with rules::executor.
//!
//! Status: partial; typed parse and AST nodes, child traversal and callback-based checking and
//! translation and parser registration are implemented. Generic reconstruction and execution remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2020 ETH Zurich.

use ferrum_silver::ast::ast::Metadata;
use ferrum_silver::ast::program::Declaration;
use ferrum_silver::ast::statement::{ExtensionStmt, ExtensionStmtHandle, Stmt, StmtKind};
use ferrum_silver::ast::utility::nodes::{Node, TraversalError};
use ferrum_silver::parser::parse_ast::{
    PExtender, PNodeHandle, PStatement, PStatementKind, PStmtHandle,
};
use ferrum_silver::parser::parse_ast_keyword::{
    PExtensionKeyword, PExtensionKeywordCategory, PReserved, Span,
};
use ferrum_silver::verifier::verification_result::{DiagnosticError, FrontendError};
use std::{any::Any, sync::Arc};

pub fn try_keyword(pos: Span) -> PReserved<PExtensionKeyword> {
    PReserved::new(
        PExtensionKeyword {
            spelling: "try".into(),
            category: PExtensionKeywordCategory::Statement,
        },
        pos,
    )
}

#[derive(Clone, Debug)]
pub struct PTryBlock {
    pub keyword: PReserved<PExtensionKeyword>,
    pub body: PStmtHandle,
    pub pos: Span,
}
impl PExtender for PTryBlock {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn statement_name_analysis_passthrough(&self) -> bool {
        true
    }
    fn typecheck_statement(
        &self,
        check: &mut dyn FnMut(
            &PStmtHandle,
        )
            -> Result<(), ferrum_silver::parser::resolver::TypeCheckError>,
    ) -> Result<(), ferrum_silver::parser::resolver::TypeCheckError> {
        check(&self.body)
    }
    fn translate_statement(
        &self,
        translate: &mut dyn FnMut(
            &PStmtHandle,
        ) -> Result<
            Stmt,
            ferrum_silver::parser::translator::TranslationError,
        >,
        meta: Metadata,
    ) -> Result<Stmt, ferrum_silver::parser::translator::TranslationError> {
        Ok(TryBlock {
            body: translate(&self.body)?,
            meta,
        }
        .statement())
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        vec![self.keyword.node().clone(), self.body.node().clone()]
    }
}
impl PTryBlock {
    pub fn statement(self) -> PStmtHandle {
        let pos = self.pos.clone();
        PStmtHandle::new(
            PStatement {
                kind: PStatementKind::Extension(Arc::new(self)),
            },
            pos,
        )
    }
    pub fn typecheck<E>(&self, check: impl FnOnce(&PStmtHandle) -> Result<(), E>) -> Result<(), E> {
        check(&self.body)
    }
    pub fn translate<E>(
        &self,
        translate: impl FnOnce(&PStmtHandle) -> Result<Stmt, E>,
        lift_metadata: impl FnOnce(&Span) -> Metadata,
    ) -> Result<Stmt, E> {
        Ok(TryBlock {
            body: translate(&self.body)?,
            meta: lift_metadata(&self.pos),
        }
        .statement())
    }
}

#[derive(Clone, Debug)]
pub struct TryBlock {
    pub body: Stmt,
    pub meta: Metadata,
}
impl TryBlock {
    pub fn statement(self) -> Stmt {
        let meta = self.meta.clone();
        Stmt::new(
            StmtKind::Extension(ExtensionStmtHandle(Arc::new(self))),
            meta,
        )
    }
    pub fn pretty(&self, print_block: impl FnOnce(&Stmt) -> String) -> String {
        format!("try {}", print_block(&self.body))
    }
}
impl ExtensionStmt for TryBlock {
    fn metadata(&self) -> &Metadata {
        &self.meta
    }
    fn with_metadata(&self, meta: Metadata) -> ExtensionStmtHandle {
        ExtensionStmtHandle(Arc::new(Self {
            body: self.body.clone(),
            meta,
        }))
    }
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionStmt) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|o| self.body == o.body)
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        Ok(vec![Node::Stmt(self.body.clone())])
    }
    fn check_product_nodes(&self) -> Result<Vec<Node>, DiagnosticError> {
        Ok(vec![Node::Stmt(self.body.clone())])
    }
    fn check(&self) -> Result<Vec<FrontendError>, DiagnosticError> {
        Ok(vec![])
    }
    fn scope_declarations(&self) -> Result<Option<Vec<Declaration>>, DiagnosticError> {
        Ok(None)
    }
}
