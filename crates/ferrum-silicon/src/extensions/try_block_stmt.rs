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
    fn copy_macro_statement(
        &self,
        copy: &dyn Fn(
            &PStmtHandle,
        )
            -> Result<PStmtHandle, ferrum_silver::parser::macro_expander::MacroError>,
    ) -> Result<Option<PStmtHandle>, ferrum_silver::parser::macro_expander::MacroError> {
        Ok(Some(
            PTryBlock {
                keyword: PReserved::new(
                    self.keyword.value().clone(),
                    self.keyword.position().clone(),
                ),
                body: copy(&self.body)?,
                pos: self.pos.clone(),
            }
            .statement(),
        ))
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
    fn pretty_doc(
        &self,
    ) -> Result<
        ferrum_silver::ast::pretty::pretty_printer::Doc,
        ferrum_silver::ast::pretty::pretty_printer::PrintError,
    > {
        use ferrum_silver::ast::pretty::pretty_printer::{Doc, show_block};
        Ok(Doc::concat([Doc::text("try "), show_block(&self.body)?]))
    }
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
    fn map_expressions(
        &self,
        _map: &dyn Fn(
            &ferrum_silver::ast::expression::Exp,
        ) -> Result<ferrum_silver::ast::expression::Exp, DiagnosticError>,
    ) -> Result<ExtensionStmtHandle, DiagnosticError> {
        Ok(ExtensionStmtHandle(Arc::new(self.clone())))
    }
    fn map_statements(
        &self,
        map: &dyn Fn(&Stmt) -> Result<Stmt, DiagnosticError>,
    ) -> Result<Option<ExtensionStmtHandle>, DiagnosticError> {
        Ok(Some(ExtensionStmtHandle(Arc::new(Self {
            body: map(&self.body)?,
            meta: self.meta.clone(),
        }))))
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

#[cfg(test)]
mod reconstruction_tests {
    use super::*;
    use ferrum_silver::ast::{
        expression::{Exp, ExpKind},
        utility::nodes::map_node_tree,
    };

    #[test]
    fn frontend_rewrites_assume_inside_try_block() {
        use crate::extensions::try_block_parser_plugin::TryBlockParserPlugin;
        use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
        use ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager;
        let plugins = SilverPluginManager::new(vec![Box::new(TryBlockParserPlugin)]);
        let mut phases = SilFrontendPhases::new(std::path::PathBuf::from("test.vpr"), plugins);
        let parsed = phases.parse("method m() { try { assume true; } }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let StmtKind::Seqn { statements, .. } = program.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!("method block")
        };
        let StmtKind::Extension(extension) = statements[0].kind() else {
            panic!("try block")
        };
        let block = extension.0.as_any().downcast_ref::<TryBlock>().unwrap();
        fn has_inhale(s: &Stmt) -> bool {
            match s.kind() {
                StmtKind::Inhale(_) => true,
                StmtKind::Seqn { statements, .. } => statements.iter().any(has_inhale),
                _ => false,
            }
        }
        assert!(has_inhale(&block.body));
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn node_mapper_rewrites_assume_inside_try_block() {
        let meta = Metadata::default();
        let condition = Exp::new(ExpKind::TrueLit, meta.clone());
        let inner = Stmt::new(StmtKind::Assume(condition), meta.clone());
        let block = TryBlock { body: inner, meta }.statement();
        let mapped = map_node_tree(&Node::Stmt(block), &|node| {
            if let Node::Stmt(stmt) = node {
                if let StmtKind::Assume(exp) = stmt.kind() {
                    return Ok(Node::Stmt(Stmt::new(
                        StmtKind::Inhale(exp.clone()),
                        stmt.metadata().clone(),
                    )));
                }
            }
            Ok(node.clone())
        })
        .unwrap();
        let Node::Stmt(stmt) = mapped else {
            panic!("expected statement")
        };
        let StmtKind::Extension(extension) = stmt.kind() else {
            panic!("expected try block")
        };
        let block = extension.0.as_any().downcast_ref::<TryBlock>().unwrap();
        assert!(matches!(block.body.kind(), StmtKind::Inhale(_)));
    }
}
