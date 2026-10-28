//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/refute/RefuteErrors.scala
//!
//! Purpose:
//! Define failures for refutations that could not be shown false.
//!
//! Planned Rust structure:
//! Represent RefuteError, RefuteErrorReason, RefuteFailed and RefutationTrue with IDs, positions,
//! node/reason replacement and cached flag.
//!
//! Behavior to preserve:
//! RefuteFailed uses expression position and special smoke message for false with
//! SmokeDetectionInfo; otherwise it reports that assertion holds or was unreachable. Preserve
//! upstream withNode behavior, which ignores its replacement argument, as an open issue.
//!
//! Integration:
//! refute_plugin creates these errors; smoke::smoke_detection_plugin supplies metadata; verifier
//! errors and reasons.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for diagnostics and error transformations.
//!
//! Open decisions:
//! Reconcile the apparent withNode bug with verifier error contracts before deciding whether to
//! correct it.
//!
//! Status: partial; refute failure and reason diagnostics are implemented with an injected
//! AST renderer. Back transformation remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use super::refute_ast_extension::Refute;
use crate::ast::expression::ExpKind;
use crate::ast::position::Position;
use crate::ast::utility::nodes::Node;
use crate::plugin::standard::smoke::smoke_detection_plugin::SmokeDetectionInfo;
use crate::verifier::verification_error::{
    ErrorNodeRenderer, ErrorReason, ExtensionErrorReason, ExtensionErrorReasonHandle,
    FailureContext,
};
use crate::verifier::verification_result::{DiagnosticError, VerificationDiagnostic};
use std::{any::Any, sync::Arc};

/// The expression whose truth is the reason the refutation failed.
#[derive(Clone, Debug)]
pub struct RefutationTrue {
    pub offending_node: Node,
}
impl RefutationTrue {
    pub fn id(&self) -> &'static str {
        "refutation.true"
    }
    pub fn readable_message(
        &self,
        renderer: &dyn ErrorNodeRenderer,
    ) -> Result<String, DiagnosticError> {
        Ok(format!(
            "Assertion {} definitely holds.",
            renderer.render_node(&self.offending_node)?
        ))
    }
    pub fn with_node(&self, node: Node) -> Self {
        Self {
            offending_node: node,
        }
    }
}

impl ExtensionErrorReason for RefutationTrue {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionErrorReason) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|o| o.offending_node == self.offending_node)
    }
    fn id(&self) -> &str {
        self.id()
    }
    fn offending_node(&self) -> Node {
        self.offending_node.clone()
    }
    fn with_node(&self, node: Node) -> Result<ExtensionErrorReasonHandle, DiagnosticError> {
        Ok(ExtensionErrorReasonHandle(Arc::new(RefutationTrue {
            offending_node: node,
        })))
    }
    fn readable_message(
        &self,
        render: &dyn Fn(&Node) -> Result<String, DiagnosticError>,
    ) -> Result<String, DiagnosticError> {
        Ok(format!(
            "Assertion {} definitely holds.",
            render(&self.offending_node)?
        ))
    }
}

#[derive(Clone, Debug)]
pub struct RefuteFailed {
    pub offending_node: Refute,
    pub reason: ErrorReason,
    pub cached: bool,
    pub failure_contexts: Vec<Arc<dyn FailureContext>>,
    pub offending_stmt: crate::ast::statement::Stmt,
    pub renderer: Arc<dyn ErrorNodeRenderer>,
}
impl RefuteFailed {
    pub fn text(&self) -> &'static str {
        if matches!(self.offending_node.exp.kind(), ExpKind::FalseLit)
            && self
                .offending_node
                .meta
                .info
                .find_extension::<SmokeDetectionInfo>()
                .is_some()
        {
            "Smoke detection: False could be proven here (which should never hold)."
        } else {
            "Refute holds in all cases or could not be reached (e.g. see Silicon `numberOfErrorsToReport`)."
        }
    }
    /// Upstream withNode deliberately retains the original offending refute.
    pub fn with_node(&self, _node: Node) -> Self {
        Self {
            failure_contexts: Vec::new(),
            ..self.clone()
        }
    }
    pub fn with_reason(&self, reason: ErrorReason) -> Self {
        Self {
            reason,
            failure_contexts: Vec::new(),
            ..self.clone()
        }
    }
}
impl VerificationDiagnostic for RefuteFailed {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn full_id(&self) -> String {
        format!("refute.failed:{}", self.reason.id())
    }
    fn position(&self) -> Position {
        self.offending_node.exp.metadata().position.clone()
    }
    fn readable_message(&self) -> Result<String, DiagnosticError> {
        let mut text = format!(
            "{} {} ({})",
            self.text(),
            self.reason
                .readable_message(&|node| self.renderer.render_node(node))?,
            self.position()
        );
        for context in &self.failure_contexts {
            text.push('\n');
            text.push_str(&context.render());
        }
        Ok(text)
    }
    fn render(&self) -> Result<String, DiagnosticError> {
        let without_contexts = Self {
            failure_contexts: Vec::new(),
            ..self.clone()
        };
        let mut result = format!(
            "[{}] {}",
            self.full_id(),
            without_contexts.readable_message()?
        );
        if self.cached {
            result.push_str(" - cached");
        }
        Ok(result)
    }
    fn cached(&self) -> bool {
        self.cached
    }
    fn offending_node(&self) -> Result<Node, DiagnosticError> {
        Ok(Node::Stmt(self.offending_stmt.clone()))
    }
    fn reason(&self) -> Result<ErrorReason, DiagnosticError> {
        Ok(self.reason.clone())
    }
    fn with_node(&self, node: Node) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Ok(Arc::new(RefuteFailed::with_node(self, node)))
    }
    fn with_reason(
        &self,
        reason: ErrorReason,
    ) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Ok(Arc::new(RefuteFailed::with_reason(self, reason)))
    }
    fn failure_contexts(&self) -> Result<Vec<Arc<dyn FailureContext>>, DiagnosticError> {
        Ok(self.failure_contexts.clone())
    }
    fn with_failure_contexts(
        &self,
        contexts: Vec<Arc<dyn FailureContext>>,
    ) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Ok(Arc::new(Self {
            failure_contexts: contexts,
            ..self.clone()
        }))
    }
    fn transformed_error(&self) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        crate::verifier::verification_error::transform_diagnostic(Arc::new(self.clone()))
    }
}
