//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/TerminationErrors.scala
//!
//! Purpose:
//! Define termination failure and reason variants.
//!
//! Planned Rust structure:
//! Port AbstractTerminationError, FunctionTerminationError, MethodTerminationError,
//! LoopTerminationError and five condition/tuple reason types.
//!
//! Behavior to preserve:
//! Preserve termination.failed and reason IDs/messages, offending nodes, cached flag and reason
//! mappings; tuple failure variants share tuple.false. Upstream withNode on the three verification
//! errors ignores the replacement argument.
//!
//! Integration:
//! transformation::{error_trafo_factory,function_check,method_check} and verifier error/reason
//! interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for diagnostics, positions and transformations.
//!
//! Open decisions:
//! Reconcile apparent withNode bug with verifier before selecting behavior; record deliberate
//! changes.
//!
//! Status: partial; typed termination reasons and function/method/loop diagnostics are implemented.
//! The shared back-transformation pipeline and plugin integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::utility::nodes::Node;
use crate::verifier::verification_error::{ExtensionErrorReason, ExtensionErrorReasonHandle};
use crate::verifier::verification_result::DiagnosticError;
use std::{any::Any, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TerminationReasonKind {
    Condition,
    TupleCondition,
    TupleSimple,
    TupleDecreases,
    TupleBounded,
}
#[derive(Clone, Debug)]
pub struct TerminationReason {
    pub kind: TerminationReasonKind,
    pub offending_node: Node,
}
impl TerminationReasonKind {
    pub fn id(self) -> &'static str {
        match self {
            Self::Condition => "termination.condition.false",
            Self::TupleCondition => "tuple.condition.false",
            Self::TupleSimple | Self::TupleDecreases | Self::TupleBounded => "tuple.false",
        }
    }
    pub fn text(self) -> &'static str {
        match self {
            Self::Condition => "Required termination condition might not hold.",
            Self::TupleCondition => "Required tuple condition might not hold.",
            Self::TupleSimple => "Termination measure might not decrease or might not be bounded.",
            Self::TupleDecreases => "Termination measure might not decrease.",
            Self::TupleBounded => "Termination measure might not bounded.",
        }
    }
}
impl ExtensionErrorReason for TerminationReason {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionErrorReason) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|o| self.kind == o.kind && self.offending_node == o.offending_node)
    }
    fn id(&self) -> &str {
        self.kind.id()
    }
    fn offending_node(&self) -> Node {
        self.offending_node.clone()
    }
    fn with_node(&self, node: Node) -> Result<ExtensionErrorReasonHandle, DiagnosticError> {
        Ok(ExtensionErrorReasonHandle(Arc::new(Self {
            kind: self.kind,
            offending_node: node,
        })))
    }
    fn readable_message(
        &self,
        _: &dyn Fn(&Node) -> Result<String, DiagnosticError>,
    ) -> Result<String, DiagnosticError> {
        Ok(self.kind.text().into())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TerminationErrorKind {
    Function,
    Method,
    Loop,
}
#[derive(Clone, Debug)]
pub struct TerminationError {
    pub scope: Arc<std::sync::RwLock<Option<Arc<crate::ast::program::Member>>>>,
    pub kind: TerminationErrorKind,
    pub offending_node: Node,
    pub reason: crate::verifier::verification_error::ErrorReason,
    pub cached: bool,
    pub failure_contexts: Vec<Arc<dyn crate::verifier::verification_error::FailureContext>>,
    pub renderer: Arc<dyn crate::verifier::verification_error::ErrorNodeRenderer>,
    position: crate::ast::position::Position,
}
impl TerminationError {
    /// Validate the source node's position before constructing a diagnostic.
    pub fn new(
        kind: TerminationErrorKind,
        offending_node: Node,
        reason: crate::verifier::verification_error::ErrorReason,
        cached: bool,
        renderer: Arc<dyn crate::verifier::verification_error::ErrorNodeRenderer>,
    ) -> Result<Self, DiagnosticError> {
        let position = crate::verifier::verification_error::node_position(&offending_node)?;
        Ok(Self {
            kind,
            offending_node,
            reason,
            cached,
            failure_contexts: Vec::new(),
            scope: Default::default(),
            renderer,
            position,
        })
    }
    pub fn text(&self) -> &'static str {
        match self.kind {
            TerminationErrorKind::Function => "Function might not terminate.",
            TerminationErrorKind::Method => "Method might not terminate.",
            TerminationErrorKind::Loop => "Loop might not terminate.",
        }
    }
}
impl crate::verifier::verification_result::VerificationDiagnostic for TerminationError {
    fn scope(&self) -> Result<Option<Arc<crate::ast::program::Member>>, DiagnosticError> {
        Ok(self
            .scope
            .read()
            .expect("poisoned plugin diagnostic scope")
            .clone())
    }
    fn set_scope(
        &self,
        scope: Option<Arc<crate::ast::program::Member>>,
    ) -> Result<(), DiagnosticError> {
        *self
            .scope
            .write()
            .expect("poisoned plugin diagnostic scope") = scope;
        Ok(())
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn full_id(&self) -> String {
        format!("termination.failed:{}", self.reason.id())
    }
    fn position(&self) -> crate::ast::position::Position {
        self.position.clone()
    }
    fn readable_message(&self) -> Result<String, DiagnosticError> {
        let mut text = format!(
            "{} {} ({})",
            self.text(),
            self.reason
                .readable_message(&|node| self.renderer.render_node(node))?,
            self.position
        );
        for context in &self.failure_contexts {
            text.push('\n');
            text.push_str(&context.render());
        }
        Ok(text)
    }
    fn render(&self) -> Result<String, DiagnosticError> {
        let clean = Self {
            failure_contexts: Vec::new(),
            ..self.clone()
        };
        let mut text = format!("[{}] {}", self.full_id(), clean.readable_message()?);
        if self.cached {
            text.push_str(" - cached");
        }
        Ok(text)
    }
    fn cached(&self) -> bool {
        self.cached
    }
    fn offending_node(&self) -> Result<Node, DiagnosticError> {
        Ok(self.offending_node.clone())
    }
    fn reason(&self) -> Result<crate::verifier::verification_error::ErrorReason, DiagnosticError> {
        Ok(self.reason.clone())
    }
    /// All three upstream error classes ignore their withNode argument.
    fn with_node(
        &self,
        _: Node,
    ) -> Result<
        Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>,
        DiagnosticError,
    > {
        Ok(Arc::new(Self {
            failure_contexts: Vec::new(),
            ..self.clone()
        }))
    }
    fn with_reason(
        &self,
        reason: crate::verifier::verification_error::ErrorReason,
    ) -> Result<
        Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>,
        DiagnosticError,
    > {
        Ok(Arc::new(Self {
            reason,
            failure_contexts: Vec::new(),
            ..self.clone()
        }))
    }
    fn failure_contexts(
        &self,
    ) -> Result<Vec<Arc<dyn crate::verifier::verification_error::FailureContext>>, DiagnosticError>
    {
        Ok(self.failure_contexts.clone())
    }
    fn with_failure_contexts(
        &self,
        contexts: Vec<Arc<dyn crate::verifier::verification_error::FailureContext>>,
    ) -> Result<
        Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>,
        DiagnosticError,
    > {
        Ok(Arc::new(Self {
            failure_contexts: contexts,
            ..self.clone()
        }))
    }
    fn transformed_error(
        &self,
    ) -> Result<
        Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>,
        DiagnosticError,
    > {
        crate::verifier::verification_error::transform_diagnostic(Arc::new(self.clone()))
    }
}
