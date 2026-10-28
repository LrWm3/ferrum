//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/predicateinstance/PredicateInstanceErrors.scala
//!
//! Purpose:
//! Define verification errors for inaccessible predicate instances.
//!
//! Planned Rust structure:
//! Port PredicateInstanceError and PredicateInstanceNoAccess, including id, text, cached flag and
//! withNode/withReason.
//!
//! Behavior to preserve:
//! Preserve predicateinstance.no.access identity and offending-node provenance. Upstream
//! withReason ignores its new reason, a potential bug needing explicit reconciliation.
//!
//! Integration:
//! predicate_instance_plugin maps precondition errors; verifier error/reason interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for error and reason mapping.
//!
//! Open decisions:
//! Resolve withReason behavior with verifier error contract and differential tests.
//!
//! Status: partial; the typed diagnostic and source withReason behavior are implemented.
//! Error transformation and full positioned-node dispatch remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{position::Position, utility::nodes::Node};
use crate::verifier::verification_error::{ErrorNodeRenderer, ErrorReason};
use crate::verifier::verification_result::{DiagnosticError, VerificationDiagnostic};
use std::{any::Any, sync::Arc};

/// Error attached to generated predicate-instance function precondition failures.
#[derive(Clone, Debug)]
pub struct PredicateInstanceNoAccess {
    pub offending_node: Node,
    pub reason: ErrorReason,
    pub cached: bool,
    pub failure_contexts: Vec<Arc<dyn crate::verifier::verification_error::FailureContext>>,
    pub renderer: Arc<dyn ErrorNodeRenderer>,
}
impl PredicateInstanceNoAccess {
    pub fn with_node(&self, offending_node: Node) -> Self {
        Self {
            offending_node,
            failure_contexts: Vec::new(),
            ..self.clone()
        }
    }
    /// The upstream implementation ignores its replacement reason.
    pub fn with_reason(&self, _reason: ErrorReason) -> Self {
        Self {
            failure_contexts: Vec::new(),
            ..self.clone()
        }
    }
    fn node_position(&self) -> Result<Position, DiagnosticError> {
        match &self.offending_node {
            Node::Exp(e) => Ok(e.metadata().position.clone()),
            Node::Stmt(s) => Ok(s.metadata().position.clone()),
            Node::LocalVar(v) => Ok(v.meta.position.clone()),
            Node::FieldAccess(v) => Ok(v.meta.position.clone()),
            Node::PredicateAccess(v) => Ok(v.meta.position.clone()),
            Node::PredicateAccessPredicate(v) => Ok(v.meta.position.clone()),
            _ => Err(DiagnosticError::Unsupported(
                "predicate instance error node position",
            )),
        }
    }
    /// Validate position support before converting this into an infallibly positioned diagnostic.
    pub fn into_diagnostic(self) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        self.node_position()?;
        Ok(Arc::new(self))
    }
}
impl VerificationDiagnostic for PredicateInstanceNoAccess {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn full_id(&self) -> String {
        format!("predicateinstance.no.access:{}", self.reason.id())
    }
    fn position(&self) -> Position {
        self.node_position()
            .expect("validated predicate instance diagnostic position")
    }
    fn readable_message(&self) -> Result<String, DiagnosticError> {
        let reason = self
            .reason
            .readable_message(&|node| self.renderer.render_node(node))?;
        let mut text = format!(
            "Accessing predicate instance might fail. {reason} ({})",
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
        Ok(self.offending_node.clone())
    }
    fn reason(&self) -> Result<ErrorReason, DiagnosticError> {
        Ok(self.reason.clone())
    }
    fn with_node(&self, node: Node) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        PredicateInstanceNoAccess::with_node(self, node).into_diagnostic()
    }
    fn with_reason(
        &self,
        reason: ErrorReason,
    ) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        PredicateInstanceNoAccess::with_reason(self, reason).into_diagnostic()
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
    ) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Self {
            failure_contexts: contexts,
            ..self.clone()
        }
        .into_diagnostic()
    }
    fn transformed_error(&self) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        crate::verifier::verification_error::transform_diagnostic(Arc::new(self.clone()))
    }
}
