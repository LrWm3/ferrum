//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/ErrorTrafoFactory.scala
//!
//! Purpose:
//! Map failed generated assertions to termination-specific reasons.
//!
//! Planned Rust structure:
//! Port AbstractReasonTrafoFactory and ReasonTrafoFactory with termination condition, tuple
//! condition, simple, decreases and bounded reason constructors.
//!
//! Behavior to preserve:
//! Transform AssertionFalse into the corresponding reason at the selected offending node; retain
//! default node behavior.
//!
//! Integration:
//! decreases_check, function_check, method_check and termination_errors; ast error/reason trafos.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for error transformations and source attribution.
//!
//! Open decisions:
//! Agree on composable reason transform ownership with ast and verifier.
//!
//! Status: implemented for the five reason transformations; general diagnostic pipeline and
//! termination transformation integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::ast::ErrorTransformation;
use crate::ast::utility::nodes::Node;
use crate::plugin::standard::termination::termination_errors::{
    TerminationReason, TerminationReasonKind,
};
use crate::verifier::verification_error::{ErrorReason, ExtensionErrorReasonHandle};
use crate::verifier::verification_result::DiagnosticError;
use std::{any::Any, sync::Arc};

/// Each source partial transformation only matches AssertionFalse; all other
/// reason variants pass unchanged through the composition.
#[derive(Clone, Debug)]
pub struct ReasonTrafo {
    pub kind: TerminationReasonKind,
    pub offending_node: Node,
}
impl ErrorTransformation for ReasonTrafo {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn transform_reason(
        &self,
        reason: &ErrorReason,
    ) -> Result<Option<ErrorReason>, DiagnosticError> {
        Ok(if matches!(reason, ErrorReason::AssertionFalse(_)) {
            Some(ErrorReason::Extension(ExtensionErrorReasonHandle(
                Arc::new(TerminationReason {
                    kind: self.kind,
                    offending_node: self.offending_node.clone(),
                }),
            )))
        } else {
            None
        })
    }
}
#[derive(Clone, Debug)]
pub struct ReasonTrafoFactory {
    pub offending_node: Node,
}
impl ReasonTrafoFactory {
    pub fn make(
        &self,
        kind: TerminationReasonKind,
        override_node: Option<Node>,
    ) -> Arc<dyn ErrorTransformation> {
        Arc::new(ReasonTrafo {
            kind,
            offending_node: override_node.unwrap_or_else(|| self.offending_node.clone()),
        })
    }
    pub fn generate_termination_condition_false(
        &self,
        node: Option<Node>,
    ) -> Arc<dyn ErrorTransformation> {
        self.make(TerminationReasonKind::Condition, node)
    }
    pub fn generate_tuple_condition_false(
        &self,
        node: Option<Node>,
    ) -> Arc<dyn ErrorTransformation> {
        self.make(TerminationReasonKind::TupleCondition, node)
    }
    pub fn generate_tuple_simple_false(&self, node: Option<Node>) -> Arc<dyn ErrorTransformation> {
        self.make(TerminationReasonKind::TupleSimple, node)
    }
    pub fn generate_tuple_decreases_false(
        &self,
        node: Option<Node>,
    ) -> Arc<dyn ErrorTransformation> {
        self.make(TerminationReasonKind::TupleDecreases, node)
    }
    pub fn generate_tuple_bounded_false(&self, node: Option<Node>) -> Arc<dyn ErrorTransformation> {
        self.make(TerminationReasonKind::TupleBounded, node)
    }
}
