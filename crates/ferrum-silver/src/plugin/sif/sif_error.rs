//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/sif/SIFError.scala
//!
//! Purpose:
//! Define information-flow check failures and reasons.
//!
//! Planned Rust structure:
//! Port SIFTerminationChannelCheckFailed, SIFGotoCheckFailed and fold, unfold,
//! termination-condition and goto reason variants.
//!
//! Behavior to preserve:
//! Preserve IDs, texts, offending node types and reason transformations. Error withNode/withReason
//! constructors omit cached flag and thereby reset it to false; preserve as an observed issue for
//! reconciliation.
//!
//! Integration:
//! sif_extended_transformer attaches errors and reasons; verifier error interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for diagnostics, metadata and error transformations.
//!
//! Open decisions:
//! Reconcile cached-flag behavior and typed error-node replacement with verifier.
//!
//! Status: partial; both SIF errors and all source reason variants are implemented. Some node
//! back-transformations and SIF transformation integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2025 ETH Zurich.

use crate::ast::{
    position::Position,
    statement::{Stmt, StmtKind},
    utility::nodes::Node,
};
use crate::verifier::verification_error::{
    ErrorNodeRenderer, ErrorReason, ExtensionErrorReason, ExtensionErrorReasonHandle,
    FailureContext, node_position,
};
use crate::verifier::verification_result::{DiagnosticError, VerificationDiagnostic};
use std::{any::Any, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SifErrorKind {
    TerminationChannel,
    Goto,
}
#[derive(Clone, Debug)]
pub struct SifError {
    pub scope: Arc<std::sync::RwLock<Option<Arc<crate::ast::program::Member>>>>,
    pub kind: SifErrorKind,
    pub offending_node: Node,
    pub reason: ErrorReason,
    pub cached: bool,
    pub failure_contexts: Vec<Arc<dyn FailureContext>>,
    pub renderer: Arc<dyn ErrorNodeRenderer>,
    position: Position,
}
impl SifError {
    pub fn new(
        kind: SifErrorKind,
        offending_node: Node,
        reason: ErrorReason,
        cached: bool,
        renderer: Arc<dyn ErrorNodeRenderer>,
    ) -> Result<Self, DiagnosticError> {
        let position = node_position(&offending_node)?;
        Ok(Self {
            kind,
            offending_node,
            reason,
            cached,
            failure_contexts: vec![],
            scope: Default::default(),
            renderer,
            position,
        })
    }
    fn text(&self) -> &'static str {
        match self.kind {
            SifErrorKind::TerminationChannel => "Termination channel might exist.",
            SifErrorKind::Goto => "Side conditions for goto might not hold.",
        }
    }
}
impl VerificationDiagnostic for SifError {
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
        let id = match self.kind {
            SifErrorKind::TerminationChannel => "termination_channel_check.failed",
            SifErrorKind::Goto => "sif.goto_check.failed",
        };
        format!("{id}:{}", self.reason.id())
    }
    fn position(&self) -> Position {
        self.position.clone()
    }
    fn readable_message(&self) -> Result<String, DiagnosticError> {
        let mut text = format!(
            "{} {} ({})",
            self.text(),
            self.reason
                .readable_message(&|n| self.renderer.render_node(n))?,
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
            failure_contexts: vec![],
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
    fn reason(&self) -> Result<ErrorReason, DiagnosticError> {
        Ok(self.reason.clone())
    }
    /// Both source copy methods reset `cached` and failure contexts.
    fn with_node(&self, node: Node) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Ok(Arc::new(Self::new(
            self.kind,
            node,
            self.reason.clone(),
            false,
            self.renderer.clone(),
        )?))
    }
    fn with_reason(
        &self,
        reason: ErrorReason,
    ) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Ok(Arc::new(Self::new(
            self.kind,
            self.offending_node.clone(),
            reason,
            false,
            self.renderer.clone(),
        )?))
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
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SifReasonKind {
    FoldNotLow,
    UnfoldNotLow,
    GotoNotLowEvent,
}
#[derive(Clone, Debug)]
pub struct SifReason {
    pub kind: SifReasonKind,
    pub statement: Stmt,
}
impl SifReason {
    pub fn new(kind: SifReasonKind, statement: Stmt) -> Result<Self, DiagnosticError> {
        let valid = matches!(
            (kind, statement.kind()),
            (SifReasonKind::FoldNotLow, StmtKind::Fold(_))
                | (SifReasonKind::UnfoldNotLow, StmtKind::Unfold(_))
                | (SifReasonKind::GotoNotLowEvent, StmtKind::Goto(_))
        );
        if !valid {
            return Err(DiagnosticError::InvalidNode(
                "incorrect SIF reason statement",
            ));
        }
        Ok(Self { kind, statement })
    }
}
impl ExtensionErrorReason for SifReason {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionErrorReason) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|o| self.kind == o.kind && self.statement == o.statement)
    }
    fn id(&self) -> &str {
        match self.kind {
            SifReasonKind::FoldNotLow => "sif.fold",
            SifReasonKind::UnfoldNotLow => "sif.unfold",
            SifReasonKind::GotoNotLowEvent => "sif.goto",
        }
    }
    fn offending_node(&self) -> Node {
        Node::Stmt(self.statement.clone())
    }
    fn with_node(&self, node: Node) -> Result<ExtensionErrorReasonHandle, DiagnosticError> {
        let Node::Stmt(statement) = node else {
            return Err(DiagnosticError::InvalidNode("SIF reason expects statement"));
        };
        Ok(ExtensionErrorReasonHandle(Arc::new(Self::new(
            self.kind, statement,
        )?)))
    }
    fn readable_message(
        &self,
        _: &dyn Fn(&Node) -> Result<String, DiagnosticError>,
    ) -> Result<String, DiagnosticError> {
        Ok(match self.statement.kind() {
            StmtKind::Fold(acc) | StmtKind::Unfold(acc) => format!("The low parts of predicate {} might not hold.", acc.location.predicate_name),
            StmtKind::Goto(_) => "Goto statement might not be executed by both executions after assuming that both executions enter this method, which is required by the chosen SIF encoding.".into(),
            _ => return Err(DiagnosticError::InvalidNode("incorrect SIF reason statement")),
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SifTerminationReasonKind {
    ConditionNotLow,
    ConditionNotLowEvent,
    ConditionNotTight,
}
#[derive(Clone, Debug)]
pub struct SifTerminationReason {
    pub kind: SifTerminationReasonKind,
    pub expression: crate::ast::expression::Exp,
}
impl SifTerminationReason {
    pub fn new(
        kind: SifTerminationReasonKind,
        expression: crate::ast::expression::Exp,
    ) -> Result<Self, DiagnosticError> {
        use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
        use crate::ast::expression::ExpKind;
        let valid = matches!(expression.kind(), ExpKind::Extension(e) if matches!(e.0.as_any().downcast_ref::<SifExpression>(), Some(SifExpression { kind: SifExpressionKind::Terminates { .. }, .. })));
        if !valid {
            return Err(DiagnosticError::InvalidNode(
                "SIF termination reason expects terminates expression",
            ));
        }
        Ok(Self { kind, expression })
    }
}
impl ExtensionErrorReason for SifTerminationReason {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionErrorReason) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|o| self.kind == o.kind && self.expression == o.expression)
    }
    fn id(&self) -> &str {
        match self.kind {
            SifTerminationReasonKind::ConditionNotLow => "sif_termination.condition_not_low",
            SifTerminationReasonKind::ConditionNotLowEvent => "sif_termination.not_lowevent",
            SifTerminationReasonKind::ConditionNotTight => "sif_termination.condition_not_tight",
        }
    }
    fn offending_node(&self) -> Node {
        Node::Exp(self.expression.clone())
    }
    fn with_node(&self, node: Node) -> Result<ExtensionErrorReasonHandle, DiagnosticError> {
        let Node::Exp(expression) = node else {
            return Err(DiagnosticError::InvalidNode(
                "SIF termination reason expects expression",
            ));
        };
        Ok(ExtensionErrorReasonHandle(Arc::new(Self::new(
            self.kind, expression,
        )?)))
    }
    fn readable_message(
        &self,
        render: &dyn Fn(&Node) -> Result<String, DiagnosticError>,
    ) -> Result<String, DiagnosticError> {
        use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
        use crate::ast::expression::ExpKind;
        let ExpKind::Extension(extension) = self.expression.kind() else {
            return Err(DiagnosticError::InvalidNode("SIF termination expression"));
        };
        let Some(SifExpression {
            kind: SifExpressionKind::Terminates { condition },
            ..
        }) = extension.0.as_any().downcast_ref::<SifExpression>()
        else {
            return Err(DiagnosticError::InvalidNode("SIF termination expression"));
        };
        let condition = render(&Node::Exp(condition.clone()))?;
        Ok(match self.kind {
            SifTerminationReasonKind::ConditionNotLow => {
                format!("Termination condition {condition} might not be low.")
            }
            SifTerminationReasonKind::ConditionNotLowEvent => format!(
                "Termination condition {condition} evaluating to false might not imply both executions don't terminate."
            ),
            SifTerminationReasonKind::ConditionNotTight => {
                format!("Termination condition {condition} might not be tight.")
            }
        })
    }
}

#[cfg(test)]
mod scope_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        expression::{Exp, ExpKind},
        program::{Member, Method, MethodData},
    };
    use crate::verifier::verification_error::NativeErrorNodeRenderer;
    #[test]
    fn cloned_plugin_error_shares_scope_but_source_copy_resets_it() {
        let meta = Metadata::default();
        let node = Node::Exp(Exp::new(ExpKind::TrueLit, meta.clone()));
        let error = SifError::new(
            SifErrorKind::TerminationChannel,
            node.clone(),
            ErrorReason::Dummy,
            false,
            Arc::new(NativeErrorNodeRenderer),
        )
        .unwrap();
        let member = Arc::new(Member::Method(Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta,
        })));
        error.set_scope(Some(member.clone())).unwrap();
        assert!(Arc::ptr_eq(
            &error.clone().scope().unwrap().unwrap(),
            &member
        ));
        assert!(error.with_node(node).unwrap().scope().unwrap().is_none());
    }
}
