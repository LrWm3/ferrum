//! Port plan: Represent verification outcomes and frontend errors.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/VerificationResult.scala
//!
//! Purpose:
//! Represent verification outcomes and frontend errors.
//!
//! Planned Rust structure:
//! VerificationResult Success/Failure and AbstractError; ParseReport, ParseError/ParseWarning,
//! TypecheckerWarning/Error, VerifierWarning, ConsistencyError, CliOptionError,
//! DependencyNotFoundError, TimeoutOccurred and AbortedExceptionally.
//!
//! Behavior to preserve:
//! Failure transforms each error in order; retain full IDs, messages, positions, cached flag and
//! optional member scope. AbstractError string avoids repeating a position already in its message.
//! Timeout and exceptional termination stay distinct from verification failure and warnings.
//!
//! Integration:
//! ast::{position,program}, verifier::verification_error, parser, frontend and reporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile typed failure payloads, mutable scope and exception reporting with frontend and
//! backend results.
//!
//! Status: partial; verification outcomes, parse and frontend diagnostics are
//! implemented. Concrete verification errors and exceptional stack-trace side
//! effects remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{position::Position, program::Member};
use std::sync::{Arc, RwLock};

/// The parser-report subset of AbstractError; verification outcomes remain unimplemented.
#[derive(Clone, Debug)]
pub struct ParseError {
    pub message: String,
    pub pos: Position,
    scope: Arc<RwLock<Option<Arc<Member>>>>,
}
#[derive(Clone, Debug)]
pub struct ParseWarning {
    pub message: String,
    pub pos: Position,
    scope: Arc<RwLock<Option<Arc<Member>>>>,
}
impl PartialEq for ParseError {
    fn eq(&self, other: &Self) -> bool {
        self.message == other.message && self.pos == other.pos
    }
}
impl Eq for ParseError {}
impl PartialEq for ParseWarning {
    fn eq(&self, other: &Self) -> bool {
        self.message == other.message && self.pos == other.pos
    }
}
impl Eq for ParseWarning {}
impl ParseError {
    pub fn new(message: impl Into<String>, pos: Position) -> Self {
        Self {
            message: message.into(),
            pos,
            scope: Arc::new(RwLock::new(None)),
        }
    }
}
impl ParseWarning {
    pub fn new(message: impl Into<String>, pos: Position) -> Self {
        Self {
            message: message.into(),
            pos,
            scope: Arc::new(RwLock::new(None)),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ParseReport {
    Error(ParseError),
    Warning(ParseWarning),
}
impl ParseReport {
    pub fn pos(&self) -> &Position {
        match self {
            Self::Error(e) => &e.pos,
            Self::Warning(e) => &e.pos,
        }
    }
    pub fn message(&self) -> &str {
        match self {
            Self::Error(e) => &e.message,
            Self::Warning(e) => &e.message,
        }
    }
    pub fn full_id(&self) -> &'static str {
        match self {
            Self::Error(_) => "parser.error",
            Self::Warning(_) => "parser.warning",
        }
    }
    pub fn readable_message(&self) -> String {
        let kind = match self {
            Self::Error(_) => "Parse error",
            Self::Warning(_) => "Parse warning",
        };
        format!("{kind}: {} ({})", self.message(), self.pos())
    }
    pub fn cached(&self) -> bool {
        false
    }
    pub fn scope(&self) -> Option<Arc<Member>> {
        match self {
            Self::Error(e) => e.scope.read().expect("poisoned report scope").clone(),
            Self::Warning(e) => e.scope.read().expect("poisoned report scope").clone(),
        }
    }
    pub fn set_scope(&self, scope: Option<Arc<Member>>) {
        match self {
            Self::Error(e) => *e.scope.write().expect("poisoned report scope") = scope,
            Self::Warning(e) => *e.scope.write().expect("poisoned report scope") = scope,
        }
    }
    pub fn transformed_error(&self) -> &Self {
        self
    }
}
impl std::fmt::Display for ParseReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.readable_message())
    }
}

/// A backend diagnostic can carry typed node/reason transformations without
/// requiring the frontend result type to depend on a particular backend.
pub trait VerificationDiagnostic: std::fmt::Debug + Send + Sync {
    fn as_any(&self) -> &dyn std::any::Any;
    fn full_id(&self) -> String;
    fn position(&self) -> Position;
    fn readable_message(&self) -> Result<String, DiagnosticError>;
    /// Source AbstractVerificationError.toString includes its ID and cached marker.
    fn render(&self) -> Result<String, DiagnosticError>;
    fn cached(&self) -> bool;
    fn transformed_error(&self) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError>;
    fn offending_node(&self) -> Result<crate::ast::utility::nodes::Node, DiagnosticError> {
        Err(DiagnosticError::Unsupported("diagnostic offending node"))
    }
    fn reason(&self) -> Result<super::verification_error::ErrorReason, DiagnosticError> {
        Err(DiagnosticError::Unsupported("diagnostic reason"))
    }
    fn with_node(
        &self,
        _node: crate::ast::utility::nodes::Node,
    ) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Err(DiagnosticError::Unsupported("diagnostic with_node"))
    }
    fn with_reason(
        &self,
        _reason: super::verification_error::ErrorReason,
    ) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Err(DiagnosticError::Unsupported("diagnostic with_reason"))
    }
    fn failure_contexts(
        &self,
    ) -> Result<Vec<Arc<dyn super::verification_error::FailureContext>>, DiagnosticError> {
        Err(DiagnosticError::Unsupported("diagnostic failure contexts"))
    }
    fn with_failure_contexts(
        &self,
        _contexts: Vec<Arc<dyn super::verification_error::FailureContext>>,
    ) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Err(DiagnosticError::Unsupported(
            "diagnostic with failure contexts",
        ))
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiagnosticError {
    Unsupported(&'static str),
    InvalidNode(&'static str),
}

/// The non-verification diagnostic families in VerificationResult.scala.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FrontendErrorKind {
    TypecheckerWarning(String),
    VerifierWarning(String),
    ConsistencyError(String),
    TypecheckerError(String),
    CliOptionError(String),
    DependencyNotFoundError(String),
    TimeoutOccurred {
        duration: i64,
        units: String,
    },
    /// The source wraps a Throwable and uses its stack trace in the message.
    AbortedExceptionally {
        cause: String,
        stack_trace: Vec<String>,
    },
}
#[derive(Clone, Debug)]
pub struct FrontendError {
    pub kind: FrontendErrorKind,
    pub position: Position,
    scope: Arc<RwLock<Option<Arc<Member>>>>,
}
impl FrontendError {
    pub fn new(kind: FrontendErrorKind, position: Position) -> Self {
        // The source's CLI, dependency, timeout and exceptional errors always
        // report NoPosition regardless of their payload.
        let position = match kind {
            FrontendErrorKind::CliOptionError(_)
            | FrontendErrorKind::DependencyNotFoundError(_)
            | FrontendErrorKind::TimeoutOccurred { .. }
            | FrontendErrorKind::AbortedExceptionally { .. } => Position::NoPosition,
            _ => position,
        };
        Self {
            kind,
            position,
            scope: Arc::new(RwLock::new(None)),
        }
    }
    pub fn scope(&self) -> Option<Arc<Member>> {
        self.scope.read().expect("poisoned error scope").clone()
    }
    pub fn set_scope(&self, scope: Option<Arc<Member>>) {
        *self.scope.write().expect("poisoned error scope") = scope;
    }
    pub fn full_id(&self) -> &'static str {
        match self.kind {
            FrontendErrorKind::TypecheckerWarning(_) => "typechecker.warning",
            FrontendErrorKind::VerifierWarning(_) => "verifier.warning",
            FrontendErrorKind::ConsistencyError(_) => "consistency.error",
            FrontendErrorKind::TypecheckerError(_) => "typechecker.error",
            FrontendErrorKind::CliOptionError(_) => "clioption.error",
            FrontendErrorKind::DependencyNotFoundError(_) => "dependencynotfound.error",
            FrontendErrorKind::TimeoutOccurred { .. } => "timeout.error",
            FrontendErrorKind::AbortedExceptionally { .. } => "exceptional.error",
        }
    }
    pub fn readable_message(&self) -> Result<String, DiagnosticError> {
        Ok(match &self.kind {
            FrontendErrorKind::TypecheckerWarning(s) => {
                format!("Type checker warning: {s} ({})", self.position)
            }
            FrontendErrorKind::VerifierWarning(s) => {
                format!("Verifier warning: {s} ({})", self.position)
            }
            FrontendErrorKind::ConsistencyError(s) => {
                format!("Consistency error: {s} ({})", self.position)
            }
            FrontendErrorKind::TypecheckerError(s) => format!("{s} ({})", self.position),
            FrontendErrorKind::CliOptionError(s) => format!("Command-line interface: {s}"),
            FrontendErrorKind::DependencyNotFoundError(s) => format!("Dependency not found: {s}"),
            FrontendErrorKind::TimeoutOccurred { duration, units } => {
                format!("Timeout occurred after {duration} {units}")
            }
            FrontendErrorKind::AbortedExceptionally { cause, stack_trace } => {
                let frame = stack_trace.get(1).ok_or(DiagnosticError::Unsupported(
                    "exception stack has no second frame",
                ))?;
                format!("Verification aborted exceptionally ({cause}, {frame})")
            }
        })
    }
}
impl PartialEq for FrontendError {
    fn eq(&self, b: &Self) -> bool {
        self.kind == b.kind && self.position == b.position
    }
}
impl Eq for FrontendError {}

#[derive(Clone, Debug)]
pub enum AbstractError {
    Parse(ParseReport),
    Frontend(FrontendError),
    Verification(Arc<dyn VerificationDiagnostic>),
}
impl AbstractError {
    pub fn full_id(&self) -> String {
        match self {
            Self::Parse(e) => e.full_id().into(),
            Self::Frontend(e) => e.full_id().into(),
            Self::Verification(e) => e.full_id(),
        }
    }
    pub fn position(&self) -> Position {
        match self {
            Self::Parse(e) => e.pos().clone(),
            Self::Frontend(e) => e.position.clone(),
            Self::Verification(e) => e.position(),
        }
    }
    pub fn readable_message(&self) -> Result<String, DiagnosticError> {
        match self {
            Self::Parse(e) => Ok(e.readable_message()),
            Self::Frontend(e) => e.readable_message(),
            Self::Verification(e) => e.readable_message(),
        }
    }
    pub fn transformed_error(&self) -> Result<Self, DiagnosticError> {
        Ok(match self {
            Self::Parse(e) => Self::Parse(e.clone()),
            Self::Frontend(e) => Self::Frontend(e.clone()),
            Self::Verification(e) => Self::Verification(e.transformed_error()?),
        })
    }
    pub fn render(&self) -> Result<String, DiagnosticError> {
        if let Self::Verification(e) = self {
            return e.render();
        }
        let msg = self.readable_message()?;
        let pos = self.position().to_string();
        Ok(if msg.contains(&pos) {
            msg
        } else {
            format!("{msg} ({pos})")
        })
    }
}

#[derive(Clone, Debug)]
pub enum VerificationResult {
    Success,
    Failure(Vec<AbstractError>),
}
impl VerificationResult {
    pub fn transformed_result(&self) -> Result<Self, DiagnosticError> {
        Ok(match self {
            Self::Success => Self::Success,
            Self::Failure(errors) => Self::Failure(
                errors
                    .iter()
                    .map(AbstractError::transformed_error)
                    .collect::<Result<_, _>>()?,
            ),
        })
    }
    pub fn render(&self) -> Result<String, DiagnosticError> {
        Ok(match self {
            Self::Success => "Verification successful.".into(),
            Self::Failure(errors) => format!(
                "Verification failed with {} errors:\n  {}",
                errors.len(),
                errors
                    .iter()
                    .map(|e| Ok(format!("[{}] {}", e.full_id(), e.readable_message()?)))
                    .collect::<Result<Vec<_>, DiagnosticError>>()?
                    .join("\n  ")
            ),
        })
    }
}
