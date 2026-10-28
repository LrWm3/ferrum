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
//! Status: partial; parse reports implemented, verification outcomes and other errors pending.

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
