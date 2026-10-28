//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ViperAstProvider.scala
//!
//! Purpose:
//! Produce a checked Silver AST without backend verification.
//!
//! Planned Rust structure:
//! Represent ViperAstProvider, Config and AstProvidingVerifier; specialize phase list, result,
//! finish, verifier creation and optional disabled-plugin manager.
//!
//! Behavior to preserve:
//! Run parsing, analysis, translation and consistency only; success requires a program and
//! consistency state. Report AST construction result; disabled plugins use an empty manager on
//! reset. The stub verifier succeeds but is not a verification phase.
//!
//! Integration:
//! frontend::sil_frontend, parser and reporter::message; reformatter_ast_provider specializes
//! this provider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on provider composition and plugin manager lifetime with sil_frontend.
//!
//! Status: partial; phase selection and result handling implemented. Concrete parser,
//! verifier creation and plugin-manager integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::frontend::{DefaultFrontend, DefaultState, FrontendError, FrontendPhases, Phase};
use crate::reporter::message::Message;
use crate::reporter::reporter::{ReportError, Reporter};
use crate::verifier::verification_result::VerificationResult;
use std::sync::Arc;

pub const PHASES: &[Phase] = &[
    Phase::Parsing,
    Phase::SemanticAnalysis,
    Phase::Translation,
    Phase::ConsistencyCheck,
];
pub struct ViperAstProvider<F: FrontendPhases> {
    pub frontend: DefaultFrontend<F>,
    pub reporter: Arc<dyn Reporter>,
    /// The concrete plugin manager must honor this flag on reset.
    pub disable_plugins: bool,
}
impl<F: FrontendPhases> ViperAstProvider<F> {
    pub fn new(
        frontend: DefaultFrontend<F>,
        reporter: Arc<dyn Reporter>,
        disable_plugins: bool,
    ) -> Self {
        Self {
            frontend,
            reporter,
            disable_plugins,
        }
    }
    pub fn result(&self) -> Result<VerificationResult, FrontendError> {
        if !self.frontend.errors.is_empty() {
            return Ok(VerificationResult::Failure(self.frontend.errors.clone()));
        }
        if self.frontend.program.is_none() {
            return Ok(VerificationResult::Failure(Vec::new()));
        }
        if self.frontend.state < DefaultState::ConsistencyCheck {
            return Err(FrontendError::MissingPhaseResult("consistency"));
        }
        Ok(VerificationResult::Success)
    }
    pub fn finish(&self, time: i64) -> Result<(), ProviderFinishError> {
        let result = self.result().map_err(ProviderFinishError::Frontend)?;
        let message = match result {
            VerificationResult::Success => Message::AstConstructionSuccess { time },
            VerificationResult::Failure(errors) => Message::AstConstructionFailure { time, errors },
        };
        self.reporter
            .report(message)
            .map_err(ProviderFinishError::Reporter)
    }
}
#[derive(Debug)]
pub enum ProviderFinishError {
    Frontend(FrontendError),
    Reporter(ReportError),
}
