//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ViperPAstProvider.scala
//!
//! Purpose:
//! Provide a parsed and semantically analyzed parse AST without translating or verifying.
//!
//! Planned Rust structure:
//! Represent ViperPAstProvider, Config and PAstProvidingVerifier; override phase list, result,
//! creation and plugin selection.
//!
//! Behavior to preserve:
//! Run Parsing then SemanticAnalysis only; require semantic state for success and return recorded
//! errors otherwise. Disabled plugins select empty manager after reset.
//!
//! Integration:
//! frontend::sil_frontend, parser::parse_ast and reporter/verifier interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on provider composition and shared plugin lifetime with viper_ast_provider.
//!
//! Status: partial; phase selection and result handling implemented. Concrete parser,
//! verifier creation and plugin-manager integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::frontend::{DefaultFrontend, DefaultState, FrontendError, FrontendPhases, Phase};
use crate::verifier::verification_result::VerificationResult;

pub const PHASES: &[Phase] = &[Phase::Parsing, Phase::SemanticAnalysis];
pub struct ViperPAstProvider<F: FrontendPhases> {
    pub frontend: DefaultFrontend<F>,
    pub disable_plugins: bool,
}
impl<F: FrontendPhases> ViperPAstProvider<F> {
    pub fn result(&self) -> Result<VerificationResult, FrontendError> {
        if !self.frontend.errors.is_empty() {
            return Ok(VerificationResult::Failure(self.frontend.errors.clone()));
        }
        if self.frontend.state < DefaultState::SemanticAnalysis {
            return Err(FrontendError::MissingPhaseResult("semantic analysis"));
        }
        Ok(VerificationResult::Success)
    }
}
