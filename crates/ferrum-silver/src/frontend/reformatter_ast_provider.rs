//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ReformatterAstProvider.scala
//!
//! Purpose:
//! Expose parse-only AST construction for reformatting.
//!
//! Planned Rust structure:
//! Provide ReformatterAstProvider over ViperAstProvider, overriding phase list, parsing and
//! result.
//!
//! Behavior to preserve:
//! Run only parsing with macro expansion disabled; return Success after Parsing when no errors,
//! otherwise Failure.
//!
//! Integration:
//! frontend::viper_ast_provider and parser::fast_parser feed parser::reformat_pretty_printer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on reuse/composition with viper_ast_provider.
//!
//! Status: partial; phase selection and result handling implemented. Concrete parser,
//! verifier creation and plugin-manager integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2024 ETH Zurich.

use super::frontend::{DefaultFrontend, DefaultState, FrontendError, FrontendPhases, Phase};
use crate::verifier::verification_result::VerificationResult;

pub const PHASES: &[Phase] = &[Phase::Parsing];
pub struct ReformatterAstProvider<F: FrontendPhases> {
    pub frontend: DefaultFrontend<F>,
}
impl<F: FrontendPhases> ReformatterAstProvider<F> {
    /// The concrete parser must disable macro expansion for this provider.
    pub fn result(&self) -> Result<VerificationResult, FrontendError> {
        if !self.frontend.errors.is_empty() {
            return Ok(VerificationResult::Failure(self.frontend.errors.clone()));
        }
        if self.frontend.state < DefaultState::Parsing {
            return Err(FrontendError::MissingPhaseResult("parsing"));
        }
        Ok(VerificationResult::Success)
    }
}
