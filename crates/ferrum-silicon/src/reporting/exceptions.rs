//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/Exceptions.scala
//!
//! Purpose:
//! Translate external tool and prover interaction failures to Silver diagnostics.
//!
//! Planned Rust structure:
//! Port SiliconException, ExternalToolError and ProverInteractionFailed with asViperError.
//!
//! Behavior to preserve:
//! Preserve no-position diagnostics, external.tool.error and prover.interaction.failed IDs and
//! tool/prover-specific messages.
//!
//! Integration:
//! reporting::package, decider/prover and Silver verifier errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for error variants and causal information.
//!
//! Open decisions:
//! Agree on native exception/result boundary with verifier.
//!
//! Status: native external-tool and prover errors with Silver diagnostic conversion implemented.
//! Concrete process/verifier error adapters remain to be connected.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use ferrum_silver::ast::position::Position;
use ferrum_silver::verifier::verification_result::{
    AbstractError, DiagnosticError, VerificationDiagnostic,
};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SiliconException {
    ExternalToolError { tool: String, message: String },
    ProverInteractionFailed { prover_id: String, message: String },
}
impl SiliconException {
    pub fn message(&self) -> &str {
        match self {
            Self::ExternalToolError { message, .. }
            | Self::ProverInteractionFailed { message, .. } => message,
        }
    }
    pub fn as_viper_error(&self) -> AbstractError {
        AbstractError::Verification(Arc::new(self.clone()))
    }
}
impl std::fmt::Display for SiliconException {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.message())
    }
}
impl std::error::Error for SiliconException {}
impl VerificationDiagnostic for SiliconException {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn full_id(&self) -> String {
        match self {
            Self::ExternalToolError { .. } => "external.tool.error",
            Self::ProverInteractionFailed { .. } => "prover.interaction.failed",
        }
        .into()
    }
    fn position(&self) -> Position {
        Position::NoPosition
    }
    fn readable_message(&self) -> Result<String, DiagnosticError> {
        Ok(match self {
            Self::ExternalToolError { tool, message } => {
                format!("Problem with external tool {tool}: {message}")
            }
            Self::ProverInteractionFailed { prover_id, message } => {
                format!("Interaction with prover (instance {prover_id}) failed: {message}")
            }
        })
    }
    fn render(&self) -> Result<String, DiagnosticError> {
        let message = self.readable_message()?;
        let position = self.position().to_string();
        Ok(if message.contains(&position) {
            message
        } else {
            format!("{message} ({position})")
        })
    }
    fn cached(&self) -> bool {
        false
    }
    fn transformed_error(&self) -> Result<Arc<dyn VerificationDiagnostic>, DiagnosticError> {
        Ok(Arc::new(self.clone()))
    }
}
