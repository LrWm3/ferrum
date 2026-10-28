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
//! Status: description only; implementation has not started.
