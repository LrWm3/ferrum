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
//! Status: description only; implementation has not started.
