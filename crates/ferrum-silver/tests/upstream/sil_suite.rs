//! Port plan: SilSuite.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/SilSuite.scala
//!
//! Purpose:
//! Port the upstream SilSuite.scala test or test-harness component.
//!
//! Planned Rust structure:
//! SilSuite, VerifierUnderTest and SilOutput.
//!
//! Behavior to preserve:
//! Configure and start verifiers before suite, stop afterwards; split config keys by at most one
//! colon, run frontend phases with timings, transform verification errors, and match output
//! IDs/locations. SourcePosition compares only line while TranslatedPosition also compares file;
//! preserve and investigate this distinction.
//!
//! Integration:
//! annotation_based_test_suite, verifier, frontend and timing utilities.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Reconcile lifecycle and source-path matching with backend harness and diagnostics.
//!
//! Status: description only; implementation has not started.
