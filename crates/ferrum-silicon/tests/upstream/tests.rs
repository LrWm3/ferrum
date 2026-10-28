//! Port plan: tests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/tests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! tests package helper: DummyFrontend, instantiateFrontend, loadProgram and verifyProgram.
//!
//! Behavior to preserve:
//! Start Silicon with --ignoreFile dummy.sil, initialize frontend, translate resource
//! <prefix><name>.vpr, and transform AbstractVerificationErrors on failure. DummyFrontend
//! verifier/config construction intentionally fails.
//!
//! Integration:
//! error_message_tests, node_backtranslation_tests, Silicon and Silver frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Agree on lifecycle cleanup and resource loading without turning missing hooks into success.
//!
//! Status: description only; implementation has not started.
