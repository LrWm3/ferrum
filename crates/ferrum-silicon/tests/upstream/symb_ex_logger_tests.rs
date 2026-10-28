//! Port plan: SymbExLoggerTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SymbExLoggerTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SymbExLoggerTests, SiliconFrontendWithUnitTesting, comparison and SymbExLogUnitTestError.
//!
//! Behavior to preserve:
//! Run symbExLogTests with --timeout 300 --disableCaching --ideModeAdvanced
//! --numberOfParallelVerifiers 1. When .elog exists write .alog and match expected lines as
//! ordered subsequence with actual indentation at least expected; append log mismatch to verifier
//! failure. Source comparison checks expected.hasNext at end and may miss an unmatched final
//! current line.
//!
//! Integration:
//! Silicon symbolic log, Silver annotated suite and .elog fixtures.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Reconcile log output ownership, temporary files and comparison edge case without silently
//! strengthening behavior.
//!
//! Status: description only; implementation has not started.
