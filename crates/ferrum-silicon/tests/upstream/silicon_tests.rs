//! Port plan: SiliconTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconTests shared annotated end-to-end suite and frontend/config setup.
//!
//! Behavior to preserve:
//! Discover consistency, all, quantifiedpermissions, quantifiedpredicates, quantifiedcombinations,
//! wands, termination, refute and examples. Require one file, use NoopReporter; parse --timeout
//! 600 plus silicon-prefixed config and dummy filename. UnexpectedOutput cancels; MissingOutput
//! cancels except issue 34.
//!
//! Integration:
//! Silver sil_suite/annotation_based_test_suite, SiliconFrontend and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Preserve configuration precedence, lifecycle and issue-specific cancellation with native
//! harness.
//!
//! Status: description only; implementation has not started.
