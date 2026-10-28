//! Port plan: SiliconTestsSimplifiedUnfold.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconTestsSimplifiedUnfold.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconTestsSimplifiedUnfold inherits SiliconTests.
//!
//! Behavior to preserve:
//! Run all/predicates fixtures with --timeout 300 --enableSimplifiedUnfolds.
//!
//! Integration:
//! silicon_tests and unfold rules.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Preserve option and annotation outcomes.
//!
//! Status: description only; implementation has not started.
