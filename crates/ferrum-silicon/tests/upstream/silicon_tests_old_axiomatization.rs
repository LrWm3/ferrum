//! Port plan: SiliconTestsOldAxiomatization.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconTestsOldAxiomatization.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconTestsOldAxiomatization inherits SiliconTests.
//!
//! Behavior to preserve:
//! Run oldaxiomatization fixtures with --timeout 300 --useOldAxiomatization.
//!
//! Integration:
//! silicon_tests and alternative encoding resources.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Keep old encoding option and corpus separate.
//!
//! Status: description only; implementation has not started.
