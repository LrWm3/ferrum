//! Port plan: SiliconTestsGreedyQP.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconTestsGreedyQP.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconTestsGreedyQP inherits SiliconTests.
//!
//! Behavior to preserve:
//! Run greedyQP fixtures with --timeout 600 --exhaleModeQP=0, selecting pure greedy mode rather
//! than fallback; fixture annotations determine expected results.
//!
//! Integration:
//! silicon_tests and quantified permission consumption.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Keep exact mode selection and source fixture expectations.
//!
//! Status: description only; implementation has not started.
