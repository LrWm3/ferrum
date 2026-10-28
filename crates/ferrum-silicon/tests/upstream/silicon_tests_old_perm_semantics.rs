//! Port plan: SiliconTestsOldPermSemantics.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconTestsOldPermSemantics.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconTestsOldPermSemantics inherits SiliconTests.
//!
//! Behavior to preserve:
//! Run oldpermsemantics fixtures with --timeout 300 --respectFunctionPrePermAmounts.
//!
//! Integration:
//! silicon_tests and Silver/Silicon permission semantics.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Coordinate legacy flag with frontend consistency checks.
//!
//! Status: description only; implementation has not started.
