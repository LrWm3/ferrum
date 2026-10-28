//! Port plan: SiliconBackendTypeTest.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconBackendTypeTest.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconBackendTypeTest supplies a Silicon verifier to Silver BackendTypeTest.
//!
//! Behavior to preserve:
//! Inherited suite starts verifier and tests bitvector/float types, operations, fields, QPs and
//! success/failure AST attribution; this file only instantiates it with NoopReporter.
//!
//! Integration:
//! ferrum_silver::testing::backend_type_test and Silicon verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Coordinate shared suite and solver lifecycle across crates.
//!
//! Status: description only; implementation has not started.
