//! Port plan: SiliconTestsSIFPlugin.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconTestsSIFPlugin.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconTestsSIFPlugin inherits SiliconTests.
//!
//! Behavior to preserve:
//! Run sif fixtures with --timeout 300 and --plugin=viper.silver.plugin.sif.SIFPlugin.
//!
//! Integration:
//! silicon_tests and Silver SIF plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Reconcile native plugin registration with inherited configuration.
//!
//! Status: description only; implementation has not started.
