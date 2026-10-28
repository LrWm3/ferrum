//! Port plan: AdtPluginTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/AdtPluginTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! AdtPluginTests extends SiliconTests and owns a dedicated Silicon instance.
//!
//! Behavior to preserve:
//! Run adt fixtures with one verifier and inject silicon:plugin =
//! viper.silver.plugin.standard.adt.AdtPlugin into config before inherited configuration; retain
//! inherited result/annotation checks.
//!
//! Integration:
//! silicon_tests, Silver plugin manager and ADT fixtures.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Map native plugin registration while retaining option precedence.
//!
//! Status: description only; implementation has not started.
