//! Port plan: ARPPluginTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/ARPPluginTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! ARPPluginTests extends SiliconTests.
//!
//! Behavior to preserve:
//! Run arp fixtures with --timeout 300 and --plugin viper.silver.plugin.standard.arp.ARPPlugin;
//! outcomes are checked by inherited annotated suite.
//!
//! Integration:
//! silicon_tests and Silver ARP plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Preserve plugin selection and annotated fixture expectations.
//!
//! Status: description only; implementation has not started.
