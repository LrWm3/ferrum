//! Port plan: ViperTutorialExamples.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/ViperTutorialExamples.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! ViperTutorialExamples extends SiliconTests and is DoNotDiscover.
//!
//! Behavior to preserve:
//! Select viper_tutorial_examples directory with inherited verification and annotations; suite
//! requires explicit discovery/run.
//!
//! Integration:
//! silicon_tests and tutorial fixture resources.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Retain non-default discovery and actual fixture availability.
//!
//! Status: description only; implementation has not started.
