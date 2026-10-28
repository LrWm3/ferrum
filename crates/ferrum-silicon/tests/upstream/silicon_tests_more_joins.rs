//! Port plan: SiliconTestsMoreJoins.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconTestsMoreJoins.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconTestsMoreJoins overrides inclusion and config.
//!
//! Behavior to preserve:
//! Run examples with --timeout 300 --moreJoins=2 but exclude
//! examples/vmcai2016/linked-list-predicates.vpr due to incompleteness, in addition to inherited
//! filters.
//!
//! Integration:
//! silicon_tests and branching/join rules.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Preserve exclusion and inherited annotation checks.
//!
//! Status: description only; implementation has not started.
