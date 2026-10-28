//! Port plan: GeneralCounterexampleTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/GeneralCounterexampleTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! GeneralCounterexampleTests extends SiliconTests and uses Silver CounterexampleTestInput.
//!
//! Behavior to preserve:
//! Run counterexample_mapped and counterexample_general fixtures with --counterexample resolved,
//! checking custom ExpectedCounterexample annotations using inherited output matching.
//!
//! Integration:
//! silicon_tests, Silver expected_counterexample_annotation and Silicon resolved model.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Agree on resolved model conversion and fixture selection.
//!
//! Status: description only; implementation has not started.
