//! Port plan: SiliconCounterexampleVariablesTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SiliconCounterexampleVariablesTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SiliconCounterexampleVariablesTests and SiliconExpectedValuesCounterexampleAnnotation.
//!
//! Behavior to preserve:
//! Use inherited counterexample_variables fixtures with --counterexample=variables and
//! --exhaleMode=1. Match expected equalities against SiliconVariableCounterexample.model in
//! failure contexts, using Silver CounterexampleComparison.
//!
//! Integration:
//! silicon_tests, Silver counterexample_variables_tests and Silicon interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Reconcile legacy variable model representation with failure contexts.
//!
//! Status: description only; implementation has not started.
