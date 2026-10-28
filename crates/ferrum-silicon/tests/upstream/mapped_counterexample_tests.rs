//! Port plan: MappedCounterexampleTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/MappedCounterexampleTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! MappedCounterexampleTests, CounterexampleTestInput and ExpectedMappedCounterexampleAnnotation.
//!
//! Behavior to preserve:
//! Run counterexample_mapped with --counterexample mapped. Parse expected equalities/access
//! predicates, match failure ID/line and mapped failure context, resolve integers, rationals,
//! locals, reference fields and sequence indices, compare model entries and permissions. Retain
//! restricted pattern matches and parser position setup.
//!
//! Integration:
//! silicon_tests, Silicon reporting extracted model, Silver counterexample parser and test
//! annotations.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Reconcile mapped model, partial pattern failures and exact rational equality.
//!
//! Status: description only; implementation has not started.
