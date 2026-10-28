//! Port plan: ConcurrentInstantiationTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/ConcurrentInstantiationTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! ConcurrentInstantiationTests has two concurrent initialization cases.
//!
//! Behavior to preserve:
//! Run ten tasks in a ten-thread executor, await within 20 seconds: construct Silicon and parse
//! --logLevel ALL with dummy-program.sil; separately parse dummy input and start each verifier. No
//! verification or explicit stop is asserted.
//!
//! Integration:
//! Silicon config, verifier lifecycle and logging.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Reconcile independent verifier ownership and bounded concurrency without claiming verification
//! coverage.
//!
//! Status: description only; implementation has not started.
