//! Port plan: MemoryConsumptionTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/MemoryConsumptionTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! MemoryTests and DummySilverFrontend.
//!
//! Behavior to preserve:
//! The tagged memory case is ignored by default: start verifier, translate
//! src/test/scala/linkedlist.silver, verify 1001 times and sample GC-reported memory every ten
//! runs, then stop. Leak-detection assertion is commented out; this is observational, not a
//! passing leak check.
//!
//! Integration:
//! Silicon verifier and Silver frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Decide native memory measurement separately while marking upstream disabled checks explicitly.
//!
//! Status: description only; implementation has not started.
