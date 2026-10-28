//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/VerificationUnit.scala
//!
//! Purpose:
//! Expose a stateful unit verifier.
//!
//! Planned Rust structure:
//! VerificationUnit provides units and verify(State, unit) returning a sequence of
//! VerificationResult.
//!
//! Behavior to preserve:
//! Preserve result multiplicity and component lifecycle.
//!
//! Integration:
//! interfaces::preamble, supporters and state::state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Unit and state ownership with verification orchestration.
//!
//! Status: description only; implementation has not started.
