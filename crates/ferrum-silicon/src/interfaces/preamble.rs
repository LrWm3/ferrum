//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/Preamble.scala
//!
//! Purpose:
//! Define preamble reading and contributor lifecycle.
//!
//! Planned Rust structure:
//! PreambleReader reads ordinary and parametric resources and emits to ProverLike;
//! PreambleContributor analyzes program and declares sorts, symbols and axioms;
//! VerifyingPreambleContributor adds post-verification outputs.
//!
//! Behavior to preserve:
//! Resource overload reads before emission; options flag is passed through. Keep analysis
//! and verification stages and their declarations separate.
//!
//! Integration:
//! decider::prover, supporters and interfaces::verification_unit.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Generic input/output and component lifecycle.
//!
//! Status: description only; implementation has not started.
