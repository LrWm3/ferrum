//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/BaseVerifier.scala
//!
//! Purpose:
//! Assemble worker-local verifier services and select heap/state strategies.
//!
//! Planned Rust structure:
//! BaseVerifier owns counters, decider, term and symbol converters, identifier factory,
//! trigger/axiom and quantifier supporters, formatter, snapshot supporter and optional member log;
//! choose heap and consolidation implementations from config/member annotations.
//!
//! Behavior to preserve:
//! Unique id must be globally unique and valid for files and solver symbols. Mask heap overrides
//! consolidation and selects mask snapshot/heap supporters. Per-member consolidation annotation
//! overrides configured mode otherwise; preserve every mode. Lifecycle starts/resets/stops decider,
//! converter and identifiers in order; reset clears error count and counters.
//!
//! Integration:
//! verifier::verifier, decider, rules::{state_consolidator,heap_supporter}, supporters and logger.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Worker-owned mutable services, logging and strategy lifetimes.
//!
//! Status: description only; implementation has not started.
