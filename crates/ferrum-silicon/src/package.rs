//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/package.scala
//!
//! Purpose:
//! Provide deterministic collection and trigger aliases for Silicon.
//!
//! Planned Rust structure:
//! TriggerSet/TriggerSets, immutable Map/toMap, Stack, MList, MSet, MMap, MStack and predefMapToMap
//! conversion.
//!
//! Behavior to preserve:
//! Immutable map uses TreeSeqMap insertion order; mutable sets/maps are linked, stack is
//! sequence/list. Preserve order and duplicate-key behavior rather than random hash iteration.
//!
//! Integration:
//! state, rules, decider and verifier collections.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Native ordered collections and aliases.
//!
//! Status: description only; implementation has not started.
