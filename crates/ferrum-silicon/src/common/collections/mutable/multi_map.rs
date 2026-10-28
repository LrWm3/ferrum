//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/collections/mutable/MultiMap.scala
//!
//! Purpose:
//! Provide deterministic mutable multimap operations.
//!
//! Planned Rust structure:
//! MMultiMap supports addBinding, removeBinding and entryExists over linked maps and sets.
//!
//! Behavior to preserve:
//! Keep key and value insertion order; removal of the last value removes its key.
//!
//! Integration:
//! common::collections and graph/analysis clients.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Ordered collection implementation.
//!
//! Status: description only; implementation has not started.
