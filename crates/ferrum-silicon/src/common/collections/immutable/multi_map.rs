//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/collections/immutable/MultiMap.scala
//!
//! Purpose:
//! Provide immutable map-of-sets helpers.
//!
//! Planned Rust structure:
//! MultiMap wrapper and empty factory expose addBinding and removeBinding.
//!
//! Behavior to preserve:
//! Removing the last value leaves the key mapped to an empty set; missing keys leave the
//! map unchanged.
//!
//! Integration:
//! common::collections and callers using immutable maps.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Whether extension methods become free functions.
//!
//! Status: description only; implementation has not started.
