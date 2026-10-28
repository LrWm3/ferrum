//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/package.scala
//!
//! Purpose:
//! Define the common merge contract.
//!
//! Planned Rust structure:
//! Mergeable exposes merge(other) returning the same logical type.
//!
//! Behavior to preserve:
//! Merge semantics belong to each implementation, not a generic overwrite.
//!
//! Integration:
//! state::state and its mergeable recorders.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Trait shape and ownership with state merging.
//!
//! Status: description only; implementation has not started.
