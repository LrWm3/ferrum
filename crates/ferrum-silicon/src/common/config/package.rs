//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/config/package.scala
//!
//! Purpose:
//! Supply wildcard and version utilities.
//!
//! Planned Rust structure:
//! wildcardToRegex, VersionComparator and Version relational, equality and prefix
//! operators.
//!
//! Behavior to preserve:
//! Replacement order escapes dot and dollar and maps ? to .? and * to .*?; comparator
//! consumes integer dot components until one stops, while equality compares original
//! strings.
//!
//! Integration:
//! config and interfaces::decider::prover.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Exact Scanner integer token behavior and version wrapper API.
//!
//! Status: description only; implementation has not started.
