//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/collections/package.scala
//!
//! Purpose:
//! Compute Cartesian products.
//!
//! Planned Rust structure:
//! crossProduct folds left from one empty vector, appending each element in nested
//! iteration order.
//!
//! Behavior to preserve:
//! Empty outer input yields one empty sequence; any empty inner input yields no
//! combinations.
//!
//! Integration:
//! common::collections and state::terms::utils.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Generic iterator ownership.
//!
//! Status: description only; implementation has not started.
