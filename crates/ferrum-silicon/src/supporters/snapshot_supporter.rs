//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/SnapshotSupporter.scala
//!
//! Purpose:
//! Choose snapshot sorts and split/combine snapshots for assertion production and consumption.
//!
//! Planned Rust structure:
//! Port SnapshotSupporter and DefaultSnapshotSupporter optimalSnapshotSort, unit/combine/finalize,
//! empty constraint, production adaptation and createSnapshotPair.
//!
//! Behavior to preserve:
//! Default uses Unit and Combine, finalization is identity and empty constraint lazily requires
//! snapshot = Unit. Choose field sort, recursively inspect predicate body with cycle guard,
//! quantified field-value function sort or Snap fallback; preserve purity and conditional cases.
//! Split non-Unit snapshot via First/Second and assume its reconstruction equality; Unit cannot be
//! decomposed.
//!
//! Integration:
//! rules::{producer,consumer}, supporters::qps::predicate_snap_generator and
//! mask_heap_snapshot_supporter; state::terms and decider::decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for lazy snapshot effects, metadata and ownership.
//!
//! Open decisions:
//! Reconcile snapshot function/continuation signatures and optimal-sort recursion with producer,
//! consumer and mask heap alternative.
//!
//! Status: description only; implementation has not started.
