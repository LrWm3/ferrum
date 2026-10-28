//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/MaskHeapSnapshotSupporter.scala
//!
//! Purpose:
//! Adapt snapshot handling to per-resource mask/heap encoding.
//!
//! Planned Rust structure:
//! Port MaskHeapSnapshotSupporter overrides for unit/combine/finalize, produce adaptation, empty
//! constraint and snapshot pairing.
//!
//! Behavior to preserve:
//! Consume snapshots as ordered resource masks, merge preserving first order and fill absent
//! resource masks with zero; finalize against the evaluation heap into heap-restricted snapshot
//! tree. Produce converts snapshot tree leaves to aliased per-resource heaps when needed. Empty
//! constraint is absent and both conjuncts receive the same snapshot function rather than
//! splitting.
//!
//! Integration:
//! supporters::snapshot_supporter, rules::{mask_heap_supporter,magic_wand_supporter},
//! state::{terms,heap} and decider::decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for branch state, ordering, solver aliasing and snapshot
//! identity.
//!
//! Open decisions:
//! Agree on resource-key identity, heap lifetime and alias ownership with mask_heap_supporter and
//! producer/consumer.
//!
//! Status: description only; implementation has not started.
