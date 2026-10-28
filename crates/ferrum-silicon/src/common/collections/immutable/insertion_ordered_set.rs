//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/collections/immutable/InsertionOrderedSet.scala
//!
//! Purpose:
//! Provide immutable insertion-ordered set operations.
//!
//! Planned Rust structure:
//! InsertionOrderedSet and its factory/builder implement contains, incl, excl, iteration,
//! size, from and clear.
//!
//! Behavior to preserve:
//! Reinsertion retains position; removal then insertion moves it; builder deduplicates and
//! empty/from may reuse instances.
//!
//! Integration:
//! state::terms, state::state and interfaces::decider::prover.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Persistent ordered-set representation and equality.
//!
//! Status: description only; implementation has not started.
