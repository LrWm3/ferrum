//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Heap.scala
//!
//! Purpose:
//! Hold an ordered sequence of symbolic chunks.
//!
//! Planned Rust structure:
//! Heap and HeapFactory expose values, append heap/chunk, remove and equalChunks;
//! ListBackedHeap uses a vector.
//!
//! Behavior to preserve:
//! Append retains duplicates and order; removal deletes the first matching chunk and fails
//! if absent. equalChunks sorts by string then compares chunks.
//!
//! Integration:
//! interfaces::state::chunks and state::state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Persistent heap representation and equality with branch merging.
//!
//! Status: description only; implementation has not started.
