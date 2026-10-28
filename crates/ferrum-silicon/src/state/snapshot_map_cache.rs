//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/SnapshotMapCache.scala
//!
//! Purpose:
//! Cache quantified-resource snapshot map summaries.
//!
//! Planned Rust structure:
//! SnapshotMapCache key is resource plus chunk sequence; value includes
//! SnapshotMapDefinition, total permission and optional domain condition. Implement get,
//! insert and union.
//!
//! Behavior to preserve:
//! Hit only for equal requested/cached conditions or cached True with no requested domain;
//! right side wins on union.
//!
//! QuantifiedChunkSupport bypasses a hit in extended exhale and honors the
//! disable-value-map-caching option; it emits definitions even on a hit.
//! HeapSupporter re-assumes cached value definitions before field access.
//!
//! Integration:
//! state::state, state::chunks and rules quantified snapshot definitions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Resource/chunk equality and cache ownership.
//!
//! Status: description only; implementation has not started.
