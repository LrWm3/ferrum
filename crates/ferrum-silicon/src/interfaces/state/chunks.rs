//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/state/Chunks.scala
//!
//! Purpose:
//! Define symbolic heap chunk contracts.
//!
//! Planned Rust structure:
//! Chunk, ChunkIdentifer, MaskHeapChunk, GeneralChunk, NonQuantifiedChunk and
//! QuantifiedChunk describe substitution, resource, permission, snapshot and update
//! interfaces.
//!
//! Behavior to preserve:
//! Preserve subtype-specific return contracts, optional debug expressions, tags, inverse
//! functions and quantified variables; condition and permission updates return chunks.
//!
//! Integration:
//! state::chunks, resources and rules::quantified_chunk_support.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Enum versus trait representation with state::chunks.
//!
//! Status: description only; implementation has not started.
