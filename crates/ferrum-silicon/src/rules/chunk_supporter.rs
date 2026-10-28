//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/ChunkSupporter.scala
//!
//! Purpose:
//! Consume, produce and look up nonquantified resource chunks.
//!
//! Planned Rust structure:
//! ChunkSupportRules and chunkSupporter implement consume/consume2/consumeGreedy, produce,
//! lookup/lookupGreedy, findChunk, findChunksWithID and splitHeap.
//!
//! Behavior to preserve:
//! Find literal aliases first then ask solver; splitHeap rejects matching quantified chunks. Greedy
//! exact read takes min and removes or reinserts residual chunk, checks remaining permissions;
//! constrainable read assumes strict bound, read-only checks positive access without removal. In
//! package mode transfer through wand reserves; otherwise retry with temporary main heap, choosing
//! complete or greedy exhale. Smoke-dead paths return Success, except package lookup yields fresh
//! value; ordinary failures build counterexample. Missing returned snapshot creates and records a
//! fresh snapshot despite stale upstream comment suggesting unit. Produce consolidates and assumes
//! properties.
//!
//! Integration:
//! rules::more_complete_exhale_supporter, magic_wand_supporter, state_consolidator,
//! consumption_result and resources::properties.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Alias matching, snapshots and continuations with heap supporter.
//!
//! Status: description only; implementation has not started.
