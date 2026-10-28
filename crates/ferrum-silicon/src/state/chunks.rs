//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Chunks.scala
//!
//! Purpose:
//! Implement heap chunks for ordinary, quantified, wand and mask-heap resources.
//!
//! Planned Rust structure:
//! ChunkIdentifier/BasicChunkIdentifier and MagicWandIdentifier; BasicChunk,
//! QuantifiedBasicChunk, QuantifiedFieldChunk, QuantifiedPredicateChunk,
//! QuantifiedMagicWandChunk, MagicWandChunk and BasicMaskHeapChunk. Implement condition,
//! permission arithmetic, snapshot replacement, lookup and substitution for each.
//!
//! Behavior to preserve:
//! Check permission/snapshot sorts and field lookup arity; quantified field/predicate
//! permission is conditional and their scaling uses computed permission. Preserve optional
//! expression assumptions, tags, hints, inverse functions and singleton arguments. Wand
//! identifier equality uses structure index hash only; wand snapshot replacement requires
//! MagicWandSnapshot and no expression. Substitution follows each class fields, not all
//! metadata.
//!
//! Merging quantified chunks may retain inverse functions from multiple source
//! assertions because their definitions and matching triggers remain needed.
//! Quantified wand snapshots use predicate snapshot functions with wand-snapshot
//! codomain; the field's synthetic receiver is ?r and debug declarations are
//! created only in debugging mode.
//!
//! Integration:
//! interfaces::state::chunks, state::terms, resources, rules::quantified_chunk_support
//! (InverseFunctions) and ferrum_silver::ast.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Chunk identity, expression pairing and wand structural indexing with heap and state.
//!
//! Status: description only; implementation has not started.
