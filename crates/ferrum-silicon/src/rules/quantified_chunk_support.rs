//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/QuantifiedChunkSupport.scala
//!
//! Purpose:
//! Implement quantified permissions, snapshot/permission summaries and chunk matching.
//!
//! Planned Rust structure:
//! InverseFunctions carries condition, invertibles, additional arguments, inverse/image functions
//! and paired axioms; SnapshotMapDefinition and PermMapDefinition carry emitted definitions.
//! QuantifiedChunkSupport and quantifiedChunkSupporter implement singleton/general chunk
//! construction, heap partition, snapshot/permission map creation and caching,
//! quantified/single-location produce and consume, assertReadPermission/removePermissions, inverse
//! and injectivity axioms, alias matching, snapshot-map combination and chunk-order heuristics.
//!
//! Behavior to preserve:
//! Construct field, predicate and wand chunks with proper sorts, singleton args, inverse
//! substitutions and tags; splitHeap rejects matching nonquantified chunks. Summary definitions
//! condition value equality on positive permission, use snapshot-tuple codomains for
//! predicates/wands, preserve optional domains and configured triggers. Snapshot-map cache keys
//! use resource and ordered chunks; a hit also requires compatible stored domain condition
//! (equal, or cached True with no requested condition). Bypass snapshot cache in extended exhale
//! and re-emit value definitions on hits, plus domain definitions when requested. Permission-map
//! cache uses resource/chunks and likewise re-emits its value definitions.
//! Production scales permissions, selects explicit or inferred inverse triggers, checks nonnegative
//! and optionally injectivity, assumes inverse and resource properties then merges chunk; retain
//! function recorder and trigger summaries. Consumption checks nonnegative and injectivity, handles
//! wand reserve transfer, and otherwise removes from threaded partial heap. Greedy modes retry
//! after consolidation; complete mode avoids extra retry. Single-location paths distinguish missing
//! wand from insufficient permission and return wand snapshot-function lookup without Snap
//! conversion. Removal respects read-only mode, configurable ordering, greedy subset checks versus
//! complete matching, exact versus constrainable permissions, short intermediate checks and
//! mandatory final check; track untouched chunks for summaries and optional permission macros.
//! Inverse creation asserts arity/sorts and generates image functions for every quantified variable
//! despite older prose suggesting exceptions; axioms preserve trigger choices and global scope.
//! Greedy matching prioritizes original condition/tag then subset proof; complete matching proves
//! locations and conditions. Fresh snapshot maps when neither permission is provably positive avoid
//! unsound reuse.
//!
//! Integration:
//! rules::heap_supporter, mask_heap_supporter, consumer, producer, havoc_supporter,
//! magic_wand_supporter, state_consolidator, state::snapshot_map_cache, resources and
//! state::triggers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Inverse/trigger identity, caches, snapshot map and continuation/solver ownership with all heap
//! encodings.
//!
//! Status: description only; implementation has not started.
