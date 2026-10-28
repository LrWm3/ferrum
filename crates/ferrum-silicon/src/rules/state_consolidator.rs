//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/StateConsolidator.scala
//!
//! Purpose:
//! Merge heap chunks and derive permission and snapshot facts.
//!
//! Planned Rust structure:
//! StateConsolidationRules plus MinimalStateConsolidator, DefaultStateConsolidator,
//! RetryingStateConsolidator, RetryingFailOnlyStateConsolidator, LastRetryStateConsolidator,
//! LastRetryFailOnlyStateConsolidator, MinimalRetryingStateConsolidator,
//! MoreComplexExhaleStateConsolidator and MaskHeapStateConsolidator. Default implements
//! singleMerge, alias matching, chunk merging, combineSnapshots and quantified field bounds.
//!
//! Behavior to preserve:
//! Default saturates then repeatedly merges each main/reserve heap until no snapshot equalities
//! arise, assuming instance and delayed resource properties. During wand packaging retain only
//! first three newly consolidated reserve heaps; later outer heaps remain original. Basic aliases
//! combine permission and guard snapshot equalities; uncertain positivity creates fresh constrained
//! snapshot. Quantified merge behavior depends on exhaleModeQP: more-complete combines only
//! matching field/predicate maps; all other modes summarise, retaining both inverse-function lists
//! and singleton only for identical tuples. Bounds use field triggers or inverse-function/pointwise
//! singleton triggers; no untriggered bound for chunks without either. Retry and last-retry variants
//! control when consolidation runs; fail-only variants suppress optional consolidation. Minimal
//! retrying keeps simple merge and no quantified bounds. MoreComplexExhaleStateConsolidator only
//! assumes nonquantified field bounds on the main heap when retrying, without consolidating it.
//! MaskHeapStateConsolidator delegates heap merge to mask heap rules; its single-chunk merge is
//! upstream unimplemented.
//!
//! Integration:
//! rules::chunk_supporter, quantified_chunk_support, more_complete_exhale_supporter,
//! mask_heap_supporter, resources and state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Heap and snapshot equality, quantifier identity and consolidator selection.
//!
//! Status: description only; implementation has not started.
