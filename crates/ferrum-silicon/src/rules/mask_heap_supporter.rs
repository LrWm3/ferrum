//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/MaskHeapSupporter.scala
//!
//! Purpose:
//! Implement alternative mask-and-heap symbolic resource encoding.
//!
//! Planned Rust structure:
//! maskHeapSupporter implements HeapSupportRules and StatefulComponent: resource sequence
//! cache/lifecycle, ordered map merge, mask heap lookup/creation, wand heap merge and snapshot
//! conversions; mask subtraction/single-add simplification and bounds; single/quantified consume
//! and produce; field, current permission, havoc, forperm, function/predicate snapshots, resource
//! triggers and wand operations.
//!
//! Behavior to preserve:
//! Cache ordered resource sequences and clear on reset; resources sorted by name and first-map
//! ordering retained during map merge. Wand heap merge sums overlapping masks and merges heaps,
//! retaining resources appearing on just one side. Consume checks exact or constrainable permissions
//! and read-only access, uses reserve transfer during packaging and sums consumed masks; otherwise
//! subtract mask
//! and optionally freshen heap constrained to agree on known locations. simplifyOnConsume selects
//! solver-assisted cancellation. Quantified paths assume auxiliary and inverse definitions, assert
//! nonnegative permission and injectivity, build mask definitions and report appropriate failures;
//! inhale injectivity may be configured as assumed. Produce merges masks and heaps, assumes
//! good-mask and field bounds/non-nullness. Empty heaps use zero masks with fresh or dummy heaps.
//! Field reads/assignments assert permission, havoc frames untouched locations, trigger variants
//! offer heap and mask lookups, and function triggers use frame encoding. Preserve resource
//! snapshot conversion, predicate and wand-specific layouts and reserve merging.
//!
//! Integration:
//! rules::heap_supporter, quantified_chunk_support, magic_wand_supporter, evaluator, state::terms,
//! supporters::functions::mask_heap_function_encoding and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Mask/snapshot representation, ordered resource identity and solver/continuation ownership.
//!
//! Status: description only; implementation has not started.
