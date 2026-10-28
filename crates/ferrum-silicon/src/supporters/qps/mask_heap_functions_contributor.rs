//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/qps/MaskHeapFunctionsContributor.scala
//!
//! Purpose:
//! Contribute map, mask and wrapper preambles for mask-heap encoding.
//!
//! Planned Rust structure:
//! Port MaskHeapFunctionsContributor analysis, field/predicate/wand sort collection, parameterized
//! declaration and axiom generation, and lifecycle/emission.
//!
//! Behavior to preserve:
//! Only analyze under maskHeapMode; collect all fields and predicates, add mask/predicate sorts
//! and wand heap sort when wands occur. Emit map and zero-mask definitions, predicate/wand
//! variants and per-resource wrappers in source order with exact sort/name substitutions.
//!
//! Integration:
//! rules::mask_heap_supporter, state::terms sorts, config, preamble_reader and prover;
//! default_sets_contributor.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for configuration and ordered prover emission; retain maps_*,
//! mask_* and heapwrappers_*.smt2 resources.
//!
//! Open decisions:
//! Reconcile template substitutions, predicate/wand sort identity and configuration ownership with
//! mask heap rules.
//!
//! Status: description only; implementation has not started.
