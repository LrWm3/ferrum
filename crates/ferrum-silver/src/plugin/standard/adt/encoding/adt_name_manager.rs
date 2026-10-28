//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/encoding/AdtNameManager.scala
//!
//! Purpose:
//! Generate and remember collision-free names for ADT encoding.
//!
//! Planned Rust structure:
//! Port AdtNameManager usedNames, memoized getName, uniqueName and fixed
//! contains/well-founded/destructor/tag naming helpers.
//!
//! Behavior to preserve:
//! Seed from transitive scoped declarations; reuse mapping for each requested base and append
//! numeric suffixes from 1 on collision. ContainsDomain, contains and well-founded names are fixed
//! resource interfaces; preserve source reservation behavior for initially unused names.
//!
//! Integration:
//! encoding::adt_encoder and resources/adt/contains.vpr; termination well-founded-order resources.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for deterministic naming and collection semantics.
//!
//! Open decisions:
//! Reconcile name collisions and generated-name reservation with encoder and resources.
//!
//! Status: description only; implementation has not started.
