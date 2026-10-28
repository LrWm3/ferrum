//! Port plan: TestAnnotations.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/TestAnnotations.scala
//!
//! Purpose:
//! Port the upstream TestAnnotations.scala test or test-harness component.
//!
//! Planned Rust structure:
//! TestAnnotations, OutputAnnotationId, Located/Output/ProjectSpecific/Custom annotations and
//! concrete expected/missing/unexpected/ignore variants.
//!
//! Behavior to preserve:
//! Project matching is case-insensitive and allows hyphen-separated prefixes/suffixes; filter
//! output IDs by key prefix and preserve errors. Match full IDs by key and optional first value,
//! sameSource uses filesystem identity and line. IgnoreFileList causes file ignoring; retain
//! source behavior.
//!
//! Integration:
//! annotation_based_test_suite, test_annotation_parser and project_info.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Reconcile file identity and project matching against native path semantics.
//!
//! Status: description only; implementation has not started.
