//! Port plan: TestInput.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/TestInput.scala
//!
//! Purpose:
//! Port the upstream TestInput.scala test or test-harness component.
//!
//! Planned Rust structure:
//! TestInput, DefaultTestInput and filename grouping/tag creation.
//!
//! Behavior to preserve:
//! Group files matching <base>_file<number> in same directory sorted numerically; derive canonical
//! name and tags from full/relative paths, filename, stem and parent prefixes. file returns first
//! entry; preserve source parsing and failure behavior for malformed numeric suffixes.
//!
//! Integration:
//! resource_based_test_suite, annotation_based_test_suite and test annotations.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Agree on platform path handling, resource discovery and tagging semantics.
//!
//! Status: description only; implementation has not started.
