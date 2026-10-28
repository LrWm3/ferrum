//! Port plan: ResourceBasedTestSuite.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/ResourceBasedTestSuite.scala
//!
//! Purpose:
//! Port the upstream ResourceBasedTestSuite.scala test or test-harness component.
//!
//! Planned Rust structure:
//! ResourceBasedTestSuite registration and test-directory traversal.
//!
//! Behavior to preserve:
//! Recursively visit sorted directories/files, include readable .sil/.vpr by default, build inputs
//! and register multifile group only at its first file; respect runner tag filters and register
//! once. Missing resource or non-directory asserts; registration may occur before config map is
//! populated.
//!
//! Integration:
//! test_input and annotation_based_test_suite; upstream resources.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Reconcile filesystem discovery, tags and delayed registration with Rust test runner.
//!
//! Status: description only; implementation has not started.
