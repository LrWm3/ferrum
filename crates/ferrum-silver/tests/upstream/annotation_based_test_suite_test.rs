//! Port plan: AnnotationBasedTestSuiteTest.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/AnnotationBasedTestSuiteTest.scala
//!
//! Purpose:
//! Port the upstream AnnotationBasedTestSuiteTest.scala test or test-harness component.
//!
//! Planned Rust structure:
//! TestFixtures, DummyOutput, OutputMatcherTest, TestAnnotationsTest and OutputAnnotationIdTest.
//!
//! Behavior to preserve:
//! Exercise expected, unexpected, missing and additional output matching, project and key-prefix
//! filtering, ignore-file behavior and IDs foo/foo:bar. Preserve exact fixtures and assertions:
//! source additional-output case invokes actualFoo1 but expects actualFoo2, and missing-output
//! fixture references another file; flag these apparent mismatches rather than silently treating
//! them as valid passing tests.
//!
//! Integration:
//! annotation_based_test_suite, test_annotations, test_errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Resolve source assertion mismatches with upstream baseline before claiming compatibility.
//!
//! Status: description only; implementation has not started.
