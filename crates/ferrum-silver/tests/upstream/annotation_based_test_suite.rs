//! Port plan: AnnotationBasedTestSuite.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/AnnotationBasedTestSuite.scala
//!
//! Purpose:
//! Port the upstream AnnotationBasedTestSuite.scala test or test-harness component.
//!
//! Planned Rust structure:
//! AnnotationBasedTestSuite, OutputMatcher, SystemUnderTest, AbstractOutput, AnnotatedTestInput
//! and DefaultAnnotatedTestInput.
//!
//! Behavior to preserve:
//! Register each input per system after project filtering; ignored empty file groups become
//! ignored tests. Match actual outputs by ID and location, prioritizing MissingOutput, then
//! expected/unexpected/custom and IgnoreOthers; one matched annotation is removed. Distinguish
//! additional, absent expected/unexpected, and present declared-missing outputs. Annotation/parser
//! errors may fail or cancel; known missing/unexpected annotations cancel.
//!
//! Integration:
//! resource_based_test_suite, test_annotations, test_errors, test_input, sil_suite.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Reconcile matching multiplicity and cancellation semantics with backend-specific test suites.
//!
//! Status: description only; implementation has not started.
