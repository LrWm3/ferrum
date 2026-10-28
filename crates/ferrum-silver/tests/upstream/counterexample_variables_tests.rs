//! Port plan: CounterexampleVariablesTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/CounterexampleVariablesTests.scala
//!
//! Purpose:
//! Port the upstream CounterexampleVariablesTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! CounterexampleVariablesTests, CounterexampleTestInput, ExpectedValuesCounterexampleAnnotation
//! and CounterexampleComparison.
//!
//! Behavior to preserve:
//! Discover counterexample_variables fixtures; extend annotation parser for ExpectedCounterexample
//! and parse with initialized FastParser offsets. Match ID/line plus some failure context; legacy
//! comparison resolves integer, Boolean, negative and variable constants and requires all expected
//! equalities.
//!
//! Integration:
//! sil_suite, test_annotation_parser, expected_counterexample_annotation, parser and verifier
//! model.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Coordinate backend-specific annotation implementation and model entry comparison with resolved
//! counterexamples.
//!
//! Status: description only; implementation has not started.
