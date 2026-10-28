//! Port plan: TestErrors.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/TestErrors.scala
//!
//! Purpose:
//! Port the upstream TestErrors.scala test or test-harness component.
//!
//! Planned Rust structure:
//! TestErrorType and TestError variants for annotation parsing, extra/missing/present outputs and
//! custom errors.
//!
//! Behavior to preserve:
//! Preserve error category group messages and per-error payload formatting including file/line,
//! output full ID and expected annotations.
//!
//! Integration:
//! annotation_based_test_suite, test_annotations and test_annotation_parser.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Represent test outcomes and diagnostic messages consistently with harness cancellation.
//!
//! Status: description only; implementation has not started.
