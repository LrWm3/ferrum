//! Port plan: TestAnnotationParser.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/TestAnnotationParser.scala
//!
//! Purpose:
//! Port the upstream TestAnnotationParser.scala test or test-harness component.
//!
//! Planned Rust structure:
//! TestAnnotationParser parsing, annotation finders and location finalization.
//!
//! Behavior to preserve:
//! Read annotations starting //:: followed by a space, collect parse errors and attach pending
//! located annotations to next non-comment line. Recognize ExpectedOutput, UnexpectedOutput,
//! MissingOutput, IgnoreOthers, IgnoreFile and IgnoreFileList with optional IDs/project issues;
//! preserve finder order and EOF behavior.
//!
//! Integration:
//! test_annotations, test_errors, counterexample annotation extensions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Reconcile newline/encoding handling and extensible finders with source fixtures.
//!
//! Status: description only; implementation has not started.
