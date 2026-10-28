//! Port plan: AstAnnotationTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/AstAnnotationTests.scala
//!
//! Purpose:
//! Port the upstream AstAnnotationTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! AstAnnotationTests and a string-input ViperAstProvider helper.
//!
//! Behavior to preserve:
//! Parse, pretty-print and reparse the inline annotated program; assert annotations on field,
//! repeated predicate annotations merged in order, domain function, assignment, RHS and nested
//! arguments while LHS and right operand remain unannotated.
//!
//! Integration:
//! frontend, parser, ast::{ast,program,pretty} and reporter/logger.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Coordinate source annotation values and parser/pretty-printer roundtrip with AST metadata
//! ownership.
//!
//! Status: description only; implementation has not started.
