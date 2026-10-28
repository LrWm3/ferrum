//! Port plan: AstPositionsTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/AstPositionsTests.scala
//!
//! Purpose:
//! Port the upstream AstPositionsTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! AstPositionsTests and string-input ViperAstProvider helper.
//!
//! Behavior to preserve:
//! Parse inline field, methods, quantifier, chained comparisons and function; assert exact
//! start/end positions for field, method/argument, postconditions and their components, block,
//! forall statement, assert expression, second method/precondition and function. Field/function
//! start allow either keyword or identifier column.
//!
//! Integration:
//! frontend, parser translation and ast::position.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Reconcile line/column and end-position conventions with parser; keep allowed alternative
//! starts.
//!
//! Status: description only; implementation has not started.
