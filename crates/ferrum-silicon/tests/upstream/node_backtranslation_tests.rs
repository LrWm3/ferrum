//! Port plan: NodeBacktranslationTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/NodeBacktranslationTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! NodeBacktranslationTests.runTest and two issue #348 fixtures.
//!
//! Behavior to preserve:
//! Load errorMessageTests/misc/0348-1 and 0348-2; build assignment map, force-copy locals with
//! NodeTrafo and compare against a substitution-derived expected exhale. Verify rewritten program,
//! require Failure, and assert first readable error contains substituted assertion text.
//!
//! Integration:
//! tests helper, Silver AST metadata/rewrite and Silicon verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Preserve metadata-only force-copy and error backtranslation semantics.
//!
//! Status: description only; implementation has not started.
