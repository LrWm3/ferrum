//! Port plan: ErrorMessageTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/ErrorMessageTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! ErrorMessageTests and executeTest compare baseline and rewritten verification.
//!
//! Behavior to preserve:
//! Run errorMessageTests/misc/simple, whileToIfGoto/simple,
//! combinedRewrites/{simple,involved,involved2} and
//! methodInlining/{simple,withArgs,withArgsNRes,withFields}. Rewrite asserts/exhales, loop
//! invariants and inlined contracts with error/node trafos; compare results or equal-length
//! failures by ordered fullId. Nested while fixture is commented out.
//!
//! Integration:
//! tests helper, Silver AST rewriting/diagnostics and Silicon verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Reconcile backtranslation hook behavior and preserve exact comparison, including its limited
//! fullId fallback.
//!
//! Status: description only; implementation has not started.
