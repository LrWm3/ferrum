//! Port plan: SimpleArithmeticTermSolverTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/SimpleArithmeticTermSolverTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! SimpleArithmeticTermSolverTests and shared term DSL.
//!
//! Behavior to preserve:
//! Initialize empty verifier Config before each case. Check simple and nested isolation with
//! addition/subtraction, exact partial SolvingFailure at f(y), and non-success expectations;
//! pre-solving tests only assert SolverResult supertype, with DSL b itself Int-sorted, so do not
//! claim they establish type-error behavior.
//!
//! Integration:
//! state::{terms,triggers::SimpleArithmeticSolver} and verifier config; DSL also serves
//! trigger rewriter tests.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Preserve term normalization/equality and note weak source assertions.
//!
//! Status: description only; implementation has not started.
