//! Port plan: Isolate a variable in a restricted arithmetic expression for trigger rewriting.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/GenericArithmeticSolver.scala
//!
//! Purpose:
//! Isolate a variable in a restricted arithmetic expression for trigger rewriting.
//!
//! Planned Rust structure:
//! GenericArithmeticSolver adapters for type, traversal, containment, plus/minus and
//! SolverResult variants PreSolvingError, SolvingFailure, SolvingSuccess.
//!
//! Behavior to preserve:
//! Reject non-integer sides, identical lhs and target, or target occurrence count other than
//! one. Recursively invert addition and subtraction on the side containing the variable;
//! return failure for unsupported shapes, including the partially transformed equation.
//!
//! Integration:
//! ast::utility::{generic_axiom_rewriter,triggers} supplies the Silver-specific solver.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile generic expression operations and failure/diagnostic representation with the
//! axiom rewriter.
//!
//! Status: description only; implementation has not started.
