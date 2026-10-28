//! Port plan: SimplifierTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/SimplifierTests.scala
//!
//! Purpose:
//! Port the upstream SimplifierTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! SimplifierTests for conditional, division, modulo, equality and permissions.
//!
//! Behavior to preserve:
//! Assert impure conditional becomes implication while pure becomes disjunction; fold positive
//! division/remainder but leave zero divisor and negative operands untouched. Preserve
//! self-equality containing undefined sequence index. Fold permission subtraction and minimum to
//! conditional zero/full.
//!
//! Integration:
//! ast::utility::simplifier and ast::expression.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Use exact numeric semantics and preserve well-definedness guards.
//!
//! Status: description only; implementation has not started.
