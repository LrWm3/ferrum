//! Port plan: Simplify expressions and statements through bottom-up rewriting.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Simplifier.scala
//!
//! Purpose:
//! Simplify expressions and statements through bottom-up rewriting.
//!
//! Planned Rust structure:
//! Simplifier.simplify, AnyPermLiteral and ratToPerm; cached per-expression simplification and
//! well-definedness option.
//!
//! Behavior to preserve:
//! Preserve pattern order for Boolean, implication/conditional, comparison, integer and exact
//! rational permission reductions and empty/trivial statements. Only fold division/modulo for
//! nonnegative dividend and positive divisor; never fold zero divisors. Several rules depend
//! on known well-definedness or the explicit assumption flag. Cache both old and resulting
//! expression and skip cached descendants; source cache does not key by flag.
//!
//! Integration:
//! ast::{expression,statement}, ast::utility::{expressions,statements,rewriter}, utility
//! rational arithmetic.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile cache identity, assumption-sensitive reuse and metadata with AST handles and
//! callers; investigate source cache behavior rather than silently changing it.
//!
//! Status: description only; implementation has not started.
