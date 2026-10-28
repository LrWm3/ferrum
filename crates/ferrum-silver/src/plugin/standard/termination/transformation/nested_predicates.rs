//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/NestedPredicates.scala
//!
//! Purpose:
//! Generate nested predicate-instance relationships for termination measures.
//!
//! Planned Rust structure:
//! Port NestedPredicates containsPredicateInstances, addNestedPredicateInformation, unfold/body
//! transformation, predicate assignments and unique local generation.
//!
//! Behavior to preserve:
//! When unfolding, assign caller instance, unfold, then inspect instantiated predicate body once
//! and inhale nested relations for predicate accesses; field accesses contribute nothing. Respect
//! conditional/implication branches and sequential binary traversal. Missing nestedPredicates
//! function reports consistency error and produces empty statement; preserve generated-name and
//! local-variable bookkeeping.
//!
//! Integration:
//! predicateinstance::predicate_instance_ast_extension, program_manager and function/method
//! checks; ast rewriter and verifier consistency errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact node metadata, naming and mutable state.
//!
//! Open decisions:
//! Reconcile hash-derived local names, domain substitutions and ownership with predicateinstance
//! and AST.
//!
//! Status: description only; implementation has not started.
