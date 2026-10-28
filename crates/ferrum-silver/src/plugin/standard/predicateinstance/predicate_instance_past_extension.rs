//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/predicateinstance/PredicateInstancePASTExtension.scala
//!
//! Purpose:
//! Represent #predicate(args) in the parse AST.
//!
//! Planned Rust structure:
//! Port PPredicateInstanceKeyword, PMarkerSymbol and PPredicateInstance with mutable
//! substitutions, typecheck, forceSubstitution and translateExp.
//!
//! Behavior to preserve:
//! Retype reference as a predicate call and reuse its typechecking/substitutions; force
//! substitutions on arguments; preserve source position on translation. The undefined-name branch
//! lacks a return before the subsequent independent if, so examine its observed behavior rather
//! than assume the intended error.
//!
//! Integration:
//! parser::parse_ast, resolver and translator; predicate_instance_ast_extension and
//! predicate_instance_plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for mutable parse nodes and extension hooks.
//!
//! Open decisions:
//! Reconcile undefined-name control flow and type representation with resolver before
//! implementation.
//!
//! Status: description only; implementation has not started.
