//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/predicateinstance/PredicateInstancePlugin.scala
//!
//! Purpose:
//! Lower predicate instance expressions into generated functions guarded by predicate permission.
//!
//! Planned Rust structure:
//! Port PredicateInstancePlugin predicateInstance parser, beforeParse/beforeVerify, generated
//! function cache and entity/program error mapping.
//!
//! Behavior to preserve:
//! Register # expression at start. Bottom-up rewrite creates one PI_<predicate> function per used
//! predicate in insertion order with wildcard predicate-access precondition and PredicateInstance
//! domain result, appending them to functions. Report missing domain as consistency error; map
//! PreconditionInAppFalse through ErrTrafo to PredicateInstanceNoAccess.
//!
//! Integration:
//! parser::fast_parser and translator; predicate_instance AST/PAST/errors, ast::utility::rewriter
//! and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, diagnostics and AST identity.
//!
//! Open decisions:
//! Agree on generated names, domain resolution and error transformation with ast and verifier.
//!
//! Status: description only; implementation has not started.
