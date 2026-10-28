//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/ExpTransformer.scala
//!
//! Purpose:
//! Turn expressions into statements that check termination while maintaining evaluation context.
//!
//! Planned Rust structure:
//! Port ExpTransformer transformExp, ExpressionContext, toPureBooleanExp, fresh-variable
//! substitution, emptiness and unsupported-expression helpers.
//!
//! Behavior to preserve:
//! Preserve conjunction inhale ordering via nondeterministic branch, short circuit for boolean
//! operators, conditional branches, unfolding/applying and inhale-exhale choices, let bindings and
//! quantified variable substitutions. ForPerm checks body under positive permission and kills
//! branch; Exists inhales witnesses. Access predicates check amount then inhale; unsupported
//! extension expressions report consistency errors.
//!
//! Integration:
//! function_check overrides function calls; program_manager, ast::utility::{expressions,rewriter}
//! and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for branching, state independence, metadata and name order.
//!
//! Open decisions:
//! Agree on traversal and explicit expression context with function_check and ast rewriter.
//!
//! Status: description only; implementation has not started.
