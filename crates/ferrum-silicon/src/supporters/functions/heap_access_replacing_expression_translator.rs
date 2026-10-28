//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/HeapAccessReplacingExpressionTranslator.scala
//!
//! Purpose:
//! Translate function contracts and bodies using snapshots recorded during symbolic execution.
//!
//! Planned Rust structure:
//! Port HeapAccessReplacingExpressionTranslator translate/body/precondition/postcondition, context
//! stack and getOrFail; extend expression_translator.
//!
//! Behavior to preserve:
//! Preconditions use exhale interpretation and ignore access predicates/wands; postconditions use
//! inhale interpretation. Resolve locations and calls by AST plus let/quantifier context,
//! normalize quantified variable suffixes and choose limited versus defined application by call
//! height and opaque/reveal annotations. Missing recordings warn once unless prior failure,
//! optionally mark failure and yield a fresh unresolved symbol; nested-context fallback applies
//! under quantifiers. Preserve encoding-specific function application and source behavior of
//! mutable flags. translatePrecondition sets ignoreAccessPredicates to true; the other public
//! translation methods do not reset it, an upstream behavior to reconcile with callers.
//!
//! Integration:
//! functions::{function_data,function_recorder,function_encoding},
//! supporters::expression_translator, rules::function_supporter, state::terms and reporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for AST keys, source context, diagnostic and symbol freshness.
//!
//! Open decisions:
//! Review mutable ignoreAccessPredicates/reset behavior and unresolved symbol dependence on
//! quantified variables with function axiom generation.
//!
//! Status: description only; implementation has not started.
