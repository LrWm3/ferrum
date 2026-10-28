//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/ExpressionTranslator.scala
//!
//! Purpose:
//! Translate heap-independent Silver expressions to symbolic terms.
//!
//! Planned Rust structure:
//! Port ExpressionTranslator translate with quantifier, Boolean/arithmetic,
//! function/domain/backend, permissions, sequence, set/multiset, map and let dispatch.
//!
//! Behavior to preserve:
//! Translate forall/exists triggers using limited heap-dependent function versions; preserve
//! quantifier weights and builtin-domain naming mode. Pure functions receive snapshot arguments;
//! collections preserve operand orientation, literals fold in source order, maps desugar.
//! Explicitly reject unexpected heap-dependent/extension expressions rather than assume them.
//!
//! Integration:
//! supporters::domains and functions::heap_access_replacing_expression_translator,
//! rules::{function_supporter,evaluator}, state::terms and Silver AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact arithmetic, term identity, trigger order and explicit
//! context.
//!
//! Open decisions:
//! Reconcile builtin mode and pure-function snapshot argument conventions with domain and function
//! encoders.
//!
//! Status: description only; implementation has not started.
