//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/extensions/ConditionalPermissionRewriter.scala
//!
//! Purpose:
//! Rewrite conditional accessibility into conditional permissions when well-defined.
//!
//! Planned Rust structure:
//! Port ConditionalPermissionRewriter, Condition, ternaryRewriter, contextual rewriter,
//! conditionalize and makeCondExp.
//!
//! Behavior to preserve:
//! First split impure ternaries into implication conjunctions when condition lacks permission
//! introspection; then rewrite functions separately from predicates/methods, honoring function
//! wildcard option. Do not push through permission introspection, wildcard where forbidden, or
//! unsafe let-bound expressions; skip triggers and access children. For unsafe field receivers use
//! conditional null; unsafe predicate arguments and wands retain implication. Preserve metadata
//! and seen-node guard.
//!
//! Integration:
//! ferrum_silver::ast::utility::{expressions,rewriter}, Silicon verifier preprocessing/config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for contextual rewrites, metadata and AST identity.
//!
//! Open decisions:
//! Agree on proof-obligation and expression identity semantics with Silver rewriter and verifier.
//!
//! Status: description only; implementation has not started.
