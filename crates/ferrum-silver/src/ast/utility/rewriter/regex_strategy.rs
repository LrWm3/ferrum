//! Port plan: Match tree-regex paths and rewrite marked nodes with context.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/RegexStrategy.scala
//!
//! Purpose:
//! Match tree-regex paths and rewrite marked nodes with context.
//!
//! Planned Rust structure:
//! RegexContext, PartialContextR, SimpleRegexContext, SlimRegexStrategy and RegexStrategy with
//! MatchSet and top-down replacement.
//!
//! Behavior to preserve:
//! Walk automaton states and marked nodes, accumulate context actions and record accepted
//! matches by node and ancestor identity; combine contexts for repeated paths and consume
//! matches in traversal order. Reconstruct recursively under noRec/recursion controls. The
//! ChildSelectInfo branch computes a filter without assigning its result, and ancestor
//! comparison uses zip without length check; examine these apparent quirks before porting.
//!
//! Integration:
//! ast::utility::rewriter::{strategy,rewritable,t_regex,t_regex_automaton},
//! ast::utility::viper_strategy.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile identity, match ordering, metadata propagation and child-selection behavior with
//! strategy and regex callers.
//!
//! Status: description only; implementation has not started.
