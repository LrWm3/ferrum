//! Port plan: Represent and execute tree-regex automata.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/TRegexAutomaton.scala
//!
//! Purpose:
//! Represent and execute tree-regex automata.
//!
//! Planned Rust structure:
//! TRegexAutomaton, State, Transition/ETransition/MTransition and TransitionInfo variants
//! ChildSelectInfo, MarkedForRewrite, ContextInfo.
//!
//! Behavior to preserve:
//! At most one matching transition per state; epsilon closure traverses cycles and caches
//! effective states, invalidated when epsilon edges are added. A state with no transitions
//! accepts; input on epsilon state asserts, failed match produces empty states/actions.
//! Preserve action sequence and reachable-state set semantics.
//!
//! Integration:
//! ast::utility::rewriter::{t_regex,regex_strategy,rewritable}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Agree on state identity, closure cache invalidation and iteration order with
//! regex_strategy.
//!
//! Status: description only; implementation has not started.
