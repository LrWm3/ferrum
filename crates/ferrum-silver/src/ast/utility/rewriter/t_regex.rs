//! Port plan: Tree-path regular expression DSL and automaton construction.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/TRegex.scala
//!
//! Purpose:
//! Tree-path regular expression DSL and automaton construction.
//!
//! Planned Rust structure:
//! Match and NMatch/ContextNMatch/ChildSelectNMatch, Nested/OrMatch/Star/Questionmark, tree
//! regex builders and n/c/iC factories.
//!
//! Behavior to preserve:
//! Construct matching and epsilon-transition automata for concatenation, alternation, optional
//! and repetition; derived plus, descendant and nonconsecutive repetition compose primitives.
//! Typed predicates can mark rewrites, extract context or select a child; preserve match and
//! action order.
//!
//! Integration:
//! ast::utility::rewriter::{t_regex_automaton,regex_strategy,rewritable} and
//! ast::utility::viper_strategy.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Replace runtime type reflection with explicit node-kind matching while reconciling
//! extension support and action ordering with regex_strategy.
//!
//! Status: description only; implementation has not started.
