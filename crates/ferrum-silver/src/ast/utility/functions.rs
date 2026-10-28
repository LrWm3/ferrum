//! Port plan: Analyze Silver function call graphs, recursion and dependencies.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Functions.scala
//!
//! Purpose:
//! Analyze Silver function call graphs, recursion and dependencies.
//!
//! Planned Rust structure:
//! Functions.FuncName, Edge, allSubexpressions, unfolding-aware collection, callgraph,
//! heights, recursiveCallsAndSurroundingUnfoldings and cycle queries.
//!
//! Behavior to preserve:
//! Collect pres, posts and body; unfolding-aware traversal follows each predicate body once.
//! SCC condensation and topological numbering give each SCC a common height. Recursion walk
//! carries outermost-first unfoldings and skips unfolding access; source Let replacement and
//! result prepending have specific behavior. Cycle maps preserve source iteration choices.
//!
//! Integration:
//! ast::{expression,program}, ast::utility::{consistency,visitor}, graph-dependent verifier
//! and termination consumers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Select graph library and stable iteration only after checking source ordering and
//! function-height consumers; examine Let recursion behavior.
//!
//! Status: description only; implementation has not started.
