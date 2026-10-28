//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/CallGraph.scala
//!
//! Purpose:
//! Classify recursive dependencies in directed call graphs.
//!
//! Planned Rust structure:
//! Port CallGraph mutuallyRecursiveVertices and clearlyNonRecursiveVertices.
//!
//! Behavior to preserve:
//! Compute strongly connected components; nonrecursive routine destructively removes incoming
//! edges starting at leaves, enqueueing predecessors once outdegree reaches zero. Preserve
//! iteration consequences where observable.
//!
//! Integration:
//! function_check, method_check and termination_plugin build graphs of Silver members.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for graph ordering and native graph algorithms.
//!
//! Open decisions:
//! Agree on graph ownership and iteration order with callers.
//!
//! Status: description only; implementation has not started.
