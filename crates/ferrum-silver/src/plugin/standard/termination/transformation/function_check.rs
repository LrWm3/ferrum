//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/FunctionCheck.scala
//!
//! Purpose:
//! Generate proof methods for function termination and recursive-call decreases.
//!
//! Planned Rust structure:
//! Port FunctionCheck generateProofMethods, removeConcretePermissionAmounts, transformExp
//! override, FContext and SCC call graph.
//!
//! Behavior to preserve:
//! Only functions with tuple specifications generate proofs; independently process body, posts and
//! pres in that order, omit empty proofs and preserve result/inhale-exhale locals. Check arguments
//! first; recursive calls check condition and lexicographic decrease using old caller tuple, other
//! calls check callee termination condition. Optional legacy permission mode rewrites concrete
//! positive amounts to wildcard and merges quantified-permission implications. Map assertion
//! failures to FunctionTerminationError; add nested predicate info when needed.
//!
//! Integration:
//! trafo, call_graph, decreases_check, exp_transformer, nested_predicates and
//! termination_ast_extension; ast simplifier and quantified permissions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, exact permission handling, metadata and contexts.
//!
//! Open decisions:
//! Reconcile proof method names, permission option and error transforms with termination_plugin
//! and verifier.
//!
//! Status: description only; implementation has not started.
