//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/MethodCheck.scala
//!
//! Purpose:
//! Insert termination obligations around method calls and loops.
//!
//! Planned Rust structure:
//! Port MethodCheck transformMethod, bottom-up methodStrategy, methodTransformer, loop
//! marker/counter, MContext and SCC graph.
//!
//! Behavior to preserve:
//! Skip expression traversal. For recursive calls check callee tuple condition and decrease
//! against old caller tuple; nonrecursive calls check callee termination condition, then execute
//! call. For loops check method termination condition, save tuple and condition before body, then
//! check next iteration condition and decrease; mark transformed loops to prevent repeat
//! processing. Add nested predicate information when required and preserve error mapping.
//!
//! Integration:
//! trafo, call_graph, decreases_check, nested_predicates, termination_ast_extension and errors;
//! ast rewriter and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered checks, context, AST metadata and branch state.
//!
//! Open decisions:
//! Agree on loop marker identity, generated locals and error transformations with AST and
//! verifier.
//!
//! Status: description only; implementation has not started.
