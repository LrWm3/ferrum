//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/TerminationPlugin.scala
//!
//! Purpose:
//! Parse decreases specifications, import well-founded orders and generate termination
//! obligations.
//!
//! Planned Rust structure:
//! Port TerminationPlugin grammar/registration, beforeResolve predicate-instance rewriting,
//! beforeTranslate domain import and warning logic, beforeVerify extraction/Trafo, result mapping,
//! PAstProvider and constants.
//!
//! Behavior to preserve:
//! Register tuple, wildcard and star syntax in pre/post/invariant hooks. Rewrite predicate
//! accesses only in decreases tuples with unfolding/applying/current-permission recursion
//! boundaries. Unless disabled, warn on unexpectedly constrained types and import missing
//! type-specific well-founded-order resources, retaining domains only. Before verification check
//! unsafe recursive function postconditions lacking decreases, extract clauses into metadata with
//! duplicate and forbidden tuple diagnostics, then generate checks with permission option.
//! Disabled mode still extracts clauses but skips imports, checks and error mapping. Map
//! transformed AssertFailed at entity and overall result boundaries.
//!
//! Integration:
//! parser::fast_parser/resolver, frontend::viper_p_ast_provider, predicateinstance, termination
//! transformation, ast::utility functions/rewriter, reporter and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for plugin order, source positions, native resource loading and
//! mutable contexts.
//!
//! Open decisions:
//! Agree on import ordering and provider lifecycle, parser extension registration and persistent
//! decreasesClauses state with frontend and parser.
//!
//! Status: description only; implementation has not started.
