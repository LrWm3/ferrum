//! Port plan: Check local and context-dependent Silver AST consistency.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Consistency.scala
//!
//! Purpose:
//! Check local and context-dependent Silver AST consistency.
//!
//! Planned Rust structure:
//! Consistency diagnostics accumulator and legacy function-precondition flag;
//! identifier/assignability/purity and contract helpers, wildcard, trigger, forperm, backend
//! type, recursion and wand context checks; Context and InsideWandStatus.
//!
//! Behavior to preserve:
//! Preserve diagnostics order and positions, parser keyword restrictions and assignability
//! subtype rules. Legacy flag controls wildcard restrictions in function preconditions.
//! Validate trigger coverage, forperm direct resource arguments, wand proof scripts and
//! old[lhs] location, backend interpretation consistency, and recursion via function
//! preconditions. Existing extension-expression exception in noPermissions and mutable message
//! accumulator remain explicit.
//!
//! Integration:
//! ast::{ast,expression,statement,program,type},
//! ast::utility::{expressions,functions,viper_strategy}, parser keywords and verifier errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile per-run message/config ownership and extension rules with frontend and plugin
//! callers, preserving source diagnostics.
//!
//! Status: description only; implementation has not started.
