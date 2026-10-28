//! Port plan: Lower Silver methods and statements into CFGs.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/silver/CfgGenerator.scala
//!
//! Purpose:
//! Lower Silver methods and statements into CFGs.
//!
//! Planned Rust structure:
//! Port methodToCfg, statementToCfg and computeCfg; TmpLabel/TmpStmt and TmpEdge variants, Phase1
//! linearization and Phase2 block/edge assembly.
//!
//! Behavior to preserve:
//! Phase1 expands If and While into fresh labels and jumps, adds local declaration statements,
//! optionally preserves gotos, wraps ordinary and extension statements. Phase2 creates condition and
//! metadata-preserving Not edges, records syntactic loop nesting, resolves labels or fails, and moves
//! label invariants to provisional block metadata. Prune unreachable before optional loop detection and
//! simplification. Method precondition always precedes body; append postcondition only when exit
//! remains reachable. Empty absent body is allowed.
//!
//! Integration:
//! Uses ast::{statement,expression,program},
//! cfg::{block,edge,silver::silver_cfg,utility::{cfg_simplifier,loop_detector}}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Reconcile temporary/final block identity, label IDs and loop metadata with loop_detector and AST
//! rewriter; retain flag-dependent control flow.
//!
//! Status: description only; implementation has not started.
