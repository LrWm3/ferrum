//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/qps/PredicateSnapGenerator.scala
//!
//! Purpose:
//! Determine predicate snapshot sorts and formal symbolic variables.
//!
//! Planned Rust structure:
//! Port PredicateSnapGenerator setup/getSnap, snapMap/formalVarMap and lifecycle.
//!
//! Behavior to preserve:
//! Visit predicate accesses; derive sort from body optimalSnapshotSort or Snap for abstract
//! predicate, convert formal parameters to variables. getSnap returns cached sort with true or
//! default Snap with false; reset clears maps.
//!
//! Integration:
//! supporters::snapshot_supporter and qps::predicate_and_wand_snap_functions_contributor;
//! state::symbol_converter and Silver AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for snapshot identity and lifecycle.
//!
//! Open decisions:
//! Reconcile setup ordering and cache ownership with verifier and snapshot_supporter.
//!
//! Status: description only; implementation has not started.
