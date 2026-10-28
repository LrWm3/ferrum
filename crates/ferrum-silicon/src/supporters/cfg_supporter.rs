//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/CfgSupporter.scala
//!
//! Purpose:
//! Verify a supplied Silver CFG using symbolic execution.
//!
//! Planned Rust structure:
//! Port CfgVerificationUnit, DefaultCfgVerificationUnitProvider and cfgSupporter
//! analyze/units/verify/lifecycle.
//!
//! Behavior to preserve:
//! Initialize fresh store, empty heap, old heaps and method CFG; optionally print DOT, execute
//! locally and return one verification result. Upstream analyze is unimplemented; do not represent
//! it as successful.
//!
//! Integration:
//! rules::{execution_flow_controller,executor}, state::{state,store}, verifier and Silver CFG.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state isolation and lifecycle.
//!
//! Open decisions:
//! Agree on CFG unit discovery and verifier ownership with verifier and method_supporter.
//!
//! Status: description only; implementation has not started.
