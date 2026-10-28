//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/SiliconDebugger.scala
//!
//! Purpose:
//! Inspect and replay a failed proof obligation interactively.
//!
//! Planned Rust structure:
//! Port ProofObligation and SiliconDebugger: failure selection, state/heap/branch/assumption
//! rendering, typechecker initialization, worker/prover replay, command loop and
//! solver/timeout/assumption helpers.
//!
//! Behavior to preserve:
//! Require debugging and available failure context; replay declarations, preamble and assumption
//! terms into fresh worker. Preserve commands for zoom, reset, remove/add free or proven
//! assumptions, prove, configure, change solver and timeout; typecheck input as Bool in captured
//! scope, evaluate before optional proof and assumption. Retain source versus internal display and
//! basic/quantified field/predicate/wand heap formatting.
//!
//! Integration:
//! debugger::{debug_exp,debug_parser,debug_typechecker}, decider prover/path conditions,
//! rules::evaluator, verifier worker and failure contexts.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for solver/process lifecycle, state isolation and diagnostics;
//! interactive IO remains an explicit native interface.
//!
//! Open decisions:
//! Reconcile replay worker cleanup, solver selection and debug metadata availability with verifier
//! and decider.
//!
//! Status: description only; implementation has not started.
