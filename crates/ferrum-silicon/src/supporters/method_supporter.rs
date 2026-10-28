//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/MethodSupporter.scala
//!
//! Purpose:
//! Verify methods by producing contracts and executing their CFGs.
//!
//! Planned Rust structure:
//! Port MethodVerificationUnit and DefaultMethodVerificationUnitProvider analyze/verify/lifecycle,
//! including annotations and debug logging.
//!
//! Behavior to preserve:
//! Set member prover options; warn for ignored non-loop label invariants; initialize fresh store,
//! empty heap and old heaps. Locally produce preconditions, saturate and save pre-state,
//! separately check postcondition wellformedness in empty heap and execute CFG then consume
//! postconditions. Preserve continuation ordering, failure attribution and prover-option reset.
//!
//! Integration:
//! rules::{producer,consumer,executor,execution_flow_controller}, state::{state,store},
//! decider::decider and Silver CFG/reporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for independent states, continuations and solver lifecycle.
//!
//! Open decisions:
//! Reconcile option cleanup on exceptional paths and debug-heap ownership with verifier and rules.
//!
//! Status: description only; implementation has not started.
