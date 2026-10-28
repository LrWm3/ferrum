//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/WorkerVerifier.scala
//!
//! Purpose:
//! Host worker-local method and CFG verification components.
//!
//! Planned Rust structure:
//! WorkerVerifier extends BaseVerifier, keeps main verifier/reporter/debug mode, provides method
//! and CFG supporters and delegates pool and member log creation to main.
//!
//! Behavior to preserve:
//! Start, reset and stop base components before worker subcomponents, preserving lifecycle order;
//! open member scope on main root logger with worker path conditions.
//!
//! Integration:
//! verifier::base_verifier, verifier::verification_pool_manager, supporters::method_supporter and
//! cfg_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Main/worker lifetime, logging and solver ownership.
//!
//! Status: description only; implementation has not started.
