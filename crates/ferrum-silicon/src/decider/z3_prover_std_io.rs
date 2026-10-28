//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/Z3ProverStdIO.scala
//!
//! Purpose:
//! Specialize shared SMT-LIB transport for Z3.
//!
//! Planned Rust structure:
//! Z3ProverStdIO companion supplies version, dependency, executable, preamble, startup and seed
//! options; implementation resolves path, emits settings and timeout.
//!
//! Behavior to preserve:
//! Minimum 4.5.0, startup -smt2 -in; cache timeout changes, select rlimit scaled by resources/ms or
//! timeout, and read success. When configured disableNL, emit smt.arith.nl false after settings.
//!
//! Integration:
//! decider::prover_std_io, interfaces::decider::prover, config and common::config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Timeout arithmetic and process lifecycle.
//!
//! Status: description only; implementation has not started.
