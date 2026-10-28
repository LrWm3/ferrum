//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/CVC5ProverStdIO.scala
//!
//! Purpose:
//! Specialize the shared SMT-LIB process transport for cvc5.
//!
//! Planned Rust structure:
//! Cvc5ProverStdIO companion supplies name, version bounds, executable environment, dependency,
//! preamble, arguments and random seeds; implementation selects path, settings and timeout.
//!
//! Behavior to preserve:
//! Minimum version 1.0.0, startup --lang=smt2.6; update timeout only when changed, choosing
//! reproducible resource limit multiplied by configured resources/ms or tlimit-per, then consume
//! success response. emitSettings delegates to emit.
//!
//! Integration:
//! decider::prover_std_io, interfaces::decider::prover, config and common::config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Timeout arithmetic and process ownership.
//!
//! Status: description only; implementation has not started.
