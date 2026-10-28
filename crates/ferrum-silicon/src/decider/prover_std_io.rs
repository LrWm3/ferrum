//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/ProverStdIO.scala
//!
//! Purpose:
//! Drive an SMT solver process over ordered line-oriented commands.
//!
//! Planned Rust structure:
//! ProverStdIO implements Prover lifecycle, scopes, emit/assume/declare/fresh, settings, assertion
//! modes, satisfiability checks, saturation, models/statistics/unknown reason, and protocol I/O
//! helpers; solver subclasses provide executable and timeouts.
//!
//! Behavior to preserve:
//! Start rejects repeated startup, validates executable and redirects stderr; reset stops and
//! restarts; stop flushes, forcibly destroys process before closing streams, waits up to ten
//! seconds, removes shutdown hook and clears recorded declarations/emits/preamble assumptions.
//! Preserve push/pop depth and response ordering, timeout caching in subclasses, lazy log comments
//! and debug recordings. Push-pop assertions refute negation, retrieve model and unknown reason
//! before pop; soft-constraint assertion uses fresh guard and retrieves model without reason query.
//! sat and unknown both fail assertion while check distinguishes sat/unsat/unknown. Skip/report
//! warning and quantifier-profile lines, reject unexpected success/EOF responses, and preserve
//! model-read error behavior.
//!
//! Integration:
//! decider::{z3_prover_std_io,cvc5_prover_std_io,term_to_smt_lib2_converter},
//! interfaces::decider::prover, state::identifiers and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Child-process cancellation, scope ownership, diagnostic and protocol error APIs.
//!
//! Status: description only; implementation has not started.
