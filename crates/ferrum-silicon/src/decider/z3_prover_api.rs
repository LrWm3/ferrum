//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/Z3ProverAPI.scala
//!
//! Purpose:
//! Implement the in-process Z3 API prover route.
//!
//! Planned Rust structure:
//! Z3ProverAPI owns native context/solver, converter, preamble buffers, declarations, macro
//! definitions, model and timeout; provides lifecycle, options, scopes, assertions/checks,
//! assumptions, saturation and model conversion.
//!
//! Behavior to preserve:
//! Version bounds both 4.16.0.0; configure typed parameters and optional nonlinear disabling,
//! buffer preamble commands and assumptions until first solver use, then parse with recorded
//! declarations. emit after preamble fails; settings are mostly ignored except seed randomization
//! and dynamic setOption fails explicitly. Expand macros in Silicon terms. Invalid-trigger Z3
//! exceptions clean quantifier triggers and retry/report warning, while unchanged failing assertion
//! becomes external-tool error. Push-pop asserts negation and pops before fetching model/reason as
//! upstream; soft constraints use guard. Distinguish sat/unsat/unknown in check; reset converter
//! and context, close context on stop; timeouts select rlimit or milliseconds.
//!
//! Integration:
//! decider::term_to_z3_api_converter, state::triggers and state::terms, interfaces::decider::prover and
//! verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Native Z3 context lifecycle, identity cache and assertion model semantics.
//!
//! Status: description only; implementation has not started.
