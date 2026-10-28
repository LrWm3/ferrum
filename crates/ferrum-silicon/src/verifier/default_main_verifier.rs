//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/DefaultMainVerifier.scala
//!
//! Purpose:
//! Assemble preambles and orchestrate program verification across main and worker verifiers.
//!
//! Planned Rust structure:
//! MainVerifier and DefaultMainVerifier own contributors, predicate snapshot generator,
//! function/predicate units, preamble reader, worker pool and broadcast allProvers. verify
//! preprocesses, builds initial state, emits static and analyzed preambles, runs units and
//! collects/reports results. Helpers select member/CFG states, exclusions, contributor order, sort
//! wrappers and error scopes.
//!
//! Behavior to preserve:
//! Compute triggers bottom-up before parallel work, optionally rewrite conditional permissions,
//! then emit static settings and preamble; analyze contributors before ordered sorts, wrappers,
//! symbols, uniqueness and axioms. Verify functions then predicates on main, flatten previous
//! results, stop main prover, emit post-verification declarations/axioms to workers, queue methods
//! and CFGs and collect futures in input order. Preserve contributor dependency order, timeout
//! saturation, include/exclude filters, annotation/config exhale and join modes, wildcard
//! permission locations, and CFG initialization treating fields/predicates quantified but not
//! quantified wands. Member failures carry error scope; report termination/traces and optional
//! debugger. Lifecycle manages all subcomponents and worker pool in order.
//!
//! Integration:
//! verifier::{base_verifier,worker_verifier,verification_pool_manager}, supporters,
//! decider::smt_lib2_preamble_reader, rules and silicon.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Worker ownership/cancellation, contributor ordering and fresh solver lifecycle.
//!
//! Status: description only; implementation has not started.
