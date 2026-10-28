//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/decider/Prover.scala
//!
//! Purpose:
//! Define solver interaction and result contracts.
//!
//! Planned Rust structure:
//! Result Sat/Unsat/Unknown, ProverLike emission, assumptions, declarations, options,
//! comments and saturation; Prover lifecycle, checks, fresh symbols, models, versions and
//! scopes.
//!
//! Behavior to preserve:
//! assumeAxioms records debug axioms only in debug mode then assumes terms in insertion
//! order; comments are by-name. Preserve timeout, push/pop depth, model validity and
//! unknown as distinct outcomes.
//!
//! Integration:
//! decider implementations, state::terms, verifier and common::config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Solver ownership, errors and lazy comments with decider.
//!
//! Status: description only; implementation has not started.
