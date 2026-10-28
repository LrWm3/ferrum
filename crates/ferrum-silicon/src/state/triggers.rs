//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Triggers.scala
//!
//! Purpose:
//! Generate and rewrite term-level quantifier triggers.
//!
//! Planned Rust structure:
//! Trigger, TriggerGenerator, AxiomRewriter and SimpleArithmeticSolver adapt Silver generic
//! trigger and arithmetic machinery to Silicon terms.
//!
//! Behavior to preserve:
//! First trigger group may introduce extra variables; assemble then attempt rewrite,
//! falling back to original. Custom trigger predicates override defaults;
//! arithmetic/boolean operations are forbidden except advanced plus/minus; reconstruction
//! checks arity. Fresh rewrite variables use @rw counter.
//!
//! Search-based assembly installs the advanced filter temporarily and clears it
//! after search; the mutable generator is explicitly not thread-safe.
//!
//! Integration:
//! state::terms, state::utils and ferrum_silver::ast::utility trigger machinery.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Generic trigger extension points and counter ownership.
//!
//! Status: description only; implementation has not started.
