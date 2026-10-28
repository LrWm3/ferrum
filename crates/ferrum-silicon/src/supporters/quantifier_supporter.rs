//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/QuantifierSupporter.scala
//!
//! Purpose:
//! Generate and validate triggers and eliminate heap-dependent trigger terms.
//!
//! Planned Rust structure:
//! Port QuantifierSupporter and DefaultQuantifierSupporter autoTrigger,
//! makeTriggersHeapIndependent and detectQuantificationProblems.
//!
//! Behavior to preserve:
//! Keep explicit triggers; otherwise append generator extra variables. Split each distinct trigger
//! into a quantification with fresh projection variables replacing field/predicate snapshot
//! function applications. For forall report missing triggers, missing bound variables, invalid and
//! forbidden terms in source check order; exists has no checks.
//!
//! Integration:
//! state::triggers trigger generator, rules::evaluator and verifier; Silver parser debug types.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for quantifier identity, variable freshness and trigger order.
//!
//! Open decisions:
//! Agree on fresh declaration/quantifier metadata and mapping iteration with evaluator and term
//! factories.
//!
//! Status: description only; implementation has not started.
