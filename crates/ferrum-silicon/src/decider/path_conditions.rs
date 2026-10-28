//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/PathConditions.scala
//!
//! Purpose:
//! Track scoped symbolic assumptions, branch conditions and debug records.
//!
//! Planned Rust structure:
//! RecordedPathConditions and PathConditionStack interfaces, PathConditionStackLayer, layered
//! aggregation, DefaultRecordedPathConditions, LayeredPathConditionStack and
//! PathConditions.isGlobal implement scope marks, additions, duplicate, after, conditionalized and
//! quantified projections.
//!
//! Behavior to preserve:
//! Split added conjunctions, track global/non-global and defining assumptions in insertion order,
//! and assign one branch condition per layer. conditionalized iterates oldest first, accumulating
//! branch guards; quantified separates globals and quantifies guarded non-global assumptions,
//! omitting ignored conjuncts. Debug expression stacks are inherited into child layers and
//! completed without duplicate reporting. Mark pushes a layer, after reads newer layers, pop
//! removes layers and cached assumptions, duplicate clones mutable layers/counter. definitionsOnly
//! excludes branch conditions. Global classification includes global quantifiers, read permission
//! variables and domain markers. Preserve source cache behavior for repeated assumptions across
//! layers for reconciliation.
//!
//! Integration:
//! decider::decider, rules::{brancher,joiner,evaluator}, state::terms and debugger.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Clone/mark semantics, duplicate assumption cache and solver scope ownership.
//!
//! Status: description only; implementation has not started.
