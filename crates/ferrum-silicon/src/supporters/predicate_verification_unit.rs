//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/PredicateVerificationUnit.scala
//!
//! Purpose:
//! Verify predicate bodies and collect trigger symbols and simplified-unfold data.
//!
//! Planned Rust structure:
//! Port PredicateData, PredicateContentsTree branch/leaf variants, PredicateVerificationUnit and
//! provider analyze/verify/makePredTree/preamble/lifecycle.
//!
//! Behavior to preserve:
//! Declare trigger per predicate. Verify body by producing with fresh snapshot and args; abstract
//! predicate succeeds. When simplified unfolds enabled, record branch conditions, heap and
//! assumptions and merge function recorders; create branch tree only on nonfatal result. Declare
//! recorded symbols after verification with macros last to avoid undeclared dependencies.
//!
//! Integration:
//! rules::{producer,execution_flow_controller}, supporters::functions::function_recorder,
//! state::{heap,terms} and decider::decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for branching, ordered assumptions, snapshots and symbol
//! declaration ordering.
//!
//! Open decisions:
//! Agree on branch tree identity, recorder ownership and failure/empty-branch behavior with
//! predicate rules and function recorder.
//!
//! Status: description only; implementation has not started.
