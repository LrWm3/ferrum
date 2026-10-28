//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/qps/FieldValueFunctionsContributor.scala
//!
//! Purpose:
//! Contribute field value function preambles for quantified permissions.
//!
//! Planned Rust structure:
//! Port FieldValueFunctionsContributor and DefaultFieldValueFunctionsContributor with analyze,
//! declaration/axiom template generation, emission and reset.
//!
//! Behavior to preserve:
//! Collect fields from quantified permissions and field accesses in forall/exists triggers in
//! insertion order; emit field-value-function sorts and parameterized declarations/axioms. Select
//! no-trigger axiom template when disableISCTriggers is set.
//!
//! Integration:
//! supporters::default_sets_contributor, state::{symbol_converter,terms},
//! interfaces::preamble and interfaces::decider::term_converter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for prover emission and ordering; retain
//! field_value_functions_*.smt2 templates as resources.
//!
//! Open decisions:
//! Agree on template substitution and preamble ownership with prover and set contributor.
//!
//! Status: description only; implementation has not started.
