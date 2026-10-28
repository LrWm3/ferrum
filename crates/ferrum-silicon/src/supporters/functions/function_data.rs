//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/FunctionData.scala
//!
//! Purpose:
//! Accumulate function verification recordings and construct phase-specific axioms.
//!
//! Planned Rust structure:
//! Port FunctionRecorderHandler and FunctionData: formal/state/result variables,
//! function/limited/stateless/precondition symbols, phase transitions, nested definitions,
//! predicate triggers, post/definition/precondition-propagation axioms.
//!
//! Behavior to preserve:
//! Merge recorders and retain insertion-ordered fresh declarations across phases; filter nested
//! definitions with unknown free variables. Limited and trigger axioms precede post axiom; phase 1
//! post axiom binds result to limited application, phase 2 definition guards body equality by
//! precondition and suppresses predicate triggers for opaque functions. Derive predicate triggers
//! from outer recursive unfoldings whose arguments have no free variables outside the formals;
//! arguments may be expressions. Preserve propagation axioms and encoding adaptations.
//!
//! Integration:
//! functions::{function_recorder,function_encoding,heap_access_replacing_expression_translator,function_verification_unit},
//! supporters::predicate_verification_unit, rules quantified definitions and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for term identity, ordering, source contexts and phase ownership.
//!
//! Open decisions:
//! Resolve free-variable filtering, recorder lifecycle and snapshot/heap encoding contracts with
//! function verification and rules.
//!
//! Status: description only; implementation has not started.
