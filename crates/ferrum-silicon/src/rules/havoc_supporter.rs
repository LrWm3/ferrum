//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/HavocSupporter.scala
//!
//! Purpose:
//! Execute single and quantified resource havoc.
//!
//! Planned Rust structure:
//! havocSupporter defines HavocHelperData, HavocOneData, HavocallData, execHavoc, execHavocall,
//! resourceName and getCodomainQVars.
//!
//! Behavior to preserve:
//! Single havoc defaults absent condition to true, evaluates condition then resource arguments and
//! replaces heap via heapSupporter. Havocall evaluates quantified condition and arguments, assumes
//! function-precondition transform, checks injectivity and fails with QuasihavocallNotInjective if
//! false; on success constructs and assumes inverse axioms and replaces heap. A missing quantified
//! result continues unchanged.
//!
//! Integration:
//! rules::evaluator, rules::quantified_chunk_support, rules::heap_supporter,
//! state::function_precondition_transformer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Quantified evaluation result and solver ownership.
//!
//! Status: description only; implementation has not started.
