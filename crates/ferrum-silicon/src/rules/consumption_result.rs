//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/ConsumptionResult.scala
//!
//! Purpose:
//! Represent whether permission consumption has completed.
//!
//! Planned Rust structure:
//! ConsumptionResult, Complete and Incomplete carry completion and missing permission term/debug
//! expression; factory checks nonpositivity directly or universally quantified.
//!
//! Behavior to preserve:
//! Use decider.check with supplied timeout; complete short-circuits || while incomplete evaluates
//! and returns the alternative. A failed check yields Incomplete, not an assertion failure.
//!
//! Integration:
//! rules::chunk_supporter, rules::quantified_chunk_support, state::terms and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Permission-result and solver timeout ownership.
//!
//! Status: description only; implementation has not started.
