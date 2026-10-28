//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Joiner.scala
//!
//! Purpose:
//! Collect local branch results and join states with their path conditions.
//!
//! Planned Rust structure:
//! JoinDataEntry supports path-condition-aware merge with or without consolidation; JoiningRules
//! and joiner.join collect entries via local execution, a merge callback and continuation Q.
//!
//! Behavior to preserve:
//! Reset selected store, heap, join, cache, partially consumed heap, invariant and retry fields
//! when requested; no collected entries returns Success without Q. Otherwise merge, optionally
//! record debug heap, assume each conditionalized path and disjunction of feasible branch
//! conditions, then invoke Q. Preserve ordered collection and result combine.
//!
//! Integration:
//! rules::execution_flow_controller, rules::brancher, state::state and decider::path_conditions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Join callbacks, result sequencing and context ownership.
//!
//! Status: description only; implementation has not started.
