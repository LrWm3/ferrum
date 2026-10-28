//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/ExecutionFlowController.scala
//!
//! Purpose:
//! Scope local execution and retry failed symbolic operations.
//!
//! Planned Rust structure:
//! ExecutionFlowRules and executionFlowController implement locallyWithResult/locally and
//! tryOrFail0/1/2 through private tryOrFailWithResult.
//!
//! Behavior to preserve:
//! Push/pop solver scope before inspecting local result; invoke Q only on nonfatal result with
//! exactly one captured datum. Initial attempt increments retryLevel and restores it at Q; retry
//! only after fatal result with no local continuation success, rewind path conditions, consolidate,
//! choose temporary more-complete modes from member annotations/config. On retry continuation,
//! restore the two mode flags and set retrying to false. Preserve upstream caveat for a successful
//! branch followed by a failing branch.
//!
//! Integration:
//! rules::state_consolidator, interfaces::verification, decider::path_conditions and
//! supporters::annotation_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Closure/result protocol and solver scope ownership.
//!
//! Status: description only; implementation has not started.
