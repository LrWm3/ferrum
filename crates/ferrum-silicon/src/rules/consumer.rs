//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Consumer.scala
//!
//! Purpose:
//! Consume assertions and permissions from a symbolic heap, optionally returning a snapshot.
//!
//! Planned Rust structure:
//! ConsumptionRules and consumer implement consume/consumes, ordered consumeTlcs, recursive
//! consumeR, wrappedConsumeTlc, consumeTlc, consumeConditionalTlcMoreJoins and evalAndAssert.
//! Dispatch impure implication/conditional with branch or more-joins, access predicates, quantified
//! permissions, impure lets, invalid inhale-exhale nodes, and pure expression assertion.
//!
//! Behavior to preserve:
//! Select whenExhaling, flatten conjuncts in order with original per-assertion error and combine
//! snapshots; finalize against original heap before Q and restore partiallyConsumedHeap. Wrapper
//! temporarily sets the consumed heap as main heap for failure-driven consolidation, then restores
//! evaluation heap. Access evaluates args/permission, checks nonnegative, applies scaling and
//! configured wildcard optimization, triggers resource and updates partial heap. Quantified path
//! records entry/exit and delegates errors including noninjectivity and insufficient permission.
//! Impure joins merge heaps and snapshots conditionally; pure checks switch to wand evaluation heap
//! and restore reserve/exhale state. Quantifier checks assume transformed preconditions;
//! final-retry failure may assume assertion and continue to report further errors.
//!
//! Integration:
//! rules::producer, evaluator, execution_flow_controller, brancher, joiner, heap_supporter,
//! permission_supporter, magic_wand_supporter and supporters::snapshot_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Snapshot lifecycle, continuation and retry state with producer and heap supporter.
//!
//! Status: description only; implementation has not started.
