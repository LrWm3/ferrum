//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/SymbExLogger.scala
//!
//! Purpose:
//! Manage symbolic execution member logs, scopes and branch events.
//!
//! Planned Rust structure:
//! Port SymbExLogger/ofConfig, SymbExLog/Noop/StateReporting variants, MemberSymbExLogger,
//! MemberSymbExLog and discarding/noop implementations; scope, branch, query, statistics and macro
//! helpers.
//!
//! Behavior to preserve:
//! Select full log for ideModeAdvanced, lightweight stalled-state log for reportStateAfter,
//! otherwise noop; invalid JSON config warns and falls back. Allocate unique IDs, append data then
//! open event, timestamp scope events, route nested branches to current branch and assert matching
//! branch IDs. Filter data and corresponding scope events by blacklist/whitelist; close member at
//! root, track failed SMT query, numeric statistic deltas and macros. Preserve close/race and
//! no-op behavior.
//!
//! Integration:
//! logger::{log_config,state_reporting,records,renderer}, verifier and rules/decider event
//! producers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for worker ownership, ordered events, lifecycle and thread
//! synchronization.
//!
//! Open decisions:
//! Reconcile concurrent branch logging, shutdown semantics and record state snapshots with
//! verifier and state_reporting.
//!
//! Status: description only; implementation has not started.
