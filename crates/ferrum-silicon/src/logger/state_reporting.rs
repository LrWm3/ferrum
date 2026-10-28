//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/StateReporting.scala
//!
//! Purpose:
//! Report verifier state when a member log stops making progress.
//!
//! Planned Rust structure:
//! Port StateReporter, TakenBranch variants and StateReportingMemberSymbExLogger scope/branch
//! hooks, currentState and stall detection.
//!
//! Behavior to preserve:
//! Require positive threshold; poll at threshold/10 clamped 50–1000ms on lazily started daemon.
//! Synchronize active logs and per-log frames, track scope closures separately per branch and
//! across branches, report once until next progress, unregister on finish. Prefer source branch
//! expression, then term, else alternative index; truncate multiline step description.
//!
//! Integration:
//! logger::symb_ex_logger/records, Silver reporter VerifierStateMessage and verification
//! lifecycle.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for worker lifecycle, locks, timing and diagnostics.
//!
//! Open decisions:
//! Agree on scheduler shutdown and branch-path snapshot ownership with symb_ex_logger and
//! reporter.
//!
//! Status: description only; implementation has not started.
