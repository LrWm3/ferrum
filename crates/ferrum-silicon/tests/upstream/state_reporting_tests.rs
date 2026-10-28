//! Port plan: StateReportingTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/test/scala/StateReportingTests.scala
//!
//! Purpose:
//! Port this Silicon upstream test suite or test-harness component.
//!
//! Planned Rust structure:
//! StateReportingTests with synchronized CollectingReporter and source-position helper.
//!
//! Behavior to preserve:
//! At 300 ms period, open method/statement/branch scopes, expect one report without progress, none
//! repeated, then another after switching to negated branch; finishing member suppresses further
//! reports. Verify exact rendered frames and nodes. Second case closes a scope in both branches
//! and checks only later statement remains.
//!
//! Integration:
//! logger::{state_reporting::StateReporter,symb_ex_logger::StateReportingSymbExLog},
//! Silver reporter message and AST positions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identities, errors and provisional ownership. Reuse
//! upstream fixtures and distinguish configured modes from asserted behavior.
//!
//! Open decisions:
//! Use controlled timing where possible while preserving progress and scope semantics.
//!
//! Status: description only; implementation has not started.
