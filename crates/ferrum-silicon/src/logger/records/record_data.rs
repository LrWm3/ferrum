//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/RecordData.scala
//!
//! Purpose:
//! Collect optional metadata for a symbolic execution log record.
//!
//! Planned Rust structure:
//! Port RecordData fields refId, isSmtQuery, smtStatistics, timeMs, pos, lastSMTQuery, store,
//! heap, oldHeap and pcs.
//!
//! Behavior to preserve:
//! Defaults are absent except isSmtQuery=false; retain ordered path conditions and optional
//! state/query details for serialization.
//!
//! Integration:
//! logger::records::{symbolic_record,data,scoping}, logger::writer::symb_ex_log_report_writer and
//! state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for term/state handles and ordered collections.
//!
//! Open decisions:
//! Agree on captured state ownership with logger and writer.
//!
//! Status: description only; implementation has not started.
