//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/scoping/ScopingRecord.scala
//!
//! Purpose:
//! Share scope event reference and timing metadata.
//!
//! Planned Rust structure:
//! Port ScopingRecord refId and mutable timeMs with getData.
//!
//! Behavior to preserve:
//! Initialize timeMs to zero and populate refId/timeMs in RecordData.
//!
//! Integration:
//! logger::records::scoping::{open_scope_record,close_scope_record}, symb_ex_logger and writer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for event ownership.
//!
//! Open decisions:
//! Agree on clock and scope-ID representation with logger.
//!
//! Status: description only; implementation has not started.
