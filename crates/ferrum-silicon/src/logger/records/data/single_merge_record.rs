//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/SingleMergeRecord.scala
//!
//! Purpose:
//! Record the single merge event in symbolic execution.
//!
//! Planned Rust structure:
//! Port SingleMergeRecord containing destination and new chunk sequences plus path assumptions;
//! implement its DataRecord interface and type label single merge.
//!
//! Behavior to preserve:
//! Preserve sequence order and full display with <= separator and null handling. Capture path
//! assumptions when provided and preserve inherited metadata behavior.
//!
//! Integration:
//! logger::symb_ex_logger, logger::records::data::data_record and writer/renderer; corresponding AST
//! and
//! state interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state, term and record ownership.
//!
//! Open decisions:
//! Reconcile event capture and serialization with symb_ex_logger and writer.
//!
//! Status: description only; implementation has not started.
