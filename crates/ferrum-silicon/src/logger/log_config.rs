//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/LogConfig.scala
//!
//! Purpose:
//! Configure symbolic log record filtering and optional details.
//!
//! Planned Rust structure:
//! Port LogConfig, RecordConfig, getRecordConfig and JSON protocol.
//!
//! Behavior to preserve:
//! First record config matching kind and optional exact value wins. Default is blacklist with no
//! filters and store/heap/oldHeap/pcs disabled; preserve JSON field names and optional value.
//!
//! Integration:
//! symb_ex_logger, logger::records::data and logger::writer::symb_ex_log_report_writer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for configuration and native JSON.
//!
//! Open decisions:
//! Agree on JSON compatibility and defaults with log consumers.
//!
//! Status: description only; implementation has not started.
