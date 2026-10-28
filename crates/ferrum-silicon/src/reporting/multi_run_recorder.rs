//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/MultiRunRecorder.scala
//!
//! Purpose:
//! Manage multi-run recording, source changes, sinks and lifecycle.
//!
//! Planned Rust structure:
//! Port MultiRunRecorder, PrintWriterBasedMultiRunRecorder,
//! BufferingPrintWriterBasedMultiRunRecorder and MultiRunRecorders registry.
//!
//! Behavior to preserve:
//! Detect changes in optional source, emit source headers, flush on reset and write buffered data
//! on change/stop. Registry creates named temp-directory sinks, starts empty, flushes/reset and
//! closes/clears on stop; upstream warns it is not thread-safe.
//!
//! Integration:
//! reporting::{multi_run_counting_recorder,multi_run_line_recorder}, config and verifier
//! lifecycle.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for lifecycle, native factory and IO ownership.
//!
//! Open decisions:
//! Choose typed registry/factory and concurrency policy without changing source-boundary behavior.
//!
//! Status: description only; implementation has not started.
