//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/MultiRunLineRecorder.scala
//!
//! Purpose:
//! Write recorded lines with source-boundary headers.
//!
//! Planned Rust structure:
//! Port MultiRunLineRecorder source, onSourceChanged and record.
//!
//! Behavior to preserve:
//! Detect source change before writing, print header, then print with optional newline; upstream
//! is not thread-safe.
//!
//! Integration:
//! reporting::multi_run_recorder and configured sink.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for IO and lifecycle.
//!
//! Open decisions:
//! Agree on synchronization and sink ownership with recorder registry.
//!
//! Status: description only; implementation has not started.
