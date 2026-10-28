//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/MultiRunCountingRecorder.scala
//!
//! Purpose:
//! Count occurrences per source and write totals between runs.
//!
//! Planned Rust structure:
//! Port MultiRunCountingRecorder record, source provider and writeAndClearRecordedData.
//!
//! Behavior to preserve:
//! Detect source changes before increment; emit key: count pairs then clear on source change/stop.
//! Upstream map iteration and recorder are not thread-safe.
//!
//! Integration:
//! reporting::multi_run_recorder and configured sink.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering and IO lifecycle.
//!
//! Open decisions:
//! Agree on map ordering and synchronization with recorder registry.
//!
//! Status: description only; implementation has not started.
