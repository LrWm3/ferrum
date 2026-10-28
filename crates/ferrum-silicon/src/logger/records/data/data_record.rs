//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/DataRecord.scala
//!
//! Purpose:
//! Attach source node and path conditions to symbolic data records.
//!
//! Planned Rust structure:
//! Port DataRecord value, pcs, string rendering and getData.
//!
//! Behavior to preserve:
//! Render null value as null; populate source position for Positioned nodes and include captured
//! ordered assumptions only if includePcs enabled.
//!
//! Integration:
//! logger::records::symbolic_record/record_data and concrete data records; Silver positions and
//! state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for optional data and immutable state capture.
//!
//! Open decisions:
//! Agree on source position serialization and path condition ownership with writer.
//!
//! Status: description only; implementation has not started.
