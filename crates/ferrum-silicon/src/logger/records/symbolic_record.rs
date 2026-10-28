//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/SymbolicRecord.scala
//!
//! Purpose:
//! Define the shared symbolic log record interface.
//!
//! Planned Rust structure:
//! Port SymbolicRecord id, type/simple string and getData.
//!
//! Behavior to preserve:
//! ID initially -1; default getData produces empty RecordData and string joins type and simple
//! text.
//!
//! Integration:
//! logger::records::{data,scoping,structural}, symb_ex_logger and renderer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for record identity and lifetimes.
//!
//! Open decisions:
//! Agree on enum versus trait dispatch with logger and writer.
//!
//! Status: description only; implementation has not started.
