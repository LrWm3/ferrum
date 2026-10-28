//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/structural/StructuralRecord.scala
//!
//! Purpose:
//! Mark structural symbolic-log events.
//!
//! Planned Rust structure:
//! Port StructuralRecord as the shared SymbolicRecord interface.
//!
//! Behavior to preserve:
//! Preserve distinction from ordinary data and scope records for renderer dispatch.
//!
//! Integration:
//! logger::records::structural::{branching_record,joining_record}, symb_ex_logger and renderer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for record dispatch.
//!
//! Open decisions:
//! Agree on record enum or trait representation with logger.
//!
//! Status: description only; implementation has not started.
