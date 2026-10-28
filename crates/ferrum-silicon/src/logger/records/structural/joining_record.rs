//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/structural/JoiningRecord.scala
//!
//! Purpose:
//! Represent a symbolic execution join event.
//!
//! Planned Rust structure:
//! Port JoiningRecord as DataRecord and StructuralRecord with state and optional path assumptions.
//!
//! Behavior to preserve:
//! Use joining label and null AST value; preserve captured assumption order for metadata.
//!
//! Integration:
//! logger::symb_ex_logger, logger::renderer::simple_tree_renderer and
//! logger::records::data::data_record.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state capture.
//!
//! Open decisions:
//! Agree on record dispatch and state lifetime with logger.
//!
//! Status: description only; implementation has not started.
