//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/CondExpRecord.scala
//!
//! Purpose:
//! Record the conditional expression event in symbolic execution.
//!
//! Planned Rust structure:
//! Port CondExpRecord containing CondExp, state, path assumptions and env string; implement its
//! DataRecord interface and type label conditional expression.
//!
//! Behavior to preserve:
//! Retain env even though base display uses node. Capture path assumptions when provided and
//! preserve inherited metadata behavior.
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
