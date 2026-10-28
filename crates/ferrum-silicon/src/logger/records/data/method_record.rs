//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/MethodRecord.scala
//!
//! Purpose:
//! Record the method event in symbolic execution.
//!
//! Planned Rust structure:
//! Port MethodRecord containing method AST and path assumptions; implement its MemberRecord
//! interface and type label method.
//!
//! Behavior to preserve:
//! Simple display is member name or null. Capture path assumptions when provided and preserve
//! inherited metadata behavior.
//!
//! Integration:
//! logger::symb_ex_logger, logger::records::data::member_record and writer/renderer; corresponding AST
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
