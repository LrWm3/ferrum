//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/scoping/CloseScopeRecord.scala
//!
//! Purpose:
//! Represent a scope boundary event.
//!
//! Planned Rust structure:
//! Port CloseScopeRecord as ScopingRecord; retain supplied reference ID.
//!
//! Behavior to preserve:
//! Use type label close and display reference ID as decimal; inherit timing metadata.
//!
//! Integration:
//! logger::records::scoping::scoping_record, logger::symb_ex_logger and renderer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for IDs and event ownership.
//!
//! Open decisions:
//! Agree on scope nesting and matching with symb_ex_logger.
//!
//! Status: description only; implementation has not started.
