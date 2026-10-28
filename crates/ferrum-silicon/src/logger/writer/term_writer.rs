//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/writer/TermWriter.scala
//!
//! Purpose:
//! Serialize symbolic terms and sorts to log JSON.
//!
//! Planned Rust structure:
//! Port TermWriter toJSON overloads and unary/binary/variable helpers.
//!
//! Behavior to preserve:
//! Preserve JSON type/key strings for quantification, application, lookups, Boolean combinators,
//! ITE, variables, let, literals and collection forms; quantification omits triggers/global flag.
//! Unknown terms use upstream misspelled unstructrured type. Preserve sort-specific
//! field/predicate names and array order.
//!
//! Integration:
//! logger::writer::symb_ex_log_report_writer and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for term identity, ordering and JSON compatibility.
//!
//! Open decisions:
//! Decide how to represent newer terms while retaining existing fallback and wire schema.
//!
//! Status: description only; implementation has not started.
