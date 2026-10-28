//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/writer/SymbExLogReportWriter.scala
//!
//! Purpose:
//! Serialize member symbolic execution logs and state data to JSON.
//!
//! Planned Rust structure:
//! Port SymbExLogReportWriter toJSON overloads, getAllRecords, heapChunkToJSON and
//! inverseFunctionsToJSON.
//!
//! Behavior to preserve:
//! Flatten each branching record before its branch records in order; emit id/kind/value,
//! scope/join flags, branch IDs and optional data only when present. Serialize stores, ordered
//! PCS, basic and quantified field/predicate/wand chunks including inverse axioms, hints and
//! singleton arguments; unknown chunks use upstream unstructrured_chunk fallback.
//!
//! Integration:
//! logger::records, log_config, logger::writer::term_writer, state::{heap,store,chunks} and
//! rules::quantified_chunk_support.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state capture, collection order and JSON schema.
//!
//! Open decisions:
//! Reconcile mask-heap chunk fallback and schema evolution with log consumers.
//!
//! Status: description only; implementation has not started.
