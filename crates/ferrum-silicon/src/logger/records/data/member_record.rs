//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/MemberRecord.scala
//!
//! Purpose:
//! Attach the last failed prover query to member log data.
//!
//! Planned Rust structure:
//! Port MemberRecord extension of DataRecord and lastFailedProverQuery.
//!
//! Behavior to preserve:
//! getData preserves base data and sets lastSMTQuery from the optional stored term.
//!
//! Integration:
//! function_record, method_record, predicate_record and symb_ex_logger/writer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for recorded term ownership.
//!
//! Open decisions:
//! Agree on member record mutation and query lifetime with logger.
//!
//! Status: description only; implementation has not started.
