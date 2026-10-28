//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/AnnotationSupporter.scala
//!
//! Purpose:
//! Interpret per-member verifier annotations.
//!
//! Planned Rust structure:
//! Port annotation constants and getProverConfigArgs, getExhaleMode/QP, getJoinMode and
//! getStateConsolidationMode.
//!
//! Behavior to preserve:
//! Parse option=value at first equals; warn and ignore malformed entries. Preserve named and
//! numeric mode aliases, empty moreJoins as all, and warnings on invalid values.
//!
//! Integration:
//! config modes, Silver ast annotation info and reporter; method/function verification callers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for configuration and diagnostics.
//!
//! Open decisions:
//! Agree on numeric enum parsing and map duplicate semantics with config and reporter.
//!
//! Status: description only; implementation has not started.
