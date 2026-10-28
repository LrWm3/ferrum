//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/Formatters.scala
//!
//! Purpose:
//! Render symbolic state, store, heap, old heaps and path conditions.
//!
//! Planned Rust structure:
//! Port StateFormatter and DefaultStateFormatter format overloads and legacy toJson helpers.
//!
//! Behavior to preserve:
//! Include PCs in textual state only at trace logging level; omit non-null and Combine equality
//! terms in path conditions. Legacy JSON uses pre-state old heap and source string formatting;
//! retain ordering and schema where exposed.
//!
//! Integration:
//! state::{state,store,heap}, decider::path_conditions and logger consumers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state ownership and serialization.
//!
//! Open decisions:
//! Reconcile legacy JSON escaping and ordering with logger writer without silently changing
//! output.
//!
//! Status: description only; implementation has not started.
