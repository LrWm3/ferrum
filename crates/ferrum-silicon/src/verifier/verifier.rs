//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/Verifier.scala
//!
//! Purpose:
//! Define verifier services and debug heap provenance.
//!
//! Planned Rust structure:
//! Verifier exposes worker services, atomic error count, reportFurtherErrors and DebugHeapRecorder
//! wrappers; companion holds config and old/LHS labels. DebugHeapRecorder resolves labels and
//! records key/intermediate heaps and path-condition differences.
//!
//! Behavior to preserve:
//! Error limit zero means unlimited. Heap label lookup prefers existing labelled key heaps, then
//! debug key heaps, then child and temporary matches. Record heaps from wand evaluation heap and
//! duplicate path conditions; do not overwrite existing labels, require temporary record for
//! intermediate/final operations, promote or merge child records on finish. Preserve atomic label
//! counter and branch condition differences.
//!
//! Integration:
//! verifier::base_verifier, state::{state,heap}, rules::magic_wand_supporter and
//! decider::path_conditions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Config, debug-record and verifier service ownership.
//!
//! Status: description only; implementation has not started.
