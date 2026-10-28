//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/package.scala
//!
//! Purpose:
//! Define path-condition mark type.
//!
//! Planned Rust structure:
//! Map Mark alias to a suitable native marker type used by path-condition stacks.
//!
//! Behavior to preserve:
//! Upstream Mark is Int; marks represent scope boundaries and must not be confused between stacks.
//!
//! Integration:
//! decider::path_conditions and rules::execution_flow_controller.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Marker representation with path-condition ownership.
//!
//! Status: description only; implementation has not started.
