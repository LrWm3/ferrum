//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/renderer/SimpleTreeRenderer.scala
//!
//! Purpose:
//! Render symbolic records as an indented textual branch tree.
//!
//! Planned Rust structure:
//! Port SimpleTreeRenderer render, renderMember, recursive toSimpleTree and indentation helpers.
//!
//! Behavior to preserve:
//! Open/close events change indentation with branch minimum; render data and joins, branch labels
//! use condition/negation for at most two branches or numbered branches otherwise, and unreachable
//! branches print only the unreachable marker. Preserve member and branch order.
//!
//! Integration:
//! logger::symb_ex_logger, logger::records::{data,scoping,structural} and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered record traversal.
//!
//! Open decisions:
//! Agree on renderer snapshots and branch IDs with logger.
//!
//! Status: description only; implementation has not started.
