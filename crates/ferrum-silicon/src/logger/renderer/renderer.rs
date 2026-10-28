//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/renderer/Renderer.scala
//!
//! Purpose:
//! Define rendering of member logs and collections.
//!
//! Planned Rust structure:
//! Port Renderer renderMember and render interface.
//!
//! Behavior to preserve:
//! Keep renderer result generic and preserve input member order.
//!
//! Integration:
//! logger::renderer::simple_tree_renderer and logger::symb_ex_logger.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for owned log views.
//!
//! Open decisions:
//! Agree on renderer input/output lifetimes with logger.
//!
//! Status: description only; implementation has not started.
