//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/DebugParser.scala
//!
//! Purpose:
//! Parse and translate versioned debugger expressions and debug old labels.
//!
//! Planned Rust structure:
//! Port DebugParser versioned identifiers/debugOld syntax and DebugTranslator expInternal
//! overrides.
//!
//! Behavior to preserve:
//! Register debug old and versioned identifier start extensions; parse numeric @ versions and
//! debug labels, translate to LocalVarWithVersion and DebugLabelledOld with source metadata;
//! delegate other expressions.
//!
//! Integration:
//! debugger::{debug_typechecker,silicon_debugger} and ferrum_silver::parser::{fast_parser,translator}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser strategy, source positions and extension registration.
//!
//! Open decisions:
//! Agree on debug label syntax and parser ownership with Silver frontend.
//!
//! Status: description only; implementation has not started.
