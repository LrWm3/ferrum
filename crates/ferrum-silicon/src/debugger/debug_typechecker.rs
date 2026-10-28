//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/DebugTypechecker.scala
//!
//! Purpose:
//! Resolve debugger versioned variables against captured types.
//!
//! Planned Rust structure:
//! Port DebugResolver and DebugTypeChecker checkInternal and acceptAndCheckTypedEntityWithVersion.
//!
//! Behavior to preserve:
//! Look up full versioned name in debugVariableTypes, set type or append positioned diagnostic;
//! delegate other expressions to ordinary TypeChecker.
//!
//! Integration:
//! debugger::{debug_parser,silicon_debugger}, ferrum_silver::parser::{resolver,fast_message}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for type and error ownership.
//!
//! Open decisions:
//! Agree on captured version naming and scope with debugger and parser.
//!
//! Status: description only; implementation has not started.
