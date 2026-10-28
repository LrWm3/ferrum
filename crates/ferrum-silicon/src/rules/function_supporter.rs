//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/FunctionSupporter.scala
//!
//! Purpose:
//! Build derived symbols for function encodings.
//!
//! Planned Rust structure:
//! functionSupporter creates limitedVersion, statelessVersion, preconditionVersion, frameVersion
//! and preconditionFrameVersion.
//!
//! Behavior to preserve:
//! Suffixes use %; stateless drops state arguments and returns Bool, precondition retains
//! heap-dependent arguments and returns Bool. Frame replaces n heap arguments with Snap and
//! preserves result, precondition frame returns Bool.
//!
//! Integration:
//! state::identifiers, state::terms, supporters::functions and
//! state::function_precondition_transformer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Function symbol factory and identity with terms.
//!
//! Status: description only; implementation has not started.
