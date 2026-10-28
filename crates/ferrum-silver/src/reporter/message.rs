//! Port plan: Define structured frontend, verification and progress messages.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/reporter/Message.scala
//!
//! Purpose:
//! Define structured frontend, verification and progress messages.
//!
//! Planned Rust structure:
//! Message and AST/verification result families, factories for overall/entity/cached results;
//! statistics, outline, definitions, parsed program, execution trace, exception, arguments,
//! subprocess stages, dependencies, warnings, simple, quantifier, termination, benchmarking,
//! block/path and verifier-state messages. VerifierState frames/steps and BranchCondition variants
//! render progress.
//!
//! Behavior to preserve:
//! Result factories dispatch Success/Failure; cached entity results use zero time. Preserve each
//! message name, fields and source rendering, subprocess stages and per-entity cached status.
//! State renders outermost frame first, branch indentation and optional line:column positions;
//! alternatives are displayed one-based.
//!
//! Integration:
//! reporter::{package,reporter}, verifier::{verification_result,verifier}, parser and Silicon
//! reporting.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile message ownership, extension/state payloads and serialized/rendered compatibility
//! with plugin manager and Silicon.
//!
//! Status: description only; implementation has not started.
