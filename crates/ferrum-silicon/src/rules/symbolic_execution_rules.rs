//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/SymbolicExecutionRules.scala
//!
//! Purpose:
//! Construct verifier failures and diagnostics shared by symbolic execution.
//!
//! Planned Rust structure:
//! SymbolicExecutionRules provides debugOn and createFailure overloads for term, expression,
//! description and model request.
//!
//! Behavior to preserve:
//! Count/report unexpected failures only at final retry; unwrap counterexample transformer;
//! optionally generate model and only construct counterexample when valid. Select native, variable,
//! mapped, raw or resolved model, apply transformer, optionally include unknown reason and filtered
//! branch conditions. Debug context records state, declarations and assumptions; otherwise use
//! ordinary failure context. Failure continuation flag follows reportFurtherErrors.
//!
//! Integration:
//! interfaces::verification, reporting, verifier, decider and silver::verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Failure context lifetime and solver/model ownership.
//!
//! Status: description only; implementation has not started.
