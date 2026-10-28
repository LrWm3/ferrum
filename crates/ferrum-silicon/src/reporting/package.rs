//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/package.scala
//!
//! Purpose:
//! Convert Silicon results and exceptions to Silver result boundaries.
//!
//! Planned Rust structure:
//! Port unwrapExecutionExceptions, exceptionToViperError, convertToViperResult(s),
//! condenseToViperResult and classpath diagnostic constant.
//!
//! Behavior to preserve:
//! Unwrap nested ExecutionExceptions; SiliconException maps to its Silver error, other exceptions
//! to AbortedExceptionally and fatal Error stays distinct. Success and Unreachable map to Silver
//! Success; aggregate all failures in order, returning Success only if none.
//!
//! Integration:
//! reporting::exceptions, interfaces::verification, verifier and Silver result types.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for distinct failures and exception conversion.
//!
//! Open decisions:
//! Reconcile native panic/error boundary and JVM-specific classpath message disposition with
//! verifier.
//!
//! Status: description only; implementation has not started.
