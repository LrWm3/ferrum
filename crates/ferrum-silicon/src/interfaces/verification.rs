//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/Verification.scala
//!
//! Purpose:
//! Model verification outcomes and failure contexts/counterexamples.
//!
//! Planned Rust structure:
//! VerificationResult, FatalResult, NonFatalResult, Success, Unreachable, Failure;
//! SiliconFailureContext and SiliconDebuggingFailureContext; native, variable and mapped
//! SiliconCounterexample variants.
//!
//! Behavior to preserve:
//! combine lazily evaluates other only if continuation permits, except alwaysWaitForOther;
//! retain ordered previous chains, fatal head selection and isReported. Variable model
//! includes mapped variables and integer/boolean literals. Mapped model interprets labels
//! and renames snapshot values consistently as hp_N.
//!
//! Integration:
//! silver::verifier, reporting converter/interpreter, state and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Result mutability and continuation ownership with rules and reporting.
//!
//! Status: description only; implementation has not started.
