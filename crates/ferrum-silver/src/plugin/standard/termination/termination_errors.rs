//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/TerminationErrors.scala
//!
//! Purpose:
//! Define termination failure and reason variants.
//!
//! Planned Rust structure:
//! Port AbstractTerminationError, FunctionTerminationError, MethodTerminationError,
//! LoopTerminationError and five condition/tuple reason types.
//!
//! Behavior to preserve:
//! Preserve termination.failed and reason IDs/messages, offending nodes, cached flag and reason
//! mappings; tuple failure variants share tuple.false. Upstream withNode on the three verification
//! errors ignores the replacement argument.
//!
//! Integration:
//! transformation::{error_trafo_factory,function_check,method_check} and verifier error/reason
//! interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for diagnostics, positions and transformations.
//!
//! Open decisions:
//! Reconcile apparent withNode bug with verifier before selecting behavior; record deliberate
//! changes.
//!
//! Status: description only; implementation has not started.
