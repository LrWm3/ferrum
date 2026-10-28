//! Port plan: Represent proof errors, reasons and legacy solver models.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/VerificationError.scala
//!
//! Purpose:
//! Represent proof errors, reasons and legacy solver models.
//!
//! Planned Rust structure:
//! ModelEntry/ValueEntry variants, MapEntry, Model, Counterexample and transformer; ErrorMessage,
//! VerificationError, FailureContext, PartialVerificationError, AbstractVerificationError/Reason,
//! DummyNode/Reason, errors and reasons families.
//!
//! Behavior to preserve:
//! Keep distinct error IDs and reason IDs, offending node and reason, cached flag and failure
//! contexts. Include
//! assignment/call/contracts/assert/inhale/exhale/loop/fold/wand/havoc/termination/internal errors
//! and permission, null, arithmetic, bounds, injectivity, timeout and unsupported reasons.
//! Transform error node first then reason and retain contexts; special node positions and
//! counterexample wrappers matter. Model resolution accepts ordered :var constraints, rejects
//! malformed forms, and model parse failures throw.
//!
//! Integration:
//! ast::{ast,expression,statement,program},
//! verifier::{model_parser,verification_result,counterexample}, reporter and Silicon rules.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile error-node and callback ownership, extensibility, transformed counterexamples and
//! result boundary with AST metadata, plugins and Silicon.
//!
//! Status: description only; implementation has not started.
