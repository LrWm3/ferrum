//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/PropertyInterpreter.scala
//!
//! Purpose:
//! Translate property expressions to symbolic path conditions and optional debug AST.
//!
//! Planned Rust structure:
//! Port PropertyInterpreter buildPathCondition and literal, Boolean, equality, arithmetic, ITE and
//! abstract chunk/check/foreach helpers.
//!
//! Behavior to preserve:
//! Short circuit And/Or/Implies when left is syntactically decisive. Compare argument lists
//! componentwise, handle Null specially; reject zero denominator and retain exact fractions. Debug
//! mode constructs corresponding AST; Check and ForEach are delegated. Preserve greater
//! comparisons by swapping operands and conditional AST shape.
//!
//! Integration:
//! resources::{property_expressions,non_quantified_property_interpreter,quantified_property_interpreter};
//! state::terms, verifier and Silver AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for symbolic/debug expression pairing and exact arithmetic.
//!
//! Open decisions:
//! Reconcile debug expression availability and generic interpreter dispatch with specialized
//! implementations.
//!
//! Status: description only; implementation has not started.
