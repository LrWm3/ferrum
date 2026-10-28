//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/DomainInterpreter.scala
//!
//! Purpose:
//! Interpret extracted model/domain entries recursively for counterexamples.
//!
//! Planned Rust structure:
//! Port AbstractInterpreter, ModelInterpreter, DomainInterpreter, IdentityInterpreter and
//! GenericDomainInterpreter.
//!
//! Behavior to preserve:
//! Follow unary functions on domain values, recursively resolve variables and reference fields,
//! track visited entries to break cycles and retain unresolved function marker; other values pass
//! through.
//!
//! Integration:
//! reporting::converter and extracted model entries, state::terms sorts.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for model value identity, cycles and error distinctions.
//!
//! Open decisions:
//! Agree on model entry equality and lazy recursion with converter.
//!
//! Status: description only; implementation has not started.
