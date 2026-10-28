//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/decider/TermConverter.scala
//!
//! Purpose:
//! Specify conversion of terms, sorts and declarations to solver representation.
//!
//! Planned Rust structure:
//! TermConverter has convert overloads for Term, Sort, Decl and convertSanitized for Sort.
//!
//! Behavior to preserve:
//! Sanitized sort conversion is a distinct operation; preserve backend-specific conversions
//! and errors.
//!
//! Integration:
//! decider serializers and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Associated types and backend ownership.
//!
//! Status: description only; implementation has not started.
