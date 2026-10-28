//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Identifiers.scala
//!
//! Purpose:
//! Represent and generate solver identifiers.
//!
//! Planned Rust structure:
//! Identifier, SimpleIdentifier, SuffixedIdentifier, SortBasedIdentifier and
//! IdentifierFactory/DefaultIdentifierFactory implement rename, suffix and fresh.
//!
//! Behavior to preserve:
//! Default separator is @; suffix retains identifier structure; sort-based identifiers
//! format sorts; reset resets fresh counter.
//!
//! A suffixed prefix cannot itself be suffixed; applying another suffix replaces
//! the existing one. Renaming a sort-based identifier changes only its template.
//! Fresh names append the counter and namespace in that order.
//!
//! Integration:
//! state::terms, state::symbol_converter and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Identifier rendering and counter ownership.
//!
//! Status: description only; implementation has not started.
