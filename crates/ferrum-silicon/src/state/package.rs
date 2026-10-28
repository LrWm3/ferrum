//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/package.scala
//!
//! Purpose:
//! Define state-level cache aliases.
//!
//! Planned Rust structure:
//! PmCache maps resource and quantified chunk sequence to PermMapDefinition; SsCache maps
//! resource, nonquantified chunks and terms to optional tagged snapshot, terms, result term
//! and debug expression.
//!
//! Behavior to preserve:
//! Cache keys include ordered chunk/term sequences; preserve optional fields and resource
//! identity.
//!
//! Integration:
//! state::state, state::chunks and rules::more_complete_exhale_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Cache key equality with terms and chunks.
//!
//! Status: description only; implementation has not started.
