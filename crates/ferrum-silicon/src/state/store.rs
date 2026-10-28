//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Store.scala
//!
//! Purpose:
//! Bind Silver local variables to terms and optional debug expressions.
//!
//! Planned Rust structure:
//! Store, StoreFactory and MapBackedStore expose lookup, projections and immutable
//! binding/store updates.
//!
//! Behavior to preserve:
//! Direct lookup fails on missing key; get/getExp return optional values; later store
//! bindings override earlier ones.
//!
//! Integration:
//! state::state, rules and interfaces::verification.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Map order and AST key identity with Silver.
//!
//! Status: description only; implementation has not started.
