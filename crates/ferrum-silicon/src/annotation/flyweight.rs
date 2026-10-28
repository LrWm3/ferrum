//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/annotation/src/main/scala/flyweight.scala
//!
//! Purpose:
//! Generate the historical annotation-driven flyweight classes.
//!
//! Planned Rust structure:
//! flyweight and flyweightMacro.impl inspect class and optional companion; generate private
//! constructor, pool, apply, optional copy and unapply, preserving companion definitions.
//!
//! Behavior to preserve:
//! Reject invalid annottees and explicit custom apply without return type; matching apply
//! is renamed _apply. Pool lookup and insertion are separate, and identity hash is used.
//! This annotation is dormant in the current build; Terms uses ConditionalFlyweight
//! factories.
//!
//! Integration:
//! state::terms factories and annotation build configuration.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Whether any native macro is needed once term factories are ported.
//!
//! Status: description only; implementation has not started.
