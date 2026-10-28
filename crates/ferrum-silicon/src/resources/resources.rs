//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/Resources.scala
//!
//! Purpose:
//! Map resource categories to property descriptions.
//!
//! Planned Rust structure:
//! Port ResourceID, BaseID, PredicateID, FieldID, MagicWandID and resourceDescriptions registry.
//!
//! Behavior to preserve:
//! Keep predicate and field as base resources, wand separate, and map each to its matching
//! description.
//!
//! Integration:
//! resources::resource_descriptions; state chunks and resource interpreters.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for enum and context ownership.
//!
//! Open decisions:
//! Agree on resource IDs with state and chunk interfaces.
//!
//! Status: description only; implementation has not started.
