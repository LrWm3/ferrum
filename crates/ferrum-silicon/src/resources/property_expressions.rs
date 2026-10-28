//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/PropertyExpressions.scala
//!
//! Purpose:
//! Define the typed expression language used for resource assumptions.
//!
//! Planned Rust structure:
//! Port Kind/equatable/ITE categories, Boolean, Argument, Value, Permission and Chunk kinds;
//! IfThenElse, Check, ForEach, comparisons, Boolean/permission operators, literals, placeholders
//! and accessors.
//!
//! Behavior to preserve:
//! ForEach requires nonempty distinct variable names and quantifies distinct chunk tuples of the
//! same ID; ChunkVariable cannot be named this. Preserve exact arbitrary precision fraction
//! literals and typed accessor constraints.
//!
//! Integration:
//! resources::property_interpreter and specialized interpreters, resource_descriptions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact arithmetic and typed enums or equivalent; concrete
//! representation is open.
//!
//! Open decisions:
//! Agree on typed construction and placeholder identity with both interpreters.
//!
//! Status: description only; implementation has not started.
