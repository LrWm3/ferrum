//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/Property.scala
//!
//! Purpose:
//! Name and describe a Boolean resource property.
//!
//! Planned Rust structure:
//! Port Property expression, name and description fields and display.
//!
//! Behavior to preserve:
//! Reject names containing spaces and display the name.
//!
//! Integration:
//! resources::property_expressions and resource_descriptions, property interpreters.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for property expression ownership.
//!
//! Open decisions:
//! Agree on typed property expression representation with property_expressions.
//!
//! Status: description only; implementation has not started.
