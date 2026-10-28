//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/SilNameGenerator.scala
//!
//! Purpose:
//! Configure the general name generator for valid Silver identifiers.
//!
//! Planned Rust structure:
//! Port SilNameGenerator specialization with first/other character patterns, reserved names and
//! underscore separator.
//!
//! Behavior to preserve:
//! Preserve allowed ASCII letters, $, _, digits and apostrophe in subsequent positions and
//! postcondition validIdentifier.
//!
//! Integration:
//! utility::name_generator and ast::utility::consistency.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on shared identifier validation and context ownership with name_generator.
//!
//! Status: description only; implementation has not started.
