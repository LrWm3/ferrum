//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/smoke/UnreachableASTExtension.scala
//!
//! Purpose:
//! Represent the smoke-detection unreachable marker in the verification AST.
//!
//! Planned Rust structure:
//! Port Unreachable extension statement, metadata and pretty printer; it has no subnodes.
//!
//! Behavior to preserve:
//! Preserve source position and marker until smoke preprocessing removes it.
//!
//! Integration:
//! smoke_detection_plugin and unreachable_past_extension; ast statement/metadata and pretty
//! printer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for extension node and position ownership.
//!
//! Open decisions:
//! Agree on extension elimination before verification with smoke_detection_plugin.
//!
//! Status: description only; implementation has not started.
