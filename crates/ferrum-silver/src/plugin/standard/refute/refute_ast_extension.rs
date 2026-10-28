//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/refute/RefuteASTExtension.scala
//!
//! Purpose:
//! Represent refute statements and mark their lowered assertions.
//!
//! Planned Rust structure:
//! Port Refute extension statement and RefuteInfo failure-expected metadata; provide pretty
//! printing and expression subnode.
//!
//! Behavior to preserve:
//! Keep positions, info and error transformation on Refute; RefuteInfo associates each lowered
//! assertion with its source statement.
//!
//! Integration:
//! plugin::standard::refute::refute_plugin, refute_errors and parser extension; ast statement,
//! info and pretty printer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for AST handles and metadata.
//!
//! Open decisions:
//! Agree on metadata identity and source node lifetime with refute_plugin and ast.
//!
//! Status: description only; implementation has not started.
