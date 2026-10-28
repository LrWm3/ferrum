//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/refute/RefutePASTExtension.scala
//!
//! Purpose:
//! Parse-tree representation of refute statements.
//!
//! Planned Rust structure:
//! Represent PRefuteKeyword and PRefute with typecheck and translateStmt hooks.
//!
//! Behavior to preserve:
//! Typecheck expression as Bool and translate to Refute preserving source position.
//!
//! Integration:
//! parser::fast_parser, resolver and translator; plugin::standard::refute::refute_ast_extension
//! and refute_plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser extension and position conversion.
//!
//! Open decisions:
//! Reconcile extension registration and parse-tree ownership with parser and refute_plugin.
//!
//! Status: description only; implementation has not started.
