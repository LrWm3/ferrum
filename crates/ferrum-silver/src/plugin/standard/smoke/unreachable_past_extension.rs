//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/smoke/UnreachablePASTExtension.scala
//!
//! Purpose:
//! Represent the unreachable marker in the parse AST.
//!
//! Planned Rust structure:
//! Port PUnreachableKeyword and PUnreachable typecheck and translateStmt hooks.
//!
//! Behavior to preserve:
//! Typechecking adds no diagnostics; translation retains source position in Unreachable.
//!
//! Integration:
//! parser::fast_parser, resolver and translator; smoke::unreachable_ast_extension and
//! smoke_detection_plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser extensions and positions.
//!
//! Open decisions:
//! Agree on native parser registration with fast_parser.
//!
//! Status: description only; implementation has not started.
