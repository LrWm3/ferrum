//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/arp/ARPPASTExtension.scala
//!
//! Purpose:
//! Represent and typecheck rd in the parse AST.
//!
//! Planned Rust structure:
//! Port PRdKeyword and PRdPerm, including fixed Perm type, identity substitution, expected-type
//! check and translateExp.
//!
//! Behavior to preserve:
//! No typecheck error without an expected type; delegate expected-type checking to TypeChecker and
//! preserve source position in RdPerm.
//!
//! Integration:
//! parser::fast_parser, resolver and translator; arp_plugin and arpast_extension.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser extensions and type inference.
//!
//! Open decisions:
//! Agree on parser hooks and extension dispatch with parser modules.
//!
//! Status: description only; implementation has not started.
