//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/arp/ARPASTExtension.scala
//!
//! Purpose:
//! Represent abstract read permission rd in the Silver AST until lowering.
//!
//! Planned Rust structure:
//! Port RdPerm as a pure Perm-typed extension expression with no children and rd pretty printing.
//!
//! Behavior to preserve:
//! Preserve position, metadata and error transformation; verifyExtExp is unimplemented upstream
//! and the plugin must eliminate it.
//!
//! Integration:
//! arp_plugin lowers the node; arppast_extension constructs it; ast expressions and verifier
//! interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for AST and metadata ownership.
//!
//! Open decisions:
//! Agree on unsupported unlowered extension handling with verifier.
//!
//! Status: description only; implementation has not started.
