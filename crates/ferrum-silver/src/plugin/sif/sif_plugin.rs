//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/sif/SIFPlugin.scala
//!
//! Purpose:
//! Register basic SIF syntax and apply the extended product-program transformer.
//!
//! Planned Rust structure:
//! Port PLowKeyword, PLowEventKeyword, PRelKeyword and SIFPlugin low/rel/lowEvent parsers,
//! beforeParse and beforeVerify.
//!
//! Behavior to preserve:
//! Register keywords and end-expression extensions in low, rel, lowEvent order; beforeVerify
//! installs plugin error callback and calls transform with timing disabled.
//!
//! Integration:
//! parser::fast_parser, sifp_ast_extensions, sif_extended_transformer and
//! plugin::silver_plugin_manager.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for native parser hooks and context ownership.
//!
//! Open decisions:
//! Replace upstream global transformer configuration/error callback with an agreed owned context
//! without changing configuration behavior.
//!
//! Status: description only; implementation has not started.
