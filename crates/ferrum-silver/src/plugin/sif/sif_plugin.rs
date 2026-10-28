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
//! Status: partial; SIF parser feature registration and fallible transformer dispatch are
//! implemented, with a concrete pure-method product transformer; other forms fail closed.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2025 ETH Zurich.

use crate::ast::program::Program;
use crate::parser::fast_parser::ParserFeature;
use crate::plugin::silver_plugin::{PluginHookError, SilverPlugin};

/// A concrete implementation of the SIF extended transformation must supply
/// the actual rewrite; no unchanged-program fallback represents a successful transform.
pub trait SifTransformer: Send {
    fn transform(
        &mut self,
        input: Program,
        enable_timing: bool,
    ) -> Result<Program, PluginHookError>;
}
pub struct SifPlugin<T: SifTransformer> {
    pub transformer: T,
}
impl<T: SifTransformer> SilverPlugin for SifPlugin<T> {
    fn parser_features(&self) -> Vec<ParserFeature> {
        vec![ParserFeature::Sif]
    }
    fn before_verify(&mut self, input: Program) -> Result<Program, PluginHookError> {
        self.transformer.transform(input, false)
    }
}
