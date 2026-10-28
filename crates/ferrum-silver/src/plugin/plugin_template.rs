//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/PluginTemplate.scala
//!
//! Purpose:
//! Document a skeleton for plugin authors showing all hook contracts.
//!
//! Planned Rust structure:
//! Account for PluginTemplate and each corresponding SilverPlugin hook, including transformation,
//! reporting and result hooks.
//!
//! Behavior to preserve:
//! The source is a copyable example whose methods are unimplemented; default SilverPlugin hooks
//! instead pass through. beforeFinish also runs on failures before verification, whereas result
//! mappings require verification.
//!
//! Integration:
//! plugin::silver_plugin and silver_plugin_manager; frontend::sil_frontend calls the lifecycle.
//!
//! Rust adaptations:
//! Follow porting/conventions.md; express the example as documentation or a native example without
//! executable success placeholders.
//!
//! Open decisions:
//! Decide where the native plugin example belongs once registration and public APIs are settled.
//!
//! Status: template contract and dispatch adapter implemented; upstream example bodies
//! intentionally require implementations by the downstream plugin author.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::silver_plugin::{PluginHookError, SilverPlugin};
use crate::ast::program::Program;
use crate::parser::parse_ast::PProgramHandle;
use crate::reporter::package::Entity;
use crate::verifier::verification_result::{AbstractError, VerificationResult};

/// The upstream example contains deliberately undefined bodies. Native implementers
/// provide each hook explicitly; this adapter makes the example executable without
/// treating those missing example bodies as successful transformations.
pub trait PluginTemplate: Send {
    fn errors(&self) -> &[AbstractError];
    fn report_error(&mut self, error: AbstractError);
    fn before_parse(&mut self, input: String, is_imported: bool) -> String;
    fn before_resolve(&mut self, input: PProgramHandle) -> PProgramHandle;
    fn before_translate(&mut self, input: PProgramHandle) -> PProgramHandle;
    fn before_method_filter(&mut self, input: Program) -> Program;
    fn before_verify(&mut self, input: Program) -> Program;
    fn map_entity_verification_result(
        &mut self,
        entity: &Entity,
        input: VerificationResult,
    ) -> VerificationResult;
    fn map_verification_result(
        &mut self,
        program: &Program,
        input: VerificationResult,
    ) -> VerificationResult;
    fn before_finish(&mut self, input: VerificationResult) -> VerificationResult;
}
pub struct TemplatePlugin<T: PluginTemplate>(pub T);
impl<T: PluginTemplate> SilverPlugin for TemplatePlugin<T> {
    fn errors(&self) -> &[AbstractError] {
        self.0.errors()
    }
    fn before_parse(&mut self, input: String, imported: bool) -> String {
        self.0.before_parse(input, imported)
    }
    fn before_resolve(&mut self, input: PProgramHandle) -> PProgramHandle {
        self.0.before_resolve(input)
    }
    fn before_translate(&mut self, input: PProgramHandle) -> PProgramHandle {
        self.0.before_translate(input)
    }
    fn before_method_filter(&mut self, input: Program) -> Program {
        self.0.before_method_filter(input)
    }
    fn before_verify(&mut self, input: Program) -> Result<Program, PluginHookError> {
        Ok(self.0.before_verify(input))
    }
    fn map_entity_verification_result(
        &mut self,
        entity: &Entity,
        input: VerificationResult,
    ) -> Result<VerificationResult, PluginHookError> {
        Ok(self.0.map_entity_verification_result(entity, input))
    }
    fn map_verification_result(
        &mut self,
        program: &Program,
        input: VerificationResult,
    ) -> Result<VerificationResult, PluginHookError> {
        Ok(self.0.map_verification_result(program, input))
    }
    fn before_finish(&mut self, input: VerificationResult) -> VerificationResult {
        self.0.before_finish(input)
    }
}
