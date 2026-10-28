//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/SilverPlugin.scala
//!
//! Purpose:
//! Define the plugin lifecycle hooks and accumulated transformation errors.
//!
//! Planned Rust structure:
//! Represent IOAwarePlugin and SilverPlugin, including beforeParse, beforeResolve,
//! beforeTranslate, beforeMethodFilter, beforeVerify, entity/result mappings, beforeFinish and
//! reportError.
//!
//! Behavior to preserve:
//! Default hooks return input unchanged. Entity and program result mapping occur only after
//! verification; beforeFinish also handles earlier failures. reportError appends unless an equal
//! error at the same position already exists.
//!
//! Integration:
//! plugin::silver_plugin_manager folds hooks; frontend::sil_frontend, parser::fast_parser and
//! reporter::reporter supply lifecycle and data.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, diagnostics and native plugin registration; pass
//! IO services explicitly.
//!
//! Open decisions:
//! Reconcile plugin instance ownership, mutable errors and callbacks with silver_plugin_manager
//! and frontend.
//!
//! Status: partial; hook dispatch is implemented. Plugin registry and concrete error
//! equality, parser, frontend and IO integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::program::Program;
use crate::parser::parse_ast::PProgramHandle;
use crate::reporter::package::Entity;
use crate::verifier::verification_result::{AbstractError, VerificationResult};

/// A native plugin hook could not execute its requested transformation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PluginHookError(pub String);

/// Plugin hooks default to identity, as in SilverPlugin. Concrete plugins own their error lists.
pub trait SilverPlugin: Send {
    /// A shared view of this plugin's entity mapping, or None when unavailable.
    /// The view must observe all mapping-relevant phase changes throughout its lifetime,
    /// agree with sequential `map_entity_verification_result`, and support concurrent and
    /// reentrant calls without deadlock. A view may retain shared state beyond the manager's
    /// lifetime. Built-ins capture only mapping data verified immutable during verification;
    /// custom stateful plugins must instead share their live mapping state.
    fn shared_entity_mapper(
        &self,
    ) -> Option<std::sync::Arc<dyn crate::reporter::reporter::EntityResultMapper>> {
        None
    }
    fn parser_features(&self) -> Vec<crate::parser::fast_parser::ParserFeature> {
        Vec::new()
    }
    fn errors(&self) -> &[AbstractError] {
        &[]
    }
    fn before_parse(&mut self, input: String, _is_imported: bool) -> String {
        input
    }
    fn before_resolve(&mut self, input: PProgramHandle) -> PProgramHandle {
        input
    }
    fn before_translate(&mut self, input: PProgramHandle) -> PProgramHandle {
        input
    }
    /// Standard resources to analyze and merge before translating this checked tree.
    fn additional_standard_imports(
        &self,
        _input: &PProgramHandle,
    ) -> Result<Vec<String>, PluginHookError> {
        Ok(Vec::new())
    }
    fn before_method_filter(&mut self, input: Program) -> Program {
        input
    }
    fn before_verify(&mut self, input: Program) -> Result<Program, PluginHookError> {
        Ok(input)
    }
    fn map_entity_verification_result(
        &mut self,
        _entity: &Entity,
        input: VerificationResult,
    ) -> Result<VerificationResult, PluginHookError> {
        Ok(input)
    }
    fn map_verification_result(
        &mut self,
        _program: &Program,
        input: VerificationResult,
    ) -> Result<VerificationResult, PluginHookError> {
        Ok(input)
    }
    fn before_finish(&mut self, input: VerificationResult) -> VerificationResult {
        input
    }
}
/// Error collection with the source's equality-and-position deduplication.
/// Verification diagnostics require a concrete equality contract before distinct
/// values can be compared; that unresolved case is returned to the caller.
#[derive(Default)]
pub struct PluginErrors {
    errors: Vec<AbstractError>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DiagnosticEqualityUnavailable;
impl PluginErrors {
    pub fn errors(&self) -> &[AbstractError] {
        &self.errors
    }
    pub fn report(&mut self, error: AbstractError) -> Result<(), DiagnosticEqualityUnavailable> {
        for existing in &self.errors {
            if existing.position() != error.position() {
                continue;
            }
            let equal = match (existing, &error) {
                (AbstractError::Parse(a), AbstractError::Parse(b)) => a == b,
                (AbstractError::Frontend(a), AbstractError::Frontend(b)) => a == b,
                (AbstractError::Verification(a), AbstractError::Verification(b)) => {
                    if std::sync::Arc::ptr_eq(a, b) {
                        true
                    } else {
                        return Err(DiagnosticEqualityUnavailable);
                    }
                }
                _ => false,
            };
            if equal {
                return Ok(());
            }
        }
        self.errors.push(error);
        Ok(())
    }
}

/// Source Consistency.checkPure for plugin expressions. Rendering failures are
/// propagated rather than inventing a diagnostic expression.
pub(crate) fn check_pure_expressions<'a>(
    expressions: impl IntoIterator<Item = &'a crate::ast::expression::Exp>,
) -> Result<
    Vec<crate::verifier::verification_result::FrontendError>,
    crate::verifier::verification_result::DiagnosticError,
> {
    use crate::verifier::verification_result::{DiagnosticError, FrontendError, FrontendErrorKind};
    let mut errors = Vec::new();
    for expression in expressions {
        if !expression.is_pure() {
            let rendered = crate::ast::pretty::pretty_printer::pretty_expression(expression)
                .map_err(|_| DiagnosticError::Unsupported("plugin purity diagnostic rendering"))?;
            errors.push(FrontendError::new(
                FrontendErrorKind::ConsistencyError(format!(
                    "{rendered} is non pure and appears where only pure expressions are allowed."
                )),
                expression.metadata().position.clone(),
            ));
        }
    }
    Ok(errors)
}
