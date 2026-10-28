//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/SilverPluginManager.scala
//!
//! Purpose:
//! Construct ordered plugins and apply their transformations at each pipeline boundary.
//!
//! Planned Rust structure:
//! Represent SilverPluginManager, foldWithError, hook and result mapping methods,
//! resolveAll/resolve and plugin construction errors.
//!
//! Behavior to preserve:
//! foldWithError runs in declaration order and stops at first plugin with errors, appending those
//! errors; result hooks fold all plugins in order. Colon-separated class names retain duplicates
//! and ordering. Upstream reflection tries four-argument constructor then no-argument constructor
//! and distinguishes missing, wrong type and wrong arguments.
//!
//! Integration:
//! plugin::silver_plugin, frontend::sil_frontend, parser::fast_parser and reporter::reporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md; replace JVM reflection with a native registration mechanism
//! while preserving failure distinctions.
//!
//! Open decisions:
//! Agree on native registration and instance/service lifetimes with frontend and bundled plugins.
//!
//! Status: partial; hook dispatch is implemented. Plugin registry and concrete error
//! equality, parser, frontend and IO integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::silver_plugin::SilverPlugin;
use crate::ast::program::Program;
use crate::parser::parse_ast::PProgramHandle;
use crate::reporter::package::Entity;
use crate::reporter::reporter::{EntityResultMapper, ReportError};
use crate::verifier::verification_result::{AbstractError, VerificationResult};
use std::sync::Mutex;

#[derive(Default)]
pub struct SilverPluginManager {
    pub plugins: Vec<Box<dyn SilverPlugin>>,
    errors: Vec<AbstractError>,
}
impl SilverPluginManager {
    pub fn new(plugins: Vec<Box<dyn SilverPlugin>>) -> Self {
        Self {
            plugins,
            errors: Vec::new(),
        }
    }
    pub fn errors(&self) -> &[AbstractError] {
        &self.errors
    }
    fn fold_with_error<T>(
        &mut self,
        start: T,
        mut apply: impl FnMut(&mut dyn SilverPlugin, T) -> T,
    ) -> Option<T> {
        let mut current = start;
        for plugin in &mut self.plugins {
            current = apply(plugin.as_mut(), current);
            if !plugin.errors().is_empty() {
                self.errors.extend_from_slice(plugin.errors());
                return None;
            }
        }
        Some(current)
    }
    pub fn before_parse(&mut self, input: String, imported: bool) -> Option<String> {
        self.fold_with_error(input, |p, input| p.before_parse(input, imported))
    }
    pub fn before_resolve(&mut self, input: PProgramHandle) -> Option<PProgramHandle> {
        self.fold_with_error(input, |p, input| p.before_resolve(input))
    }
    pub fn before_translate(&mut self, input: PProgramHandle) -> Option<PProgramHandle> {
        self.fold_with_error(input, |p, input| p.before_translate(input))
    }
    pub fn before_method_filter(&mut self, input: Program) -> Option<Program> {
        self.fold_with_error(input, |p, input| p.before_method_filter(input))
    }
    pub fn before_verify(&mut self, input: Program) -> Option<Program> {
        self.fold_with_error(input, |p, input| p.before_verify(input))
    }
    pub fn map_entity_verification_result(
        &mut self,
        entity: &Entity,
        mut input: VerificationResult,
    ) -> VerificationResult {
        for plugin in &mut self.plugins {
            input = plugin.map_entity_verification_result(entity, input);
        }
        input
    }
    pub fn map_verification_result(
        &mut self,
        program: &Program,
        mut input: VerificationResult,
    ) -> VerificationResult {
        for plugin in &mut self.plugins {
            input = plugin.map_verification_result(program, input);
        }
        input
    }
    pub fn before_finish(&mut self, mut input: VerificationResult) -> VerificationResult {
        for plugin in &mut self.plugins {
            input = plugin.before_finish(input);
        }
        input
    }
}
impl EntityResultMapper for Mutex<SilverPluginManager> {
    fn map_entity_result(
        &self,
        entity: &Entity,
        result: VerificationResult,
    ) -> Result<VerificationResult, ReportError> {
        Ok(self
            .lock()
            .expect("poisoned plugin manager")
            .map_entity_verification_result(entity, result))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::position::Position;
    use crate::verifier::verification_result::{ParseError, ParseReport};
    struct Stop {
        errors: Vec<AbstractError>,
    }
    impl SilverPlugin for Stop {
        fn errors(&self) -> &[AbstractError] {
            &self.errors
        }
        fn before_parse(&mut self, input: String, _: bool) -> String {
            self.errors
                .push(AbstractError::Parse(ParseReport::Error(ParseError::new(
                    "plugin",
                    Position::NoPosition,
                ))));
            format!("{input}a")
        }
    }
    struct Unreachable;
    impl SilverPlugin for Unreachable {
        fn before_parse(&mut self, _: String, _: bool) -> String {
            panic!("later plugin must not run")
        }
    }
    #[test]
    fn transformation_stops_at_first_plugin_error() {
        let mut manager = SilverPluginManager::new(vec![
            Box::new(Stop { errors: Vec::new() }),
            Box::new(Unreachable),
        ]);
        assert!(manager.before_parse("input".into(), false).is_none());
        assert_eq!(manager.errors().len(), 1);
    }
}
