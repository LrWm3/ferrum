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
//! Status: partial; hook dispatch is implemented. Native plugin registry is implemented; concrete error equality, parser,
//! frontend and IO integration remain pending.

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
use std::sync::{Arc, Mutex};

/// Explicit identity view for plugins with the source default entity mapping.
pub fn identity_entity_mapper() -> Arc<dyn EntityResultMapper> {
    Arc::new(|_: &Entity, result: VerificationResult| Ok(result))
}
struct SharedEntityMappers(Vec<Arc<dyn EntityResultMapper>>);
impl EntityResultMapper for SharedEntityMappers {
    fn map_entity_result(
        &self,
        entity: &Entity,
        mut result: VerificationResult,
    ) -> Result<VerificationResult, ReportError> {
        for mapper in &self.0 {
            result = mapper.map_entity_result(entity, result)?;
        }
        Ok(result)
    }
}

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
    pub fn shared_entity_mapper(&self) -> Result<Arc<dyn EntityResultMapper>, ReportError> {
        let mut views = Vec::with_capacity(self.plugins.len());
        for plugin in &self.plugins {
            views.push(
                plugin
                    .shared_entity_mapper()
                    .ok_or(ReportError::Unsupported(
                        "plugin does not provide a shared entity mapper",
                    ))?,
            );
        }
        Ok(Arc::new(SharedEntityMappers(views)))
    }
    pub fn parser_features(&self) -> Vec<crate::parser::fast_parser::ParserFeature> {
        self.plugins
            .iter()
            .flat_map(|plugin| plugin.parser_features())
            .collect()
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
        if !imported {
            self.errors.clear();
        }
        self.fold_with_error(input, |p, input| p.before_parse(input, imported))
    }
    pub fn before_resolve(&mut self, input: PProgramHandle) -> Option<PProgramHandle> {
        self.fold_with_error(input, |p, input| p.before_resolve(input))
    }
    pub fn before_translate(&mut self, input: PProgramHandle) -> Option<PProgramHandle> {
        self.fold_with_error(input, |p, input| p.before_translate(input))
    }
    pub fn additional_standard_imports(
        &self,
        input: &PProgramHandle,
    ) -> Result<Vec<String>, super::silver_plugin::PluginHookError> {
        let mut imports = Vec::new();
        for plugin in &self.plugins {
            for import in plugin.additional_standard_imports(input)? {
                if !imports.contains(&import) {
                    imports.push(import);
                }
            }
        }
        Ok(imports)
    }
    pub fn before_method_filter(&mut self, input: Program) -> Option<Program> {
        self.fold_with_error(input, |p, input| p.before_method_filter(input))
    }
    pub fn before_verify(
        &mut self,
        mut input: Program,
    ) -> Result<Option<Program>, super::silver_plugin::PluginHookError> {
        for plugin in &mut self.plugins {
            input = plugin.before_verify(input)?;
            if !plugin.errors().is_empty() {
                self.errors.extend_from_slice(plugin.errors());
                return Ok(None);
            }
        }
        Ok(Some(input))
    }
    pub fn map_entity_verification_result(
        &mut self,
        entity: &Entity,
        mut input: VerificationResult,
    ) -> Result<VerificationResult, super::silver_plugin::PluginHookError> {
        for plugin in &mut self.plugins {
            input = plugin.map_entity_verification_result(entity, input)?;
        }
        Ok(input)
    }
    pub fn map_verification_result(
        &mut self,
        program: &Program,
        mut input: VerificationResult,
    ) -> Result<VerificationResult, super::silver_plugin::PluginHookError> {
        for plugin in &mut self.plugins {
            input = plugin.map_verification_result(program, input)?;
        }
        Ok(input)
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
        self.lock()
            .expect("poisoned plugin manager")
            .map_entity_verification_result(entity, result)
            .map_err(|e| ReportError::Plugin(e.0))
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

/// Native registry replaces JVM class loading while retaining requested-name order and
/// distinct resolution failures. Factories can capture reporter/config/parser context.
#[derive(Default)]
pub struct PluginRegistry {
    factories: std::collections::HashMap<
        String,
        Box<dyn Fn() -> Result<Box<dyn SilverPlugin>, PluginResolutionError> + Send + Sync>,
    >,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PluginResolutionError {
    NotFound(String),
    WrongType(String),
    WrongArguments(String),
    Construction(String),
}
impl std::fmt::Display for PluginResolutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotFound(name) => write!(f, "Plugin {name} not found."),
            Self::WrongType(name) => write!(f, "Plugin {name} has wrong type."),
            Self::WrongArguments(name) => write!(
                f,
                "Plugin {name} does not implement a constructor with the required signature."
            ),
            Self::Construction(message) => f.write_str(message),
        }
    }
}
impl std::error::Error for PluginResolutionError {}
impl PluginRegistry {
    pub fn register(
        &mut self,
        name: impl Into<String>,
        factory: impl Fn() -> Result<Box<dyn SilverPlugin>, PluginResolutionError>
        + Send
        + Sync
        + 'static,
    ) {
        self.factories.insert(name.into(), Box::new(factory));
    }
    pub fn resolve(&self, name: &str) -> Result<Box<dyn SilverPlugin>, PluginResolutionError> {
        self.factories
            .get(name)
            .ok_or_else(|| PluginResolutionError::NotFound(name.into()))?()
    }
    pub fn manager(
        &self,
        names: Option<&str>,
    ) -> Result<SilverPluginManager, PluginResolutionError> {
        let Some(names) = names else {
            return Ok(SilverPluginManager::default());
        };
        // Java/Scala split removes trailing empty fields but preserves a single empty input.
        let parts: Vec<&str> = if names.is_empty() {
            vec![""]
        } else {
            names
                .split(':')
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .skip_while(|part| part.is_empty())
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .collect()
        };
        let mut plugins = Vec::with_capacity(parts.len());
        for name in parts {
            plugins.push(self.resolve(name)?);
        }
        Ok(SilverPluginManager::new(plugins))
    }
}

#[cfg(test)]
mod registry_tests {
    use super::*;
    struct Append(&'static str);
    impl SilverPlugin for Append {
        fn before_parse(&mut self, input: String, _: bool) -> String {
            format!("{input}{}", self.0)
        }
    }
    #[test]
    fn factories_preserve_requested_order_and_reject_unknown_names() {
        let mut registry = PluginRegistry::default();
        registry.register("a", || Ok(Box::new(Append("a"))));
        registry.register("b", || Ok(Box::new(Append("b"))));
        let mut manager = registry.manager(Some("b:a")).unwrap();
        assert_eq!(
            manager.before_parse(String::new(), false),
            Some("ba".into())
        );
        assert!(matches!(
            registry.manager(Some("missing")),
            Err(PluginResolutionError::NotFound(_))
        ));
    }
}
