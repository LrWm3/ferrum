//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/SilFrontend.scala
//!
//! Purpose:
//! Orchestrate CLI configuration, parsing through verification, plugin hooks and reporting.
//!
//! Planned Rust structure:
//! Represent SilFrontend, MissingDependencyException, FrontendStateCache and
//! ApplicationExitReason; retain parser, plugins, verifier, config and timing state. Provide
//! prepare, execute, resetPlugins, phase methods, verification and finish.
//!
//! Behavior to preserve:
//! Plugin order is smoke then refute when enabled, remaining defaults then explicit plugins; warn
//! on duplicates. beforeParse/Resolve/Translate, beforeMethodFilter/Verify, result mapping and
//! beforeFinish run at their respective boundaries. Preserve select/chopper empty warning, sorted
//! warnings/errors, consistency/backend checks, transformed error deduplication, exit codes and
//! exception reporting.
//!
//! Integration:
//! Uses parser::fast_parser, resolver, translator; plugin manager, ast::utility::consistency and
//! chopper, reporter and verifier; providers override phases.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Reconcile mutable cache, plugin/verifier ownership and native plugin registration with
//! frontend and plugin modules.
//!
//! Status: partial; parsing, core analysis and translation phases are connected to plugin hooks.
//! Complete consistency checks, CLI, reporting, lifecycle and verification integration remain
//! pending; verification is blocked until consistency checking exists.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::position::{LineColumn, Position};
use crate::ast::program::Program;
use crate::frontend::frontend::FrontendPhases;
use crate::parser::parse_ast::{PProgramHandle, init_properties};
use crate::parser::{fast_parser, resolver, translator};
use crate::plugin::silver_plugin_manager::SilverPluginManager;
use crate::verifier::verification_result::{
    AbstractError, FrontendError, FrontendErrorKind, ParseError, ParseReport,
};
use std::path::PathBuf;

/// Silver's native phase bodies. Unsupported semantic and consistency families
/// produce errors until their complete checks are available.
pub struct SilFrontendPhases {
    pub file: PathBuf,
    pub plugins: SilverPluginManager,
    pub local_loader: std::sync::Arc<dyn crate::ast::utility::file_loader::FileLoader>,
    pub standard_loader: Option<std::sync::Arc<dyn crate::ast::utility::file_loader::FileLoader>>,
    pub parsing_warnings: Vec<ParseReport>,
    pub typechecking_warnings: Vec<FrontendError>,
}
impl SilFrontendPhases {
    pub fn new(file: PathBuf, plugins: SilverPluginManager) -> Self {
        Self {
            file,
            plugins,
            local_loader: std::sync::Arc::new(crate::ast::utility::file_loader::DiskLoader),
            standard_loader: None,
            parsing_warnings: vec![],
            typechecking_warnings: vec![],
        }
    }
    fn failure(message: String, position: Position) -> Vec<AbstractError> {
        vec![AbstractError::Frontend(FrontendError::new(
            FrontendErrorKind::TypecheckerError(message),
            position,
        ))]
    }
    fn program_position(program: &PProgramHandle) -> Position {
        program
            .node()
            .read()
            .expect("poisoned parse node")
            .pos
            .0
            .clone()
    }
}
impl FrontendPhases for SilFrontendPhases {
    type Parsed = PProgramHandle;
    type Analyzed = PProgramHandle;
    fn parse(&mut self, input: &str) -> Result<Self::Parsed, Vec<AbstractError>> {
        let text = self
            .plugins
            .before_parse(input.to_owned(), false)
            .ok_or_else(|| self.plugins.errors().to_vec())?;
        let features = self.plugins.parser_features();
        let local_loader = self.local_loader.clone();
        let standard_loader = self.standard_loader.clone();
        let program = fast_parser::parse_program_with_imports(
            &text,
            &self.file,
            &features,
            &mut |path, standard| {
                if standard {
                    standard_loader
                        .as_ref()
                        .ok_or_else(|| {
                            "standard import resource loader is not configured".to_owned()
                        })?
                        .load_content(path)
                        .map_err(|e| e.to_string())
                } else {
                    local_loader.load_content(path).map_err(|e| e.to_string())
                }
            },
            &mut |text| {
                self.plugins.before_parse(text, true).ok_or_else(|| {
                    self.plugins
                        .errors()
                        .iter()
                        .map(|e| e.readable_message().unwrap_or_else(|_| e.full_id()))
                        .collect::<Vec<_>>()
                        .join(", ")
                })
            },
        )
        .map_err(|error| {
            vec![AbstractError::Parse(ParseReport::Error(ParseError::new(
                error.message,
                error.position,
            )))]
        })?;
        self.parsing_warnings.extend(
            program
                .errors()
                .into_iter()
                .filter(|e| matches!(e, ParseReport::Warning(_))),
        );
        init_properties(program.node()).map_err(|error| {
            Self::failure(
                format!("parse tree initialization: {error:?}"),
                Self::program_position(&program),
            )
        })?;
        Ok(program)
    }
    fn analyze(&mut self, input: Self::Parsed) -> Result<Self::Analyzed, Vec<AbstractError>> {
        let input = self
            .plugins
            .before_resolve(input)
            .ok_or_else(|| self.plugins.errors().to_vec())?;
        let mut analyser = resolver::NameAnalyser::default();
        let ok = analyser.run(input.node()).map_err(|e| {
            Self::failure(
                format!("name analysis: {e:?}"),
                Self::program_position(&input),
            )
        })?;
        let mut errors = Vec::new();
        for message in crate::parser::fast_message::sortmessages(analyser.messages) {
            let position = Position::LineColumn(LineColumn::Source(Box::new(message.pos)));
            let kind = if message.error {
                FrontendErrorKind::TypecheckerError(message.label)
            } else {
                FrontendErrorKind::TypecheckerWarning(message.label)
            };
            let diagnostic = FrontendError::new(kind, position);
            if message.error {
                errors.push(AbstractError::Frontend(diagnostic));
            } else {
                self.typechecking_warnings.push(diagnostic);
            }
        }
        if !ok {
            return Err(errors);
        }
        resolver::check_program_core(&input, &mut |node, text| {
            let position = node.read().expect("poisoned parse node").pos.0.clone();
            self.typechecking_warnings.push(FrontendError::new(
                FrontendErrorKind::TypecheckerWarning(text.into()),
                position,
            ));
        })
        .map_err(|e| {
            Self::failure(
                format!("type checking: {e:?}"),
                Self::program_position(&input),
            )
        })?;
        Ok(input)
    }
    fn translate(&mut self, input: Self::Analyzed) -> Result<Program, Vec<AbstractError>> {
        let input = self
            .plugins
            .before_translate(input)
            .ok_or_else(|| self.plugins.errors().to_vec())?;
        translator::translate_program_core(&input).map_err(|e| {
            Self::failure(
                format!("translation: {e:?}"),
                Self::program_position(&input),
            )
        })
    }
    fn check_consistency(&mut self, input: Program) -> Result<Program, Vec<AbstractError>> {
        Err(Self::failure(
            "transitive consistency checking is not yet implemented".into(),
            input.meta.position.clone(),
        ))
    }
    fn prepare_verification(&mut self, input: Program) -> Result<Program, Vec<AbstractError>> {
        let program = self
            .plugins
            .before_method_filter(input)
            .ok_or_else(|| self.plugins.errors().to_vec())?;
        self.plugins
            .before_verify(program)
            .map_err(|e| {
                Self::failure(
                    format!("plugin before verification: {}", e.0),
                    Position::NoPosition,
                )
            })?
            .ok_or_else(|| self.plugins.errors().to_vec())
    }
    fn map_verification(
        &mut self,
        program: &Program,
        input: crate::verifier::verification_result::VerificationResult,
    ) -> Result<crate::verifier::verification_result::VerificationResult, Vec<AbstractError>> {
        self.plugins
            .map_verification_result(program, input)
            .map_err(|e| {
                Self::failure(
                    format!("plugin result mapping: {}", e.0),
                    Position::NoPosition,
                )
            })
    }
    fn reset_messages(&mut self) {
        self.parsing_warnings.clear();
        self.typechecking_warnings.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn refute_plugin_parses_checks_translates_and_lowers() {
        use crate::ast::utility::nodes::Node;
        use crate::verifier::verification_error::ErrorNodeRenderer;
        use crate::verifier::verification_result::DiagnosticError;
        use std::sync::Arc;
        #[derive(Debug)]
        struct Renderer;
        impl ErrorNodeRenderer for Renderer {
            fn render_node(&self, _: &Node) -> Result<String, DiagnosticError> {
                Ok("false".into())
            }
        }
        let plugins = SilverPluginManager::new(vec![Box::new(
            crate::plugin::standard::refute::refute_plugin::RefutePlugin {
                renderer: Arc::new(Renderer),
            },
        )]);
        let mut phases = SilFrontendPhases::new(PathBuf::from("test.vpr"), plugins);
        let parsed = phases.parse("method m() { refute false; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        let result = phases
            .map_verification(
                &program,
                crate::verifier::verification_result::VerificationResult::Success,
            )
            .unwrap();
        assert!(matches!(
            result,
            crate::verifier::verification_result::VerificationResult::Failure(_)
        ));
    }
    #[test]
    fn smoke_plugin_recognizes_and_removes_unreachable_marker() {
        use crate::ast::utility::nodes::Node;
        use crate::verifier::verification_error::ErrorNodeRenderer;
        use crate::verifier::verification_result::DiagnosticError;
        use std::sync::Arc;
        #[derive(Debug)]
        struct Renderer;
        impl ErrorNodeRenderer for Renderer {
            fn render_node(&self, _: &Node) -> Result<String, DiagnosticError> {
                Ok("false".into())
            }
        }
        let plugins = SilverPluginManager::new(vec![
            Box::new(crate::plugin::standard::smoke::smoke_detection_plugin::SmokeDetectionPlugin),
            Box::new(
                crate::plugin::standard::refute::refute_plugin::RefutePlugin {
                    renderer: Arc::new(Renderer),
                },
            ),
        ]);
        let mut phases = SilFrontendPhases::new(PathBuf::from("test.vpr"), plugins);
        let parsed = phases
            .parse("method m() { unreachable; inhale true; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        let result = phases
            .map_verification(
                &program,
                crate::verifier::verification_result::VerificationResult::Success,
            )
            .unwrap();
        assert!(matches!(
            result,
            crate::verifier::verification_result::VerificationResult::Success
        ));
    }
    #[test]
    fn predicate_instance_plugin_lowers_before_verification() {
        let plugins = SilverPluginManager::new(vec![Box::new(crate::plugin::standard::predicateinstance::predicate_instance_plugin::PredicateInstancePlugin)]);
        let mut phases = SilFrontendPhases::new(PathBuf::from("test.vpr"), plugins);
        let parsed = phases
            .parse("domain PredicateInstance {} predicate p() function f(): Bool { #p() == #p() }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let lowered = phases.prepare_verification(program).unwrap();
        assert_eq!(lowered.functions.len(), 2);
        assert_eq!(lowered.functions[1].name, "PI_p");
    }
    #[test]
    fn imported_function_resolves_and_translates() {
        use std::path::Path;
        use std::sync::Arc;
        struct Loader;
        impl crate::ast::utility::file_loader::FileLoader for Loader {
            fn load_content(&self, path: &Path) -> std::io::Result<String> {
                assert!(path.ends_with("lib.vpr"));
                Ok("function f(): Int { 1 }".into())
            }
        }
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("/work/main.vpr"),
            SilverPluginManager::default(),
        );
        phases.local_loader = Arc::new(Loader);
        let parsed = phases
            .parse("import \"lib.vpr\" method m() { var x: Int := f(); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert_eq!(program.functions.len(), 1);
    }
    #[test]
    fn core_phases_do_not_skip_missing_consistency_checks() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("method m() { assert true; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert!(phases.check_consistency(program).is_err());
    }
}
