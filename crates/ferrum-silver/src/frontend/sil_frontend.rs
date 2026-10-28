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
//! Supported transitive consistency checks run before verification; unsupported checks or
//! rendering fail explicitly. CLI, full diagnostics and remaining consistency families are pending.

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

const ADT_PLUGIN: &str = "viper.silver.plugin.standard.adt.AdtPlugin";
const TERMINATION_PLUGIN: &str = "viper.silver.plugin.standard.termination.TerminationPlugin";
const PREDICATE_INSTANCE_PLUGIN: &str =
    "viper.silver.plugin.standard.predicateinstance.PredicateInstancePlugin";
const REFUTE_PLUGIN: &str = "viper.silver.plugin.standard.refute.RefutePlugin";
const SMOKE_PLUGIN: &str = "viper.silver.plugin.standard.smoke.SmokeDetectionPlugin";
const ARP_PLUGIN: &str = "viper.silver.plugin.standard.arp.ARPPlugin";

/// The exact source plugin sequence, including explicit duplicates. Callers can
/// use this list to issue the source duplicate-plugin configuration warning.
pub fn configured_plugin_names(
    config: &crate::frontend::sil_front_end_config::SilFrontendConfig,
) -> Vec<String> {
    let mut names = Vec::new();
    if config.enable_smoke_detection {
        names.extend([SMOKE_PLUGIN.to_owned(), REFUTE_PLUGIN.to_owned()]);
    }
    if !config.disable_default_plugins {
        for name in [
            ADT_PLUGIN,
            TERMINATION_PLUGIN,
            PREDICATE_INSTANCE_PLUGIN,
            REFUTE_PLUGIN,
        ] {
            if !names.iter().any(|existing| existing == name) {
                names.push(name.into());
            }
        }
    }
    if let Some(explicit) = &config.plugin {
        let mut parts: Vec<_> = explicit.split(':').collect();
        if !explicit.is_empty() {
            while parts.last() == Some(&"") {
                parts.pop();
            }
        }
        names.extend(parts.into_iter().map(str::to_owned));
    }
    names
}

#[derive(Debug)]
struct NativeErrorRenderer;
impl crate::verifier::verification_error::ErrorNodeRenderer for NativeErrorRenderer {
    fn render_node(
        &self,
        node: &crate::ast::utility::nodes::Node,
    ) -> Result<String, crate::verifier::verification_result::DiagnosticError> {
        crate::ast::pretty::pretty_printer::pretty_node(node).map_err(|_| {
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "error node pretty printing",
            )
        })
    }
}

/// Construct the configured built-in plugins in source order. Unknown plugins and
/// known plugins lacking a native transformation return explicit errors.
pub fn standard_plugin_manager(
    config: &crate::frontend::sil_front_end_config::SilFrontendConfig,
) -> Result<SilverPluginManager, crate::plugin::silver_plugin_manager::PluginResolutionError> {
    use crate::plugin::silver_plugin::SilverPlugin;
    use crate::plugin::silver_plugin_manager::PluginResolutionError;
    use crate::plugin::standard::{
        adt::adt_plugin::AdtPlugin,
        arp::arp_plugin::ArpPlugin,
        predicateinstance::predicate_instance_plugin::PredicateInstancePlugin,
        refute::refute_plugin::RefutePlugin,
        smoke::smoke_detection_plugin::SmokeDetectionPlugin,
        termination::termination_plugin::{NativeTerminationTransformer, TerminationPlugin},
    };
    let names = configured_plugin_names(config);
    let explicit: Vec<String> = config
        .plugin
        .as_ref()
        .map(|s| s.split(':').map(str::to_owned).collect())
        .unwrap_or_default();
    let mut plugins: Vec<Box<dyn SilverPlugin>> = Vec::new();
    for name in names {
        let plugin: Box<dyn SilverPlugin> = match name.as_str() {
            ADT_PLUGIN => {
                let mut plugin = AdtPlugin::default();
                plugin.has_config = true;
                plugin.disabled = config.disable_adt_plugin;
                plugin.disable_termination = config.disable_termination_plugin;
                plugin.disable_default_plugins = config.disable_default_plugins;
                plugin.explicit_plugins = explicit.clone();
                Box::new(plugin)
            }
            TERMINATION_PLUGIN => Box::new(TerminationPlugin::new(
                config.disable_termination_plugin,
                config.respect_function_pre_perm_amounts,
                Some(Box::new(NativeTerminationTransformer)),
            )),
            PREDICATE_INSTANCE_PLUGIN => Box::new(PredicateInstancePlugin),
            REFUTE_PLUGIN => Box::new(RefutePlugin {
                renderer: std::sync::Arc::new(NativeErrorRenderer),
            }),
            SMOKE_PLUGIN => Box::new(SmokeDetectionPlugin),
            ARP_PLUGIN => Box::new(ArpPlugin),
            "viper.silver.plugin.sif.SIFPlugin" => {
                return Err(PluginResolutionError::Construction(
                    "SIF transformation is not yet implemented".into(),
                ));
            }
            _ => return Err(PluginResolutionError::NotFound(name)),
        };
        plugins.push(plugin);
    }
    Ok(SilverPluginManager::new(plugins))
}

/// Silver's native phase bodies. Unsupported semantic and consistency families
/// produce errors until their complete checks are available.
pub struct SilFrontendPhases {
    pub file: PathBuf,
    pub plugins: SilverPluginManager,
    pub local_loader: std::sync::Arc<dyn crate::ast::utility::file_loader::FileLoader>,
    pub standard_loader: Option<std::sync::Arc<dyn crate::ast::utility::file_loader::FileLoader>>,
    pub backend_type_format: Option<String>,
    pub respect_function_pre_perm_amounts: bool,
    pub select: Option<String>,
    pub parsing_warnings: Vec<ParseReport>,
    pub typechecking_warnings: Vec<FrontendError>,
}
impl SilFrontendPhases {
    pub fn new(file: PathBuf, plugins: SilverPluginManager) -> Self {
        Self {
            file,
            plugins,
            local_loader: std::sync::Arc::new(crate::ast::utility::file_loader::DiskLoader),
            standard_loader: Some(std::sync::Arc::new(
                crate::resources::bundled::BundledImportLoader,
            )),
            backend_type_format: None,
            respect_function_pre_perm_amounts: false,
            select: None,
            parsing_warnings: vec![],
            typechecking_warnings: vec![],
        }
    }
    pub fn configure_consistency(
        &mut self,
        config: &crate::frontend::sil_front_end_config::SilFrontendConfig,
    ) {
        self.respect_function_pre_perm_amounts = config.respect_function_pre_perm_amounts;
        self.select = config.select.clone();
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
        use crate::ast::pretty::pretty_printer::{PrintError, pretty_expression, show_type};
        use crate::ast::utility::nodes::Node;
        let render = |node: &Node| -> Result<String, PrintError> {
            match node {
                Node::Exp(exp) => pretty_expression(exp),
                Node::Type(typ) => show_type(typ),
                Node::LocalVar(var) => pretty_expression(&crate::ast::expression::Exp::new(
                    crate::ast::expression::ExpKind::LocalVar(var.clone()),
                    var.meta.clone(),
                )),
                Node::LocalDecl(decl) => Ok(format!("{}: {}", decl.name, show_type(&decl.typ)?)),
                Node::UnnamedLocalDecl(decl) => show_type(&decl.typ),
                _ => Err(PrintError::Unsupported("consistency node rendering")),
            }
        };
        let render_seq = |_: &[Node]| -> Result<String, PrintError> {
            Err(PrintError::Unsupported("consistency sequence rendering"))
        };
        let mut errors = crate::ast::utility::consistency::check_transitively_with_options(
            &input,
            &render,
            &render_seq,
            crate::ast::utility::consistency::ConsistencyOptions {
                respect_function_pre_perm_amounts: self.respect_function_pre_perm_amounts,
            },
        )
        .map_err(|e| {
            vec![AbstractError::Frontend(FrontendError::new(
                FrontendErrorKind::ConsistencyError(format!(
                    "consistency checking unavailable: {e:?}"
                )),
                input.meta.position.clone(),
            ))]
        })?;
        if let Some(backend) = &self.backend_type_format {
            errors.extend(crate::ast::utility::consistency::check_backend_types(
                &input, backend,
            ));
        }
        if errors.is_empty() {
            Ok(input)
        } else {
            Err(errors.into_iter().map(AbstractError::Frontend).collect())
        }
    }
    fn prepare_verification(&mut self, input: Program) -> Result<Program, Vec<AbstractError>> {
        let program = self
            .plugins
            .before_method_filter(input)
            .ok_or_else(|| self.plugins.errors().to_vec())?;
        if self.select.is_some() {
            return Err(Self::failure(
                "member selection requires the Silver dependency chopper".into(),
                program.meta.position.clone(),
            ));
        }
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
    fn set_input_file(&mut self, path: &std::path::Path) {
        self.file = path.to_owned();
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
    fn configured_selection_cannot_silently_verify_all_members() {
        let mut config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        config.select = Some("m".into());
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        phases.configure_consistency(&config);
        let parsed = phases.parse("method m() {} method other() {}").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        assert!(phases.prepare_verification(program).is_err());
    }
    #[test]
    fn generic_domain_signature_preserves_bound_type_variable() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("domain D[T] { function f(x: T): T }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert_eq!(program.domains[0].type_vars[0].name, "T");
        assert!(
            matches!(&program.domains[0].functions[0].typ, crate::ast::r#type::Type::Var(v) if v.name == "T")
        );
    }
    #[test]
    fn generic_domain_call_infers_type_arguments() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse(
                "domain D[T] { function f(x: T): T } method m() { assert f(1) == 1 && f(true); }",
            )
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        fn inspect(
            node: &crate::ast::utility::nodes::Node,
            found: &mut Vec<crate::ast::r#type::Type>,
        ) {
            if let crate::ast::utility::nodes::Node::Exp(exp) = node {
                if let crate::ast::expression::ExpKind::DomainFuncApp(_, _, subst) = exp.kind() {
                    found.push(subst[&crate::ast::r#type::TypeVar::new("T")].clone());
                }
            }
            for child in crate::ast::utility::nodes::subnodes(node).unwrap() {
                inspect(&child, found);
            }
        }
        let mut types = Vec::new();
        inspect(
            &crate::ast::utility::nodes::Node::Program(program.clone()),
            &mut types,
        );
        assert_eq!(
            types,
            vec![
                crate::ast::r#type::Type::Int,
                crate::ast::r#type::Type::Bool
            ]
        );
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn bundled_integer_order_import_runs_semantic_analysis() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("import <decreases/int.vpr> method m() {}")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn plugin_scala_product_hashes_match_scala_2_13() {
        use crate::ast::ast::Metadata;
        use crate::ast::expression::ExtensionExp;
        let rd = crate::plugin::standard::arp::arpast_extension::RdPerm {
            meta: Metadata::default(),
        };
        let instance = crate::plugin::standard::predicateinstance::predicate_instance_ast_extension::PredicateInstance { predicate: "p".into(), args: vec![], meta: Metadata::default() };
        assert_eq!(rd.scala_hash().unwrap(), -1852540830);
        assert_eq!(instance.scala_hash().unwrap(), -1322434817);
    }
    #[test]
    fn native_default_plugins_prepare_method_and_load_bundled_import() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        assert_eq!(
            configured_plugin_names(&config),
            [
                ADT_PLUGIN,
                TERMINATION_PLUGIN,
                PREDICATE_INSTANCE_PLUGIN,
                REFUTE_PLUGIN
            ]
        );
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("method invalid() { assert false; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
        phases
            .parse("import <decreases/int.vpr> method m() {}")
            .unwrap();
    }
    #[test]
    fn native_smoke_plugins_prepare_marker() {
        let mut config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        config.enable_smoke_detection = true;
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("method m() { unreachable; inhale true; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn native_default_plugins_prepare_heap_and_predicate() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("field f: Int predicate p(x: Ref) { acc(x.f) } method m(x: Ref) requires acc(p(x)) { unfold acc(p(x)); x.f := 1; fold acc(p(x)); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn native_termination_parses_and_extracts_wildcard() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("method m(x: Int) decreases _ if x > 0 { assert true; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn native_termination_keeps_tuple_and_star_when_checks_disabled() {
        let mut config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        config.disable_termination_plugin = true;
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("method m(x: Int) decreases x, x + 1 if x > 0 { while (false) decreases * {} }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn native_termination_missing_order_fails_closed() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("method m(x: Int) decreases x { m(x - 1); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        assert!(phases.prepare_verification(program).is_err());
    }
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
        let program = phases.check_consistency(program).unwrap();
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
        let program = phases.check_consistency(program).unwrap();
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
    fn allocation_rejects_unknown_fields_and_non_reference_targets() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        for source in [
            "method m() { var x: Ref := new(missing); }",
            "method m() { var x: Int := new(); }",
        ] {
            let parsed = phases.parse(source).unwrap();
            assert!(phases.analyze(parsed).is_err());
        }
    }

    #[test]
    fn allocation_and_field_call_targets_translate_in_order() {
        let source = "field a: Int field next: Ref method mk() returns (r: Ref) method m(x: Ref) requires acc(x.next) { var y: Ref := new(*); x.next := mk(); x.next := new(a); }";
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse(source).unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let crate::ast::statement::StmtKind::Seqn { statements, .. } =
            program.methods[1].body.as_ref().unwrap().kind()
        else {
            panic!()
        };
        assert!(
            matches!(statements[0].kind(), crate::ast::statement::StmtKind::NewStmt { fields, .. } if fields.iter().map(|f| f.name.as_str()).collect::<Vec<_>>() == vec!["a", "next"])
        );
        for statement in &statements[1..] {
            let crate::ast::statement::StmtKind::Seqn {
                statements,
                declarations,
            } = statement.kind()
            else {
                panic!("field target temporary block")
            };
            assert_eq!(declarations.len(), 2);
            assert!(matches!(
                statements[0].kind(),
                crate::ast::statement::StmtKind::LocalVarAssign { .. }
            ));
            assert!(matches!(
                statements[2].kind(),
                crate::ast::statement::StmtKind::FieldAssign { .. }
            ));
        }
        phases.check_consistency(program).unwrap();
    }

    #[test]
    fn permission_contexts_and_wand_statements_follow_source_restrictions() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let source = "field f: Int method m(x: Ref) { assert perm(x.f) >= none; package true --* true; apply true --* true; }";
        let parsed = phases.parse(source).unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let crate::ast::statement::StmtKind::Seqn { statements, .. } =
            program.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!()
        };
        assert!(matches!(
            statements[1].kind(),
            crate::ast::statement::StmtKind::Package { .. }
        ));
        assert!(matches!(
            statements[2].kind(),
            crate::ast::statement::StmtKind::Apply(_)
        ));
        phases.check_consistency(program).unwrap();
        let parsed = phases
            .parse("field f: Int method m(x: Ref) requires perm(x.f) >= none")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
        let parsed = phases
            .parse("field f: Int method m(x: Ref) requires [perm(x.f) >= none, true]")
            .unwrap();
        assert!(phases.analyze(parsed).is_ok());
        let parsed = phases
            .parse("function f(): Bool requires true --* true { true }")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
        let parsed = phases.parse("predicate p() { true --* true }").unwrap();
        assert!(phases.analyze(parsed).is_err());
    }

    #[test]
    fn function_result_is_typed_in_postconditions_and_rejected_in_methods() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("function id(x: Int): Int ensures result == x { x }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert!(
            matches!(program.functions[0].posts[0].kind(), crate::ast::expression::ExpKind::EqCmp(left, _) if matches!(left.kind(), crate::ast::expression::ExpKind::Result(crate::ast::r#type::Type::Int)))
        );
        phases.check_consistency(program).unwrap();
        let parsed = phases.parse("method m() { assert result == 1; }").unwrap();
        assert!(phases.analyze(parsed).is_err());
    }

    #[test]
    fn asserting_and_applying_expressions_translate() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("function f(): Int { asserting (true) in 1 }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert!(matches!(
            program.functions[0].body.as_ref().unwrap().kind(),
            crate::ast::expression::ExpKind::Asserting(..)
        ));

        let parsed = phases
            .parse("function g(): Bool { applying (true --* true) in true }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert!(matches!(
            program.functions[0].body.as_ref().unwrap().kind(),
            crate::ast::expression::ExpKind::Applying(..)
        ));
    }

    #[test]
    fn unfolding_predicate_expression_reaches_consistency() {
        let source = "field f: Int predicate p(x: Ref) { acc(x.f) } function value(x: Ref): Int requires acc(p(x)) { unfolding acc(p(x)) in x.f }";
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse(source).unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert!(matches!(
            program.functions[0].body.as_ref().unwrap().kind(),
            crate::ast::expression::ExpKind::Unfolding(_, _)
        ));
        phases.check_consistency(program).unwrap();
    }

    #[test]
    fn fold_and_unfold_reject_abstract_predicates() {
        for statement in ["fold acc(p(x));", "unfold acc(p(x));"] {
            let source = format!("predicate p(x: Ref) method m(x: Ref) {{ {statement} }}");
            let mut phases =
                SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
            let parsed = phases.parse(&source).unwrap();
            assert!(phases.analyze(parsed).is_err());
        }
    }

    #[test]
    fn ordinary_method_heap_and_predicate_pipeline() {
        let cases = [
            "method invalid() { assert false; }",
            "field f: Int method heap(x: Ref) requires acc(x.f) { x.f := 1; assert x.f == 1; }",
            "field f: Int predicate p(x: Ref) { acc(x.f) } method pred(x: Ref) requires acc(p(x)) { unfold acc(p(x)); fold acc(p(x)); }",
        ];
        for source in cases {
            let mut phases =
                SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
            let parsed = phases
                .parse(source)
                .unwrap_or_else(|e| panic!("parse {source}: {e:?}"));
            let analyzed = phases
                .analyze(parsed)
                .unwrap_or_else(|e| panic!("analyze {source}: {e:?}"));
            let program = phases
                .translate(analyzed)
                .unwrap_or_else(|e| panic!("translate {source}: {e:?}"));
            phases
                .check_consistency(program)
                .unwrap_or_else(|e| panic!("consistency {source}: {e:?}"));
        }
    }

    #[test]
    fn translates_source_quantifiers() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("method m() { assert forall x: Int :: x == x; assert exists y: Int :: y == y; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let body = program.methods[0].body.as_ref().unwrap();
        let crate::ast::statement::StmtKind::Seqn { statements, .. } = body.kind() else {
            panic!("block")
        };
        assert!(
            matches!(statements[0].kind(), crate::ast::statement::StmtKind::Assert(exp) if matches!(exp.kind(), crate::ast::expression::ExpKind::Forall(_, _, _)))
        );
        assert!(
            matches!(statements[1].kind(), crate::ast::statement::StmtKind::Assert(exp) if matches!(exp.kind(), crate::ast::expression::ExpKind::Exists(_, _, _)))
        );
    }

    #[test]
    fn sif_low_passes_extension_consistency() {
        use crate::parser::{
            fast_parser::{ParserFeature, parse_program_with_features},
            resolver::{NameAnalyser, check_program_core},
            translator::translate_program_core,
        };
        let parsed = parse_program_with_features(
            "method m() { assert low(true); }",
            "test.vpr",
            &[ParserFeature::Sif],
        )
        .unwrap();
        crate::parser::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn arp_program_passes_extension_consistency_before_lowering() {
        let plugins = SilverPluginManager::new(vec![Box::new(
            crate::plugin::standard::arp::arp_plugin::ArpPlugin,
        )]);
        let mut phases = SilFrontendPhases::new(PathBuf::from("test.vpr"), plugins);
        let parsed = phases
            .parse("field f: Int method m(x: Ref) requires acc(x.f, rd)")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let checked = phases.check_consistency(program).unwrap();
        let lowered = phases.prepare_verification(checked).unwrap();
        assert_eq!(lowered.methods[0].formal_args.len(), 2);
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
        let checked = phases.check_consistency(program).unwrap();
        let lowered = phases.prepare_verification(checked).unwrap();
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
    fn consistency_reaches_backend_only_for_checked_programs() {
        use crate::components::components::LifetimeComponent;
        use crate::frontend::frontend::{DEFAULT_PHASES, DefaultFrontend, Phase};
        use crate::reporter::reporter::{NoopReporter, Reporter};
        use crate::verifier::verification_result::VerificationResult;
        use crate::verifier::verifier::{Dependency, Verifier, VerifierError};
        use std::sync::{
            Arc,
            atomic::{AtomicUsize, Ordering},
        };
        struct Counter {
            count: Arc<AtomicUsize>,
            reporter: NoopReporter,
        }
        impl LifetimeComponent for Counter {
            fn start(&mut self) {}
            fn stop(&mut self) {}
        }
        impl Verifier for Counter {
            fn name(&self) -> &str {
                "counter"
            }
            fn version(&self) -> &str {
                "0"
            }
            fn build_version(&self) -> &str {
                ""
            }
            fn copyright(&self) -> &str {
                ""
            }
            fn debug_info(&mut self, _: Vec<(String, Box<dyn std::any::Any + Send + Sync>)>) {}
            fn dependencies(&self) -> Vec<&dyn Dependency> {
                vec![]
            }
            fn parse_command_line(&mut self, _: &[String]) {}
            fn verify(&mut self, _: &Program) -> Result<VerificationResult, VerifierError> {
                self.count.fetch_add(1, Ordering::SeqCst);
                Ok(VerificationResult::Success)
            }
            fn reporter(&self) -> &dyn Reporter {
                &self.reporter
            }
        }
        struct UnavailableSif;
        impl crate::plugin::sif::sif_plugin::SifTransformer for UnavailableSif {
            fn transform(
                &mut self,
                input: Program,
                _: bool,
            ) -> Result<Program, crate::plugin::silver_plugin::PluginHookError> {
                Ok(input)
            }
        }
        let count = Arc::new(AtomicUsize::new(0));
        let mut frontend = DefaultFrontend::new(SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            SilverPluginManager::new(vec![Box::new(crate::plugin::sif::sif_plugin::SifPlugin {
                transformer: UnavailableSif,
            })]),
        ));
        frontend.init(Box::new(Counter {
            count: count.clone(),
            reporter: NoopReporter,
        }));
        frontend
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m() { assert true; }".into())
            })
            .unwrap();
        frontend
            .run_range(DEFAULT_PHASES, Phase::Parsing, Phase::Verification)
            .unwrap();
        assert!(matches!(
            frontend.result().unwrap(),
            VerificationResult::Success
        ));
        assert_eq!(count.load(Ordering::SeqCst), 1);
        frontend
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m() { assert true; }".into())
            })
            .unwrap();
        frontend
            .run_range(DEFAULT_PHASES, Phase::Parsing, Phase::Translation)
            .unwrap();
        assert!(frontend.errors.is_empty());
        let meta = crate::ast::ast::Metadata::default();
        let low = crate::plugin::sif::sif_ast_extensions::SifExpression {
            kind: crate::plugin::sif::sif_ast_extensions::SifExpressionKind::Low {
                exp: crate::ast::expression::Exp::new(
                    crate::ast::expression::ExpKind::TrueLit,
                    meta.clone(),
                ),
                comparator: None,
                type_variables: Default::default(),
            },
            meta: meta.clone(),
        }
        .expression()
        .unwrap();
        let var = crate::ast::program::LocalVarDecl::new(
            "x".into(),
            crate::ast::r#type::Type::Int,
            meta.clone(),
        );
        let quantifier = crate::ast::expression::Exp::new(
            crate::ast::expression::ExpKind::Forall(vec![var], vec![], low),
            meta.clone(),
        );
        let statement = crate::ast::statement::Stmt::new(
            crate::ast::statement::StmtKind::Assert(quantifier),
            meta,
        );
        let program = frontend.program.as_ref().unwrap().copy_with(|p| {
            p.methods[0] = p.methods[0].copy_with(|method| method.body = Some(statement));
        });
        frontend.program = Some(program);
        frontend
            .run_range(DEFAULT_PHASES, Phase::ConsistencyCheck, Phase::Verification)
            .unwrap();
        assert!(matches!(
            frontend.result().unwrap(),
            VerificationResult::Failure(_)
        ));
        assert_eq!(count.load(Ordering::SeqCst), 1);
        assert_eq!(
            frontend.state,
            crate::frontend::frontend::DefaultState::ConsistencyCheck
        );
        assert!(frontend.program.is_some());
    }
}
