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
        crate::parser::macro_expander::expand_global_expression_macros(&program).map_err(
            |error| {
                vec![AbstractError::Parse(ParseReport::Error(ParseError::new(
                    error.message,
                    error.pos.0,
                )))]
            },
        )?;
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
        init_properties(input.node()).map_err(|e| {
            Self::failure(
                format!("resolved parse tree initialization: {e:?}"),
                Self::program_position(&input),
            )
        })?;
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
        let mut input = self
            .plugins
            .before_translate(input)
            .ok_or_else(|| self.plugins.errors().to_vec())?;
        let imports = self
            .plugins
            .additional_standard_imports(&input)
            .map_err(|e| {
                Self::failure(
                    format!("plugin standard imports: {}", e.0),
                    Self::program_position(&input),
                )
            })?;
        if !imports.is_empty() {
            let text = imports
                .iter()
                .map(|name| format!("import <{name}>"))
                .collect::<Vec<_>>()
                .join("\n");
            let standard_loader = self.standard_loader.clone();
            let local_loader = self.local_loader.clone();
            let imported = fast_parser::parse_program_with_imports(
                &text,
                &self.file,
                &self.plugins.parser_features(),
                &mut |path, standard| {
                    let loader = if standard {
                        standard_loader.as_ref().ok_or_else(|| {
                            "standard import resource loader is not configured".to_owned()
                        })?
                    } else {
                        &local_loader
                    };
                    loader.load_content(path).map_err(|e| e.to_string())
                },
                &mut |text| Ok(text),
            )
            .map_err(|e| {
                vec![AbstractError::Parse(ParseReport::Error(ParseError::new(
                    e.message, e.position,
                )))]
            })?;
            init_properties(imported.node()).map_err(|e| {
                Self::failure(
                    format!("import tree initialization: {e:?}"),
                    Self::program_position(&imported),
                )
            })?;
            let mut names = resolver::NameAnalyser::default();
            let ok = names.run(imported.node()).map_err(|e| {
                Self::failure(
                    format!("import name analysis: {e:?}"),
                    Self::program_position(&imported),
                )
            })?;
            if !ok {
                return Err(Self::failure(
                    format!("import name analysis: {:?}", names.messages),
                    Self::program_position(&imported),
                ));
            }
            resolver::check_program_core(&imported, &mut |_, _| {}).map_err(|e| {
                Self::failure(
                    format!("import type checking: {e:?}"),
                    Self::program_position(&imported),
                )
            })?;
            let imported = imported.filter_members(&|m| {
                matches!(
                    m.category(),
                    crate::parser::parse_ast::PMemberCategory::Domain
                )
            });
            input = input.filter_members(&|m| {
                let node = m.node().read().expect("poisoned parse node");
                if let crate::parser::parse_ast::PNodeKind::Member(crate::parser::parse_ast::PMember { kind: crate::parser::parse_ast::PMemberKind::Domain { idndef, .. }, .. }) = &node.kind {
                    return !matches!(&idndef.read().expect("poisoned parse node").kind, crate::parser::parse_ast::PNodeKind::IdnDef(id) if id.name == "WellFoundedOrder");
                }
                true
            }).new_imported(vec![imported]);
            init_properties(input.node()).map_err(|e| {
                Self::failure(
                    format!("merged import tree initialization: {e:?}"),
                    Self::program_position(&input),
                )
            })?;
        }
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
        let mut program = self
            .plugins
            .before_method_filter(input)
            .ok_or_else(|| self.plugins.errors().to_vec())?;
        if let Some(selection) = &self.select {
            let mut names: Vec<_> = selection.split(',').collect();
            if !selection.is_empty() {
                while names.last() == Some(&"") {
                    names.pop();
                }
            }
            let names = names.into_iter().map(str::to_owned).collect();
            program = match crate::ast::utility::chopper::chopper::chop_selected(&program, &names)
                .map_err(|error| {
                Self::failure(
                    format!("member selection: {error:?}"),
                    program.meta.position.clone(),
                )
            })? {
                Some(program) => program,
                None => {
                    self.typechecking_warnings.push(FrontendError::new(
                        FrontendErrorKind::TypecheckerWarning("No members were selected.".into()),
                        program.meta.position.clone(),
                    ));
                    Program::new(
                        vec![],
                        vec![],
                        vec![],
                        vec![],
                        vec![],
                        vec![],
                        program.meta.clone(),
                    )
                }
            };
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
    fn macros_expand_permissions_and_collection_expressions() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("field f: Int define owns(v) acc(v.f) define pair(x) Seq(x, x) method m(r: Ref) requires owns(r) { var s: Seq[Int] := pair(2); assert |s| == 2; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn quantified_macro_renames_capturing_binders_and_keeps_shadowing() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("define greater(p) forall x: Int :: p > x define same(x) forall x: Int :: x == x method m(x: Int) { assert greater(x); assert same(1); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let rendered = crate::ast::pretty::pretty_printer::pretty(
            75,
            &crate::ast::pretty::pretty_printer::show_program(&program).unwrap(),
        );
        assert!(rendered.contains("x$0"), "{rendered}");
        phases.check_consistency(program).unwrap();
        let parsed = phases
            .parse(
                "domain D {} define valid(T) forall v: T :: v == v method m() { assert valid(D); }",
            )
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn typed_collection_and_ascribed_calls_copy_through_macros() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("domain D[T] { function empty(): D[T] } define v (empty(): D[Int]) define m Map[Int, Bool]() define s Seq[Int]() method f() { var x: D[Int] := v; var a: Map[Int, Bool] := m; var b: Seq[Int] := s; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn interpreted_domains_and_functions_reach_typed_ast() {
        use crate::ast::r#type::Type;
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse(r#"domain BV interpretation (SMTLIB: "(_ BitVec 32)", Boogie: "bv32") { function toBV(x: Int): BV interpretation "(_ int2bv 32)" } method m() { var x: BV := toBV(1); assert x == toBV(1); }"#).unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert_eq!(
            program.domains[0].interpretations.as_ref().unwrap()["SMTLIB"],
            "(_ BitVec 32)"
        );
        assert_eq!(
            program.domains[0].functions[0].interpretation.as_deref(),
            Some("(_ int2bv 32)")
        );
        assert!(matches!(
            program.domains[0].functions[0].typ,
            Type::Backend(_)
        ));
        fn has_backend_call(node: crate::ast::utility::nodes::Node) -> bool {
            use crate::ast::utility::nodes::{Node, subnodes};
            if let Node::Exp(exp) = &node {
                if matches!(exp.kind(), crate::ast::expression::ExpKind::BackendFuncApp(name, _) if name == "toBV")
                {
                    assert_eq!(exp.0.extra.interpretation.as_deref(), Some("(_ int2bv 32)"));
                    return true;
                }
            }
            subnodes(&node).unwrap().into_iter().any(has_backend_call)
        }
        assert!(has_backend_call(crate::ast::utility::nodes::Node::Program(
            program.clone()
        )));
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn macro_identifier_aliases_expand_in_call_positions() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("function g(x: Int): Int { x + 1 } method m() { define f g assert f(1) == 2; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        assert!(
            phases
                .parse(
                    "function g(x: Int): Int { x + 1 } method m() { define g 1 assert g(1) == 2; }"
                )
                .is_err()
        );
    }
    #[test]
    fn macro_renamer_matches_source_across_nested_body_scopes() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("define bad { if (true) { var x: Int := 0; } assert x == 1; } method m() { var x: Int := 1; bad; }").unwrap();
        assert!(phases.analyze(parsed).is_err());
    }
    #[test]
    fn macro_generated_names_do_not_leak_between_sibling_blocks() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("define add { var x: Int := 1; assert x == 1; } method m() { if (true) { add; } if (true) { add; } }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let rendered = crate::ast::pretty::pretty_printer::pretty(
            75,
            &crate::ast::pretty::pretty_printer::show_program(&program).unwrap(),
        );
        assert!(!rendered.contains("x$0"), "{rendered}");
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn let_macro_preserves_caller_names() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("define d(a) let x == (a) in x + a method m(x: Int) { assert d(x) == x + x; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let rendered = crate::ast::pretty::pretty_printer::pretty(
            75,
            &crate::ast::pretty::pretty_printer::show_program(&program).unwrap(),
        );
        assert!(rendered.contains("x$0"), "{rendered}");
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn statement_macros_expand_and_splice_without_a_scope() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("define check(x) { assert x > 0; assert x != 2; } method m() { check(1); define local(y) { check(y); } local(3); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases.parse("define update(x) { if (x > 0) { x := x + 1; } else { x := 0; } } method m() { var n: Int := 1; update(n); assert n == 2; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases.parse("define bump(v) { var x: Int := v; x := x + 1; assert x > v; } method m() { var x: Int := 2; bump(x); assert x == 2; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let rendered = crate::ast::pretty::pretty_printer::pretty(
            75,
            &crate::ast::pretty::pretty_printer::show_program(&program).unwrap(),
        );
        assert!(rendered.contains("x$0"), "{rendered}");
        phases.check_consistency(program).unwrap();
        let parsed = phases.parse("define count(x) { while (x > 0) invariant x >= 0 { x := x - 1; } } method m() { var n: Int := 1; count(n); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases.parse("define loopBody { label L invariant true goto L } method m() { loopBody; loopBody; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let rendered = crate::ast::pretty::pretty_printer::pretty(
            75,
            &crate::ast::pretty::pretty_printer::show_program(&program).unwrap(),
        );
        assert!(rendered.contains("L$0"), "{rendered}");
        phases.check_consistency(program).unwrap();
        assert!(
            phases
                .parse("define a() { a(); } method m() { a(); }")
                .is_err()
        );
    }
    #[test]
    fn local_expression_macros_are_method_scoped_and_override_globals() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("define value 1 method m() { assert value == 2; if (true) { define value 2 } } method n() { assert value == 1; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        assert!(
            phases
                .parse("method m() { define a(x) a(x) assert a(1) == 1; }")
                .is_err()
        );
        assert!(
            phases
                .parse("domain D {} method m() { define D 1 var x: D; }")
                .is_err()
        );
    }
    #[test]
    fn macro_unused_parameter_warning_is_preserved() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        phases
            .parse("define first(x, y) x method m() { assert first(1, 2) == 1; }")
            .unwrap();
        assert!(phases.parsing_warnings.iter().any(|report| {
            report
                .readable_message()
                .contains("parameters were defined but not used: y")
        }));
    }
    #[test]
    fn bundled_adt_derives_import_reaches_encoding() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("import <adt/derives.vpr> adt Box[T] { Boxed(value: T) } derives { contains } method m() { assert contains(1, Boxed(1)); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
        let parsed = phases
            .parse(
                "import <adt/derives.vpr> adt A { C(x: Int) } derives { contains without missing }",
            )
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
    }
    #[test]
    fn macro_annotations_survive_graph_copying() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("define check(v) { @s(\"stmt\") assert @e(\"expr\") v; } method m() { check(true); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let body = program.methods[0].body.as_ref().unwrap();
        let crate::ast::statement::StmtKind::Seqn { statements, .. } = body.kind() else {
            panic!("expected block")
        };
        let crate::ast::statement::StmtKind::Assert(exp) = statements[0].kind() else {
            panic!("expected assert")
        };
        assert!(
            statements[0]
                .metadata()
                .info
                .find(&|i| matches!(i, crate::ast::ast::Info::Annotation(_)))
                .is_some()
        );
        assert!(
            exp.metadata()
                .info
                .find(&|i| matches!(i, crate::ast::ast::Info::Annotation(_)))
                .is_some()
        );
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn expression_and_statement_annotations_retain_metadata() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("method m() { @s(\"stmt\") assert @e(\"outer\") @e(\"inner\") (true); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let body = program.methods[0].body.as_ref().unwrap();
        let crate::ast::statement::StmtKind::Seqn { statements, .. } = body.kind() else {
            panic!("expected block")
        };
        let stmt = &statements[0];
        let crate::ast::statement::StmtKind::Assert(exp) = stmt.kind() else {
            panic!("expected assertion")
        };
        let crate::ast::ast::Info::Annotation(stmt_info) = stmt
            .metadata()
            .info
            .find(&|info| matches!(info, crate::ast::ast::Info::Annotation(_)))
            .unwrap()
        else {
            unreachable!()
        };
        assert_eq!(stmt_info["s"], ["stmt"]);
        let crate::ast::ast::Info::Annotation(exp_info) = exp
            .metadata()
            .info
            .find(&|info| matches!(info, crate::ast::ast::Info::Annotation(_)))
            .unwrap()
        else {
            unreachable!()
        };
        assert_eq!(exp_info["e"], ["outer", "inner"]);
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn member_annotations_are_preserved_in_source_order() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse(
                "@note(\"a\", \"b\") @note(\"c\") method m() {} @tag() adt A { @ctor(\"x\") C() }",
            )
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let info = program.methods[0]
            .meta
            .info
            .find(&|info| matches!(info, crate::ast::ast::Info::Annotation(_)))
            .unwrap();
        let crate::ast::ast::Info::Annotation(values) = info else {
            unreachable!()
        };
        assert_eq!(values["note"], ["a", "b", "c"]);
        let adt = program.extensions[0]
            .0
            .as_any()
            .downcast_ref::<crate::plugin::standard::adt::adt_ast_extension::Adt>()
            .unwrap();
        assert!(
            adt.constructors[0]
                .meta
                .info
                .find(&|info| matches!(info, crate::ast::ast::Info::Annotation(_)))
                .is_some()
        );
    }
    #[test]
    fn expression_macros_expand_each_argument_occurrence_and_detect_recursion() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("define twice(x) x + x method m(y: Int) { assert twice(y + 1) == 2 * (y + 1); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        assert!(
            phases
                .parse("define a(x) b(x) define b(x) a(x) method m() { assert a(1) == 1; }")
                .is_err()
        );
        assert!(
            phases
                .parse("define a(x) x method m() { assert a(1, 2) == 1; }")
                .is_err()
        );
        assert!(
            phases
                .parse("define a(x) x method m(a: Int) { assert a > 0; }")
                .is_err()
        );
        let parsed = phases.parse("field g: Int define get(f) x.f method m(x: Ref) requires acc(x.g) { assert get(g) == x.g; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases.parse("define invoke(f, x) f(x) function inc(x: Int): Int { x + 1 } method m() { assert invoke(inc, 1) == inc(1); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        assert!(
            phases
                .parse("define get(f) x.f method m(x: Ref) { assert get(1) == 0; }")
                .is_err()
        );
    }
    #[test]
    fn forperm_resource_and_binder_reach_verification_preparation() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("field f: Int method m() { assert forperm r: Ref [r.f] :: true; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn forperm_predicate_and_nested_permission_rules() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse(
                "predicate p(r: Ref) { true } method m() { assert forperm r: Ref [p(r)] :: true; }",
            )
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases
            .parse("field f: Int method m() { assert forperm r: Ref [r.f] :: perm(r.f) > none; }")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
    }
    #[test]
    fn collection_literals_infer_element_types_and_reject_mixed_values() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("method m() { var s: Seq[Int] := Seq(1, 2); var e: Seq[Int] := Seq(); var t: Set[Bool] := Set(true, false); var u: Multiset[Int] := Multiset[Int](); var mp: Map[Int, Bool] := Map(1 := true, 2 := false); var em: Map[Int, Bool] := Map[Int, Bool](); var keys: Set[Int] := domain(mp); var values: Set[Bool] := range(mp); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases
            .parse("method m() { var s: Seq[Int] := Seq(1, true); }")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
    }
    #[test]
    fn native_termination_imports_sequence_order() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("method m(x: Seq[Int]) decreases x {}")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert!(
            program
                .domains
                .iter()
                .any(|d| d.name == "SeqWellFoundedOrder")
        );
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn native_termination_imports_remaining_builtin_orders() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        for (typ, domain) in [
            ("Ref", "RefWellFoundedOrder"),
            ("Perm", "PermWellFoundedOrder"),
            ("Set[Int]", "SetWellFoundedOrder"),
            ("Multiset[Int]", "MultiSetWellFoundedOrder"),
        ] {
            let mut phases = SilFrontendPhases::new(
                PathBuf::from("test.vpr"),
                standard_plugin_manager(&config).unwrap(),
            );
            let parsed = phases
                .parse(&format!("method m(x: {typ}) decreases x {{}}"))
                .unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            assert!(program.domains.iter().any(|d| d.name == domain));
            let program = phases.check_consistency(program).unwrap();
            phases.prepare_verification(program).unwrap();
        }
    }
    #[test]
    fn native_adt_destructor_and_discriminator_reach_encoding() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("adt Box[T] { Boxed(value: T) } method m() { var a: Box[Int] := Boxed(1); assert a.value == 1; assert a.isBoxed; var b: Box[Bool] := Boxed(true); assert b.value; assert b.isBoxed; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        assert!(program.domains.iter().any(|d| d.name == "Box"));
    }
    #[test]
    fn adt_destructor_assignment_is_rejected_as_field_access() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("adt Box[T] { Boxed(value: T) } method m(a: Box[Int]) { a.value := 1; }")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
    }
    #[test]
    fn generic_domain_call_type_ascription_resolves_in_parentheses() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("domain D[T] { function empty(): D[T] } method m() { var x: D[Int] := (empty(): D[Int]); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn impure_let_in_method_precondition_reaches_backend() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("field f: Int method m(x: Ref) requires let y == (x) in acc(y.f) {}")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn let_binder_only_scopes_over_body() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("method m(x: Int) { assert (let y == (x) in let z == (y) in z) == x; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases
            .parse("method m() { assert (let y == (y) in y) == 1; }")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
    }
    #[test]
    fn native_generic_adt_constructor_calls_reach_encoding() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("adt Box[T] { Boxed(value: T) } method m() { var a: Box[Int] := Boxed(1); var b: Box[Bool] := Boxed(true); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        fn collect(
            node: &crate::ast::utility::nodes::Node,
            types: &mut Vec<crate::ast::r#type::Type>,
        ) {
            if let crate::ast::utility::nodes::Node::Exp(exp) = node {
                if let crate::ast::expression::ExpKind::Extension(ext) = exp.kind() {
                    if let Some(app) = ext.0.as_any().downcast_ref::<crate::plugin::standard::adt::adt_ast_extension::AdtConstructorApp>() {
                        types.push(app.type_vars[&crate::ast::r#type::TypeVar::new("T")].clone());
                    }
                }
            }
            for child in crate::ast::utility::nodes::subnodes(node).unwrap() {
                collect(&child, types);
            }
        }
        let mut types = Vec::new();
        collect(
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
        let program = phases.check_consistency(program).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        assert!(program.domains.iter().any(|d| d.name == "Box"));
    }
    #[test]
    fn native_adt_declaration_reaches_domain_encoding() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("adt Tree { Leaf() } method m() {}").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        assert!(program.domains.iter().any(|d| d.name == "Tree"));
    }
    #[test]
    fn native_recursive_generic_adt_declaration_reaches_domain_encoding() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("adt List[T] { Nil(); Cons(head: T, tail: List[T]) } method m(x: List[Int]) {}")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        assert!(program.domains.iter().any(|d| d.name == "List"));
    }
    #[test]
    fn adt_invalid_type_arguments_and_discriminator_clashes_are_rejected() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        for source in [
            "adt A { C() } method m(x: A[]) {}",
            "adt A { C() } function isC(): Bool { true }",
        ] {
            let mut phases = SilFrontendPhases::new(
                PathBuf::from("test.vpr"),
                standard_plugin_manager(&config).unwrap(),
            );
            let parsed = phases.parse(source).unwrap();
            assert!(phases.analyze(parsed).is_err());
        }
    }
    #[test]
    fn adt_declaration_grammar_retains_constructors_and_derivations() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let program = phases.parse("adt List[T] { Nil(); Cons(head: T, tail: List[T]) } derives { contains[Int] without head }").unwrap();
        let member = program.all_members().remove(0);
        let node = member.node().read().unwrap();
        let crate::parser::parse_ast::PNodeKind::Member(crate::parser::parse_ast::PMember {
            kind: crate::parser::parse_ast::PMemberKind::Extension(extension),
            ..
        }) = &node.kind
        else {
            panic!("expected ADT");
        };
        let adt = extension
            .as_any()
            .downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdt>()
            .unwrap();
        assert_eq!(adt.type_vars.len(), 1);
        assert_eq!(adt.constructors.len(), 2);
        assert_eq!(adt.deriving.len(), 1);
    }
    #[test]
    fn default_plugins_prepare_refute_and_method_initializer() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        for source in [
            "method test() { refute false; }",
            "method inc(x: Int) returns (r: Int) requires x >= 0 ensures r == x + 1 method test() { var y: Int := inc(1); assert y == 2; }",
        ] {
            let mut phases = SilFrontendPhases::new(
                PathBuf::from("test.vpr"),
                standard_plugin_manager(&config).unwrap(),
            );
            let parsed = phases.parse(source).unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            let program = phases.check_consistency(program).unwrap();
            phases.prepare_verification(program).unwrap();
        }
    }
    #[test]
    fn configured_selection_chops_members() {
        let mut config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        config.select = Some("m".into());
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        phases.configure_consistency(&config);
        let parsed = phases.parse("method m() {} method other() {}").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let selected = phases.prepare_verification(program).unwrap();
        assert_eq!(selected.methods.len(), 1);
        assert_eq!(selected.methods[0].name, "m");
    }
    #[test]
    fn missing_selection_produces_empty_program_and_warning() {
        let mut config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        config.select = Some("absent".into());
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        phases.configure_consistency(&config);
        let parsed = phases.parse("method m() {}").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let selected = phases.prepare_verification(program).unwrap();
        assert!(selected.methods.is_empty());
        assert!(phases.typechecking_warnings.iter().any(|w| matches!(&w.kind, FrontendErrorKind::TypecheckerWarning(message) if message == "No members were selected.")));
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
    fn generic_domain_use_checks_arity_and_translates_arguments() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("domain D[T] {} method m(x: D[Int]) {}")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let crate::ast::r#type::Type::Domain(domain) = &program.methods[0].formal_args[0].typ
        else {
            panic!("expected domain type");
        };
        assert_eq!(domain.type_arguments(), vec![crate::ast::r#type::Type::Int]);
        let parsed = phases.parse("domain D[T] {} method m(x: D) {}").unwrap();
        assert!(phases.analyze(parsed).is_err());
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
    fn native_termination_imports_integer_order_and_prepares_recursive_method() {
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
        assert!(
            program
                .domains
                .iter()
                .any(|d| d.name == "IntWellFoundedOrder")
        );
        assert!(program.domains.iter().any(|d| d.name == "WellFoundedOrder"));
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn native_termination_imports_boolean_order() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("method m(x: Bool) decreases x { m(false); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert!(
            program
                .domains
                .iter()
                .any(|d| d.name == "BoolWellFoundedOrder")
        );
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn termination_rewrites_predicate_access_in_decreases() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("predicate p(x: Ref) { true } method m(x: Ref) decreases p(x) {}")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        assert!(
            program
                .domains
                .iter()
                .any(|d| d.name == "PredicateInstancesWellFoundedOrder")
        );
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn termination_rewrites_access_predicate_in_decreases() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("predicate p(x: Ref) { true } method m(x: Ref) decreases acc(p(x)) {}")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
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
