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

/// Result of the source SilFrontend.prepare step before frontend phases begin.
#[derive(Debug)]
pub enum PrepareOutcome {
    Ready(crate::frontend::sil_front_end_config::SilFrontendConfig),
    InvalidArguments,
    NothingToDo,
    /// Reset caught a source PluginException after preparation.
    PluginSetupFailed,
}

/// Report the verifier signature, configure it, and report optional dependencies in source order.
/// The caller supplies the backend's actual configuration operation and owned dependency values;
/// this preserves backend-specific options and avoids inventing custom dependency rendering.
pub fn prepare_frontend<V: crate::verifier::verifier::Verifier + ?Sized>(
    verifier: &mut V,
    reporter: &dyn crate::reporter::reporter::Reporter,
    args: &[String],
    configure: impl FnOnce(
        &mut V,
        &[String],
    ) -> crate::frontend::sil_front_end_config::SilFrontendConfig,
    dependencies: impl FnOnce(
        &V,
    ) -> Result<
        Vec<std::sync::Arc<dyn crate::reporter::message::ReportDependency>>,
        crate::reporter::reporter::ReportError,
    >,
) -> Result<PrepareOutcome, crate::reporter::reporter::ReportError> {
    use crate::reporter::message::{Message, SimpleMessageKind};
    let signature = verifier.signature();
    reporter.report(Message::Simple {
        kind: SimpleMessageKind::Copyright,
        text: signature.clone(),
    })?;
    let config = configure(verifier, args);
    if let Some(error) = &config.error {
        reporter.report(Message::InvalidArguments {
            tool_signature: verifier.signature(),
            errors: vec![AbstractError::Frontend(FrontendError::new(
                FrontendErrorKind::CliOptionError(format!("{error}.")),
                Position::NoPosition,
            ))],
        })?;
        return Ok(PrepareOutcome::InvalidArguments);
    }
    if config.exit() {
        return Ok(PrepareOutcome::NothingToDo);
    }
    if config.dependencies {
        reporter.report(Message::ExternalDependencies {
            dependencies: dependencies(verifier)?,
        })?;
    }
    Ok(PrepareOutcome::Ready(config))
}

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
    standard_plugin_manager_with_resolver(config, |_| Ok(None))
}

/// Resolve additional native plugins in the same configured order as built-in plugins.
pub fn standard_plugin_manager_with_resolver(
    config: &crate::frontend::sil_front_end_config::SilFrontendConfig,
    extra: impl FnMut(
        &str,
    ) -> Result<
        Option<Box<dyn crate::plugin::silver_plugin::SilverPlugin>>,
        crate::plugin::silver_plugin_manager::PluginResolutionError,
    >,
) -> Result<SilverPluginManager, crate::plugin::silver_plugin_manager::PluginResolutionError> {
    standard_plugin_manager_internal(config, extra, None)
}
pub(crate) fn standard_plugin_manager_with_origin(
    config: &crate::frontend::sil_front_end_config::SilFrontendConfig,
    origin: &mut Option<crate::reporter::message::CapturedExceptionDetails>,
) -> Result<SilverPluginManager, crate::plugin::silver_plugin_manager::PluginResolutionError> {
    standard_plugin_manager_internal(config, |_| Ok(None), Some(origin))
}
fn standard_plugin_manager_internal(
    config: &crate::frontend::sil_front_end_config::SilFrontendConfig,
    mut extra: impl FnMut(
        &str,
    ) -> Result<
        Option<Box<dyn crate::plugin::silver_plugin::SilverPlugin>>,
        crate::plugin::silver_plugin_manager::PluginResolutionError,
    >,
    origin: Option<&mut Option<crate::reporter::message::CapturedExceptionDetails>>,
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
    let mut origin = origin;
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
                Box::new(crate::plugin::sif::sif_plugin::SifPlugin {
                    transformer: crate::plugin::sif::sif_extended_transformer::NativeSifTransformer,
                })
            }
            _ => match extra(&name) {
                Ok(Some(plugin)) => plugin,
                Ok(None) => {
                    let error = PluginResolutionError::NotFound(name);
                    capture_plugin_error(&error, "plugin resolution", origin.as_deref_mut());
                    return Err(error);
                }
                Err(error) => {
                    capture_plugin_error(
                        &error,
                        "external resolver boundary",
                        origin.as_deref_mut(),
                    );
                    return Err(error);
                }
            },
        };
        plugins.push(plugin);
    }
    Ok(SilverPluginManager::new(plugins))
}

fn capture_plugin_error(
    error: &crate::plugin::silver_plugin_manager::PluginResolutionError,
    boundary: &str,
    origin: Option<&mut Option<crate::reporter::message::CapturedExceptionDetails>>,
) {
    if let Some(origin) = origin {
        let display = error.to_string();
        let trace = std::backtrace::Backtrace::force_capture();
        *origin = Some(crate::reporter::message::CapturedExceptionDetails {
            stack_trace: format!("{display}\nNative Rust backtrace ({boundary}):\n{trace}"),
            display,
            cause: None,
        });
    }
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
    /// Reformatter parsing retains macro definitions and calls.
    pub expand_macros: bool,
    /// Keep parsed source scopes for an interactive debugger session.
    pub retain_source_program: bool,
    phase_reporter: Option<std::sync::Arc<dyn crate::reporter::reporter::Reporter>>,
    phase_report_error: Option<crate::reporter::reporter::ReportError>,
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
            expand_macros: true,
            retain_source_program: false,
            phase_reporter: None,
            phase_report_error: None,
            parsing_warnings: vec![],
            typechecking_warnings: vec![],
        }
    }
    /// Enable source phase warning events for provider-driven runs.
    pub fn set_phase_reporter(
        &mut self,
        reporter: std::sync::Arc<dyn crate::reporter::reporter::Reporter>,
    ) {
        self.phase_reporter = Some(reporter);
    }
    fn report_phase(&mut self, message: crate::reporter::message::Message) -> bool {
        if let Some(reporter) = &self.phase_reporter {
            if let Err(error) = reporter.report(message) {
                self.phase_report_error = Some(error);
                return false;
            }
        }
        true
    }
    fn report_typechecking_warnings(&mut self) -> bool {
        if self.typechecking_warnings.is_empty() {
            return true;
        }
        self.report_phase(
            crate::reporter::message::Message::WarningsDuringTypechecking {
                warnings: self.typechecking_warnings.clone(),
            },
        )
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
        let macro_error = if self.expand_macros {
            crate::parser::macro_expander::expand_global_expression_macros(&program).err()
        } else {
            None
        };
        let snapshot = match &program.node().read().expect("poisoned parse node").kind {
            crate::parser::parse_ast::PNodeKind::Program(snapshot) => snapshot.clone(),
            _ => unreachable!("typed program handle"),
        };
        let mut reports = snapshot.local_errors;
        if let Some(error) = macro_error {
            reports.push(ParseReport::Error(ParseError::new(
                error.message.clone(),
                error.error_position(&program),
            )));
        }
        for imported in snapshot.imported {
            reports.extend(imported.errors());
        }
        if reports.iter().any(|r| matches!(r, ParseReport::Error(_))) {
            return Err(reports.into_iter().map(AbstractError::Parse).collect());
        }
        if !self.report_phase(crate::reporter::message::Message::WarningsDuringParsing {
            warnings: reports.clone(),
        }) {
            return Err(vec![]);
        }
        self.parsing_warnings.extend(reports);
        init_properties(program.node()).map_err(|error| {
            Self::failure(
                format!("parse tree initialization: {error:?}"),
                Self::program_position(&program),
            )
        })?;
        Ok(program)
    }
    fn analyze(&mut self, input: Self::Parsed) -> Result<Self::Analyzed, Vec<AbstractError>> {
        self.typechecking_warnings.clear();
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
        if !ok {
            analyser
                .messages
                .extend(
                    resolver::value_identifier_messages(input.node()).map_err(|e| {
                        Self::failure(
                            format!("name analysis: {e:?}"),
                            Self::program_position(&input),
                        )
                    })?,
                );
        }
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
            if !self.report_typechecking_warnings() {
                return Err(vec![]);
            }
            return Err(errors);
        }
        let checking = resolver::check_program_core(&input, &mut |node, text| {
            let position = node.read().expect("poisoned parse node").pos.0.clone();
            self.typechecking_warnings.push(FrontendError::new(
                FrontendErrorKind::TypecheckerWarning(text.into()),
                position,
            ));
        })
        .map_err(|e| {
            let errors = match &e {
                resolver::TypeCheckError::Mismatches(errors) => errors.as_slice(),
                _ => std::slice::from_ref(&e),
            };
            let mut messages = Vec::new();
            let mut fallback_errors = Vec::new();
            let mut identifier_messages_added = false;
            for error in errors {
                if let resolver::TypeCheckError::PositionedMessage { node, message } = error {
                    match crate::parser::fast_message::message_for_node(
                        node,
                        message.clone(),
                        true,
                        true,
                    ) {
                        Ok(found) => messages.extend(found),
                        Err(_) => fallback_errors.extend(Self::failure(
                            format!("type checking: {error:?}"),
                            Self::program_position(&input),
                        )),
                    }
                    continue;
                }
                if let resolver::TypeCheckError::UnresolvedValue {
                    name,
                    identifier,
                    ambiguous,
                } = error
                {
                    if identifier_messages_added {
                        continue;
                    }
                    let found =
                        resolver::value_identifier_messages(input.node()).unwrap_or_default();
                    if !found.is_empty() {
                        messages.extend(found);
                        identifier_messages_added = true;
                    } else {
                        let label = if *ambiguous {
                            format!("ambiguous identifier `{name}`")
                        } else {
                            format!("undeclared identifier `{name}`")
                        };
                        if let Ok(found) = crate::parser::fast_message::message_for_node(
                            identifier, label, true, true,
                        ) {
                            messages.extend(found);
                        } else {
                            fallback_errors.extend(Self::failure(
                                format!("type checking: {error:?}"),
                                Self::program_position(&input),
                            ));
                        }
                    }
                    continue;
                }
                if matches!(
                    error,
                    resolver::TypeCheckError::Unsupported(
                        "abstract predicates cannot be folded"
                            | "abstract predicates cannot be unfolded"
                    )
                ) {
                    if let Ok(found) = resolver::abstract_predicate_access_messages(&input) {
                        if !found.is_empty() {
                            messages.extend(found);
                            continue;
                        }
                    }
                }
                if let resolver::TypeCheckError::Positioned { node, message } = error {
                    match crate::parser::fast_message::message_for_node(node, *message, true, true)
                    {
                        Ok(found) => messages.extend(found),
                        Err(_) => fallback_errors.extend(Self::failure(
                            format!("type checking: {error:?}"),
                            Self::program_position(&input),
                        )),
                    }
                    continue;
                }
                if let resolver::TypeCheckError::FunctionPreconditionInDomainAxiom {
                    name,
                    identifier,
                } = error
                {
                    match crate::parser::fast_message::message_for_node(
                        identifier,
                        format!(
                            "Cannot use function {name}, which has preconditions, inside axiom"
                        ),
                        true,
                        true,
                    ) {
                        Ok(found) => messages.extend(found),
                        Err(_) => fallback_errors.extend(Self::failure(
                            format!("type checking: {error:?}"),
                            Self::program_position(&input),
                        )),
                    }
                    continue;
                }
                let (expression, actual, expected) = match error {
                    resolver::TypeCheckError::Incompatible {
                        expression,
                        actual,
                        expected,
                    }
                    | resolver::TypeCheckError::Unification(
                        resolver::UnificationError::Mismatch {
                            expression,
                            actual,
                            expected,
                        },
                    ) => (expression, actual, expected),
                    _ => {
                        fallback_errors.extend(Self::failure(
                            format!("type checking: {error:?}"),
                            Self::program_position(&input),
                        ));
                        continue;
                    }
                };
                fn render(typ: &crate::parser::parse_ast::PTypeHandle) -> Option<String> {
                    use crate::parser::parse_ast::{PNodeKind, PTypeKind};
                    match typ.kind() {
                        PTypeKind::Unknown => return Some("<error>".into()),
                        PTypeKind::BoolImpure => return Some("<impure>".into()),
                        PTypeKind::BoolWand => return Some("<wand>".into()),
                        PTypeKind::BoolPredicate => return Some("<predicate>".into()),
                        PTypeKind::Domain { domain, args, .. } => {
                            let name = match &domain.read().ok()?.kind {
                                PNodeKind::IdnRef(id) => id.name.clone(),
                                _ => return None,
                            };
                            if let Some(args) = args {
                                let arguments = args
                                    .inner()
                                    .to_seq()
                                    .into_iter()
                                    .map(render)
                                    .collect::<Option<Vec<_>>>()?;
                                return Some(format!("{name}[{}]", arguments.join(", ")));
                            }
                            return Some(name);
                        }
                        _ => {}
                    }
                    crate::parser::translator::translate_type(typ)
                        .ok()
                        .and_then(|t| crate::ast::pretty::pretty_printer::show_type(&t).ok())
                }
                let (Some(actual), Some(expected)) = (render(actual), render(expected)) else {
                    return Self::failure(
                        format!("type checking: {e:?}"),
                        Self::program_position(&input),
                    );
                };
                let Ok(found) = crate::parser::fast_message::message_for_node(
                    expression,
                    format!("found incompatible type `{actual}`, expected `{expected}`"),
                    true,
                    true,
                ) else {
                    return Self::failure(
                        format!("type checking: {e:?}"),
                        Self::program_position(&input),
                    );
                };
                messages.extend(found);
            }
            let mut diagnostics: Vec<_> = crate::parser::fast_message::sortmessages(messages)
                .into_iter()
                .map(|message| {
                    AbstractError::Frontend(FrontendError::new(
                        FrontendErrorKind::TypecheckerError(message.label),
                        Position::LineColumn(LineColumn::Source(Box::new(message.pos))),
                    ))
                })
                .collect();
            diagnostics.extend(fallback_errors);
            diagnostics
        });
        if !self.report_typechecking_warnings() {
            return Err(vec![]);
        }
        checking?;
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
        // Resolved identifier candidates may still point into the original imported domain
        // graph after its WellFoundedOrder member is replaced. Keep that graph alive until
        // translation has consumed those weak parent links.
        let original_for_resolution = input.clone();
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
            let reports = imported.errors();
            if reports.iter().any(|r| matches!(r, ParseReport::Error(_))) {
                return Err(reports.into_iter().map(AbstractError::Parse).collect());
            }
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
        let result = if self.retain_source_program {
            translator::translate_program_core_preserving_source(&input)
        } else {
            translator::translate_program_core(&input)
        }
        .map_err(|e| match e {
            translator::TranslationError::Positioned { message, position } => {
                Self::failure(message.into(), position)
            }
            _ => Self::failure(
                format!("translation: {e:?}"),
                Self::program_position(&input),
            ),
        });
        drop(original_for_resolution);
        let program = result?;
        // Silver Translator.translate checks triggers on the completed AST before
        // it returns the translated program, independently of later consistency.
        let errors = std::cell::RefCell::new(Vec::new());
        let failure = std::cell::RefCell::new(None);
        let root = crate::ast::utility::nodes::Node::Program(program.clone());
        let walk = crate::ast::utility::nodes::visit_check_products(&root, &|node| {
            if let crate::ast::utility::nodes::Node::Trigger(trigger) = node {
                match crate::ast::utility::consistency::check_triggers(trigger, &program, &|t| {
                    crate::ast::pretty::pretty_printer::pretty_node(
                        &crate::ast::utility::nodes::Node::Trigger(t.clone()),
                    )
                }) {
                    Ok(mut found) => errors.borrow_mut().append(&mut found),
                    Err(error) => {
                        *failure.borrow_mut() = Some(format!("{error:?}"));
                        return Err(
                            crate::verifier::verification_result::DiagnosticError::Unsupported(
                                "trigger validation",
                            ),
                        );
                    }
                }
            }
            if let crate::ast::utility::nodes::Node::Exp(exp) = node {
                if matches!(exp.kind(), crate::ast::expression::ExpKind::ForPerm(..)) {
                    match crate::ast::utility::consistency::check_for_perm_arguments(exp, &program)
                    {
                        Ok(mut found) => errors.borrow_mut().append(&mut found),
                        Err(error) => {
                            *failure.borrow_mut() = Some(format!("{error:?}"));
                            return Err(
                                crate::verifier::verification_result::DiagnosticError::Unsupported(
                                    "forperm validation",
                                ),
                            );
                        }
                    }
                }
            }
            Ok(node.clone())
        });
        if let Some(error) = failure.into_inner() {
            return Err(Self::failure(
                format!("translation validation: {error}"),
                program.meta.position.clone(),
            ));
        }
        if let Err(error) = walk {
            return Err(Self::failure(
                format!("translation validation traversal: {error:?}"),
                program.meta.position.clone(),
            ));
        }
        let mut errors = errors.into_inner();
        // These validations correspond to the translator's FastMessages in
        // Silver, which the frontend exposes as typechecker errors.
        for error in &mut errors {
            if let FrontendErrorKind::ConsistencyError(message) = &error.kind {
                error.kind = FrontendErrorKind::TypecheckerError(message.clone());
            }
        }
        if !errors.is_empty() {
            return Err(errors.into_iter().map(AbstractError::Frontend).collect());
        }
        Ok(program)
    }
    fn check_consistency(&mut self, input: Program) -> Result<Program, Vec<AbstractError>> {
        use crate::ast::pretty::pretty_printer::{
            PrintError, expression_to_string, pretty_node, show_type,
        };
        use crate::ast::utility::nodes::Node;
        let render = |node: &Node| -> Result<String, PrintError> {
            match node {
                Node::Exp(exp) => expression_to_string(exp),
                Node::Type(typ) => show_type(typ),
                Node::LocalVar(var) => expression_to_string(&crate::ast::expression::Exp::new(
                    crate::ast::expression::ExpKind::LocalVar(var.clone()),
                    var.meta.clone(),
                )),
                Node::LocalDecl(decl) => Ok(format!("{}: {}", decl.name, show_type(&decl.typ)?)),
                Node::UnnamedLocalDecl(decl) => show_type(&decl.typ),
                Node::FieldAccess(access) => {
                    expression_to_string(&crate::ast::expression::Exp::new(
                        crate::ast::expression::ExpKind::FieldAccess(access.clone()),
                        access.meta.clone(),
                    ))
                }
                Node::PredicateAccess(access) => {
                    expression_to_string(&crate::ast::expression::Exp::new(
                        crate::ast::expression::ExpKind::PredicateAccess(access.clone()),
                        access.meta.clone(),
                    ))
                }
                Node::PredicateAccessPredicate(access) => {
                    expression_to_string(&crate::ast::expression::Exp::new(
                        crate::ast::expression::ExpKind::PredicateAccessPredicate(access.clone()),
                        access.meta.clone(),
                    ))
                }
                _ => pretty_node(node),
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
        let source = if self.retain_source_program {
            input.source_program().cloned()
        } else {
            None
        };
        let restore_source = |program: Program| match (&source, program.source_program()) {
            (Some(source), None) => program.with_source_program(source.clone()),
            _ => program,
        };
        let mut program = self
            .plugins
            .before_method_filter(input)
            .ok_or_else(|| self.plugins.errors().to_vec())?;
        program = restore_source(program);
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
        let program = restore_source(program);
        self.plugins
            .before_verify(program)
            .map_err(|e| {
                Self::failure(
                    format!("plugin before verification: {}", e.0),
                    Position::NoPosition,
                )
            })?
            .ok_or_else(|| self.plugins.errors().to_vec())
            .map(restore_source)
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
    fn set_phase_reporter(
        &mut self,
        reporter: std::sync::Arc<dyn crate::reporter::reporter::Reporter>,
    ) {
        SilFrontendPhases::set_phase_reporter(self, reporter);
    }
    fn take_report_error(&mut self) -> Option<crate::reporter::reporter::ReportError> {
        self.phase_report_error.take()
    }
    fn reset_messages(&mut self) {
        self.phase_report_error = None;
        self.parsing_warnings.clear();
        self.typechecking_warnings.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn consistency_renders_statement_in_formal_reassignment_error() {
        use crate::ast::{
            ast::Metadata,
            expression::{Exp, ExpKind},
            program::{LocalVarDecl, Method, MethodData},
            statement::{Stmt, StmtKind},
            r#type::Type,
        };
        let meta = Metadata::default();
        let x = LocalVarDecl::new("x".into(), Type::Int, meta.clone());
        let assignment = Stmt::new(
            StmtKind::LocalVarAssign {
                lhs: x.local_var(),
                rhs: Exp::new(ExpKind::IntLit(1.into()), meta.clone()),
            },
            meta.clone(),
        );
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![assignment],
                declarations: vec![],
            },
            meta.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![x],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let errors = phases.check_consistency(program).unwrap_err();
        let messages = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect::<Vec<_>>();
        assert!(
            messages
                .iter()
                .any(|m| m.contains("x := 1 is a reassignment of formal argument x")),
            "{messages:?}"
        );
    }

    #[test]
    fn external_plugin_resolver_is_called_for_unknown_names_in_order() {
        let mut config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        config.plugin =
            Some("native.one:viper.silver.plugin.standard.arp.ARPPlugin:native.two".into());
        let mut seen = Vec::new();
        let manager = standard_plugin_manager_with_resolver(&config, |name| {
            seen.push(name.to_owned());
            Ok(Some(Box::new(
                crate::plugin::standard::arp::arp_plugin::ArpPlugin,
            )))
        })
        .unwrap();
        assert_eq!(seen, ["native.one", "native.two"]);
        assert_eq!(
            manager.plugins.len(),
            configured_plugin_names(&config).len()
        );
        assert!(standard_plugin_manager(&config).is_err());
    }
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
    fn assume_statements_rewrite_before_consistency() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("field f: Int method m(r: Ref) { assume true && true; assume acc(r.f); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        fn count_assumes(node: crate::ast::utility::nodes::Node) -> usize {
            use crate::ast::utility::nodes::{Node, subnodes};
            usize::from(
                matches!(&node, Node::Stmt(stmt) if matches!(stmt.kind(), crate::ast::statement::StmtKind::Assume(_))),
            ) + subnodes(&node)
                .unwrap()
                .into_iter()
                .map(count_assumes)
                .sum::<usize>()
        }
        assert_eq!(
            count_assumes(crate::ast::utility::nodes::Node::Program(program.clone())),
            0
        );
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn macro_loop_decreases_reaches_termination_lowering() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("define count(x) { while (x > 0) invariant x >= 0 decreases x { x := x - 1; } } method m() { var n: Int := 2; count(n); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn quasihavoc_resource_reaches_typed_ast() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("field f: Int method m(r: Ref, b: Bool) requires acc(r.f) { quasihavoc b ==> r.f; quasihavoc r.f; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases
            .parse("predicate P(r: Ref) method m(r: Ref) { quasihavoc P(r); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases.parse("method m(x: Int) { quasihavoc x; }").unwrap();
        assert!(phases.analyze(parsed).is_err());
        let parsed = phases
            .parse("field f: Int method m(s: Set[Ref]) { quasihavocall x: Ref :: x in s ==> x.f; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let parsed = phases.parse("field f: Int define havoc(s) { quasihavocall x: Ref :: x in s ==> x.f; } method m(x: Ref, s: Set[Ref]) { havoc(s); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
    }

    #[test]
    fn sif_plugin_builds_pure_assertion_product_and_rejects_unsupported() {
        let mut config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        config.plugin = Some("viper.silver.plugin.sif.SIFPlugin".into());
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("method labels() { label p1; assert true; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert_eq!(product.methods[0].formal_args[0].name, "p1_0");
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("method old_low(x: Int) requires low(x) ensures old(low(x)) {}")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert!(matches!(
            product.methods[0].posts[0].kind(),
            crate::ast::expression::ExpKind::Old(_)
        ));
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("method loop_product(n: Int) requires low(n) { var x: Int := n; while (x > 0) invariant low(x) { x := x - 1; } assert low(x); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("field f: Int predicate Q(r: Ref) { acc(r.f) && low(r.f) } predicate P(r: Ref) { acc(Q(r)) } method m(r: Ref) requires acc(r.f) && low(r) && low(r.f) { fold acc(Q(r)); fold acc(P(r)); unfold acc(P(r)); unfold acc(Q(r)); assert low(r.f); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert_eq!(
            product
                .functions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            ["Q$_low", "P$_low"]
        );
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("field f: Int predicate P(r: Ref) { acc(r.f) && low(r.f) } method relpred(r: Ref) requires acc(r.f) && low(r) && low(r.f) { fold acc(P(r)); unfold acc(P(r)); assert low(r.f); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert!(product.functions.iter().any(|f| f.name == "P$_low"));
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse(
                "method disjunction(x: Int, y: Int) requires low(x) { assert low(x) || low(y); }",
            )
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("field f: Int method forperm_test() { assert forperm r: Ref [r.f] :: r == r; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("field f: Int method wand_contract(r: Ref) requires acc(r.f) --* acc(r.f) { assert true; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("domain D { function value(x: D): Int } method domain_value(x: D) requires low(x) { assert low(value(x)); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("domain D { axiom { low(true) } } method m() {}")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
        let parsed = phases
            .parse(
                "method permissions(p: Perm) requires low(p) { var q: Perm := p; assert low(q); }",
            )
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("field f: Int predicate P(r: Ref) { acc(r.f) } method pred(r: Ref) requires acc(r.f) { fold acc(P(r)); unfold acc(P(r)); assert acc(r.f); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert_eq!(
            product
                .predicates
                .iter()
                .map(|p| p.name.as_str())
                .collect::<Vec<_>>(),
            ["P", "P_0"]
        );
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("field f: Int function read(r: Ref): Int requires acc(r.f) { r.f } method heapfunc(r: Ref) requires acc(r.f) && low(r) && low(r.f) { assert low(read(r)); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert_eq!(
            product
                .functions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            ["read", "read_0"]
        );
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("method collections(xs: Seq[Int]) requires low(xs) { var ys: Seq[Int] := xs ++ Seq(1); assert low(ys); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("method bindings(x: Int) requires low(x) { assert low(let y == (x) in y + 1); assert low((exists z: Int :: z == x)); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("method m(x: Int) { assert low(x); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert_eq!(
            product.methods[0]
                .formal_args
                .iter()
                .map(|a| a.name.as_str())
                .collect::<Vec<_>>(),
            ["p1", "p2", "x", "x_0"]
        );
        let rendered = crate::ast::pretty::pretty_printer::pretty(
            75,
            &crate::ast::pretty::pretty_printer::show_program(&product).unwrap(),
        );
        assert!(rendered.contains("x == x_0"), "{rendered}");
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("method m(x: Int) requires low(x) { var y: Int := x; assert low(y); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("function inc(x: Int): Int { x + 1 } method m(x: Int) requires low(x) { assert low(inc(x)); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("method m(x: Int) requires low(x) { var y: Int := 0; if (x > 0) { y := 1; } else { y := 2; } assert low(y); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("method m(x: Int) returns (r: Int) requires low(x) ensures low(r) { r := x; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert_eq!(
            product.methods[0]
                .formal_returns
                .iter()
                .map(|r| r.name.as_str())
                .collect::<Vec<_>>(),
            ["r", "r_0"]
        );
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("method identity(x: Int) returns (r: Int) requires low(x) ensures low(r) { r := x; } method m(x: Int) requires low(x) { var y: Int := identity(x); assert low(y); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("field f: Int method m(r: Ref) requires acc(r.f) && low(r) && low(r.f) { r.f := r.f + 1; assert low(r.f); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert_eq!(
            product
                .fields
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            ["f", "f$_p"]
        );
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("field f: Int method m() { var r: Ref := new(f); r.f := 1; assert low(r); assert low(r.f); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases.parse("method m(x: Int) requires low(x) ensures low(old(x)) { assert low(x > 0 ? x : 0); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("method m(x: Int) { inhale low(x); assert low(x); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse(
                "method m(x: Int, y: Int) requires low(x) ==> low(y) { assert low(x) ==> low(y); }",
            )
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("method m(x: Int) { assert forall x_0: Int :: x_0 == x_0; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        assert_eq!(product.methods[0].formal_args[3].name, "x_1");
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("method m() { assert forall i: Int :: low(i) && i == i; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("method m() { while (false) invariant [true, false] {} }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
        let parsed = phases
            .parse("method m() { while (false) invariant [[true, false], true] {} }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let product = phases.prepare_verification(program).unwrap();
        phases.check_consistency(product).unwrap();
    }
    #[test]
    fn macro_arp_expression_uses_plugin_copy_hook() {
        let mut config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        config.plugin = Some(super::ARP_PLUGIN.into());
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("define amount rd method m() { assert amount > none; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn macro_predicate_instance_reaches_plugin_lowering() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("domain PredicateInstance {} predicate p(x: Int) { true } define inst(v) #p(v) method m() { assert inst(1) == inst(1); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn macro_refute_extension_reaches_plugin_lowering() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse("define check(v) { refute v; } method m() { check(false); }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
    }
    #[test]
    fn macro_wand_proofs_copy_and_forbid_nested_definitions() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("field f: Int define p(r) { package acc(r.f) --* acc(r.f) {} } method m(x: Ref) { p(x); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        assert!(
            phases
                .parse("define unused { package true --* true { define x true } } method m() {}")
                .is_err()
        );
    }
    #[test]
    fn macro_allocation_copies_and_substitutes_fields() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("field f: Int define alloc(x, k) { x := new(k); } method m() { var r: Ref; alloc(r, f); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        assert!(phases.parse("field f: Int define alloc(x, k) { x := new(k); } method m() { var r: Ref; alloc(r, 1); }").is_err());
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
    fn explicitly_imported_order_survives_automatic_order_merge() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("import <decreases/multiset.vpr> function f(x: Int): Int decreases x { x } method m() { assert bounded(Multiset(1)); }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
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
    fn domain_function_formals_are_not_global_macro_names() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("domain D { function f(x: Int): Int } define b { var x: Int := 1; assert x == 1; } method m() { b; }").unwrap();
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
    fn macro_annotated_declarations_copy_and_resolve() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases
            .parse("define b { @s(\"x\") var x: Int := 1; } method m() { b; }")
            .unwrap();
        phases.analyze(parsed).unwrap();
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
    fn recursive_macro_diagnostic_points_to_cycle_declaration() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let errors = phases
            .parse("define a(x) b(x)\ndefine b(x) a(x)\nmethod m() { assert a(1) == 1; }\n")
            .unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec!["Parse error: Recursive macro declaration found: a (test.vpr@1.1--1.17)"]
        );
    }
    #[test]
    fn duplicate_field_call_targets_report_assignment_position() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "field n: Ref\nmethod foo() returns (x: Ref, y: Ref)\nmethod test(a: Ref) {\n  a.n, a.n := foo()\n}\n";
        let parsed = phases.parse(source).unwrap();
        let checked = phases.analyze(parsed).unwrap();
        let errors = phases.translate(checked).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "multiple targets which access the same field are not allowed (test.vpr@4.3--4.20)"
            ]
        );
    }
    #[test]
    fn permission_restrictions_report_each_expression() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "field f: Int\nfield g: Int\nfunction fun(x: Ref): Int\n  requires perm(x.f) == perm(x.g)\n  ensures forperm r: Ref [r.f] :: false\n{ 2 }\n";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "preconditions, postconditions and invariants may only contain `perm` and `forperm` expressions inside of an inhale-exhale (test.vpr@4.12--4.21)",
                "preconditions, postconditions and invariants may only contain `perm` and `forperm` expressions inside of an inhale-exhale (test.vpr@4.25--4.34)",
                "function postconditions are not allowed to contain `forperm` expressions (test.vpr@5.11--5.40)",
            ]
        );
    }
    #[test]
    fn function_post_permission_reports_follow_source_positions() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "field a: Int\nfield b: Int\nfunction fun(x: Ref): Int\n  ensures perm(x.a) == perm(x.b)\n{ 0 }\n";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(messages.len(), 4, "{messages:?}");
        assert!(
            messages[0].starts_with("function postconditions are not allowed to contain `perm`")
        );
        assert!(messages[1].starts_with("preconditions, postconditions and invariants"));
        assert!(
            messages[2].starts_with("function postconditions are not allowed to contain `perm`")
        );
        assert!(messages[3].starts_with("preconditions, postconditions and invariants"));
    }
    #[test]
    fn permission_restriction_inside_wand_is_also_reported() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("field a: Int\nfunction fun(x: Ref): Int\n  requires (perm(x.a) == none) --* true\n{ 0 }\n").unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "magic wands are not supported in function preconditions or predicates (test.vpr@3.12--3.40)",
                "preconditions, postconditions and invariants may only contain `perm` and `forperm` expressions inside of an inhale-exhale (test.vpr@3.13--3.22)",
            ]
        );
    }
    #[test]
    fn missing_standard_import_identifies_bundled_resource() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let errors = phases
            .parse("import <missing/test.vpr>\nmethod m() {}\n")
            .unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "Parse error: could not import file (resource 'import/missing/test.vpr' was not found in bundled imports) (test.vpr@1.1--1.26)"
            ]
        );
    }
    #[test]
    fn duplicate_declarations_do_not_hide_other_identifier_errors() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "method a() { assert missing == 0 }\nmethod b(x: Int, x: Int) { assert x == 0 }\nmethod c() { assert other == 0 }\n";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared identifier `missing` (test.vpr@1.21--1.28)",
                "duplicate identifier `x` at test.vpr@2.18 and at test.vpr@2.10 (test.vpr@2.18--2.19)",
                "ambiguous identifier `x` (test.vpr@2.35--2.36)",
                "undeclared identifier `other` (test.vpr@3.21--3.26)",
            ]
        );
    }
    #[test]
    fn declaration_errors_do_not_report_assignment_target_as_ordinary_value() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("method m(this: Ref) returns (this: Ref) {\n  this := this\n}\n")
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "duplicate identifier `this` at test.vpr@1.30 and at test.vpr@1.10 (test.vpr@1.30--1.34)",
                "ambiguous identifier `this` (test.vpr@2.11--2.15)",
            ]
        );
    }
    #[test]
    fn macro_expansion_rejects_non_resource_in_resource_position() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "predicate p()\ndefine P() p()\ndefine Q() true\nmethod ok() { inhale acc(P()) }\nmethod bad() { assert perm(Q()) == none }\n";
        let errors = phases.parse(source).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "Parse error: Macro expansion would result in invalid code: expected a resource access (test.vpr@5.23--5.32)"
            ]
        );
    }
    #[test]
    fn nested_forperm_reports_inner_bans() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "field f: Int\nmethod m() {\n  assert forperm x: Ref [x.f] :: (forperm y: Ref [y.f] :: perm(y.f) >= none)\n}\n";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "forperm quantifier bodies are not allowed to contain `forperm` expressions (test.vpr@3.35--3.76)",
                "forperm quantifier bodies are not allowed to contain `perm` expressions (test.vpr@3.59--3.68)",
            ]
        );
    }
    #[test]
    fn independent_undeclared_values_are_reported_without_duplicates() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("method a() { assert missing == 0 }\nmethod c() { assert other == 0 }\n")
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared identifier `missing` (test.vpr@1.21--1.28)",
                "undeclared identifier `other` (test.vpr@2.21--2.26)",
            ]
        );
    }
    #[test]
    fn unresolved_values_do_not_hide_sibling_type_errors() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "method m(x: Int, y: Ref) {\n  assert missing == 0\n  assert x < y\n  assert other == 0\n}\n";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared identifier `missing` (test.vpr@2.10--2.17)",
                "found incompatible type `Ref`, expected `Int` (test.vpr@3.14--3.15)",
                "undeclared identifier `other` (test.vpr@4.10--4.15)",
            ]
        );
    }
    #[test]
    fn unresolved_operands_and_calls_preserve_sibling_diagnostics() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "method a(x: Int, y: Ref) { assert (missing == 0) && (x < y) }\nmethod b(x: Int, y: Ref) { assert x < y }\nmethod c() { assert absent(0) == 0 }\n";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared identifier `missing` (test.vpr@1.36--1.43)",
                "found incompatible type `Ref`, expected `Int` (test.vpr@1.58--1.59)",
                "found incompatible type `Ref`, expected `Int` (test.vpr@2.39--2.40)",
                "undeclared call `absent`, expected function or predicate (test.vpr@3.21--3.27)",
            ]
        );
    }
    #[test]
    fn type_mismatch_renders_parser_only_types() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "field f: Int\nfunction a(x: Ref): Int\n  ensures acc(x.f)\n{ 0 }\nfunction b(): Int\n  ensures true --* true\n{ 0 }\n";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "found incompatible type `<impure>`, expected `Bool` (test.vpr@3.11--3.19)",
                "found incompatible type `<wand>`, expected `Bool` (test.vpr@6.11--6.24)",
            ]
        );
    }
    #[test]
    fn invalid_assignment_targets_keep_context_and_rhs_type_errors() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("method m(x: Int) { x := 1 }\nmethod n() { missing := 1 }\n")
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "expected an assignable identifier `x` as lhs (test.vpr@1.20--1.21)",
                "found incompatible type `Int`, expected `<error>` (test.vpr@1.25--1.26)",
                "undeclared identifier `missing`, expected parameter or local variable (test.vpr@2.14--2.21)",
                "found incompatible type `Int`, expected `<error>` (test.vpr@2.25--2.26)",
            ]
        );
    }
    #[test]
    fn missing_assignment_field_takes_precedence_over_receiver() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("field f: Int\nmethod m() {\n  var tmp: Int\n  f.r := tmp\n}\n")
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared field `r` (test.vpr@4.5--4.6)",
                "found incompatible type `Int`, expected `<error>` (test.vpr@4.10--4.13)",
            ]
        );
    }
    #[test]
    fn recursive_function_postconditions_report_each_call() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let source = "function f(i: Int): Int\n  ensures f(i) > 0\n{ i }\nfunction g(i: Int): Int\n  ensures g(i + 1) > 0\n{ i }\nfunction a(i: Int): Int\n  ensures b(i) > 0\n{ b(i) }\nfunction b(i: Int): Int\n{ a(i) }\n";
        let parsed = phases.parse(source).unwrap();
        let checked = phases.analyze(parsed).unwrap();
        let program = phases.translate(checked).unwrap();
        let errors = phases.prepare_verification(program).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "Consistency error: Function f has a self-reference in its postcondition and must be proven to be well-founded. Use \"result\" instead to refer to the result of the function. (test.vpr@2.11--2.15)",
                "Consistency error: Function g has a self-reference in its postcondition and must be proven to be well-founded. Add a \"decreases\" clause to prove well-foundedness. (test.vpr@5.11--5.19)",
                "Consistency error: Function a has a call to mutually-recursive function b in its postcondition and must be proven to be well-founded. Add a \"decreases\" clause to prove well-foundedness. (test.vpr@8.11--8.15)",
            ]
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
    fn multiple_assignment_reports_independent_errors() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("method f() returns (x: Int)\nmethod m() { var a: Int, b: Int := 1; a, b := 2; a, b := f(); }").unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(messages.len(), 3, "{messages:?}");
        assert_eq!(
            messages
                .iter()
                .filter(|m| m.contains("expected a method call when assigning to multiple targets"))
                .count(),
            2
        );
        assert!(
            messages
                .iter()
                .any(|m| m.contains("wrong number of targets"))
        );
    }
    #[test]
    fn domain_axiom_function_precondition_is_positioned_at_call() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("function f(x: Int): Int requires x > 0 { x }\ndomain D { function g(x: Int): Int axiom { forall x: Int :: {g(x)} g(x) == f(x) } }").unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        assert_eq!(errors.len(), 1, "{errors:?}");
        let message = errors[0].readable_message().unwrap();
        assert!(
            message.contains("Cannot use function f, which has preconditions, inside axiom"),
            "{message}"
        );
        assert!(message.contains("@2."), "{message}");
    }
    #[test]
    fn domain_axiom_reports_all_calls_with_preconditions() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "function f(x: Int): Int requires x > 0 { x }\nfunction g(x: Int): Int requires x > 1 { x }\ndomain D {\n  axiom { f(0) == g(0) }\n  axiom { f(1) == g(1) }\n}\n";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "Cannot use function f, which has preconditions, inside axiom (test.vpr@4.11--4.12)",
                "Cannot use function g, which has preconditions, inside axiom (test.vpr@4.19--4.20)",
                "Cannot use function f, which has preconditions, inside axiom (test.vpr@5.11--5.12)",
                "Cannot use function g, which has preconditions, inside axiom (test.vpr@5.19--5.20)",
            ]
        );
    }
    #[test]
    fn predicate_arity_and_argument_type_errors_are_independent() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("predicate p(x: Ref, q: Perm) { true }\nmethod m(x: Ref)\n  requires acc(p())\n  requires acc(p(x))\n  requires acc(p(x, x))\n{}\n").unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "wrong number of arguments (test.vpr@3.16--3.19)",
                "wrong number of arguments (test.vpr@4.16--4.20)",
                "found incompatible type `Ref`, expected `Perm` (test.vpr@5.21--5.22)",
            ]
        );
    }
    #[test]
    fn allocation_reports_each_undeclared_field() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse(
                "method test(x: Ref) {\n  var obj: Ref\n  obj := new(x)\n  obj := new(test)\n}\n",
            )
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared field `x` (test.vpr@3.14--3.15)",
                "undeclared field `test` (test.vpr@4.14--4.18)",
            ]
        );
    }
    #[test]
    fn invalid_access_locations_report_each_source_call() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("domain D { function loc(): Ref }\nfunction f(): Int\nmethod m()\n  requires acc(loc())\n  requires acc(f())\n{}\n").unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "specified location is not a field nor a predicate (test.vpr@4.16--4.21)",
                "specified location is not a field nor a predicate (test.vpr@5.16--5.19)",
            ]
        );
    }
    #[test]
    fn method_call_in_expression_reports_contextual_errors() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("method f(n: Int) returns (r: Int) {\n  r := f(f(n))\n}\n")
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "expected function or predicate (test.vpr@2.10--2.11)",
                "undeclared call `f`, expected function or predicate (test.vpr@2.10--2.11)",
            ]
        );
    }
    #[test]
    fn undeclared_signature_types_are_positioned_and_collected() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("method a(x: Missing) {}\nfunction f(x: Nope): Int { 1 }\n")
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared type `Missing` (test.vpr@1.13--1.20)",
                "undeclared type `Nope` (test.vpr@2.15--2.19)",
            ]
        );
    }
    #[test]
    fn undeclared_argument_and_return_types_are_collected() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("function f(x: Nope, y: Other): Unknown\nmethod a(x: Missing) returns (y: None) {}\n").unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared type `Nope` (test.vpr@1.15--1.19)",
                "undeclared type `Other` (test.vpr@1.24--1.29)",
                "undeclared type `Unknown` (test.vpr@1.32--1.39)",
                "undeclared type `Missing` (test.vpr@2.13--2.20)",
                "undeclared type `None` (test.vpr@2.34--2.38)",
            ]
        );
    }
    #[test]
    fn invalid_map_type_arguments_are_reported_independently() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("method m(x: Map[Missing, Other]) {}\n")
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared type `Missing` (test.vpr@1.17--1.24)",
                "undeclared type `Other` (test.vpr@1.26--1.31)",
            ]
        );
    }
    #[test]
    fn signature_errors_do_not_hide_independent_body_errors() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse(
                "function f(x: Missing): Int { true }\nmethod m(y: Nope) { assert false == 1 }\n",
            )
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared type `Missing` (test.vpr@1.15--1.22)",
                "found incompatible type `Bool`, expected `Int` (test.vpr@1.31--1.35)",
                "undeclared type `Nope` (test.vpr@2.13--2.17)",
                "found incompatible type `Bool`, expected `Int` (test.vpr@2.37--2.38)",
            ]
        );
    }
    #[test]
    fn unresolved_return_type_is_rendered_in_body_mismatch() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("function f(): Missing { 1 }\n").unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "undeclared type `Missing` (test.vpr@1.15--1.22)",
                "found incompatible type `Int`, expected `Missing` (test.vpr@1.25--1.26)",
            ]
        );
    }
    #[test]
    fn forbidden_wands_report_each_source_expression() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "function f(): Int\n  requires true --* true\n{ 0 }\npredicate p() { false --* true }\n";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert_eq!(
            messages,
            vec![
                "magic wands are not supported in function preconditions or predicates (test.vpr@2.12--2.25)",
                "magic wands are not supported in function preconditions or predicates (test.vpr@4.17--4.31)",
            ]
        );
    }
    #[test]
    fn mixed_type_and_unsupported_errors_are_both_retained() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("predicate p()\nmethod m(x: Int, y: Ref) { assert x < y; fold acc(p()); }")
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        assert_eq!(errors.len(), 2, "{errors:?}");
        let messages: Vec<_> = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect();
        assert!(
            messages
                .iter()
                .any(|m| m.contains("found incompatible type")),
            "{messages:?}"
        );
        assert!(
            messages
                .iter()
                .any(|m| m.contains("abstract predicates cannot be folded")),
            "{messages:?}"
        );
    }
    #[test]
    fn mismatch_diagnostics_continue_through_function_specs_and_body() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("function f(x: Int, y: Ref): Int\n requires x < y\n requires y < x\n ensures x < y\n { y }").unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        assert_eq!(errors.len(), 4, "{errors:?}");
    }
    #[test]
    fn mismatch_diagnostics_continue_through_method_specs_and_statements() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("method m(x: Int, y: Ref)\n requires x < y\n requires y < x\n { assert x < y; assert y < x; }").unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        assert_eq!(errors.len(), 4, "{errors:?}");
        for error in errors {
            assert!(
                error
                    .readable_message()
                    .unwrap()
                    .contains("found incompatible type")
            );
        }
    }
    #[test]
    fn comparison_fixture_collects_all_source_mismatches() {
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("comparisons_fail.vpr"),
            SilverPluginManager::new(vec![]),
        );
        let parsed = phases.parse(r#"// Any copyright is dedicated to the Public Domain.
// http://creativecommons.org/publicdomain/zero/1.0/

method chain(i1: Int, i2: Ref, i3: Int, i4: Int)
    //:: ExpectedOutput(typechecker.error)
    requires i1 < i2 <= i3 > i4
{
}

method chain1In(s1: Seq[Int], s2: Seq[Seq[Int]], s3: Seq[Seq[Seq[Ref]]], s4: Set[Seq[Seq[Seq[Int]]]])
    //:: ExpectedOutput(typechecker.error)
    requires s1 in s2 in s3 in s4
{
}

method chainParen(i1: Int, i2: Int, i3: Int, i4: Int)
    //:: ExpectedOutput(typechecker.error)
    requires (i1 < i2) <= i3 > i4
{
}

method chainParen2(i1: Int, i2: Int, i3: Int, i4: Int)
    //:: ExpectedOutput(typechecker.error)
    requires i1 < i2 <= (i3 > i4)
{
}
"#).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        let messages = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(messages.len(), 6);
        for (message, expected) in messages.iter().zip([
            "found incompatible type `Ref`, expected `Int` (comparisons_fail.vpr@6.19--6.21)",
            "found incompatible type `Ref`, expected `Perm` (comparisons_fail.vpr@6.19--6.21)",
            "",
            "found incompatible type `Seq[Seq[Seq[Ref]]]`, expected `Seq[Seq[Seq[Int]]]` (comparisons_fail.vpr@12.32--12.34)",
            "found incompatible type `Bool`, expected `Perm` (comparisons_fail.vpr@18.15--18.22)",
            "found incompatible type `Bool`, expected `Int` (comparisons_fail.vpr@24.26--24.33)",
        ]) { if !expected.is_empty() { assert_eq!(message, expected); } }
        assert!(
            messages[2]
                .starts_with("found incompatible type `Seq[Seq[Seq[Ref]]]`, expected `Set[#T0#")
        );
        assert!(messages[2].ends_with("]` (comparisons_fail.vpr@12.26--12.28)"));
    }
    #[test]
    fn incompatible_operator_type_has_source_message_and_operand_position() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("method m(x: Int, y: Ref)\n  requires x < y\n{}")
            .unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        assert_eq!(errors.len(), 1);
        let message = errors[0].readable_message().unwrap();
        assert!(
            message.contains("found incompatible type `Ref`, expected `Int`"),
            "{message}"
        );
        assert!(
            errors[0].position().to_string().contains("@2.16"),
            "{:?}",
            errors[0].position()
        );
    }
    #[test]
    fn abstract_predicate_diagnostics_are_aggregated_at_identifier_positions() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let source = "predicate foo()\nmethod m() {\n  fold acc(foo())\n  unfold acc(foo())\n  assert unfolding acc(foo()) in true\n}\nfunction f(): Bool { unfolding acc(foo()) in true }\npredicate p() { acc(foo()) && unfolding acc(foo()) in true }";
        let parsed = phases.parse(source).unwrap();
        let errors = phases.analyze(parsed).unwrap_err();
        assert_eq!(errors.len(), 5);
        let labels = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            labels
                .iter()
                .filter(|s| s.contains("cannot be folded"))
                .count(),
            1
        );
        assert_eq!(
            labels
                .iter()
                .filter(|s| s.contains("cannot be unfolded"))
                .count(),
            4
        );
        let positions = errors
            .iter()
            .map(|e| e.position().to_string())
            .collect::<Vec<_>>();
        assert!(positions[0].contains("@3.12"), "{positions:?}");
        assert!(positions[1].contains("@4.14"), "{positions:?}");
        assert!(positions[2].contains("@5.24"), "{positions:?}");
        assert!(positions[3].contains("@7.36"), "{positions:?}");
        assert!(positions[4].contains("@8.45"), "{positions:?}");
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
    fn forperm_requires_direct_quantified_resource_argument() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("field f: Ref field g: Int method m() ensures [true, (forperm x: Ref [x.f.g] :: true)]")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let errors = phases.translate(analyzed).unwrap_err();
        assert!(
            errors.iter().all(|e| matches!(
                e,
                AbstractError::Frontend(FrontendError {
                    kind: FrontendErrorKind::TypecheckerError(_),
                    ..
                })
            )),
            "{errors:?}"
        );
        assert!(
            errors.iter().any(|e| e
                .readable_message()
                .unwrap()
                .contains("Quantified arguments can only be used directly")),
            "{errors:?}"
        );
        let parsed = phases
            .parse("field f: Int method m() ensures [true, (forperm x: Ref [x.f] :: true)]")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        phases.translate(analyzed).unwrap();
    }
    #[test]
    fn invalid_arithmetic_trigger_is_rejected_before_verification() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases
            .parse("method m() { assert (forall i: Int :: {i+1} true) }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let errors = phases.translate(analyzed).unwrap_err();
        assert!(
            errors.iter().all(|e| matches!(
                e,
                AbstractError::Frontend(FrontendError {
                    kind: FrontendErrorKind::TypecheckerError(_),
                    ..
                })
            )),
            "{errors:?}"
        );
        let mut valid =
            SilFrontendPhases::new(PathBuf::from("valid.vpr"), SilverPluginManager::new(vec![]));
        let parsed = valid.parse("domain D { function f(i: Int): Int } method m() { assert (forall i: Int :: {f(i)} true) }").unwrap();
        let analyzed = valid.analyze(parsed).unwrap();
        valid.translate(analyzed).unwrap();
        assert!(
            errors.iter().any(|e| e
                .readable_message()
                .unwrap()
                .contains("is not a valid Trigger")),
            "{errors:?}"
        );
    }
    #[test]
    fn nested_macro_arguments_are_not_declaration_recursion() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("domain D { function f(b: Bool, i: Int): Bool } define Q(b) forall i: Int :: f(b, i) method m(c: Bool) { assume Q(Q(c)) }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        phases.translate(analyzed).unwrap();
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        assert!(
            phases
                .parse("define Q(b) Q(b) method m(c: Bool) { assume Q(c) }")
                .is_err()
        );
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
    fn elseif_chain_reaches_nested_if_translation() {
        use crate::ast::statement::StmtKind;
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let parsed = phases.parse("method m(x: Int) { if (x == 0) { assert true; } elseif (x == 1) { assert true; } elseif (x == 2) { assert true; } else { assert true; } }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let StmtKind::Seqn { statements, .. } = program.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!("method block")
        };
        let StmtKind::If { else_branch, .. } = statements[0].kind() else {
            panic!("outer if")
        };
        let StmtKind::Seqn { statements, .. } = else_branch.kind() else {
            panic!("else block")
        };
        assert!(matches!(statements[0].kind(), StmtKind::If { .. }));
        assert!(phases.parse("method m() { elseif (true) {} }").is_err());
    }

    #[test]
    fn every_macro_in_a_wand_proof_is_reported() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let errors = phases
            .parse("method m() { package true --* true { define a true define b false } }")
            .unwrap_err();
        let messages = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            messages
                .iter()
                .filter(|m| m.contains("macros cannot be defined inside magic wands proof scripts"))
                .count(),
            2,
            "{messages:?}"
        );
    }

    #[test]
    fn multiple_macro_name_errors_are_preserved_without_nested_prefixes() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let errors = phases
            .parse("define a 1 define a 2 define b 3 define b 4 method m() {}")
            .unwrap_err();
        let messages = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(messages.len(), 2, "{messages:?}");
        assert!(
            messages[0].contains("another macro named `a`")
                && messages[1].contains("another macro named `b`"),
            "{messages:?}"
        );
        assert!(
            messages
                .iter()
                .all(|m| !m.contains("Parse error: Parse error:")),
            "{messages:?}"
        );
    }

    #[test]
    fn macro_body_kind_mismatch_reports_source_diagnostic() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        for (source, expected) in [
            (
                "define m 1 method p() { m; }",
                "Expression macro used in statement position",
            ),
            (
                "define m { assert true; } method p() { assert m; }",
                "Statement macro used in expression position",
            ),
            (
                "define m 1 method p(x: m) {}",
                "Expression macro used in type position",
            ),
        ] {
            let errors = phases.parse(source).unwrap_err();
            let messages = errors
                .iter()
                .map(|e| e.readable_message().unwrap())
                .collect::<Vec<_>>();
            assert!(
                messages.iter().any(|m| m.contains(expected)),
                "{messages:?}"
            );
        }
    }

    #[test]
    fn bare_parameterized_macros_report_source_argument_suggestion() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        for (source, suggestion) in [
            (
                "define m(x, y) x + y method p() { assert m == 0; }",
                "`(x, y)`",
            ),
            ("define m() { assert true; } method p() { m; }", "`()`"),
            ("define m() true method p() { assert m; }", "`()`"),
        ] {
            let errors = phases.parse(source).unwrap_err();
            let message = errors
                .iter()
                .map(|e| e.readable_message().unwrap())
                .find(|m| m.contains("referenced without"))
                .expect("missing argument error");
            assert!(
                message.contains(suggestion) && message.contains("try adding"),
                "{message}"
            );
        }
    }

    #[test]
    fn macro_definition_diagnostic_spans_exclude_trailing_trivia() {
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::default());
        let errors = phases
            .parse("define a 1\ndefine a 2\nmethod m() {}")
            .unwrap_err();
        let message = errors[0].readable_message().unwrap();
        assert!(
            message.contains("test.vpr@1.1--1.11") && message.contains("test.vpr@2.1--2.11"),
            "{message}"
        );
    }

    #[test]
    fn imported_macro_expansion_errors_do_not_skip_siblings() {
        use std::{path::Path, sync::Arc};
        struct Loader;
        impl crate::ast::utility::file_loader::FileLoader for Loader {
            fn load_content(&self, path: &Path) -> std::io::Result<String> {
                if path.ends_with("a.vpr") {
                    Ok("define a(x) x method a_user() { assert a(); }".into())
                } else {
                    Ok("define b(x) x method b_user() { assert b(); }".into())
                }
            }
        }
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("/work/main.vpr"),
            SilverPluginManager::default(),
        );
        phases.local_loader = Arc::new(Loader);
        let errors = phases
            .parse("import \"a.vpr\" import \"b.vpr\" method m() {}")
            .unwrap_err();
        let messages = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            messages
                .iter()
                .filter(|m| m.contains("Number of macro arguments does not match"))
                .count(),
            2,
            "{messages:?}"
        );
        assert!(errors.iter().filter(|e| e.readable_message().unwrap().contains("Number of macro arguments does not match")).all(|e| matches!(e, AbstractError::Parse(ParseReport::Error(error)) if matches!(&error.pos, Position::LineColumn(LineColumn::Source(source)) if source.end.is_some()))));
    }

    #[test]
    fn imported_failures_are_aggregated_and_stop_frontend() {
        use std::{path::Path, sync::Arc};
        struct Loader;
        impl crate::ast::utility::file_loader::FileLoader for Loader {
            fn load_content(&self, path: &Path) -> std::io::Result<String> {
                if path.ends_with("bad.vpr") {
                    Ok("method broken(".into())
                } else {
                    Err(std::io::Error::new(
                        std::io::ErrorKind::NotFound,
                        "missing import",
                    ))
                }
            }
        }
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("/work/main.vpr"),
            SilverPluginManager::default(),
        );
        phases.local_loader = Arc::new(Loader);
        let errors = phases
            .parse("import \"missing.vpr\" import \"bad.vpr\" method m(x: Rational) {} ")
            .unwrap_err();
        assert_eq!(errors.len(), 3);
        let messages = errors
            .iter()
            .map(|e| e.readable_message().unwrap())
            .collect::<Vec<_>>();
        assert!(messages[0].contains("Parse warning"), "{messages:?}");
        assert!(
            messages[1].contains("could not import file"),
            "{messages:?}"
        );
        assert!(messages[2].contains("Parse error"), "{messages:?}");
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
        let field = crate::ast::program::Field::new(crate::ast::program::FieldData {
            name: "f".into(),
            typ: crate::ast::r#type::Type::Int,
            meta: meta.clone(),
        });
        let receiver = crate::ast::expression::Exp::new(
            crate::ast::expression::ExpKind::NullLit,
            meta.clone(),
        );
        let access =
            crate::ast::expression::FieldAccess::new(receiver, field.clone(), meta.clone());
        let permission = crate::ast::expression::Exp::new(
            crate::ast::expression::ExpKind::FieldAccessPredicate(access, None),
            meta.clone(),
        );
        let invalid = crate::ast::expression::Exp::new(
            crate::ast::expression::ExpKind::And(
                crate::ast::expression::Exp::new(
                    crate::ast::expression::ExpKind::TrueLit,
                    meta.clone(),
                ),
                permission,
            ),
            meta.clone(),
        );
        let var = crate::ast::program::LocalVarDecl::new(
            "x".into(),
            crate::ast::r#type::Type::Int,
            meta.clone(),
        );
        let quantifier = crate::ast::expression::Exp::new(
            crate::ast::expression::ExpKind::Forall(vec![var], vec![], invalid),
            meta.clone(),
        );
        let statement = crate::ast::statement::Stmt::new(
            crate::ast::statement::StmtKind::Assert(quantifier),
            meta,
        );
        let program = frontend.program.as_ref().unwrap().copy_with(|p| {
            p.fields.push(field);
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

#[cfg(test)]
mod debugger_source_retention_tests {
    use super::*;
    #[test]
    fn selected_empty_program_keeps_source_only_when_requested() {
        let parsed =
            crate::parser::fast_parser::parse_program("method m() { assert true }", "source.vpr")
                .unwrap();
        crate::parser::parse_ast::init_properties(parsed.node()).unwrap();
        let mut names = crate::parser::resolver::NameAnalyser::default();
        names.run(parsed.node()).unwrap();
        crate::parser::resolver::check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program =
            crate::parser::translator::translate_program_core_preserving_source(&parsed).unwrap();
        let mut phases =
            SilFrontendPhases::new(PathBuf::from("source.vpr"), SilverPluginManager::default());
        phases.select = Some("missing".into());
        phases.retain_source_program = true;
        let result = phases.prepare_verification(program.clone()).unwrap();
        assert!(result.methods.is_empty());
        assert!(result.source_program().is_some());
        phases.retain_source_program = false;
        let result = phases.prepare_verification(program).unwrap();
        assert!(result.source_program().is_none());
    }
}
