//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ViperAstProvider.scala
//!
//! Purpose:
//! Produce a checked Silver AST without backend verification.
//!
//! Planned Rust structure:
//! Represent ViperAstProvider, Config and AstProvidingVerifier; specialize phase list, result,
//! finish, verifier creation and optional disabled-plugin manager.
//!
//! Behavior to preserve:
//! Run parsing, analysis, translation and consistency only; success requires a program and
//! consistency state. Report AST construction result; disabled plugins use an empty manager on
//! reset. The stub verifier succeeds but is not a verification phase.
//!
//! Integration:
//! frontend::sil_frontend, parser and reporter::message; reformatter_ast_provider specializes
//! this provider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on provider composition and plugin manager lifetime with sil_frontend.
//!
//! Status: partial; concrete configuration, built-in plugin reset, phase selection, result
//! handling and AST-constructor verifier implemented. Complete command-line orchestration
//! and custom plugin resolution remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::frontend::{DefaultFrontend, DefaultState, FrontendError, FrontendPhases, Phase};
use crate::reporter::message::Message;
use crate::reporter::reporter::{ReportError, Reporter};
use crate::verifier::verification_result::VerificationResult;
use std::sync::Arc;

/// Source ViperAstProvider's no-op verifier. It does not create a solver.
pub struct AstProvidingVerifier {
    reporter: Arc<dyn Reporter>,
    pub config: Option<super::sil_front_end_config::SilFrontendConfig>,
}
impl AstProvidingVerifier {
    pub fn new(reporter: Arc<dyn Reporter>) -> Self {
        Self {
            reporter,
            config: None,
        }
    }
}
impl crate::components::components::LifetimeComponent for AstProvidingVerifier {
    fn start(&mut self) {}
    fn stop(&mut self) {}
}
impl crate::verifier::verifier::Verifier for AstProvidingVerifier {
    fn name(&self) -> &str {
        "Viper AST Constructor"
    }
    fn version(&self) -> &str {
        ""
    }
    fn build_version(&self) -> &str {
        ""
    }
    fn copyright(&self) -> &str {
        "(c) Copyright ETH Zurich 2012 - 2020"
    }
    fn signature(&self) -> String {
        self.name().to_owned()
    }
    fn debug_info(&mut self, _: Vec<(String, Box<dyn std::any::Any + Send + Sync>)>) {}
    fn dependencies(&self) -> Vec<&dyn crate::verifier::verifier::Dependency> {
        vec![]
    }
    fn parse_command_line(&mut self, args: &[String]) {
        self.config = Some(
            super::sil_front_end_config::SilFrontendConfig::parse_shared(
                "ViperAstProviderConfig",
                args,
            ),
        );
    }
    fn verify(
        &mut self,
        _: &crate::ast::program::Program,
    ) -> Result<VerificationResult, crate::verifier::verifier::VerifierError> {
        Ok(VerificationResult::Success)
    }
    fn reporter(&self) -> &dyn Reporter {
        self.reporter.as_ref()
    }
}

/// Errors encountered while configuring or resetting a concrete AST provider.
#[derive(Debug)]
pub enum ProviderSetupError {
    Configuration(String),
    ExitRequested,
    Frontend(FrontendError),
    Plugin(crate::plugin::silver_plugin_manager::PluginResolutionError),
    Reporter(ReportError),
}

pub(crate) fn configured_verifier(
    reporter: Arc<dyn Reporter>,
    args: &[String],
) -> Result<
    (
        AstProvidingVerifier,
        super::sil_front_end_config::SilFrontendConfig,
    ),
    ProviderSetupError,
> {
    use crate::verifier::verifier::Verifier;
    let mut verifier = AstProvidingVerifier::new(reporter);
    verifier.parse_command_line(args);
    let config = verifier.config.clone().expect("verifier configuration");
    if let Some(error) = &config.error {
        return Err(ProviderSetupError::Configuration(error.clone()));
    }
    if config.exit() {
        return Err(ProviderSetupError::ExitRequested);
    }
    Ok((verifier, config))
}

pub(crate) fn reset_configured(
    frontend: &mut DefaultFrontend<super::sil_frontend::SilFrontendPhases>,
    config: Option<&super::sil_front_end_config::SilFrontendConfig>,
    disable_plugins: bool,
    reporter: &dyn Reporter,
    input: &std::path::Path,
    load: impl FnOnce(&std::path::Path) -> std::io::Result<String>,
) -> Result<(), ProviderSetupError> {
    reset_configured_with_origin(
        frontend,
        config,
        disable_plugins,
        reporter,
        input,
        load,
        None,
    )
}
pub(crate) fn reset_configured_with_origin(
    frontend: &mut DefaultFrontend<super::sil_frontend::SilFrontendPhases>,
    config: Option<&super::sil_front_end_config::SilFrontendConfig>,
    disable_plugins: bool,
    reporter: &dyn Reporter,
    input: &std::path::Path,
    load: impl FnOnce(&std::path::Path) -> std::io::Result<String>,
    origin: Option<&mut Option<crate::reporter::message::CapturedExceptionDetails>>,
) -> Result<(), ProviderSetupError> {
    frontend
        .reset(input, load)
        .map_err(ProviderSetupError::Frontend)?;
    if let Some(config) = config {
        // Source SilFrontend.reset reconstructs the configured manager before the
        // provider's optional empty-manager override.
        super::sil_frontend::report_configured_plugin_warnings(config, reporter)
            .map_err(ProviderSetupError::Reporter)?;
        let manager = match origin {
            Some(origin) => {
                super::sil_frontend::standard_plugin_manager_with_origin(config, origin)
            }
            None => super::sil_frontend::standard_plugin_manager(config),
        }
        .map_err(ProviderSetupError::Plugin)?;
        reporter
            .bind_plugin_manager(&manager)
            .map_err(ProviderSetupError::Reporter)?;
        frontend.phases.plugins = manager;
        reporter
            .set_config(Some(config))
            .map_err(ProviderSetupError::Reporter)?;
        if disable_plugins {
            frontend.phases.plugins =
                crate::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]);
        }
    } else if disable_plugins {
        frontend.phases.plugins =
            crate::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]);
    }
    Ok(())
}

pub const PHASES: &[Phase] = &[
    Phase::Parsing,
    Phase::SemanticAnalysis,
    Phase::Translation,
    Phase::ConsistencyCheck,
];
pub struct ViperAstProvider<F: FrontendPhases> {
    pub frontend: DefaultFrontend<F>,
    pub reporter: Arc<dyn Reporter>,
    /// Select the source provider's empty plugin manager on reset.
    pub disable_plugins: bool,
    pub config: Option<super::sil_front_end_config::SilFrontendConfig>,
}
/// Failure while running the concrete AST-construction lifecycle.
#[derive(Debug)]
pub enum ProviderExecuteError {
    Reporter(ReportError),
    Setup(ProviderSetupError),
    Finish(ProviderFinishError),
    PluginReport {
        plugin: crate::plugin::silver_plugin_manager::PluginResolutionError,
        reporter: ReportError,
    },
}
impl ViperAstProvider<super::sil_frontend::SilFrontendPhases> {
    /// Execute preparation, reset, all AST-construction phases and finish reporting.
    pub fn execute(
        &mut self,
        args: &[String],
        load: impl FnOnce(&std::path::Path) -> std::io::Result<String>,
    ) -> Result<super::sil_frontend::PrepareOutcome, ProviderExecuteError> {
        use super::sil_frontend::{PrepareOutcome, prepare_frontend};
        use crate::verifier::verifier::Verifier;
        let started = std::time::Instant::now();
        let mut verifier = AstProvidingVerifier::new(self.reporter.clone());
        let outcome = prepare_frontend(
            &mut verifier,
            self.reporter.as_ref(),
            args,
            |verifier, args| {
                verifier.parse_command_line(args);
                verifier.config.clone().expect("configured verifier")
            },
            |_| Ok(vec![]),
        )
        .map_err(ProviderExecuteError::Reporter)?;
        let PrepareOutcome::Ready(config) = outcome else {
            return Ok(outcome);
        };
        let file = config.file.clone().ok_or(ProviderExecuteError::Setup(
            ProviderSetupError::Frontend(FrontendError::MissingInput),
        ))?;
        self.frontend.phases.configure_consistency(&config);
        self.frontend.init(Box::new(verifier));
        self.config = Some(config.clone());
        let mut origin = None;
        if let Err(error) = reset_configured_with_origin(
            &mut self.frontend,
            self.config.as_ref(),
            self.disable_plugins,
            self.reporter.as_ref(),
            std::path::Path::new(&file),
            load,
            Some(&mut origin),
        ) {
            use crate::plugin::silver_plugin_manager::PluginResolutionError;
            match error {
                ProviderSetupError::Plugin(
                    plugin @ (PluginResolutionError::NotFound(_)
                    | PluginResolutionError::WrongType(_)
                    | PluginResolutionError::WrongArguments(_)),
                ) => {
                    let message = match origin {
                        Some(details) => {
                            Message::captured_exception(Arc::new(plugin.clone()), details)
                        }
                        None => Message::exception(Arc::new(plugin.clone())),
                    };
                    if let Err(reporter) = self.reporter.report(message) {
                        return Err(ProviderExecuteError::PluginReport { plugin, reporter });
                    }
                    return Ok(PrepareOutcome::PluginSetupFailed);
                }
                other => return Err(ProviderExecuteError::Setup(other)),
            }
        }
        self.frontend
            .run_range(PHASES, Phase::Parsing, Phase::ConsistencyCheck)
            .map_err(|error| ProviderExecuteError::Setup(ProviderSetupError::Frontend(error)))?;
        let elapsed = i64::try_from(started.elapsed().as_millis()).unwrap_or(i64::MAX);
        self.finish(elapsed).map_err(ProviderExecuteError::Finish)?;
        Ok(PrepareOutcome::Ready(config))
    }
    pub fn initialize_configured(&mut self, args: &[String]) -> Result<(), ProviderSetupError> {
        let (verifier, config) = configured_verifier(self.reporter.clone(), args)?;
        self.frontend.phases.configure_consistency(&config);
        self.frontend
            .phases
            .set_phase_reporter(self.reporter.clone());
        self.frontend.init(Box::new(verifier));
        self.config = Some(config);
        Ok(())
    }
    pub fn reset(
        &mut self,
        input: &std::path::Path,
        load: impl FnOnce(&std::path::Path) -> std::io::Result<String>,
    ) -> Result<(), ProviderSetupError> {
        reset_configured(
            &mut self.frontend,
            self.config.as_ref(),
            self.disable_plugins,
            self.reporter.as_ref(),
            input,
            load,
        )
    }
}
impl<F: FrontendPhases> ViperAstProvider<F> {
    pub fn new(
        mut frontend: DefaultFrontend<F>,
        reporter: Arc<dyn Reporter>,
        disable_plugins: bool,
    ) -> Self {
        frontend.phases.set_phase_reporter(reporter.clone());
        Self {
            frontend,
            reporter,
            disable_plugins,
            config: None,
        }
    }
    pub fn result(&self) -> Result<VerificationResult, FrontendError> {
        if !self.frontend.errors.is_empty() {
            return Ok(VerificationResult::Failure(self.frontend.errors.clone()));
        }
        if self.frontend.program.is_none() {
            return Ok(VerificationResult::Failure(Vec::new()));
        }
        if self.frontend.state < DefaultState::ConsistencyCheck {
            return Err(FrontendError::MissingPhaseResult("consistency"));
        }
        Ok(VerificationResult::Success)
    }
    pub fn finish(&self, time: i64) -> Result<(), ProviderFinishError> {
        let result = self.result().map_err(ProviderFinishError::Frontend)?;
        let message = match result {
            VerificationResult::Success => Message::AstConstructionSuccess { time },
            VerificationResult::Failure(errors) => Message::AstConstructionFailure { time, errors },
        };
        self.reporter
            .report(message)
            .map_err(ProviderFinishError::Reporter)
    }
}
#[derive(Debug)]
pub enum ProviderFinishError {
    Frontend(FrontendError),
    Reporter(ReportError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verifier::verifier::Verifier;
    #[test]
    fn execute_runs_ast_phases_and_reports_errors_and_plugin_failure() {
        use super::super::sil_frontend::PrepareOutcome;
        use crate::reporter::{
            message::SimpleMessageKind,
            reporter::{NoopReporter, PollingReporter},
        };
        let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
        let phases = super::super::sil_frontend::SilFrontendPhases::new(
            "test.vpr".into(),
            crate::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
        );
        let mut provider =
            ViperAstProvider::new(DefaultFrontend::new(phases), reporter.clone(), false);
        let args = vec![
            "--ignoreFile".into(),
            "--disableDefaultPlugins".into(),
            "--dependencies".into(),
            "test.vpr".into(),
        ];
        assert!(matches!(
            provider
                .execute(&args, |_| Ok("method m() {}".into()))
                .unwrap(),
            PrepareOutcome::Ready(_)
        ));
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::Simple {
                kind: SimpleMessageKind::Copyright,
                ..
            }
        ));
        assert!(
            matches!(reporter.get_new_message().unwrap(), Message::ExternalDependencies { dependencies } if dependencies.is_empty())
        );
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::WarningsDuringParsing { .. }
        ));
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::AstConstructionSuccess { .. }
        ));
        assert!(!reporter.has_new_message());
        assert!(matches!(
            provider
                .execute(&args, |_| Ok("method m() { assert 1; }".into()))
                .unwrap(),
            PrepareOutcome::Ready(_)
        ));
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::Simple {
                kind: SimpleMessageKind::Copyright,
                ..
            }
        ));
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::ExternalDependencies { .. }
        ));
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::WarningsDuringParsing { .. }
        ));
        assert!(
            matches!(reporter.get_new_message().unwrap(), Message::AstConstructionFailure { errors, .. } if !errors.is_empty())
        );
        let bad = vec![
            "--ignoreFile".into(),
            "--disableDefaultPlugins".into(),
            "--plugin".into(),
            "unknown.Plugin".into(),
            "test.vpr".into(),
        ];
        assert!(matches!(
            provider.execute(&bad, |_| Ok("".into())).unwrap(),
            PrepareOutcome::PluginSetupFailed
        ));
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::Simple {
                kind: SimpleMessageKind::Copyright,
                ..
            }
        ));
        assert!(
            matches!(reporter.get_new_message().unwrap(), Message::Exception { error, .. } if error.to_string() == "Plugin unknown.Plugin not found.")
        );
        assert!(!reporter.has_new_message());
    }
    #[test]
    fn configured_ast_provider_disables_plugins_and_reports_duplicates() {
        use crate::reporter::{
            message::{Message, SimpleMessageKind},
            reporter::{NoopReporter, PollingReporter},
        };
        let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
        let phases = super::super::sil_frontend::SilFrontendPhases::new(
            "test.vpr".into(),
            crate::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
        );
        let mut provider =
            ViperAstProvider::new(DefaultFrontend::new(phases), reporter.clone(), true);
        let refute = "viper.silver.plugin.standard.refute.RefutePlugin";
        provider
            .initialize_configured(&[
                "--ignoreFile".into(),
                "--plugin".into(),
                refute.into(),
                "test.vpr".into(),
            ])
            .unwrap();
        provider
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m() {}".into())
            })
            .unwrap();
        assert!(
            provider
                .frontend
                .phases
                .plugins
                .parser_features()
                .is_empty()
        );
        assert!(
            matches!(reporter.get_new_message().unwrap(), Message::Simple { kind: SimpleMessageKind::ConfigurationWarning, text } if text.contains(refute))
        );
        provider
            .frontend
            .run_range(PHASES, Phase::Parsing, Phase::ConsistencyCheck)
            .unwrap();
        assert!(matches!(
            provider.result().unwrap(),
            VerificationResult::Success
        ));
    }

    #[test]
    fn reset_reconfigures_reporter_and_propagates_failure() {
        struct ConfigReporter(std::sync::Mutex<Vec<bool>>);
        impl Reporter for ConfigReporter {
            fn name(&self) -> &str {
                "config"
            }
            fn report(&self, _: Message) -> Result<(), ReportError> {
                Ok(())
            }
            fn set_config(
                &self,
                config: Option<&super::super::sil_front_end_config::SilFrontendConfig>,
            ) -> Result<(), ReportError> {
                let enabled = config.unwrap().report_partial_results;
                self.0.lock().unwrap().push(enabled);
                if enabled {
                    Err(ReportError::Unsupported("config failure"))
                } else {
                    Ok(())
                }
            }
        }
        let reporter = Arc::new(ConfigReporter(std::sync::Mutex::new(Vec::new())));
        let phases = super::super::sil_frontend::SilFrontendPhases::new(
            "test.vpr".into(),
            crate::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
        );
        let mut provider =
            ViperAstProvider::new(DefaultFrontend::new(phases), reporter.clone(), false);
        provider
            .initialize_configured(&["--ignoreFile".into(), "test.vpr".into()])
            .unwrap();
        provider
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m() {}".into())
            })
            .unwrap();
        provider.config.as_mut().unwrap().report_partial_results = true;
        assert!(matches!(
            provider.reset(std::path::Path::new("test.vpr"), |_| Ok(
                "method m() {}".into()
            )),
            Err(ProviderSetupError::Reporter(ReportError::Unsupported(
                "config failure"
            )))
        ));
        assert_eq!(*reporter.0.lock().unwrap(), vec![false, true]);
    }
    #[test]
    fn provider_rebinds_constructed_manager_before_disable_override() {
        struct Binding(std::sync::Mutex<Vec<usize>>);
        impl Reporter for Binding {
            fn name(&self) -> &str {
                "binding"
            }
            fn report(&self, _: Message) -> Result<(), ReportError> {
                Ok(())
            }
            fn bind_plugin_manager(
                &self,
                manager: &crate::plugin::silver_plugin_manager::SilverPluginManager,
            ) -> Result<(), ReportError> {
                manager.shared_entity_mapper()?;
                self.0.lock().unwrap().push(manager.plugins.len());
                Ok(())
            }
        }
        let reporter = Arc::new(Binding(std::sync::Mutex::new(Vec::new())));
        let phases = super::super::sil_frontend::SilFrontendPhases::new(
            "test.vpr".into(),
            crate::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
        );
        let mut provider =
            ViperAstProvider::new(DefaultFrontend::new(phases), reporter.clone(), true);
        provider
            .initialize_configured(&["--ignoreFile".into(), "test.vpr".into()])
            .unwrap();
        for _ in 0..2 {
            provider
                .reset(std::path::Path::new("test.vpr"), |_| {
                    Ok("method m() {}".into())
                })
                .unwrap();
        }
        let calls = reporter.0.lock().unwrap();
        assert_eq!(calls.len(), 2);
        assert!(calls.iter().all(|count| *count > 0));
        assert!(provider.frontend.phases.plugins.plugins.is_empty());
    }
    #[test]
    fn ast_constructor_retains_shared_command_line_config() {
        let mut verifier =
            AstProvidingVerifier::new(Arc::new(crate::reporter::reporter::NoopReporter));
        assert!(verifier.config.is_none());
        verifier.parse_command_line(&[
            "--ignoreFile".into(),
            "--no-timing".into(),
            "test.vpr".into(),
        ]);
        let config = verifier.config.as_ref().unwrap();
        assert!(config.error.is_none());
        assert!(config.no_timing);
        assert_eq!(config.file.as_deref(), Some("test.vpr"));
        assert!(verifier.dependencies().is_empty());
    }
}
