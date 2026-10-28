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
    frontend
        .reset(input, load)
        .map_err(ProviderSetupError::Frontend)?;
    if let Some(config) = config {
        // Source SilFrontend.reset reconstructs the configured manager before the
        // provider's optional empty-manager override.
        let names = super::sil_frontend::configured_plugin_names(config);
        let mut duplicates = Vec::new();
        for name in &names {
            if names.iter().filter(|other| *other == name).count() > 1 && !duplicates.contains(name)
            {
                duplicates.push(name.clone());
            }
        }
        if !duplicates.is_empty() {
            reporter.report(Message::Simple {
                kind: crate::reporter::message::SimpleMessageKind::ConfigurationWarning,
                text: format!("The following plugins will be executed multiple times, which is most likely a configuration mistake: {}.", duplicates.join(", ")),
            }).map_err(ProviderSetupError::Reporter)?;
        }
        let manager = super::sil_frontend::standard_plugin_manager(config)
            .map_err(ProviderSetupError::Plugin)?;
        frontend.phases.plugins = if disable_plugins {
            crate::plugin::silver_plugin_manager::SilverPluginManager::new(vec![])
        } else {
            manager
        };
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
impl ViperAstProvider<super::sil_frontend::SilFrontendPhases> {
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
