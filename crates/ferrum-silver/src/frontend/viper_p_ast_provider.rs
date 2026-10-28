//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ViperPAstProvider.scala
//!
//! Purpose:
//! Provide a parsed and semantically analyzed parse AST without translating or verifying.
//!
//! Planned Rust structure:
//! Represent ViperPAstProvider, Config and PAstProvidingVerifier; override phase list, result,
//! creation and plugin selection.
//!
//! Behavior to preserve:
//! Run Parsing then SemanticAnalysis only; require semantic state for success and return recorded
//! errors otherwise. Disabled plugins select empty manager after reset.
//!
//! Integration:
//! frontend::sil_frontend, parser::parse_ast and reporter/verifier interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on provider composition and shared plugin lifetime with viper_ast_provider.
//!
//! Status: partial; concrete parser, verifier and built-in plugin configuration are wired.
//! Inherited finish reporting is wired; complete command-line orchestration remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::frontend::{DefaultFrontend, DefaultState, FrontendError, FrontendPhases, Phase};
use crate::verifier::verification_result::VerificationResult;

use crate::reporter::reporter::Reporter;
use std::sync::Arc;

/// Source ViperPAstProvider's no-op verifier, which does not start a solver.
pub struct PAstProvidingVerifier {
    reporter: Arc<dyn Reporter>,
    pub config: Option<super::sil_front_end_config::SilFrontendConfig>,
}
impl PAstProvidingVerifier {
    pub fn new(reporter: Arc<dyn Reporter>) -> Self {
        Self {
            reporter,
            config: None,
        }
    }
}
impl crate::components::components::LifetimeComponent for PAstProvidingVerifier {
    fn start(&mut self) {}
    fn stop(&mut self) {}
}
impl crate::verifier::verifier::Verifier for PAstProvidingVerifier {
    fn name(&self) -> &str {
        "Viper PAST Constructor"
    }
    fn version(&self) -> &str {
        ""
    }
    fn build_version(&self) -> &str {
        ""
    }
    fn copyright(&self) -> &str {
        "(c) Copyright ETH Zurich 2012 - 2023"
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
                "ViperPAstProviderConfig",
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

pub const PHASES: &[Phase] = &[Phase::Parsing, Phase::SemanticAnalysis];
pub struct ViperPAstProvider<F: FrontendPhases> {
    pub frontend: DefaultFrontend<F>,
    pub disable_plugins: bool,
    pub reporter: Arc<dyn Reporter>,
    pub config: Option<super::sil_front_end_config::SilFrontendConfig>,
}
#[derive(Debug)]
pub enum PAstFinishError {
    Frontend(FrontendError),
    Diagnostic(crate::verifier::verification_result::DiagnosticError),
    Reporter(crate::reporter::reporter::ReportError),
}
impl ViperPAstProvider<super::sil_frontend::SilFrontendPhases> {
    /// Apply the inherited SilFrontend finish hooks and report the resulting outcome.
    pub fn finish(&mut self, time: i64) -> Result<(), PAstFinishError> {
        use crate::reporter::message::Message;
        let transformed = self
            .result()
            .map_err(PAstFinishError::Frontend)?
            .transformed_result()
            .map_err(PAstFinishError::Diagnostic)?;
        let result = self.frontend.phases.plugins.before_finish(transformed);
        let filtered = match result {
            VerificationResult::Success => VerificationResult::Success,
            VerificationResult::Failure(errors) => {
                let mut seen = std::collections::HashSet::new();
                let mut unique = Vec::new();
                for error in errors {
                    let key = error
                        .transformed_error()
                        .map_err(PAstFinishError::Diagnostic)?
                        .readable_message()
                        .map_err(PAstFinishError::Diagnostic)?;
                    if seen.insert(key) {
                        unique.push(error);
                    }
                }
                VerificationResult::Failure(unique)
            }
        };
        self.frontend.verification_result = Some(filtered.clone());
        let verifier = self
            .frontend
            .verifier
            .as_ref()
            .ok_or(PAstFinishError::Frontend(FrontendError::NotInitialized))?;
        let message = match filtered {
            VerificationResult::Success => Message::OverallSuccess {
                verifier: verifier.name().into(),
                time,
            },
            VerificationResult::Failure(errors) => Message::OverallFailure {
                verifier: verifier.name().into(),
                time,
                errors,
            },
        };
        self.reporter
            .report(message)
            .map_err(PAstFinishError::Reporter)
    }
    pub fn initialize_configured(
        &mut self,
        args: &[String],
    ) -> Result<(), super::viper_ast_provider::ProviderSetupError> {
        use super::viper_ast_provider::ProviderSetupError;
        use crate::verifier::verifier::Verifier;
        let mut verifier = PAstProvidingVerifier::new(self.reporter.clone());
        verifier.parse_command_line(args);
        let config = verifier.config.clone().expect("verifier configuration");
        if let Some(error) = &config.error {
            return Err(ProviderSetupError::Configuration(error.clone()));
        }
        if config.exit() {
            return Err(ProviderSetupError::ExitRequested);
        }
        self.frontend.phases.configure_consistency(&config);
        self.frontend.init(Box::new(verifier));
        self.config = Some(config);
        Ok(())
    }
    pub fn reset(
        &mut self,
        input: &std::path::Path,
        load: impl FnOnce(&std::path::Path) -> std::io::Result<String>,
    ) -> Result<(), super::viper_ast_provider::ProviderSetupError> {
        super::viper_ast_provider::reset_configured(
            &mut self.frontend,
            self.config.as_ref(),
            self.disable_plugins,
            self.reporter.as_ref(),
            input,
            load,
        )
    }
}
impl<F: FrontendPhases> ViperPAstProvider<F> {
    pub fn new(
        frontend: DefaultFrontend<F>,
        reporter: Arc<dyn Reporter>,
        disable_plugins: bool,
    ) -> Self {
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
        if self.frontend.state < DefaultState::SemanticAnalysis {
            return Err(FrontendError::MissingPhaseResult("semantic analysis"));
        }
        Ok(VerificationResult::Success)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::sil_frontend::SilFrontendPhases;
    use crate::plugin::silver_plugin_manager::SilverPluginManager;
    use crate::reporter::reporter::NoopReporter;

    #[test]
    fn finish_applies_plugin_then_deduplicates_and_reports() {
        use crate::plugin::silver_plugin::SilverPlugin;
        use crate::reporter::{message::Message, reporter::PollingReporter};
        use crate::verifier::verification_result::{AbstractError, ParseError, ParseReport};
        struct FinishPlugin;
        impl SilverPlugin for FinishPlugin {
            fn before_finish(&mut self, _: VerificationResult) -> VerificationResult {
                let error = AbstractError::Parse(ParseReport::Error(ParseError::new(
                    "same",
                    crate::ast::position::Position::NoPosition,
                )));
                VerificationResult::Failure(vec![error.clone(), error])
            }
        }
        let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
        let phases = SilFrontendPhases::new(
            "test.vpr".into(),
            SilverPluginManager::new(vec![Box::new(FinishPlugin)]),
        );
        let mut provider =
            ViperPAstProvider::new(DefaultFrontend::new(phases), reporter.clone(), false);
        provider
            .frontend
            .init(Box::new(PAstProvidingVerifier::new(reporter.clone())));
        assert!(matches!(
            provider.finish(0),
            Err(PAstFinishError::Frontend(
                FrontendError::MissingPhaseResult(_)
            ))
        ));
        provider
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m() {}".into())
            })
            .unwrap();
        provider
            .frontend
            .run_range(PHASES, Phase::Parsing, Phase::SemanticAnalysis)
            .unwrap();
        provider.finish(42).unwrap();
        assert!(
            matches!(reporter.get_new_message().unwrap(), Message::OverallFailure { verifier, time: 42, errors } if verifier == "Viper PAST Constructor" && errors.len() == 1)
        );
        assert!(
            matches!(&provider.frontend.verification_result, Some(VerificationResult::Failure(errors)) if errors.len() == 1)
        );
        assert!(matches!(
            provider.result().unwrap(),
            VerificationResult::Success
        ));
    }

    #[test]
    fn finish_reports_success_from_analyzed_program() {
        use crate::reporter::{message::Message, reporter::PollingReporter};
        let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
        let phases = SilFrontendPhases::new("test.vpr".into(), SilverPluginManager::new(vec![]));
        let mut provider =
            ViperPAstProvider::new(DefaultFrontend::new(phases), reporter.clone(), false);
        provider
            .frontend
            .init(Box::new(PAstProvidingVerifier::new(reporter.clone())));
        provider
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m() {}".into())
            })
            .unwrap();
        provider
            .frontend
            .run_range(PHASES, Phase::Parsing, Phase::SemanticAnalysis)
            .unwrap();
        provider.finish(3).unwrap();
        assert!(
            matches!(reporter.get_new_message().unwrap(), Message::OverallSuccess { verifier, time: 3 } if verifier == "Viper PAST Constructor")
        );
    }

    #[test]
    fn configured_provider_runs_only_parse_and_semantic_analysis() {
        let phases = SilFrontendPhases::new("test.vpr".into(), SilverPluginManager::new(vec![]));
        let mut provider =
            ViperPAstProvider::new(DefaultFrontend::new(phases), Arc::new(NoopReporter), false);
        provider
            .initialize_configured(&["--ignoreFile".into(), "test.vpr".into()])
            .unwrap();
        assert_eq!(
            provider.frontend.verifier.as_ref().unwrap().name(),
            "Viper PAST Constructor"
        );
        provider
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m(x:Int) { assert x == x }".into())
            })
            .unwrap();
        provider
            .frontend
            .run_range(PHASES, Phase::Parsing, Phase::SemanticAnalysis)
            .unwrap();
        assert!(matches!(
            provider.result().unwrap(),
            VerificationResult::Success
        ));
        assert_eq!(provider.frontend.state, DefaultState::SemanticAnalysis);
        assert!(provider.frontend.program.is_none());
        provider
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m() { assert missing }".into())
            })
            .unwrap();
        provider
            .frontend
            .run_range(PHASES, Phase::Parsing, Phase::SemanticAnalysis)
            .unwrap();
        assert!(
            matches!(provider.result().unwrap(), VerificationResult::Failure(errors) if !errors.is_empty())
        );
    }

    #[test]
    fn disabled_plugins_select_empty_manager_on_each_reset() {
        let phases = SilFrontendPhases::new("test.vpr".into(), SilverPluginManager::new(vec![]));
        let mut provider =
            ViperPAstProvider::new(DefaultFrontend::new(phases), Arc::new(NoopReporter), true);
        provider
            .initialize_configured(&[
                "--ignoreFile".into(),
                "--enableSmokeDetection".into(),
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
        provider.disable_plugins = false;
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
                .contains(&crate::parser::fast_parser::ParserFeature::Unreachable)
        );
    }
}
