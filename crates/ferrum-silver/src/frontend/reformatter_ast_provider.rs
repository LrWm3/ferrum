//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ReformatterAstProvider.scala
//!
//! Purpose:
//! Expose parse-only AST construction for reformatting.
//!
//! Planned Rust structure:
//! Provide ReformatterAstProvider over ViperAstProvider, overriding phase list, parsing and
//! result.
//!
//! Behavior to preserve:
//! Run only parsing with macro expansion disabled; return Success after Parsing when no errors,
//! otherwise Failure.
//!
//! Integration:
//! frontend::viper_ast_provider and parser::fast_parser feed parser::reformat_pretty_printer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on reuse/composition with viper_ast_provider.
//!
//! Status: partial; concrete parse-only provider, macro toggle, AST-constructor verifier and
//! finish reporting, shared configuration and built-in plugin reset are wired. Complete
//! command-line orchestration and custom plugin resolution remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2024 ETH Zurich.

use super::frontend::{DefaultFrontend, DefaultState, FrontendError, FrontendPhases, Phase};
use crate::verifier::verification_result::VerificationResult;

pub const PHASES: &[Phase] = &[Phase::Parsing];
pub struct ReformatterAstProvider<F: FrontendPhases> {
    pub frontend: DefaultFrontend<F>,
    pub reporter: std::sync::Arc<dyn crate::reporter::reporter::Reporter>,
    pub config: Option<super::sil_front_end_config::SilFrontendConfig>,
    pub disable_plugins: bool,
}
impl ReformatterAstProvider<super::sil_frontend::SilFrontendPhases> {
    /// Construct the source parse-only provider with macro expansion disabled.
    pub fn new(phases: super::sil_frontend::SilFrontendPhases) -> Self {
        Self::with_reporter(
            phases,
            std::sync::Arc::new(crate::reporter::reporter::NoopReporter),
        )
    }
    pub fn with_reporter(
        mut phases: super::sil_frontend::SilFrontendPhases,
        reporter: std::sync::Arc<dyn crate::reporter::reporter::Reporter>,
    ) -> Self {
        phases.expand_macros = false;
        Self {
            frontend: DefaultFrontend::new(phases),
            reporter,
            config: None,
            disable_plugins: false,
        }
    }
    /// Configure before initialization, as the source frontend does before reset.
    pub fn initialize_configured(
        &mut self,
        args: &[String],
    ) -> Result<(), super::viper_ast_provider::ProviderSetupError> {
        let (verifier, config) =
            super::viper_ast_provider::configured_verifier(self.reporter.clone(), args)?;
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
    /// Initialize with the inherited AST-construction verifier, which never starts a solver.
    pub fn initialize(&mut self) {
        self.frontend.init(Box::new(
            super::viper_ast_provider::AstProvidingVerifier::new(self.reporter.clone()),
        ));
    }
}
impl<F: FrontendPhases> ReformatterAstProvider<F> {
    /// Emit the inherited AST-construction completion message using this provider's result.
    pub fn finish(&self, time: i64) -> Result<(), super::viper_ast_provider::ProviderFinishError> {
        use super::viper_ast_provider::ProviderFinishError;
        use crate::reporter::message::Message;
        let message = match self.result().map_err(ProviderFinishError::Frontend)? {
            VerificationResult::Success => Message::AstConstructionSuccess { time },
            VerificationResult::Failure(errors) => Message::AstConstructionFailure { time, errors },
        };
        self.reporter
            .report(message)
            .map_err(ProviderFinishError::Reporter)
    }
    pub fn result(&self) -> Result<VerificationResult, FrontendError> {
        if !self.frontend.errors.is_empty() {
            return Ok(VerificationResult::Failure(self.frontend.errors.clone()));
        }
        if self.frontend.state < DefaultState::Parsing {
            return Err(FrontendError::MissingPhaseResult("parsing"));
        }
        Ok(VerificationResult::Success)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::sil_frontend::SilFrontendPhases;
    use crate::parser::reformat_pretty_printer::{LeafReformatAdapter, show_program};
    use crate::plugin::silver_plugin_manager::SilverPluginManager;
    use crate::verifier::verifier::NoVerifier;
    use std::path::PathBuf;

    #[test]
    fn configured_reset_recreates_plugins_and_honors_disable_override() {
        use crate::parser::fast_parser::ParserFeature;
        let phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let mut provider = ReformatterAstProvider::new(phases);
        provider
            .initialize_configured(&[
                "--ignoreFile".into(),
                "--enableSmokeDetection".into(),
                "--disableDefaultPlugins".into(),
                "--respectFunctionPrePermAmounts".into(),
                "--select".into(),
                "m".into(),
                "test.vpr".into(),
            ])
            .unwrap();
        assert!(provider.frontend.phases.respect_function_pre_perm_amounts);
        assert_eq!(provider.frontend.phases.select.as_deref(), Some("m"));
        let input = std::path::Path::new("test.vpr");
        provider
            .reset(input, |_| Ok("method m(){unreachable}".into()))
            .unwrap();
        assert!(
            provider
                .frontend
                .phases
                .plugins
                .parser_features()
                .contains(&ParserFeature::Unreachable)
        );
        provider.frontend.run_phase(Phase::Parsing).unwrap();
        assert!(matches!(
            provider.result().unwrap(),
            VerificationResult::Success
        ));
        provider.disable_plugins = true;
        provider
            .reset(input, |_| Ok("method m(){unreachable}".into()))
            .unwrap();
        assert!(
            provider
                .frontend
                .phases
                .plugins
                .parser_features()
                .is_empty()
        );
        provider.frontend.run_phase(Phase::Parsing).unwrap();
        assert!(matches!(
            provider.result().unwrap(),
            VerificationResult::Success
        ));
        provider.disable_plugins = false;
        provider
            .reset(input, |_| Ok("method m(){unreachable}".into()))
            .unwrap();
        provider.frontend.run_phase(Phase::Parsing).unwrap();
        assert!(matches!(
            provider.result().unwrap(),
            VerificationResult::Success
        ));
    }

    #[test]
    fn configuration_failure_precedes_initialization_and_plugin_reset() {
        use super::super::viper_ast_provider::ProviderSetupError;
        let phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let mut provider = ReformatterAstProvider::new(phases);
        assert!(matches!(
            provider.initialize_configured(&["--bogus".into()]),
            Err(ProviderSetupError::Configuration(_))
        ));
        assert_eq!(provider.frontend.state, DefaultState::Initial);
        assert!(matches!(
            provider.initialize_configured(&["--help".into()]),
            Err(ProviderSetupError::ExitRequested)
        ));
        provider
            .initialize_configured(&[
                "--ignoreFile".into(),
                "--plugin".into(),
                "unknown.Plugin".into(),
                "test.vpr".into(),
            ])
            .unwrap();
        assert!(matches!(
            provider.reset(std::path::Path::new("test.vpr"), |_| Ok("".into())),
            Err(ProviderSetupError::Plugin(_))
        ));
        assert_eq!(provider.frontend.state, DefaultState::InputSet);
    }

    #[test]
    fn inherited_verifier_and_finish_report_success_and_failure() {
        use crate::reporter::{
            message::Message,
            reporter::{NoopReporter, PollingReporter},
        };
        use std::sync::Arc;
        let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
        let phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let mut provider = ReformatterAstProvider::with_reporter(phases, reporter.clone());
        assert!(provider.finish(1).is_err());
        assert!(!reporter.has_new_message());
        provider.initialize();
        let verifier = provider.frontend.verifier.as_mut().unwrap();
        assert_eq!(verifier.name(), "Viper AST Constructor");
        assert_eq!(verifier.signature(), "Viper AST Constructor");
        let program = crate::ast::program::Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Default::default(),
        );
        assert!(matches!(
            verifier.verify(&program).unwrap(),
            VerificationResult::Success
        ));
        provider
            .frontend
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m() {}".into())
            })
            .unwrap();
        provider
            .frontend
            .run_range(PHASES, Phase::Parsing, Phase::Parsing)
            .unwrap();
        provider.finish(12).unwrap();
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::AstConstructionSuccess { time: 12 }
        ));
        provider
            .frontend
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m( {".into())
            })
            .unwrap();
        provider.frontend.run_phase(Phase::Parsing).unwrap();
        provider.finish(34).unwrap();
        assert!(
            matches!(reporter.get_new_message().unwrap(), Message::AstConstructionFailure { time: 34, errors } if !errors.is_empty())
        );
        assert!(!reporter.has_new_message());
    }

    #[test]
    fn default_parser_expands_macros_and_reformatter_uses_plugins() {
        use crate::plugin::standard::smoke::smoke_detection_plugin::SmokeDetectionPlugin;
        let source = "define p(x) x + 1\nmethod m(){assert p(1)==2}\n";
        let mut standard =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let expanded = standard.parse(source).unwrap();
        let text = show_program(expanded.node(), &LeafReformatAdapter).unwrap();
        assert!(!text.contains("p(1)"));

        let phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            SilverPluginManager::new(vec![Box::new(SmokeDetectionPlugin)]),
        );
        let mut provider = ReformatterAstProvider::new(phases);
        provider.frontend.init(Box::new(NoVerifier::default()));
        provider
            .frontend
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m(){unreachable}".into())
            })
            .unwrap();
        provider.frontend.run_phase(Phase::Parsing).unwrap();
        assert!(matches!(
            provider.result().unwrap(),
            VerificationResult::Success
        ));
        assert_eq!(
            show_program(
                provider.frontend.parsing_result.as_ref().unwrap().node(),
                &LeafReformatAdapter
            )
            .unwrap(),
            "method m() {\n    unreachable\n}"
        );
    }

    #[test]
    fn concrete_provider_retains_macros_and_reports_parse_errors() {
        let phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let mut provider = ReformatterAstProvider::new(phases);
        provider.frontend.init(Box::new(NoVerifier::default()));
        let source = "define p(x) x + 1\nmethod m(){assert p(1)==2}\n";
        provider
            .frontend
            .reset(std::path::Path::new("test.vpr"), |_| Ok(source.to_owned()))
            .unwrap();
        provider.frontend.run_phase(Phase::Parsing).unwrap();
        assert!(matches!(
            provider.result().unwrap(),
            VerificationResult::Success
        ));
        let parsed = provider.frontend.parsing_result.as_ref().unwrap();
        assert_eq!(
            show_program(parsed.node(), &LeafReformatAdapter).unwrap(),
            "define p(x) x + 1\nmethod m() {\n    assert p(1) == 2\n}\n"
        );
        provider
            .frontend
            .reset(std::path::Path::new("test.vpr"), |_| {
                Ok("method m( {".into())
            })
            .unwrap();
        provider.frontend.run_phase(Phase::Parsing).unwrap();
        assert!(matches!(
            provider.result().unwrap(),
            VerificationResult::Failure(_)
        ));
    }
}
