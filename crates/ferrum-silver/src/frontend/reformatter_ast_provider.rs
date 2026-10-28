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
//! custom plugin resolution and complete diagnostic compatibility remain pending.

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
/// Failure to execute the concrete parse-only frontend lifecycle.
#[derive(Debug)]
pub enum ReformatterExecuteError {
    Reporter(crate::reporter::reporter::ReportError),
    Setup(super::viper_ast_provider::ProviderSetupError),
    Finish(super::viper_ast_provider::ProviderFinishError),
    PluginReport {
        plugin: crate::plugin::silver_plugin_manager::PluginResolutionError,
        reporter: crate::reporter::reporter::ReportError,
    },
}
impl ReformatterAstProvider<super::sil_frontend::SilFrontendPhases> {
    /// Execute the source frontend preparation, reset, parse, and finish sequence.
    pub fn execute(
        &mut self,
        args: &[String],
        load: impl FnOnce(&std::path::Path) -> std::io::Result<String>,
    ) -> Result<super::sil_frontend::PrepareOutcome, ReformatterExecuteError> {
        use super::{
            sil_frontend::{PrepareOutcome, prepare_frontend},
            viper_ast_provider::{AstProvidingVerifier, ProviderSetupError},
        };
        let started = std::time::Instant::now();
        use crate::verifier::verifier::Verifier;
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
        .map_err(ReformatterExecuteError::Reporter)?;
        let PrepareOutcome::Ready(config) = outcome else {
            return Ok(outcome);
        };
        let file = config.file.clone().ok_or(ReformatterExecuteError::Setup(
            ProviderSetupError::Frontend(FrontendError::MissingInput),
        ))?;
        self.frontend.phases.configure_consistency(&config);
        self.frontend.init(Box::new(verifier));
        self.config = Some(config.clone());
        let mut origin = None;
        if let Err(error) = super::viper_ast_provider::reset_configured_with_origin(
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
                        Some(details) => crate::reporter::message::Message::captured_exception(
                            std::sync::Arc::new(plugin.clone()),
                            details,
                        ),
                        None => crate::reporter::message::Message::exception(std::sync::Arc::new(
                            plugin.clone(),
                        )),
                    };
                    if let Err(reporter) = self.reporter.report(message) {
                        return Err(ReformatterExecuteError::PluginReport { plugin, reporter });
                    }
                    return Ok(PrepareOutcome::PluginSetupFailed);
                }
                other => return Err(ReformatterExecuteError::Setup(other)),
            }
        }
        self.frontend
            .run_range(PHASES, Phase::Parsing, Phase::Parsing)
            .map_err(|error| ReformatterExecuteError::Setup(ProviderSetupError::Frontend(error)))?;
        let elapsed = i64::try_from(started.elapsed().as_millis()).unwrap_or(i64::MAX);
        self.finish(elapsed)
            .map_err(ReformatterExecuteError::Finish)?;
        Ok(PrepareOutcome::Ready(config))
    }
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
        phases.set_phase_reporter(reporter.clone());
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
    fn execute_prints_origin_captured_plugin_exception_to_stdout_reporter() {
        use super::super::sil_frontend::PrepareOutcome;
        use crate::reporter::reporter::StdIoReporter;
        use std::io::Write;
        struct SharedWriter(std::sync::Arc<std::sync::Mutex<Vec<u8>>>);
        impl Write for SharedWriter {
            fn write(&mut self, data: &[u8]) -> std::io::Result<usize> {
                self.0.lock().unwrap().extend_from_slice(data);
                Ok(data.len())
            }
            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        let bytes = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let reporter = std::sync::Arc::new(StdIoReporter::new(SharedWriter(bytes.clone()), false));
        let phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let mut provider = ReformatterAstProvider::with_reporter(phases, reporter);
        let args = vec![
            "--ignoreFile".into(),
            "--disableDefaultPlugins".into(),
            "--plugin".into(),
            "unknown.Plugin".into(),
            "test.vpr".into(),
        ];
        assert!(matches!(
            provider.execute(&args, |_| Ok("".into())).unwrap(),
            PrepareOutcome::PluginSetupFailed
        ));
        let output = String::from_utf8(bytes.lock().unwrap().clone()).unwrap();
        assert!(
            output.contains("Verification aborted exceptionally: Plugin unknown.Plugin not found.")
        );
        assert!(output.contains("Native Rust backtrace (plugin resolution):"));
    }
    #[test]
    fn execute_reports_plugin_exception_and_preserves_reporter_failure() {
        use super::super::sil_frontend::PrepareOutcome;
        use crate::plugin::silver_plugin_manager::PluginResolutionError;
        use crate::reporter::{
            message::{Message, SimpleMessageKind},
            reporter::{NoopReporter, PollingReporter, ReportError, Reporter},
        };
        let args = vec![
            "--ignoreFile".into(),
            "--disableDefaultPlugins".into(),
            "--plugin".into(),
            "unknown.Plugin".into(),
            "test.vpr".into(),
        ];
        let reporter = std::sync::Arc::new(PollingReporter::new(std::sync::Arc::new(NoopReporter)));
        let phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let mut provider = ReformatterAstProvider::with_reporter(phases, reporter.clone());
        assert!(matches!(
            provider
                .execute(&args, |_| Ok("method m() {}".into()))
                .unwrap(),
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
            matches!(reporter.get_new_message().unwrap(), Message::Exception { error, details: Some(details) } if error.to_string() == "Plugin unknown.Plugin not found." && details.stack_trace.contains("Native Rust backtrace (plugin resolution):"))
        );
        assert!(!reporter.has_new_message());
        struct Reject;
        impl Reporter for Reject {
            fn name(&self) -> &str {
                "reject"
            }
            fn report(&self, message: Message) -> Result<(), ReportError> {
                if matches!(message, Message::Exception { .. }) {
                    Err(ReportError::Unsupported("exception"))
                } else {
                    Ok(())
                }
            }
        }
        let phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let mut provider =
            ReformatterAstProvider::with_reporter(phases, std::sync::Arc::new(Reject));
        assert!(
            matches!(provider.execute(&args, |_| Ok("".into())), Err(ReformatterExecuteError::PluginReport { plugin: PluginResolutionError::NotFound(name), reporter: ReportError::Unsupported("exception") }) if name == "unknown.Plugin")
        );
    }
    #[test]
    fn execute_reports_prepare_then_parsing_and_finish_and_handles_early_exits() {
        use super::super::sil_frontend::PrepareOutcome;
        use crate::reporter::{
            message::{Message, SimpleMessageKind},
            reporter::{NoopReporter, PollingReporter},
        };
        let reporter = std::sync::Arc::new(PollingReporter::new(std::sync::Arc::new(NoopReporter)));
        let phases =
            SilFrontendPhases::new(PathBuf::from("test.vpr"), SilverPluginManager::new(vec![]));
        let mut provider = ReformatterAstProvider::with_reporter(phases, reporter.clone());
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
                .execute(&["--unknown".into()], |_| panic!(
                    "load after invalid arguments"
                ))
                .unwrap(),
            PrepareOutcome::InvalidArguments
        ));
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::Simple {
                kind: SimpleMessageKind::Copyright,
                ..
            }
        ));
        assert!(
            matches!(reporter.get_new_message().unwrap(), Message::InvalidArguments { errors, .. } if errors.len() == 1 && errors[0].full_id() == "clioption.error")
        );
        assert!(matches!(
            provider
                .execute(&["--help".into()], |_| panic!("load after help"))
                .unwrap(),
            PrepareOutcome::NothingToDo
        ));
        assert!(matches!(
            reporter.get_new_message().unwrap(),
            Message::Simple {
                kind: SimpleMessageKind::Copyright,
                ..
            }
        ));
        assert!(!reporter.has_new_message());
    }
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
        assert!(
            matches!(reporter.get_new_message().unwrap(), Message::WarningsDuringParsing { warnings } if warnings.is_empty())
        );
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
