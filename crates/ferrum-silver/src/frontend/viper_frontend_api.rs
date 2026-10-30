//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ViperFrontendAPI.scala
//!
//! Purpose:
//! Accept constructed Silver programs through a reusable frontend and plugin pipeline.
//!
//! Planned Rust structure:
//! Represent ViperFrontendAPI and MinimalViperFrontendAPI with initialize, verify, stop and
//! starting-state override.
//!
//! Behavior to preserve:
//! Initialize builds/configures verifier with ignoreFile and dummy filename, resets plugins;
//! verify and stop require initialization. Preserve upstream starting state and phase lists,
//! including Minimal’s verification-only path. The base API sets state to ConsistencyCheck
//! before running phases; DefaultFrontend.consistencyCheck only runs at Translation, so its
//! listed consistency phase is skipped in this call path. Verification still runs, including
//! plugin filtering. SiliconFrontendAPI supplies no override of this state or phase method.
//!
//! Integration:
//! frontend::sil_frontend, ast::program, plugin manager and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Reconcile repeated-call state/reset and the apparent skipped consistency check with
//! frontend::frontend, SiliconFrontendAPI and PLAN.md; record any deliberate correction.
//!
//! Status: partial; configured backend factory, built-in/custom plugin reset and injected
//! program phase execution are connected. Full backend construction remains caller supplied.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::frontend::{DefaultFrontend, DefaultState, FrontendError, FrontendPhases, Phase};
use super::sil_front_end_config::SilFrontendConfig;
use crate::ast::program::Program;
use crate::verifier::verification_result::VerificationResult;
use crate::verifier::verifier::Verifier;

pub const DUMMY_INPUT_FILENAME: &str =
    "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver";
pub const PHASES: &[Phase] = &[Phase::ConsistencyCheck, Phase::Verification];
pub const MINIMAL_PHASES: &[Phase] = &[Phase::Verification];

/// Frontends using this API inject an already constructed program. The concrete Silver
/// initializer accepts a backend factory and installs configured plugins.
pub struct ViperFrontendApi<F: FrontendPhases> {
    pub frontend: DefaultFrontend<F>,
    pub config: Option<SilFrontendConfig>,
    pub minimal: bool,
    initialized: bool,
}
/// Failure while configuring the injected-AST frontend.
#[derive(Debug)]
pub enum FrontendApiInitError {
    Backend(String),
    Configuration(String),
    ExitRequested,
    Plugin(crate::plugin::silver_plugin_manager::PluginResolutionError),
    Reporter(crate::reporter::reporter::ReportError),
}

impl ViperFrontendApi<super::sil_frontend::SilFrontendPhases> {
    /// Construct and configure the backend exactly once, then install the configured plugins.
    /// The factory receives the original arguments for verifier construction and the augmented
    /// arguments for backend configuration; it returns that verifier's effective Silver config.
    pub fn initialize_with_factory(
        &mut self,
        args: &[String],
        reporter: &dyn crate::reporter::reporter::Reporter,
        factory: impl FnOnce(
            &[String],
            &[String],
        ) -> Result<(Box<dyn Verifier>, SilFrontendConfig), String>,
        resolver: impl FnMut(
            &str,
        ) -> Result<
            Option<Box<dyn crate::plugin::silver_plugin::SilverPlugin>>,
            crate::plugin::silver_plugin_manager::PluginResolutionError,
        >,
    ) -> Result<(), FrontendApiInitError> {
        let mut complete_args = args.to_vec();
        complete_args.push("--ignoreFile".into());
        complete_args.push(DUMMY_INPUT_FILENAME.into());
        let (verifier, config) =
            factory(args, &complete_args).map_err(FrontendApiInitError::Backend)?;
        if let Some(error) = &config.error {
            return Err(FrontendApiInitError::Configuration(error.clone()));
        }
        if config.exit() {
            return Err(FrontendApiInitError::ExitRequested);
        }
        super::sil_frontend::report_configured_plugin_warnings(&config, reporter)
            .map_err(FrontendApiInitError::Reporter)?;
        let plugins = super::sil_frontend::standard_plugin_manager_with_resolver(&config, resolver)
            .map_err(FrontendApiInitError::Plugin)?;
        reporter
            .bind_plugin_manager(&plugins)
            .map_err(FrontendApiInitError::Reporter)?;
        self.frontend.phases.configure_consistency(&config);
        self.frontend.phases.plugins = plugins;
        self.frontend.init(verifier);
        self.config = Some(config);
        self.initialized = true;
        Ok(())
    }
}
impl<F: FrontendPhases> ViperFrontendApi<F> {
    pub fn new(frontend: DefaultFrontend<F>, minimal: bool) -> Self {
        Self {
            frontend,
            config: None,
            minimal,
            initialized: false,
        }
    }
    /// Compatibility initializer for callers which supply their own plugin reset.
    /// Backend-specific options require `initialize_with_factory` instead.
    pub fn initialize(
        &mut self,
        mut verifier: Box<dyn Verifier>,
        args: &[String],
        reset_plugins: impl FnOnce(&SilFrontendConfig),
    ) -> Result<(), String> {
        let mut complete_args = args.to_vec();
        complete_args.push("--ignoreFile".into());
        complete_args.push(DUMMY_INPUT_FILENAME.into());
        verifier.parse_command_line(&complete_args);
        let config = SilFrontendConfig::parse_shared(verifier.name(), &complete_args);
        if let Some(error) = &config.error {
            return Err(error.clone());
        }
        if config.exit() {
            return Err("frontend configuration requested exit".into());
        }
        self.frontend.init(verifier);
        reset_plugins(&config);
        self.config = Some(config);
        self.initialized = true;
        Ok(())
    }
    pub fn verify(&mut self, program: Program) -> Result<VerificationResult, FrontendError> {
        if !self.initialized {
            return Err(FrontendError::NotInitialized);
        }
        // Upstream starts at ConsistencyCheck, so its consistency phase is a no-op
        // even in the non-minimal variant; verification is then run.
        self.frontend.state = DefaultState::ConsistencyCheck;
        self.frontend.program = Some(program);
        let phases = if self.minimal { MINIMAL_PHASES } else { PHASES };
        self.frontend
            .run_range(phases, phases[0], *phases.last().expect("API phases"))?;
        self.frontend.result()
    }
    pub fn stop(&mut self) -> Result<(), FrontendError> {
        if !self.initialized {
            return Err(FrontendError::NotInitialized);
        }
        if let Some(verifier) = self.frontend.verifier.as_mut() {
            verifier.try_stop().map_err(FrontendError::Verifier)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::components::components::LifetimeComponent;
    use crate::frontend::sil_frontend::SilFrontendPhases;
    use crate::plugin::{
        silver_plugin::{PluginHookError, SilverPlugin},
        silver_plugin_manager::SilverPluginManager,
    };
    use crate::reporter::reporter::{NoopReporter, Reporter};
    use crate::verifier::verifier::{Dependency, VerifierError};
    use std::{
        any::Any,
        sync::{
            Arc,
            atomic::{AtomicUsize, Ordering},
        },
    };

    struct StubVerifier {
        calls: Arc<AtomicUsize>,
        stopped: Arc<AtomicUsize>,
        configured: Arc<AtomicUsize>,
        reporter: NoopReporter,
    }
    impl LifetimeComponent for StubVerifier {
        fn start(&mut self) {}
        fn stop(&mut self) {
            self.stopped.fetch_add(1, Ordering::SeqCst);
        }
    }
    impl Verifier for StubVerifier {
        fn name(&self) -> &str {
            "stub"
        }
        fn version(&self) -> &str {
            ""
        }
        fn build_version(&self) -> &str {
            ""
        }
        fn copyright(&self) -> &str {
            ""
        }
        fn debug_info(&mut self, _: Vec<(String, Box<dyn Any + Send + Sync>)>) {}
        fn dependencies(&self) -> Vec<&dyn Dependency> {
            vec![]
        }
        fn parse_command_line(&mut self, args: &[String]) {
            assert!(args.iter().any(|a| a == "--backend-option"));
            self.configured.fetch_add(1, Ordering::SeqCst);
        }
        fn verify(&mut self, _: &Program) -> Result<VerificationResult, VerifierError> {
            self.calls.fetch_add(1, Ordering::SeqCst);
            Ok(VerificationResult::Success)
        }
        fn reporter(&self) -> &dyn Reporter {
            &self.reporter
        }
    }
    struct HookPlugin(Arc<AtomicUsize>);
    impl SilverPlugin for HookPlugin {
        fn before_verify(&mut self, program: Program) -> Result<Program, PluginHookError> {
            self.0.fetch_add(1, Ordering::SeqCst);
            Ok(program)
        }
    }
    fn empty_program() -> Program {
        Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Default::default(),
        )
    }
    #[test]
    fn configured_backend_and_plugins_verify_repeated_injected_programs() {
        let phases = SilFrontendPhases::new("unused.vpr".into(), SilverPluginManager::new(vec![]));
        let mut api = ViperFrontendApi::new(DefaultFrontend::new(phases), false);
        assert!(matches!(
            api.verify(empty_program()),
            Err(FrontendError::NotInitialized)
        ));
        let calls = Arc::new(AtomicUsize::new(0));
        let stopped = Arc::new(AtomicUsize::new(0));
        let configured = Arc::new(AtomicUsize::new(0));
        let plugin_calls = Arc::new(AtomicUsize::new(0));
        let args = vec![
            "--backend-option".into(),
            "--disableDefaultPlugins".into(),
            "--plugin".into(),
            "custom.Plugin".into(),
        ];
        api.initialize_with_factory(
            &args,
            &NoopReporter,
            |original, complete| {
                assert_eq!(original, args);
                assert_eq!(
                    &complete[complete.len() - 2..],
                    &["--ignoreFile", DUMMY_INPUT_FILENAME]
                );
                let mut verifier = StubVerifier {
                    calls: calls.clone(),
                    stopped: stopped.clone(),
                    configured: configured.clone(),
                    reporter: NoopReporter,
                };
                verifier.parse_command_line(complete);
                let shared = complete
                    .iter()
                    .filter(|arg| arg.as_str() != "--backend-option")
                    .cloned()
                    .collect::<Vec<_>>();
                Ok((
                    Box::new(verifier),
                    SilFrontendConfig::parse_shared("backend", &shared),
                ))
            },
            |name| {
                Ok((name == "custom.Plugin")
                    .then(|| Box::new(HookPlugin(plugin_calls.clone())) as Box<dyn SilverPlugin>))
            },
        )
        .unwrap();
        assert_eq!(configured.load(Ordering::SeqCst), 1);
        for _ in 0..2 {
            assert!(matches!(
                api.verify(empty_program()).unwrap(),
                VerificationResult::Success
            ));
        }
        assert_eq!(calls.load(Ordering::SeqCst), 2);
        assert_eq!(plugin_calls.load(Ordering::SeqCst), 2);
        api.stop().unwrap();
        assert_eq!(stopped.load(Ordering::SeqCst), 1);
    }
    #[test]
    fn plugin_preparation_failure_does_not_call_verifier() {
        struct Reject;
        impl SilverPlugin for Reject {
            fn before_verify(&mut self, _: Program) -> Result<Program, PluginHookError> {
                Err(PluginHookError("rejected".into()))
            }
        }
        let phases = SilFrontendPhases::new("unused.vpr".into(), SilverPluginManager::new(vec![]));
        let mut api = ViperFrontendApi::new(DefaultFrontend::new(phases), false);
        let calls = Arc::new(AtomicUsize::new(0));
        api.initialize_with_factory(
            &[],
            &NoopReporter,
            |_, complete| {
                let mut config = SilFrontendConfig::parse_shared("backend", complete);
                config.disable_default_plugins = true;
                config.plugin = Some("custom.Reject".into());
                Ok((
                    Box::new(StubVerifier {
                        calls: calls.clone(),
                        stopped: Arc::new(AtomicUsize::new(0)),
                        configured: Arc::new(AtomicUsize::new(0)),
                        reporter: NoopReporter,
                    }),
                    config,
                ))
            },
            |name| Ok((name == "custom.Reject").then(|| Box::new(Reject) as Box<dyn SilverPlugin>)),
        )
        .unwrap();
        assert!(
            matches!(api.verify(empty_program()).unwrap(), VerificationResult::Failure(errors) if !errors.is_empty())
        );
        assert_eq!(calls.load(Ordering::SeqCst), 0);
        // Source verify does not clear accumulated frontend errors between calls.
        api.frontend.phases.plugins = SilverPluginManager::new(vec![]);
        assert!(
            matches!(api.verify(empty_program()).unwrap(), VerificationResult::Failure(errors) if !errors.is_empty())
        );
        assert_eq!(calls.load(Ordering::SeqCst), 0);
    }

    #[test]
    fn stop_propagates_backend_cleanup_error() {
        struct StopFailure(NoopReporter);
        impl LifetimeComponent for StopFailure {
            fn start(&mut self) {}
            fn stop(&mut self) {}
        }
        impl Verifier for StopFailure {
            fn name(&self) -> &str {
                "test"
            }
            fn version(&self) -> &str {
                ""
            }
            fn build_version(&self) -> &str {
                ""
            }
            fn copyright(&self) -> &str {
                ""
            }
            fn debug_info(&mut self, _: Vec<(String, Box<dyn Any + Send + Sync>)>) {}
            fn dependencies(&self) -> Vec<&dyn Dependency> {
                vec![]
            }
            fn parse_command_line(&mut self, _: &[String]) {}
            fn verify(&mut self, _: &Program) -> Result<VerificationResult, VerifierError> {
                Ok(VerificationResult::Success)
            }
            fn reporter(&self) -> &dyn Reporter {
                &self.0
            }
            fn try_stop(&mut self) -> Result<(), VerifierError> {
                Err(VerifierError::Backend("stop failed".into()))
            }
        }
        let phases = SilFrontendPhases::new("unused.vpr".into(), SilverPluginManager::new(vec![]));
        let mut api = ViperFrontendApi::new(DefaultFrontend::new(phases), false);
        api.frontend.init(Box::new(StopFailure(NoopReporter)));
        api.initialized = true;
        assert!(
            matches!(api.stop(), Err(FrontendError::Verifier(VerifierError::Backend(message))) if message == "stop failed")
        );
    }

    #[test]
    fn injected_start_state_skips_consistency_in_both_phase_lists() {
        use crate::verifier::verification_result::AbstractError;
        struct Phases;
        impl FrontendPhases for Phases {
            type Parsed = ();
            type Analyzed = ();
            fn parse(&mut self, _: &str) -> Result<(), Vec<AbstractError>> {
                unreachable!()
            }
            fn analyze(&mut self, _: ()) -> Result<(), Vec<AbstractError>> {
                unreachable!()
            }
            fn translate(&mut self, _: ()) -> Result<Program, Vec<AbstractError>> {
                unreachable!()
            }
            fn check_consistency(&mut self, _: Program) -> Result<Program, Vec<AbstractError>> {
                panic!("source starting state skips consistency")
            }
            fn reset_messages(&mut self) {}
        }
        for minimal in [false, true] {
            let calls = Arc::new(AtomicUsize::new(0));
            let verifier = StubVerifier {
                calls: calls.clone(),
                stopped: Arc::new(AtomicUsize::new(0)),
                configured: Arc::new(AtomicUsize::new(0)),
                reporter: NoopReporter,
            };
            let mut api = ViperFrontendApi::new(DefaultFrontend::new(Phases), minimal);
            api.frontend.init(Box::new(verifier));
            api.initialized = true;
            assert!(matches!(
                api.verify(empty_program()).unwrap(),
                VerificationResult::Success
            ));
            assert_eq!(calls.load(Ordering::SeqCst), 1);
        }
    }

    #[test]
    fn failed_plugin_resolution_does_not_initialize_frontend() {
        let phases = SilFrontendPhases::new("unused.vpr".into(), SilverPluginManager::new(vec![]));
        let mut api = ViperFrontendApi::new(DefaultFrontend::new(phases), true);
        let result = api.initialize_with_factory(
            &[],
            &NoopReporter,
            |_, complete| {
                let mut config = SilFrontendConfig::parse_shared("backend", complete);
                config.disable_default_plugins = true;
                config.plugin = Some("unknown.Plugin".into());
                Ok((
                    Box::new(crate::verifier::verifier::NoVerifier::default()),
                    config,
                ))
            },
            |_| Ok(None),
        );
        assert!(matches!(result, Err(FrontendApiInitError::Plugin(_))));
        assert!(matches!(api.stop(), Err(FrontendError::NotInitialized)));
    }
}
