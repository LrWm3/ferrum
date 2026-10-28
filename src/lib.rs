//! Upstream:
//! Ferrum-owned assembly described in PLAN.md; this file has no one-to-one Scala counterpart.
//! Backend and embedding reference:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Silicon.scala
//!
//! Purpose:
//! Expose the native verification library used by the CLI and a future Prusti adapter.
//!
//! Planned Rust structure:
//! Re-export selected Silver program, diagnostic and verification-result types. Provide a thin
//! configuration/session facade over ferrum_silicon::silicon and its frontend APIs, with entry
//! paths for source input and already constructed programs. Keep verification rules in Silicon.
//!
//! Behavior to preserve:
//! Retain configure/start/verify/reset/stop lifecycle boundaries, reporter delivery and failure
//! distinctions. Source inputs run the translated frontend phases; constructed AST inputs use
//! the embedding path. Reconcile that path's upstream skipped frontend consistency phase with
//! Silicon's own consistency checks before defining a public guarantee. Library calls return
//! results and diagnostics; process exit belongs to the CLI.
//!
//! Integration:
//! ferrum_silver::{ast,frontend,verifier,reporter}, ferrum_silicon::{silicon,config,verifier},
//! and src/main.rs. A Prusti adapter consumes this facade without rustc_private in these crates.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for explicit session ownership and lifecycle cleanup. Public
//! signatures, cancellation and borrowing of programs/reporters remain provisional.
//!
//! Open decisions:
//! Agree on source-versus-AST entry APIs, repeated-run reset, cancellation and error ownership
//! with both crate roots and backend orchestration. Do not duplicate configuration translation.
//!
//! Status: native frontend/backend assembly; unsupported runtime services remain errors.

/// Symbolic execution backend modules under active translation.
pub use ferrum_silicon as silicon;
/// Shared language infrastructure for callers constructing a Silver program.
pub use ferrum_silver as silver;

use silicon::{
    config::Config,
    decider::{
        decider::DefaultDecider,
        prover_std_io::{ProverEvent, ProverStdIo},
    },
    interfaces::verification::{ResultKind, VerificationResult as SiliconResult},
    silicon::{Silicon, SiliconBackend, SiliconOutcome},
    state::terms::{TermFactory, TermOptions},
    verifier::{
        base_verifier::BaseVerifier,
        native_context::{NativeContext, NativeFunctionData, NativeOptions, NativeVerifierContext},
    },
};
use silver::{
    ast::{
        program::Program,
        utility::nodes::{Node, TraversalError},
    },
    cfg::silver::silver_cfg::SilverCfg,
    frontend::{
        frontend::FrontendPhases,
        sil_frontend::{SilFrontendPhases, standard_plugin_manager},
    },
    verifier::{
        verification_error::{
            NativeErrorNodeRenderer, RenderedVerificationError, VerificationError,
        },
        verification_result::{AbstractError, VerificationResult},
    },
};
use std::{
    path::Path,
    sync::{Arc, Mutex},
};

#[derive(Debug)]
pub enum FerrumError {
    Configuration(String),
    Input(std::io::Error),
    Diagnostics(Vec<AbstractError>),
    Execution(String),
    Cleanup {
        primary: Box<FerrumError>,
        cleanup: Box<FerrumError>,
    },
}
impl std::fmt::Display for FerrumError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Configuration(message) | Self::Execution(message) => f.write_str(message),
            Self::Input(error) => write!(f, "{error}"),
            Self::Diagnostics(errors) => {
                for (i, error) in errors.iter().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "{}", error.render().unwrap_or_else(|_| error.full_id()))?;
                }
                Ok(())
            }
            Self::Cleanup { primary, cleanup } => {
                write!(f, "{primary}; solver cleanup also failed: {cleanup}")
            }
        }
    }
}
impl std::error::Error for FerrumError {}
fn execution(error: impl std::fmt::Debug) -> FerrumError {
    FerrumError::Execution(format!("{error:?}"))
}
fn diagnostic(error: VerificationError) -> Result<AbstractError, FerrumError> {
    RenderedVerificationError::new(error, Arc::new(NativeErrorNodeRenderer))
        .map(|e| AbstractError::Verification(Arc::new(e)))
        .map_err(execution)
}
fn final_result(errors: Vec<AbstractError>) -> VerificationResult {
    if errors.is_empty() {
        VerificationResult::Success
    } else {
        VerificationResult::Failure(errors)
    }
}

/// SilFrontend.finish groups failures by the transformed readable message,
/// retaining the first occurrence and preserving source order.
fn distinct_failures(result: VerificationResult) -> Result<VerificationResult, FerrumError> {
    let VerificationResult::Failure(errors) = result else {
        return Ok(result);
    };
    let mut seen = std::collections::HashSet::new();
    let mut distinct = Vec::new();
    for error in errors {
        let key = error
            .transformed_error()
            .and_then(|error| error.readable_message())
            .map_err(execution)?;
        if seen.insert(key) {
            distinct.push(error);
        }
    }
    Ok(VerificationResult::Failure(distinct))
}

type ExecutingContext<P> = NativeVerifierContext<
    P,
    silicon::supporters::predicate_verification_unit::PredicateData,
    NativeFunctionData,
>;

enum OwnedContext {
    Stdio(Box<NativeContext>),
    #[cfg(feature = "native-z3")]
    Api(Box<ExecutingContext<silicon::decider::native_z3::LinkedZ3Prover>>),
}
impl OwnedContext {
    fn verify_program(
        &mut self,
        program: &Program,
        cfgs: &[SilverCfg],
    ) -> Result<Vec<SiliconResult<VerificationError>>, FerrumError> {
        match self {
            Self::Stdio(context) => context.verify_program(program, cfgs).map_err(execution),
            #[cfg(feature = "native-z3")]
            Self::Api(context) => context.verify_program(program, cfgs).map_err(execution),
        }
    }
    fn stop(&mut self) -> Result<(), FerrumError> {
        match self {
            Self::Stdio(context) => context.stop().map_err(execution),
            #[cfg(feature = "native-z3")]
            Self::Api(context) => context.stop().map_err(execution),
        }
    }
    fn warnings(&mut self) -> &mut Vec<String> {
        match self {
            Self::Stdio(context) => &mut context.warnings,
            #[cfg(feature = "native-z3")]
            Self::Api(context) => &mut context.warnings,
        }
    }
}

fn start_context<P: silicon::interfaces::decider::prover::Prover>(
    prover: P,
    identifiers: silicon::state::identifiers::DefaultIdentifierFactory,
    config: &Config,
    factory: TermFactory,
    options: NativeOptions,
) -> Result<ExecutingContext<P>, FerrumError>
where
    P::Error: std::fmt::Debug,
{
    let decider = DefaultDecider::new(
        prover,
        config.enable_debugging,
        config.assert_timeout,
        Some(config.check_timeout),
        Some(config.push_timeout),
    );
    let base = BaseVerifier::new_with_identifiers(
        "main".into(),
        decider,
        factory.clone(),
        config.mask_heap_mode,
        config.state_consolidation_mode,
        identifiers,
    );
    let mut context = ExecutingContext::new(base, factory, options);
    // The API adapter receives typed startup options in its constructor. Stdio
    // transports receive the same configuration as SMT-LIB settings instead.
    let settings: Vec<_> = if config.prover == "Z3-API" {
        Vec::new()
    } else {
        config
            .prover_config_args
            .iter()
            .map(|(key, value)| format!("(set-option :{key} {value})"))
            .collect()
    };
    context
        .start(config.prover_args.as_deref(), &settings)
        .map_err(execution)?;
    Ok(context)
}

struct NativeBackend {
    config: Config,
    context: Option<OwnedContext>,
    recorded_source: Option<String>,
    warnings: Arc<Mutex<Vec<String>>>,
}
impl NativeBackend {
    fn new(config: Config) -> Self {
        Self {
            config,
            context: None,
            recorded_source: None,
            warnings: Arc::new(Mutex::new(Vec::new())),
        }
    }
}
impl SiliconBackend for NativeBackend {
    type Error = FerrumError;
    type Output = VerificationResult;
    fn configure(&mut self, args: &[String]) -> Result<(), FerrumError> {
        if !args.is_empty() {
            self.config =
                Config::parse(args).map_err(|e| FerrumError::Configuration(e.to_string()))?;
        }
        self.config
            .validate()
            .map_err(|e| FerrumError::Configuration(e.to_string()))
    }
    fn start(&mut self) -> Result<(), FerrumError> {
        let config = &self.config;
        let options = NativeOptions::from_config(config).map_err(execution)?;
        let factory = TermFactory::new(TermOptions {
            use_flyweight: config.use_flyweight(),
            use_old_axiomatization: config.use_old_axiomatization,
            mask_heap_mode: config.mask_heap_mode,
        });
        if config.prover == "Z3-API" {
            #[cfg(not(feature = "native-z3"))]
            return Err(FerrumError::Configuration(
                "Z3-API requires a build with --features native-z3 and libz3 4.16.0".into(),
            ));
            #[cfg(feature = "native-z3")]
            {
                use silicon::decider::{
                    native_z3::{LinkedProverOptions, LinkedZ3, LinkedZ3Prover},
                    z3_prover_api::ApiTimeoutSettings,
                };
                if config.output_prover_log() {
                    return Err(FerrumError::Configuration(
                        "Z3-API prover logging is not yet connected".into(),
                    ));
                }
                let version = LinkedZ3::library_version();
                if version != (4, 16, 0, 0) {
                    return Err(FerrumError::Configuration(format!(
                        "Z3-API requires the pinned libz3 4.16.0.0; linked library is {}.{}.{}.{}",
                        version.0, version.1, version.2, version.3
                    )));
                }
                let prover = LinkedZ3Prover::new(
                    "main",
                    factory.clone(),
                    LinkedProverOptions {
                        timeout: ApiTimeoutSettings {
                            default_timeout_ms: config
                                .prover_timeout()
                                .map_err(|e| FerrumError::Configuration(e.to_string()))?,
                            use_time_bounds: config.prover_enable_time_bounds,
                            resources_per_millisecond: config.z3_resources_per_millisecond,
                        },
                        counterexamples: config.frontend.counterexample.is_some(),
                        report_reason_unknown: config.report_reason_unknown,
                        debug: config.enable_debugging,
                        custom_options: config
                            .prover_config_args
                            .iter()
                            .map(|(key, value)| (key.clone(), value.clone()))
                            .collect(),
                        disable_nonlinear: config.disable_nl,
                        soft_assertions: config.assertion_mode
                            == silicon::config::AssertionMode::SoftConstraints,
                    },
                );
                let identifiers = prover.identifier_factory();
                self.context = Some(OwnedContext::Api(Box::new(start_context(
                    prover,
                    identifiers,
                    config,
                    factory,
                    options,
                )?)));
                return Ok(());
            }
        }
        let settings = config
            .prover_settings("main")
            .map_err(|e| FerrumError::Configuration(e.to_string()))?;
        let profile = match config.prover.as_str() {
            "Z3" => silicon::decider::z3_prover_std_io::profile(),
            "cvc5" => silicon::decider::cvc5_prover_std_io::profile(),
            name => {
                return Err(FerrumError::Configuration(format!(
                    "Unsupported native solver transport {name}"
                )));
            }
        };
        let warnings = self.warnings.clone();
        let prover = ProverStdIo::new(
            "main".into(),
            settings,
            profile,
            factory.clone(),
            move |event| {
                if let ProverEvent::Warning(warning) = event {
                    warnings
                        .lock()
                        .expect("poisoned warning buffer")
                        .push(warning);
                }
            },
        );
        let identifiers = prover.identifier_factory();
        self.context = Some(OwnedContext::Stdio(Box::new(start_context(
            prover,
            identifiers,
            config,
            factory,
            options,
        )?)));
        Ok(())
    }
    fn reset(&mut self) -> Result<(), FerrumError> {
        // Recreate the owned native context so declarations, path conditions,
        // counters and source preambles all belong to the new verification run.
        self.stop()?;
        self.start()
    }
    fn stop(&mut self) -> Result<(), FerrumError> {
        if let Some(mut context) = self.context.take() {
            self.warnings
                .lock()
                .expect("poisoned warning buffer")
                .append(context.warnings());
            context.stop()?;
        }
        Ok(())
    }
    fn input_file(&self) -> Option<&str> {
        self.config.frontend.file.as_deref()
    }
    fn ignore_file(&self) -> bool {
        self.config.frontend.ignore_file
    }
    fn set_recorded_source(&mut self, file: Option<&str>) {
        self.recorded_source = file.map(str::to_owned);
    }
    fn render_node(&self, node: &Node) -> Result<String, TraversalError> {
        silver::ast::pretty::pretty_printer::pretty_node(node)
            .map_err(|_| TraversalError::Extension("native AST rendering"))
    }
    fn run(
        &mut self,
        program: &Program,
        cfgs: &[SilverCfg],
        _file: Option<&str>,
    ) -> Result<VerificationResult, FerrumError> {
        let context = self
            .context
            .as_mut()
            .ok_or_else(|| FerrumError::Execution("Native solver has not been started".into()))?;
        let results = context.verify_program(program, cfgs);
        self.warnings
            .lock()
            .expect("poisoned warning buffer")
            .append(context.warnings());
        let results: Vec<SiliconResult<VerificationError>> = results?;
        // Main verification already flattens each member's predecessor results.
        // Silicon.runVerifier selects only failures and sorts on transformed position.
        let mut errors = Vec::new();
        for result in results {
            if let Some(error) = result.with_kind(|kind| match kind {
                ResultKind::Failure(e) => Some(e.clone()),
                _ => None,
            }) {
                let error = diagnostic(error)?;
                let transformed = error.transformed_error().map_err(execution)?;
                let position = transformed.position();
                let key = position
                    .line_column()
                    .map_or((-1, -1), |p| (p.line(), p.column()));
                errors.push((key, error));
            }
        }
        errors.sort_by_key(|(key, _)| *key);
        Ok(final_result(
            errors.into_iter().map(|(_, error)| error).collect(),
        ))
    }
}

/// An owned solver session for native Silver programs, including repeated runs.
/// AST clients bypass frontend plugins but retain Silicon's mandatory consistency check.
pub struct Session {
    silicon: Silicon<NativeBackend>,
}
impl Session {
    pub fn new(config: Config) -> Result<Self, FerrumError> {
        let mut silicon = Silicon::new(NativeBackend::new(config));
        silicon.configure(&[]).map_err(execution)?;
        silicon.start().map_err(execution)?;
        Ok(Self { silicon })
    }
    pub fn verify(
        &mut self,
        program: &Program,
        cfgs: &[SilverCfg],
    ) -> Result<VerificationResult, FerrumError> {
        match self.silicon.verify(program, cfgs).map_err(execution)? {
            SiliconOutcome::BackendResult(result) => Ok(result),
            SiliconOutcome::ConsistencyFailures(errors) => Ok(final_result(
                errors
                    .into_iter()
                    .map(diagnostic)
                    .collect::<Result<_, _>>()?,
            )),
        }
    }
    pub fn stop(&mut self) -> Result<(), FerrumError> {
        self.silicon.stop().map_err(execution)
    }
    /// Drain solver and verifier warnings, including warnings from a failed run.
    pub fn take_warnings(&mut self) -> Vec<String> {
        std::mem::take(
            &mut *self
                .silicon
                .backend()
                .warnings
                .lock()
                .expect("poisoned warning buffer"),
        )
    }
}
impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.stop();
    }
}

#[derive(Debug)]
pub enum RunOutcome {
    Parsed,
    Verified(VerificationResult),
}
#[derive(Debug)]
pub struct RunReport {
    pub outcome: RunOutcome,
    pub warnings: Vec<String>,
}

/// Execute the source frontend and native backend; parsing alone is a distinct outcome.
pub fn run_file(config: Config) -> Result<RunReport, FerrumError> {
    let file = config
        .frontend
        .file
        .as_deref()
        .ok_or_else(|| FerrumError::Configuration("Missing input file".into()))?;
    let source = std::fs::read_to_string(file).map_err(FerrumError::Input)?;
    let plugins = standard_plugin_manager(&config.frontend)
        .map_err(|e| FerrumError::Configuration(e.to_string()))?;
    let mut phases = SilFrontendPhases::new(file.into(), plugins);
    phases.configure_consistency(&config.frontend);
    let parsed = phases.parse(&source).map_err(FerrumError::Diagnostics)?;
    let mut warnings = phases
        .parsing_warnings
        .iter()
        .map(|w| w.readable_message())
        .collect::<Vec<_>>();
    if config.frontend.parse_only {
        return Ok(RunReport {
            outcome: RunOutcome::Parsed,
            warnings,
        });
    }
    let analyzed = phases.analyze(parsed).map_err(FerrumError::Diagnostics)?;
    let translated = phases
        .translate(analyzed)
        .map_err(FerrumError::Diagnostics)?;
    let program = phases
        .check_consistency(translated)
        .map_err(FerrumError::Diagnostics)?;
    let program = phases
        .prepare_verification(program)
        .map_err(FerrumError::Diagnostics)?;
    warnings.extend(
        phases
            .typechecking_warnings
            .iter()
            .map(|w| w.readable_message().unwrap_or_else(|_| w.full_id().into())),
    );
    let mut session = Session::new(config)?;
    let result = session.verify(&program, &[]);
    let cleanup = session.stop();
    warnings.extend(session.take_warnings());
    let result = match (result, cleanup) {
        (Ok(result), Ok(())) => result,
        (Err(error), Ok(())) | (Ok(_), Err(error)) => return Err(error),
        (Err(primary), Err(cleanup)) => {
            return Err(FerrumError::Cleanup {
                primary: Box::new(primary),
                cleanup: Box::new(cleanup),
            });
        }
    };
    let result = phases
        .map_verification(&program, result)
        .map_err(FerrumError::Diagnostics)?;
    // Source finish transforms before plugins and groups after beforeFinish.
    // The AST Session entry point deliberately returns the backend result.
    let result = result.transformed_result().map_err(execution)?;
    let result = phases.plugins.before_finish(result);
    let result = distinct_failures(result)?;
    Ok(RunReport {
        outcome: RunOutcome::Verified(result),
        warnings,
    })
}

pub fn verify_file(path: &Path) -> Result<VerificationResult, FerrumError> {
    let mut config = Config::default();
    config.frontend.file = Some(
        path.to_str()
            .ok_or_else(|| FerrumError::Configuration("Input path must be UTF-8".into()))?
            .into(),
    );
    match run_file(config)?.outcome {
        RunOutcome::Verified(result) => Ok(result),
        RunOutcome::Parsed => Err(FerrumError::Execution(
            "Verification was not executed".into(),
        )),
    }
}
