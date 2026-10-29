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

use silicon::verifier::verification_pool_manager::{
    BroadcastingProver, CancellationController, NativeMethodWorker, ThreadVerificationPool,
    native_method_worker, verify_native_parallel_with_reporting,
};
use silicon::{
    config::Config,
    decider::{
        decider::DefaultDecider,
        prover_std_io::{ProverEvent, ProverStdIo},
    },
    interfaces::verification::{ResultKind, VerificationResult as SiliconResult},
    silicon::{Silicon, SiliconBackend, SiliconOutcome},
    state::terms::{Term, TermFactory, TermOptions},
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
        sil_frontend::{SilFrontendPhases, standard_plugin_manager_with_resolver},
    },
    verifier::{
        verification_error::{
            NativeErrorNodeRenderer, RenderedVerificationError, VerificationError,
        },
        verification_result::{AbstractError, VerificationResult},
    },
};
use std::{cell::RefCell, rc::Rc};
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

type WorkerPool<P> = ThreadVerificationPool<NativeMethodWorker<P>>;
type ParallelMain<P> = ExecutingContext<BroadcastingProver<P, NativeMethodWorker<P>>>;
type SharedWarnings = Arc<Mutex<Vec<String>>>;
type StartedProvers = Arc<Mutex<std::collections::HashSet<String>>>;
type SharedPostconditionAxioms = Rc<RefCell<Vec<Term>>>;
type RunLogAttachment = silicon::logger::run_owner::RunLogAttachment;
type RunLogOwner = silicon::logger::run_owner::RunLogOwner;
type ProverFactory<P> =
    fn(
        &str,
        &Config,
        TermFactory,
        SharedWarnings,
        Option<CancellationController>,
        Option<Arc<dyn silver::reporter::reporter::Reporter>>,
        Option<silicon::logger::general::GeneralLogger>,
    ) -> Result<(P, silicon::state::identifiers::DefaultIdentifierFactory), FerrumError>;

struct ParallelContext<P>
where
    P: silicon::interfaces::decider::prover::Prover + 'static,
    P::Error: Send + std::fmt::Debug + 'static,
{
    context: Option<ParallelMain<P>>,
    pool: Option<Rc<RefCell<WorkerPool<P>>>>,
    warning_sink: SharedWarnings,
    warnings: Vec<String>,
    cancellation: Option<CancellationController>,
}
impl<P> ParallelContext<P>
where
    P: silicon::interfaces::decider::prover::Prover + 'static,
    P::Error: Send + std::fmt::Debug + 'static,
{
    fn start(
        main: P,
        identifiers: silicon::state::identifiers::DefaultIdentifierFactory,
        config: &Config,
        factory: TermFactory,
        options: NativeOptions,
        warning_sink: SharedWarnings,
        count: usize,
        make_prover: ProverFactory<P>,
        cancellation: Option<CancellationController>,
        logging: Option<RunLogAttachment>,
        general_logger: Option<silicon::logger::general::GeneralLogger>,
        reporter: Option<Arc<dyn silver::reporter::reporter::Reporter>>,
        postcondition_axioms: SharedPostconditionAxioms,
        started_provers: StartedProvers,
    ) -> Result<Self, FerrumError>
    where
        P: silicon::interfaces::decider::prover::Prover<
                Version = silicon::common::config::package::Version,
            >,
    {
        let worker_config = config.clone();
        let worker_factory = factory.clone();
        let worker_options = options.clone();
        let worker_warnings = warning_sink.clone();
        let worker_cancellation = cancellation.clone();
        let worker_logging = logging.clone();
        let worker_general_logger = general_logger.clone();
        let worker_reporter = reporter.clone();
        let worker_started_provers = started_provers.clone();
        let create = move |index| {
            // Counterexample lookup uses raw term identifiers, as in upstream.
            // Keep generated worker names unchanged by SMT symbol sanitization.
            let id = format!("worker_{index}");
            let (prover, identifiers) = make_prover(
                &id,
                &worker_config,
                worker_factory.clone(),
                worker_warnings.clone(),
                worker_cancellation.clone(),
                worker_reporter.clone(),
                worker_general_logger.clone(),
            )
            .map_err(|error| {
                silicon::verifier::native_context::NativeError::Execution(error.to_string())
            })?;
            let mut worker = native_method_worker(
                id.clone(),
                prover,
                identifiers,
                worker_factory.clone(),
                worker_options.clone(),
                &worker_config,
            );
            attach_version_observer(
                &mut worker.context,
                &id,
                &worker_config,
                worker_started_provers.clone(),
                worker_reporter.clone(),
                worker_general_logger.clone(),
                worker_warnings.clone(),
            )
            .map_err(|e| {
                silicon::verifier::native_context::NativeError::Diagnostic(format!("{e:?}"))
            })?;
            if let Some(logging) = &worker_logging {
                logging.attach(
                    &mut worker.context,
                    Rc::new(silicon::logger::records::data::data_record::FullStateRecordFactory),
                );
            }
            if let Some(logger) = &worker_general_logger {
                worker.context.set_general_worker_logger_name(index);
                worker
                    .context
                    .set_general_logging(logger.clone(), worker_config.prover_config_args.clone());
            }
            if let Some(c) = &worker_cancellation {
                worker.set_cancellation(c.clone());
            }
            Ok(worker)
        };
        let pool = match &cancellation {
            Some(c) => ThreadVerificationPool::start_with_cancellation(
                count,
                VERIFICATION_STACK_SIZE,
                c.clone(),
                create,
            ),
            None => ThreadVerificationPool::start(count, create),
        }
        .map_err(execution)?;
        let pool = Rc::new(RefCell::new(pool));
        let context = start_context(
            BroadcastingProver::new(main, pool.clone()),
            identifiers,
            config,
            factory,
            options,
            cancellation.clone(),
            logging.as_ref(),
            general_logger,
            postcondition_axioms,
            started_provers,
            reporter,
            warning_sink.clone(),
        );
        match context {
            Ok(context) => Ok(Self {
                context: Some(context),
                pool: Some(pool),
                warning_sink,
                warnings: Vec::new(),
                cancellation,
            }),
            Err(primary) => {
                let cleanup = Rc::try_unwrap(pool)
                    .map_err(|_| {
                        FerrumError::Execution(
                            "Worker pool is still borrowed after startup failure".into(),
                        )
                    })?
                    .into_inner()
                    .shutdown()
                    .map_err(execution);
                match cleanup {
                    Ok(()) => Err(primary),
                    Err(cleanup) => Err(FerrumError::Cleanup {
                        primary: Box::new(primary),
                        cleanup: Box::new(cleanup),
                    }),
                }
            }
        }
    }
    fn verify_program(
        &mut self,
        program: &Program,
        cfgs: &[SilverCfg],
        file: Option<&str>,
        reporter: Option<Arc<dyn silver::reporter::reporter::Reporter>>,
    ) -> Result<Vec<SiliconResult<VerificationError>>, FerrumError> {
        let context = self
            .context
            .as_mut()
            .ok_or_else(|| FerrumError::Execution("Parallel verifier has stopped".into()))?;
        let result = verify_native_parallel_with_reporting(
            context,
            program,
            cfgs,
            file,
            reporter,
            Some(self.warning_sink.clone()),
        )
        .map_err(execution);
        self.warnings.append(&mut context.warnings);
        result
    }
    fn stop(&mut self) -> Result<(), FerrumError> {
        let mut context = self.context.take();
        let main = match context.as_mut() {
            Some(context) => {
                let result = context.stop().map_err(execution);
                self.warnings.append(&mut context.warnings);
                result
            }
            None => Ok(()),
        };
        drop(context);
        let workers = match self.pool.take() {
            Some(pool) => match Rc::try_unwrap(pool) {
                Ok(pool) => {
                    let pool = pool.into_inner();
                    if self.cancellation.as_ref().is_some_and(|c| c.is_cancelled()) {
                        let errors = pool.cancel_and_join();
                        if errors.is_empty() {
                            Ok(())
                        } else {
                            Err(execution(errors))
                        }
                    } else {
                        pool.shutdown().map_err(execution)
                    }
                }
                Err(pool) => {
                    self.pool = Some(pool);
                    Err(FerrumError::Execution(
                        "Worker pool is still borrowed during shutdown".into(),
                    ))
                }
            },
            None => Ok(()),
        };
        match (main, workers) {
            (Ok(()), Ok(())) => Ok(()),
            (Err(error), Ok(())) | (Ok(()), Err(error)) => Err(error),
            (Err(primary), Err(cleanup)) => Err(FerrumError::Cleanup {
                primary: Box::new(primary),
                cleanup: Box::new(cleanup),
            }),
        }
    }
}
impl<P> Drop for ParallelContext<P>
where
    P: silicon::interfaces::decider::prover::Prover + 'static,
    P::Error: Send + std::fmt::Debug + 'static,
{
    fn drop(&mut self) {
        let _ = self.stop();
    }
}

enum OwnedContext {
    Stdio(Box<NativeContext>),
    ParallelStdio(Box<ParallelContext<ProverStdIo>>),
    #[cfg(feature = "native-z3")]
    Api(Box<ExecutingContext<silicon::decider::native_z3::LinkedZ3Prover>>),
    #[cfg(feature = "native-z3")]
    ParallelApi(Box<ParallelContext<silicon::decider::native_z3::LinkedZ3Prover>>),
}
impl OwnedContext {
    fn verify_program(
        &mut self,
        program: &Program,
        cfgs: &[SilverCfg],
        file: Option<&str>,
        reporter: Option<Arc<dyn silver::reporter::reporter::Reporter>>,
    ) -> Result<Vec<SiliconResult<VerificationError>>, FerrumError> {
        match self {
            Self::Stdio(context) => {
                context.set_preprocessing_reporter(reporter);
                context.verify_program(program, cfgs).map_err(execution)
            }
            Self::ParallelStdio(context) => context.verify_program(program, cfgs, file, reporter),
            #[cfg(feature = "native-z3")]
            Self::Api(context) => {
                context.set_preprocessing_reporter(reporter);
                context.verify_program(program, cfgs).map_err(execution)
            }
            #[cfg(feature = "native-z3")]
            Self::ParallelApi(context) => context.verify_program(program, cfgs, file, reporter),
        }
    }
    fn stop(&mut self) -> Result<(), FerrumError> {
        match self {
            Self::Stdio(context) => context.stop().map_err(execution),
            Self::ParallelStdio(context) => context.stop(),
            #[cfg(feature = "native-z3")]
            Self::Api(context) => context.stop().map_err(execution),
            #[cfg(feature = "native-z3")]
            Self::ParallelApi(context) => context.stop(),
        }
    }
    fn trace_factory(&self) -> Option<TermFactory> {
        match self {
            Self::Stdio(context) => Some(context.factory.clone()),
            Self::ParallelStdio(context) => {
                context.context.as_ref().map(|main| main.factory.clone())
            }
            #[cfg(feature = "native-z3")]
            Self::Api(context) => Some(context.factory.clone()),
            #[cfg(feature = "native-z3")]
            Self::ParallelApi(context) => context.context.as_ref().map(|main| main.factory.clone()),
        }
    }
    fn workers_quiesced(&self) -> bool {
        match self {
            Self::ParallelStdio(context) => context.pool.is_none(),
            #[cfg(feature = "native-z3")]
            Self::ParallelApi(context) => context.pool.is_none(),
            _ => true,
        }
    }
    fn warnings(&mut self) -> &mut Vec<String> {
        match self {
            Self::Stdio(context) => &mut context.warnings,
            Self::ParallelStdio(context) => &mut context.warnings,
            #[cfg(feature = "native-z3")]
            Self::Api(context) => &mut context.warnings,
            #[cfg(feature = "native-z3")]
            Self::ParallelApi(context) => &mut context.warnings,
        }
    }
}

/// Decider.createProver reports a version only for the first start of each
/// source verifier. Native reset reconstructs contexts, so history belongs to
/// the backend session rather than a transient prover object.
fn attach_version_observer<P>(
    context: &mut ExecutingContext<P>,
    id: &str,
    config: &Config,
    started: StartedProvers,
    reporter: Option<Arc<dyn silver::reporter::reporter::Reporter>>,
    logger: Option<silicon::logger::general::GeneralLogger>,
    warnings: SharedWarnings,
) -> Result<(), FerrumError>
where
    P: silicon::interfaces::decider::prover::Prover<
            Version = silicon::common::config::package::Version,
        > + 'static,
    P::Error: std::fmt::Debug,
{
    let location = if config.prover == "Z3-API" {
        "No Path".to_owned()
    } else {
        config
            .prover_settings(id)
            .map_err(|e| FerrumError::Configuration(e.to_string()))?
            .executable
            .display()
            .to_string()
    };
    let id = id.to_owned();
    let logger_name = if id == "main" {
        "viper.silicon.verifier.DefaultMainVerifier-00".to_owned()
    } else {
        let index: usize = id.strip_prefix("worker_").unwrap().parse().unwrap();
        format!("viper.silicon.verifier.WorkerVerifier-{:02}", index + 1)
    };
    context.set_start_observer(move |prover| {
        use silicon::decider::decider::DeciderError;
        use silicon::logger::general::Level;
        use silicon::verifier::native_context::NativeError;
        use silver::reporter::message::{Message, SimpleMessageKind};
        if started
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .contains(&id)
        {
            return Ok(());
        }
        let version = prover
            .version()
            .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        let message = format!("Using {} {version} located at {location}", prover.name());
        if let Some(reporter) = &reporter {
            reporter
                .report(Message::Simple {
                    kind: SimpleMessageKind::ConfigurationConfirmation,
                    text: message.clone(),
                })
                .map_err(|e| NativeError::Diagnostic(format!("prover version reporter: {e:?}")))?;
        }
        if let Some(logger) = &logger {
            logger.emit(&logger_name, Level::Debug, || message);
        }
        let mut version_warnings = Vec::new();
        if version.less_than(&prover.min_version()) {
            version_warnings.push(format!(
                "Expected at least {} version {}, but found {version}",
                prover.name(),
                prover.min_version()
            ));
        }
        if let Some(maximum) = prover.max_version().filter(|m| m.less_than(&version)) {
            version_warnings.push(format!(
                "Silicon might not work with {} version {version}, consider using {maximum}",
                prover.name()
            ));
        }
        for message in version_warnings {
            if let Some(reporter) = &reporter {
                reporter
                    .report(Message::Simple {
                        kind: SimpleMessageKind::InternalWarning,
                        text: message.clone(),
                    })
                    .map_err(|e| {
                        NativeError::Diagnostic(format!("prover version warning reporter: {e:?}"))
                    })?;
            } else {
                warnings
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .push(message.clone());
            }
            if let Some(logger) = &logger {
                logger.emit(&logger_name, Level::Warn, || message);
            }
        }
        started
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(id.clone());
        Ok(())
    });
    Ok(())
}

fn start_context<
    P: silicon::interfaces::decider::prover::Prover<
            Version = silicon::common::config::package::Version,
        > + 'static,
>(
    prover: P,
    identifiers: silicon::state::identifiers::DefaultIdentifierFactory,
    config: &Config,
    factory: TermFactory,
    options: NativeOptions,
    cancellation: Option<CancellationController>,
    logging: Option<&RunLogAttachment>,
    general_logger: Option<silicon::logger::general::GeneralLogger>,
    postcondition_axioms: SharedPostconditionAxioms,
    started_provers: StartedProvers,
    reporter: Option<Arc<dyn silver::reporter::reporter::Reporter>>,
    warnings: SharedWarnings,
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
    context.set_postcondition_axioms_store(postcondition_axioms);
    attach_version_observer(
        &mut context,
        "main",
        config,
        started_provers,
        reporter,
        general_logger.clone(),
        warnings,
    )?;
    context.set_preamble_config(config.prover_config_args.clone());
    if let Some(logger) = general_logger {
        context.set_general_logging(logger, config.prover_config_args.clone());
    }
    if let Some(logging) = logging {
        logging.attach(
            &mut context,
            Rc::new(silicon::logger::records::data::data_record::FullStateRecordFactory),
        );
    }
    if let Some(c) = cancellation {
        context.set_cancellation(c);
    }
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

fn make_stdio_prover(
    id: &str,
    config: &Config,
    factory: TermFactory,
    warning_sink: SharedWarnings,
    cancellation: Option<CancellationController>,
    reporter: Option<Arc<dyn silver::reporter::reporter::Reporter>>,
    general_logger: Option<silicon::logger::general::GeneralLogger>,
) -> Result<
    (
        ProverStdIo,
        silicon::state::identifiers::DefaultIdentifierFactory,
    ),
    FerrumError,
> {
    let settings = config
        .prover_settings(id)
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
    let warnings = warning_sink;
    let logger_name = match config.prover.as_str() {
        "Z3" => "viper.silicon.decider.Z3ProverStdIO",
        "cvc5" => "viper.silicon.decider.Cvc5ProverStdIO",
        _ => unreachable!(),
    };
    let mut prover = ProverStdIo::new(id.into(), settings, profile, factory, move |event| {
        if let ProverEvent::Warning(warning) = event {
            warnings
                .lock()
                .expect("poisoned warning buffer")
                .push(warning);
        }
    });
    if reporter.is_some() || general_logger.is_some() {
        prover.set_configuration_observer(move |message| {
            if let Some(reporter) = &reporter {
                reporter
                    .report(silver::reporter::message::Message::Simple {
                        kind:
                            silver::reporter::message::SimpleMessageKind::ConfigurationConfirmation,
                        text: message.into(),
                    })
                    .map_err(|error| format!("prover configuration reporter: {error:?}"))?;
            }
            if let Some(logger) = &general_logger {
                logger.emit(logger_name, silicon::logger::general::Level::Debug, || {
                    message.into()
                });
            }
            Ok(())
        });
    }
    if let Some(c) = cancellation {
        c.register_stdio(prover.cancellation_handle());
    }
    let identifiers = prover.identifier_factory();
    Ok((prover, identifiers))
}

#[cfg(feature = "native-z3")]
fn make_api_prover(
    id: &str,
    config: &Config,
    factory: TermFactory,
    warning_sink: SharedWarnings,
    cancellation: Option<CancellationController>,
    _reporter: Option<Arc<dyn silver::reporter::reporter::Reporter>>,
    _general_logger: Option<silicon::logger::general::GeneralLogger>,
) -> Result<
    (
        silicon::decider::native_z3::LinkedZ3Prover,
        silicon::state::identifiers::DefaultIdentifierFactory,
    ),
    FerrumError,
> {
    use silicon::decider::{
        native_z3::{LinkedProverOptions, LinkedZ3, LinkedZ3Prover},
        z3_prover_api::ApiTimeoutSettings,
    };
    // Pinned Z3ProverAPI intentionally ignores the stdio transcript options.
    let version = LinkedZ3::library_version();
    if version != (4, 16, 0, 0) {
        return Err(FerrumError::Configuration(format!(
            "Z3-API requires the pinned libz3 4.16.0.0; linked library is {}.{}.{}.{}",
            version.0, version.1, version.2, version.3
        )));
    }
    let mut prover = LinkedZ3Prover::new(
        id,
        factory,
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
    let warnings = warning_sink;
    prover.set_warning_reporter(move |warning| {
        warnings
            .lock()
            .expect("poisoned warning buffer")
            .push(warning.to_owned());
    });
    if let Some(c) = cancellation {
        c.register_linked(prover.cancellation_handle());
    }
    let identifiers = prover.identifier_factory();
    Ok((prover, identifiers))
}

// Deadline covers runVerifier and its result assembly. Solver interrupts do not
// preempt pure Rust computation: the verification paths use cooperative checkpoints.
struct Deadline {
    shared: Arc<(Mutex<(bool, bool)>, std::sync::Condvar)>, // (done, expired)
    thread: Option<std::thread::JoinHandle<()>>,
    instant: std::time::Instant,
    cancellation: CancellationController,
}
impl Deadline {
    fn start(seconds: u64, cancellation: CancellationController) -> Result<Self, FerrumError> {
        let shared = Arc::new((Mutex::new((false, false)), std::sync::Condvar::new()));
        let worker_shared = shared.clone();
        let worker_cancellation = cancellation.clone();
        let instant = std::time::Instant::now() + std::time::Duration::from_secs(seconds);
        let thread = std::thread::Builder::new()
            .name("ferrum-deadline".into())
            .spawn(move || {
                let (lock, ready) = &*worker_shared;
                let deadline = instant;
                let mut state = lock.lock().unwrap_or_else(|e| e.into_inner());
                while !state.0 && !state.1 {
                    let now = std::time::Instant::now();
                    if now >= deadline {
                        state.1 = true;
                        break;
                    }
                    state = ready
                        .wait_timeout(state, deadline - now)
                        .unwrap_or_else(|e| e.into_inner())
                        .0;
                }
                if !state.1 {
                    return;
                }
                drop(state);
                worker_cancellation.cancel();
                let mut state = lock.lock().unwrap_or_else(|e| e.into_inner());
                while !state.0 {
                    let (next, _) = ready
                        .wait_timeout(state, std::time::Duration::from_millis(50))
                        .unwrap_or_else(|e| e.into_inner());
                    state = next;
                    if !state.0 {
                        drop(state);
                        worker_cancellation.interrupt_again();
                        state = lock.lock().unwrap_or_else(|e| e.into_inner());
                    }
                }
            })
            .map_err(|error| {
                FerrumError::Execution(format!("Cannot start deadline monitor: {error}"))
            })?;
        Ok(Self {
            shared,
            thread: Some(thread),
            instant,
            cancellation,
        })
    }
    // Atomically settles completion against expiration. An expired run must
    // clean up first while the monitor keeps retrying interrupts.
    fn completed_before_deadline(&self) -> bool {
        let (lock, ready) = &*self.shared;
        let mut state = lock.lock().unwrap_or_else(|e| e.into_inner());
        if !state.1 && std::time::Instant::now() >= self.instant {
            state.1 = true;
            ready.notify_all();
        }
        if state.1 {
            false
        } else {
            state.0 = true;
            ready.notify_all();
            true
        }
    }
    fn cancel_for_unwind(&self) {
        let (lock, ready) = &*self.shared;
        lock.lock().unwrap_or_else(|e| e.into_inner()).1 = true;
        ready.notify_all();
        self.cancellation.cancel();
    }
    fn finish(&mut self) -> Result<(), FerrumError> {
        let (lock, ready) = &*self.shared;
        lock.lock().unwrap_or_else(|e| e.into_inner()).0 = true;
        ready.notify_all();
        if let Some(thread) = self.thread.take() {
            thread
                .join()
                .map_err(|_| FerrumError::Execution("Deadline monitor panicked".into()))?;
        }
        Ok(())
    }
}
impl Drop for Deadline {
    fn drop(&mut self) {
        // Unwinding must interrupt owner-thread work before Session/pool teardown.
        if self.thread.is_some() {
            self.cancellation.cancel();
            let _ = self.finish();
        }
    }
}

struct NativeBackend {
    config: Config,
    context: Option<OwnedContext>,
    recorded_source: Option<String>,
    cancellation: Option<CancellationController>,
    warnings: Arc<Mutex<Vec<String>>>,
    reporter: Option<Arc<dyn silver::reporter::reporter::Reporter>>,
    logging: Option<RunLogOwner>,
    general_logger: Option<silicon::logger::general::GeneralLogger>,
    started_provers: StartedProvers,
    // Same owner-thread function postcondition vector survives source verifier resets.
    postcondition_axioms: SharedPostconditionAxioms,
}
impl NativeBackend {
    fn new(config: Config) -> Self {
        let general_logger = silicon::logger::general::GeneralLogger::new(
            config.log_level.as_deref(),
            &config.logger,
            Arc::new(silicon::logger::general::StdoutSink),
        );
        Self {
            config,
            context: None,
            recorded_source: None,
            cancellation: None,
            warnings: Arc::new(Mutex::new(Vec::new())),
            reporter: None,
            logging: None,
            general_logger: Some(general_logger),
            started_provers: Arc::new(Mutex::new(Default::default())),
            postcondition_axioms: Rc::new(RefCell::new(Vec::new())),
        }
    }
    /// Return whether all worker contexts are gone and logger close succeeded, independently
    /// of solver-stop warnings that may occur after cancellation interrupts stdio.
    fn stop_with_reportability(&mut self) -> (Result<(), FerrumError>, bool) {
        let primary = self.stop_context();
        if self.context.is_some() {
            return (primary, false);
        }
        let cleanup = match self.logging.take() {
            Some(owner) => owner.close().map_err(execution),
            None => Ok(()),
        };
        let reportable = cleanup.is_ok();
        (combine_logger_cleanup(primary, cleanup), reportable)
    }
    /// Source timeout closes the root but retains it for subsequent verification runs.
    fn close_after_timeout(&mut self) -> (Result<(), FerrumError>, bool) {
        let primary = self.stop_context();
        if self.context.is_some() {
            return (primary, false);
        }
        let cleanup = match self.logging.as_ref() {
            Some(owner) => owner.close().map_err(execution),
            None => Ok(()),
        };
        let reportable = cleanup.is_ok();
        (combine_logger_cleanup(primary, cleanup), reportable)
    }
    /// Reset tears down only solver contexts; the run-owned logger survives.
    fn stop_context(&mut self) -> Result<(), FerrumError> {
        if let Some(mut context) = self.context.take() {
            let result = context.stop();
            self.warnings
                .lock()
                .expect("poisoned warning buffer")
                .append(context.warnings());
            if !context.workers_quiesced() {
                self.context = Some(context);
            }
            result?;
        }
        Ok(())
    }
}
fn combine_logger_cleanup(
    primary: Result<(), FerrumError>,
    cleanup: Result<(), FerrumError>,
) -> Result<(), FerrumError> {
    match (primary, cleanup) {
        (Ok(()), result) | (result, Ok(())) => result,
        (Err(primary), Err(cleanup)) => Err(FerrumError::Cleanup {
            primary: Box::new(primary),
            cleanup: Box::new(cleanup),
        }),
    }
}
/// Build the source-selected native logger using the reporter effective at startup.
fn configured_run_log_owner(
    config: &Config,
    reporter: Option<Arc<dyn silver::reporter::reporter::Reporter>>,
    factory: TermFactory,
    warnings: SharedWarnings,
) -> Result<RunLogOwner, FerrumError> {
    let reporter = reporter.ok_or_else(|| {
        FerrumError::Configuration("configured logging requires a reporter".into())
    })?;
    let log_warnings = warnings.clone();
    let state_warnings = warnings;
    let root = silicon::logger::symb_ex_logger::NativeSymbExLogger::of_config(
        config,
        reporter,
        factory,
        move |warning| {
            log_warnings
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .push(warning)
        },
        move |error| {
            state_warnings
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .push(format!("state reporting failed: {error:?}"))
        },
    )
    .map_err(execution)?;
    RunLogOwner::new(
        Arc::new(root),
        Some(silicon::logger::symb_ex_logger::native_statistics_double),
        config.frontend.ide_mode_advanced,
    )
    .map_err(execution)
}
impl Drop for NativeBackend {
    fn drop(&mut self) {
        // Standalone paths stop contexts before releasing the run logger. Production
        // pool Rc clones are confined to the main prover and lexical verification;
        // neither survives this teardown. Private callers must release any extra
        // clone and retry stop before dropping the backend.
        let _ = <Self as SiliconBackend>::stop(self);
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
        self.cancellation = (config.timeout > 0).then(CancellationController::default);
        let options = NativeOptions::from_config(config).map_err(execution)?;
        let factory = TermFactory::new(TermOptions {
            use_flyweight: config.use_flyweight(),
            use_old_axiomatization: config.use_old_axiomatization,
            mask_heap_mode: config.mask_heap_mode,
        });
        if (config.frontend.ide_mode_advanced || config.report_state_after.is_some())
            && self.logging.is_none()
        {
            self.logging = Some(configured_run_log_owner(
                config,
                self.reporter.clone(),
                factory.clone(),
                self.warnings.clone(),
            )?);
        }
        // Preserve the initial native single-worker default; explicit source configuration
        // selects the now-connected worker pool.
        let count = if config.is_supplied("numberOfParallelVerifiers") {
            usize::try_from(config.number_of_parallel_verifiers)
                .map_err(|_| FerrumError::Configuration("Invalid worker count".into()))?
        } else {
            1
        };
        if config.prover == "Z3-API" {
            #[cfg(not(feature = "native-z3"))]
            return Err(FerrumError::Configuration(
                "Z3-API requires a build with --features native-z3 and libz3 4.16.0".into(),
            ));
            #[cfg(feature = "native-z3")]
            {
                let (prover, identifiers) = make_api_prover(
                    "main",
                    config,
                    factory.clone(),
                    self.warnings.clone(),
                    self.cancellation.clone(),
                    self.reporter.clone(),
                    self.general_logger.clone(),
                )?;
                self.context = Some(if count > 1 || config.parallelize_branches {
                    OwnedContext::ParallelApi(Box::new(ParallelContext::start(
                        prover,
                        identifiers,
                        config,
                        factory,
                        options,
                        self.warnings.clone(),
                        count,
                        make_api_prover,
                        self.cancellation.clone(),
                        self.logging.as_ref().map(RunLogOwner::attachment),
                        self.general_logger.clone(),
                        self.reporter.clone(),
                        self.postcondition_axioms.clone(),
                        self.started_provers.clone(),
                    )?))
                } else {
                    OwnedContext::Api(Box::new(start_context(
                        prover,
                        identifiers,
                        config,
                        factory,
                        options,
                        self.cancellation.clone(),
                        self.logging.as_ref().map(RunLogOwner::attachment).as_ref(),
                        self.general_logger.clone(),
                        self.postcondition_axioms.clone(),
                        self.started_provers.clone(),
                        self.reporter.clone(),
                        self.warnings.clone(),
                    )?))
                });
                return Ok(());
            }
        }
        let (prover, identifiers) = make_stdio_prover(
            "main",
            config,
            factory.clone(),
            self.warnings.clone(),
            self.cancellation.clone(),
            self.reporter.clone(),
            self.general_logger.clone(),
        )?;
        self.context = Some(if count > 1 || config.parallelize_branches {
            OwnedContext::ParallelStdio(Box::new(ParallelContext::start(
                prover,
                identifiers,
                config,
                factory,
                options,
                self.warnings.clone(),
                count,
                make_stdio_prover,
                self.cancellation.clone(),
                self.logging.as_ref().map(RunLogOwner::attachment),
                self.general_logger.clone(),
                self.reporter.clone(),
                self.postcondition_axioms.clone(),
                self.started_provers.clone(),
            )?))
        } else {
            OwnedContext::Stdio(Box::new(start_context(
                prover,
                identifiers,
                config,
                factory,
                options,
                self.cancellation.clone(),
                self.logging.as_ref().map(RunLogOwner::attachment).as_ref(),
                self.general_logger.clone(),
                self.postcondition_axioms.clone(),
                self.started_provers.clone(),
                self.reporter.clone(),
                self.warnings.clone(),
            )?))
        });
        Ok(())
    }
    fn reset(&mut self) -> Result<(), FerrumError> {
        self.stop_context()?;
        self.start()
    }
    fn stop(&mut self) -> Result<(), FerrumError> {
        self.stop_with_reportability().0
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
        file: Option<&str>,
    ) -> Result<VerificationResult, FerrumError> {
        let mut deadline = self
            .cancellation
            .clone()
            .map(|controller| Deadline::start(self.config.timeout as u64, controller))
            .transpose()?;
        let work = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
            || -> Result<VerificationResult, FerrumError> {
                let context = self.context.as_mut().ok_or_else(|| {
                    FerrumError::Execution("Native solver has not been started".into())
                })?;
                let results = context.verify_program(program, cfgs, file, self.reporter.clone());
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
            },
        ));
        let result =
            match work {
                Ok(result) => result,
                Err(panic) => {
                    if let Some(deadline) = &mut deadline {
                        deadline.cancel_for_unwind();
                        let cleanup =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.stop()));
                        let warning = match cleanup {
                            Ok(Ok(())) => None,
                            Ok(Err(error)) => {
                                Some(format!("verification panic cleanup failed: {error}"))
                            }
                            Err(_) => Some("verification panic cleanup also panicked".into()),
                        };
                        if let Some(warning) = warning {
                            self.warnings
                                .lock()
                                .unwrap_or_else(|e| e.into_inner())
                                .push(warning);
                        }
                        if let Err(error) = deadline.finish() {
                            self.warnings
                                .lock()
                                .unwrap_or_else(|e| e.into_inner())
                                .push(format!("verification panic monitor failed: {error}"));
                        }
                        if let Some(controller) = &self.cancellation {
                            self.warnings
                                .lock()
                                .unwrap_or_else(|e| e.into_inner())
                                .extend(controller.take_errors().into_iter().map(|e| {
                                    format!("verification panic interruption failed: {e}")
                                }));
                        }
                    }
                    std::panic::resume_unwind(panic);
                }
            };
        if let Some(deadline) = &mut deadline {
            if !deadline.completed_before_deadline() {
                // Completion may observe the deadline before the monitor gets
                // scheduled; latch cancellation before selecting pool teardown.
                if let Some(controller) = &self.cancellation {
                    controller.cancel();
                }
                if let Err(error) = &result {
                    // Pool startup/broadcast may already have joined workers and
                    // attached cleanup failures to the original operation error.
                    self.warnings
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .push(format!("timeout verification terminated: {error}"));
                }
                // Preserve the actual run-owned logger and term factory until after
                // workers stop and the logger closes; source reports timeout logs afterward.
                let timeout_attachment = self.logging.as_ref().map(RunLogOwner::attachment);
                let timeout_factory = self.context.as_ref().and_then(OwnedContext::trace_factory);
                // Keep the retry monitor alive until all owner threads and solver
                // contexts have stopped, including failures on the proof path.
                let (cleanup, trace_ready) = self.close_after_timeout();
                let cleanup_error = cleanup.err();
                if let Some(error) = &cleanup_error {
                    self.warnings
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .push(format!("timeout cleanup failed: {error}"));
                }
                if let Err(error) = deadline.finish() {
                    self.warnings
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .push(format!("timeout monitor failed: {error}"));
                }
                if let Some(controller) = &self.cancellation {
                    self.warnings
                        .lock()
                        .unwrap_or_else(|e| e.into_inner())
                        .extend(
                            controller
                                .take_errors()
                                .into_iter()
                                .map(|e| format!("timeout interruption failed: {e}")),
                        );
                }
                if let Some(attachment) = timeout_attachment.filter(RunLogAttachment::trace_enabled)
                {
                    if !trace_ready {
                        let cleanup = cleanup_error.unwrap_or_else(|| {
                            FerrumError::Execution("timeout logger did not close".into())
                        });
                        return Err(FerrumError::Cleanup {
                            primary: Box::new(FerrumError::Execution(
                                "verification timed out".into(),
                            )),
                            cleanup: Box::new(cleanup),
                        });
                    }
                    let factory = timeout_factory.ok_or_else(|| {
                        FerrumError::Execution("timeout trace term factory unavailable".into())
                    })?;
                    let message = attachment
                        .timeout_trace(&factory)
                        .map_err(execution)?
                        .ok_or_else(|| {
                            FerrumError::Execution("timeout trace unexpectedly disabled".into())
                        })?;
                    let reporter = self.reporter.as_ref().ok_or_else(|| {
                        FerrumError::Execution("timeout trace reporter unavailable".into())
                    })?;
                    reporter.report(message).map_err(execution)?;
                }
                return Ok(final_result(vec![AbstractError::Frontend(
                    silver::verifier::verification_result::FrontendError::new(
                        silver::verifier::verification_result::FrontendErrorKind::TimeoutOccurred {
                            duration: self.config.timeout as i64,
                            units: "second(s)".into(),
                        },
                        silver::ast::position::Position::NoPosition,
                    ),
                )]));
            }
            deadline.finish()?;
        }
        result
    }
}

/// Stack reserved by the file runner, matching pinned Silicon's `-Xss128m` launcher.
/// This is a finite bound for the source continuation-based verification algorithms.
pub const VERIFICATION_STACK_SIZE: usize = 128 * 1024 * 1024;

/// An owned solver session for native Silver programs, including repeated runs.
/// AST clients bypass frontend plugins but retain Silicon's mandatory consistency check.
/// Sessions run on the caller's thread. For recursive programs, create and use the
/// session inside a thread configured with [`VERIFICATION_STACK_SIZE`]. Native
/// solver handles stay on the thread where the session is created.
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
    /// Construct a native session that delivers verifier events to the supplied reporter.
    /// The session remains owner-thread bound and uses the same configuration gates as `new`.
    pub fn new_with_reporter(
        config: Config,
        reporter: Arc<dyn silver::reporter::reporter::Reporter>,
    ) -> Result<Self, FerrumError> {
        Self::new_with_warning_sink(config, Arc::new(Mutex::new(Vec::new())), reporter)
    }
    /// Share the backend warning sink from construction onward, including failed startup.
    fn new_with_warning_sink(
        config: Config,
        warnings: SharedWarnings,
        reporter: Arc<dyn silver::reporter::reporter::Reporter>,
    ) -> Result<Self, FerrumError> {
        let mut backend = NativeBackend::new(config);
        backend.warnings = warnings;
        backend.reporter = Some(reporter);
        let mut silicon = Silicon::new(backend);
        silicon.configure(&[]).map_err(execution)?;
        if let Err(error) = silicon.start() {
            let primary = execution(error);
            return match silicon.stop() {
                Ok(()) => Err(primary),
                Err(cleanup) => Err(FerrumError::Cleanup {
                    primary: Box::new(primary),
                    cleanup: Box::new(execution(cleanup)),
                }),
            };
        }
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

/// Thread-owned adapter from the Silver verifier interface to a native Session.
struct SessionVerifier {
    session: Option<Session>,
    reporter: Arc<dyn silver::reporter::reporter::Reporter>,
    dependencies: Vec<silver::verifier::verifier::DefaultDependency>,
}
impl SessionVerifier {
    fn solver_dependencies() -> Vec<silver::verifier::verifier::DefaultDependency> {
        [
            silicon::decider::z3_prover_std_io::profile(),
            silicon::decider::cvc5_prover_std_io::profile(),
        ]
        .into_iter()
        .map(|profile| silver::verifier::verifier::DefaultDependency {
            name: profile.name,
            version: profile.minimum_version.version,
            location: profile.dependency_url,
        })
        .collect()
    }
    fn stop_session(&mut self) -> Result<(), silver::verifier::verifier::VerifierError> {
        let Some(mut session) = self.session.take() else {
            return Ok(());
        };
        let result = session.stop();
        result
            .map_err(|error| silver::verifier::verifier::VerifierError::Backend(error.to_string()))
    }
}
impl silver::components::components::LifetimeComponent for SessionVerifier {
    fn start(&mut self) {} // Session::new already configured and started the owner-thread backend.
    fn stop(&mut self) {
        let _ = self.stop_session();
    }
}
impl silver::verifier::verifier::Verifier for SessionVerifier {
    fn name(&self) -> &str {
        "Silicon"
    }
    fn version(&self) -> &str {
        // This identifies the native Ferrum build, not the upstream JVM build.
        env!("CARGO_PKG_VERSION")
    }
    fn build_version(&self) -> &str {
        "<unknown-build-version>"
    }
    fn copyright(&self) -> &str {
        "(c) Copyright ETH Zurich 2012 - 2026"
    }
    fn debug_info(&mut self, _: Vec<(String, Box<dyn std::any::Any + Send + Sync>)>) {}
    fn dependencies(&self) -> Vec<&dyn silver::verifier::verifier::Dependency> {
        self.dependencies
            .iter()
            .map(|dependency| dependency as &dyn silver::verifier::verifier::Dependency)
            .collect()
    }
    fn parse_command_line(&mut self, _: &[String]) {} // The factory already parsed backend arguments.
    fn verify(
        &mut self,
        program: &Program,
    ) -> Result<VerificationResult, silver::verifier::verifier::VerifierError> {
        let Some(mut session) = self.session.take() else {
            return Err(silver::verifier::verifier::VerifierError::Backend(
                "native session is stopped".into(),
            ));
        };
        let result = session.verify(program, &[]);
        self.session = Some(session);
        result
            .map_err(|error| silver::verifier::verifier::VerifierError::Backend(error.to_string()))
    }
    fn reporter(&self) -> &dyn silver::reporter::reporter::Reporter {
        self.reporter.as_ref()
    }
    fn try_stop(&mut self) -> Result<(), silver::verifier::verifier::VerifierError> {
        self.stop_session()
    }
}
impl Drop for SessionVerifier {
    fn drop(&mut self) {
        let _ = self.stop_session();
    }
}

/// Injected-AST frontend with source plugin processing and an owner-thread native session.
/// It follows ViperFrontendAPI's starting state, which skips the frontend consistency phase;
/// Session still performs Silicon's mandatory backend consistency check. Create and use this
/// value on the same thread, using [`VERIFICATION_STACK_SIZE`] for recursive programs.
pub struct NativeFrontendApi {
    frontend: silver::frontend::viper_frontend_api::ViperFrontendApi<SilFrontendPhases>,
    warnings: Arc<Mutex<Vec<String>>>,
}
impl NativeFrontendApi {
    pub fn new(
        args: &[String],
        reporter: Arc<dyn silver::reporter::reporter::Reporter>,
        minimal: bool,
    ) -> Result<Self, FerrumError> {
        Self::new_with_warning_sink(args, reporter, minimal, Arc::new(Mutex::new(Vec::new())))
    }
    /// Use a caller-owned sink to retain warnings even if plugin initialization fails.
    pub fn new_with_warning_sink(
        args: &[String],
        reporter: Arc<dyn silver::reporter::reporter::Reporter>,
        minimal: bool,
        warnings: Arc<Mutex<Vec<String>>>,
    ) -> Result<Self, FerrumError> {
        use silver::frontend::{frontend::DefaultFrontend, viper_frontend_api::ViperFrontendApi};
        let mut phases = SilFrontendPhases::new(
            silver::frontend::viper_frontend_api::DUMMY_INPUT_FILENAME.into(),
            silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
        );
        phases.backend_type_format = Some("SMTLIB".into());
        let mut frontend = ViperFrontendApi::new(DefaultFrontend::new(phases), minimal);
        let mut complete_args = args.to_vec();
        complete_args.push("--ignoreFile".into());
        complete_args.push(silver::frontend::viper_frontend_api::DUMMY_INPUT_FILENAME.into());
        let native_config = Config::parse(&complete_args)
            .map_err(|error| FerrumError::Configuration(error.to_string()))?;
        if native_config.frontend.exit() {
            return Err(FerrumError::Configuration(
                "frontend configuration requested exit".into(),
            ));
        }
        let factory_reporter = reporter.clone();
        let factory_warnings = warnings.clone();
        frontend
            .initialize_with_factory(
                args,
                reporter.as_ref(),
                move |_, _| {
                    let shared = native_config.frontend.clone();
                    let session = Session::new_with_warning_sink(
                        native_config,
                        factory_warnings,
                        factory_reporter.clone(),
                    )
                    .map_err(|error| error.to_string())?;
                    let verifier = SessionVerifier {
                        session: Some(session),
                        reporter: factory_reporter,
                        dependencies: SessionVerifier::solver_dependencies(),
                    };
                    Ok((Box::new(verifier), shared))
                },
                |name| {
                    Ok(match name {
                        "viper.silicon.extensions.TryBlockParserPlugin" => Some(Box::new(
                            silicon::extensions::try_block_parser_plugin::TryBlockParserPlugin,
                        )
                            as Box<dyn silver::plugin::silver_plugin::SilverPlugin>),
                        _ => None,
                    })
                },
            )
            .map_err(|error| match error {
                silver::frontend::viper_frontend_api::FrontendApiInitError::Backend(message) => {
                    FerrumError::Execution(message)
                }
                silver::frontend::viper_frontend_api::FrontendApiInitError::Reporter(error) => {
                    FerrumError::Execution(format!("reporting: {error:?}"))
                }
                other => FerrumError::Configuration(format!("{other:?}")),
            })?;
        Ok(Self { frontend, warnings })
    }
    pub fn verify(&mut self, program: &Program) -> Result<VerificationResult, FerrumError> {
        self.frontend.verify(program.clone()).map_err(execution)
    }
    pub fn stop(&mut self) -> Result<(), FerrumError> {
        self.frontend.stop().map_err(execution)
    }
    pub fn take_warnings(&mut self) -> Vec<String> {
        std::mem::take(
            &mut *self
                .warnings
                .lock()
                .unwrap_or_else(|poisoned| poisoned.into_inner()),
        )
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

/// Execute the frontend and backend on a thread with the upstream launcher's stack size.
/// Solver handles and plugins are constructed and destroyed on that thread.
/// Parsing alone is a distinct outcome.
pub fn run_file(config: Config) -> Result<RunReport, FerrumError> {
    std::thread::Builder::new()
        .name("ferrum-verifier".into())
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(move || run_file_on_current_thread(config))
        .map_err(|error| FerrumError::Execution(format!("Cannot start verifier thread: {error}")))?
        .join()
        .map_err(|_| FerrumError::Execution("Native verifier thread panicked".into()))?
}

/// Forward only symbolic diagnostics; the CLI already prints final verification results.
struct CliLoggingReporter(silver::reporter::reporter::StdIoReporter<std::io::Stdout>);
impl silver::reporter::reporter::Reporter for CliLoggingReporter {
    fn name(&self) -> &str {
        "ferrum_cli_logging"
    }
    fn report(
        &self,
        message: silver::reporter::message::Message,
    ) -> Result<(), silver::reporter::reporter::ReportError> {
        if matches!(
            &message,
            silver::reporter::message::Message::ExecutionTrace { .. }
                | silver::reporter::message::Message::VerifierState { .. }
        ) {
            silver::reporter::reporter::Reporter::report(&self.0, message)?;
        }
        Ok(())
    }
}

fn run_file_on_current_thread(config: Config) -> Result<RunReport, FerrumError> {
    let file = config
        .frontend
        .file
        .as_deref()
        .ok_or_else(|| FerrumError::Configuration("Missing input file".into()))?;
    let source = std::fs::read_to_string(file).map_err(FerrumError::Input)?;
    let plugins = standard_plugin_manager_with_resolver(&config.frontend, |name| {
        Ok(match name {
            "viper.silicon.extensions.TryBlockParserPlugin" => Some(Box::new(
                silicon::extensions::try_block_parser_plugin::TryBlockParserPlugin,
            )
                as Box<dyn silver::plugin::silver_plugin::SilverPlugin>),
            _ => None,
        })
    })
    .map_err(|e| FerrumError::Configuration(e.to_string()))?;
    let mut phases = SilFrontendPhases::new(file.into(), plugins);
    phases.configure_consistency(&config.frontend);
    phases.backend_type_format = Some("SMTLIB".into());
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
    let mut session = if config.frontend.ide_mode_advanced || config.report_state_after.is_some() {
        let reporter = CliLoggingReporter(silver::reporter::reporter::StdIoReporter::new(
            std::io::stdout(),
            !config.frontend.no_timing,
        ));
        Session::new_with_reporter(config, Arc::new(reporter))?
    } else {
        Session::new(config)?
    };
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

#[cfg(test)]
mod deadline_tests {
    use super::*;
    #[test]
    fn deadline_handshake_distinguishes_completed_and_expired() {
        let c = CancellationController::default();
        let mut deadline = Deadline::start(60, c.clone()).unwrap();
        assert!(deadline.completed_before_deadline());
        deadline.finish().unwrap();
        assert!(!c.is_cancelled());
        let c = CancellationController::default();
        let mut deadline = Deadline::start(0, c.clone()).unwrap();
        assert!(!deadline.completed_before_deadline());
        // The monitor must latch and invoke callbacks before it may be joined.
        while !c.is_cancelled() {
            std::thread::yield_now();
        }
        deadline.finish().unwrap();
        assert!(c.is_cancelled());
    }

    #[test]
    fn unwinding_deadline_cancels_owner_work() {
        let c = CancellationController::default();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _deadline = Deadline::start(60, c.clone()).unwrap();
            panic!("verification task panicked");
        }));
        assert!(result.is_err());
        assert!(c.is_cancelled());
    }
}

#[cfg(test)]
mod native_verifier_metadata_tests {
    use super::*;
    use silver::verifier::verifier::Verifier;

    #[test]
    fn native_verifier_reports_both_pinned_solver_dependencies() {
        let verifier = SessionVerifier {
            session: None,
            reporter: Arc::new(silver::reporter::reporter::NoopReporter),
            dependencies: SessionVerifier::solver_dependencies(),
        };
        let dependencies = verifier.dependencies();
        let actual: Vec<_> = dependencies
            .iter()
            .map(|d| (d.name(), d.version(), d.location()))
            .collect();
        assert_eq!(
            actual,
            vec![
                ("Z3", "4.5.0", "https://github.com/Z3Prover/z3"),
                ("cvc5", "1.0.0", "https://github.com/cvc5/cvc5")
            ]
        );
        assert_eq!(verifier.version(), env!("CARGO_PKG_VERSION"));
    }
}

#[cfg(test)]
mod run_logging_factory_tests {
    use super::*;
    use silicon::logger::{
        log_config::LogConfig,
        symb_ex_logger::{NativeSymbExLogger, SymbExLog},
    };
    use silver::{
        frontend::frontend::FrontendPhases,
        reporter::{
            message::Message,
            reporter::{NoopReporter, PollingReporter},
        },
    };

    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn timed_out_trace_uses_retained_logs_and_source_timeout_axiom_lists() {
        std::thread::Builder::new()
            .stack_size(VERIFICATION_STACK_SIZE)
            .spawn(|| {
                let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
                let n = 25;
                let vars = (0..n).map(|i| format!("x{i}: Int")).collect::<Vec<_>>();
                let mut clauses = (0..n)
                    .map(|i| format!("(0 <= x{i} && x{i} < {})", n - 1))
                    .collect::<Vec<_>>();
                for i in 0..n {
                    for j in i + 1..n {
                        clauses.push(format!("x{i} != x{j}"));
                    }
                }
                let source = format!(
                    "method hard({}) {{ assert !({}); }}",
                    vars.join(", "),
                    clauses.join(" && ")
                );
                let mut phases = SilFrontendPhases::new(
                    "timeout.vpr".into(),
                    silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                );
                let parsed = phases.parse(&source).unwrap();
                let checked = phases.analyze(parsed).unwrap();
                let program = phases.translate(checked).unwrap();
                for workers in [1, 2] {
                    let config = Config::parse(&[
                        "--ignoreFile".into(),
                        "--z3Exe".into(),
                        z3.clone(),
                        "--numberOfParallelVerifiers".into(),
                        workers.to_string(),
                        "--timeout".into(),
                        "1".into(),
                        "--assertTimeout".into(),
                        "0".into(),
                        "--checkTimeout".into(),
                        "0".into(),
                        "timeout.vpr".into(),
                    ])
                    .unwrap();
                    let root = Arc::new(NativeSymbExLogger::Enabled(SymbExLog::new(
                        LogConfig::default(),
                    )));
                    let owner =
                        RunLogOwner::new(root.clone(), Some(|value| value.to_string()), true)
                            .unwrap();
                    let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                    let mut backend = NativeBackend::new(config);
                    backend.logging = Some(owner);
                    backend.reporter = Some(reporter.clone());
                    let mut silicon = Silicon::new(backend);
                    silicon.configure(&[]).unwrap();
                    silicon.start().unwrap();
                    let SiliconOutcome::BackendResult(VerificationResult::Failure(errors)) =
                        silicon.verify(&program, &[]).unwrap()
                    else {
                        panic!("timeout failure expected")
                    };
                    assert!(
                        errors
                            .iter()
                            .any(|error| error.full_id() == "timeout.error")
                    );
                    let mut traces = 0;
                    let mut terminated = false;
                    while reporter.has_new_message() {
                        match reporter.get_new_message().unwrap() {
                            Message::ExecutionTrace {
                                member_traces,
                                axioms,
                                function_post_axioms,
                            } => {
                                assert!(
                                    !member_traces.is_empty(),
                                    "real method log must be retained"
                                );
                                assert_eq!(member_traces.len(), root.logs().unwrap().len());
                                assert!(
                                    root.logs()
                                        .unwrap()
                                        .iter()
                                        .all(|log| log.is_closed().unwrap())
                                );
                                assert!(axioms.is_empty() && function_post_axioms.is_empty());
                                traces += 1;
                            }
                            Message::VerificationTermination => terminated = true,
                            _ => {}
                        }
                    }
                    assert_eq!(traces, 1);
                    assert!(!terminated);
                    assert!(
                        silicon.backend().logging.is_some(),
                        "timeout must retain the run owner"
                    );
                    let parsed = phases.parse("method after_timeout() {}").unwrap();
                    let checked = phases.analyze(parsed).unwrap();
                    let simple = phases.translate(checked).unwrap();
                    assert!(matches!(
                        silicon.verify(&simple, &[]).unwrap(),
                        SiliconOutcome::BackendResult(VerificationResult::Success)
                    ));
                    let mut next_trace = false;
                    let mut next_termination = false;
                    while reporter.has_new_message() {
                        match reporter.get_new_message().unwrap() {
                            Message::ExecutionTrace { member_traces, .. } => {
                                assert!(
                                    member_traces.len() >= 2,
                                    "same root must retain timeout and subsequent member logs"
                                );
                                next_trace = true;
                            }
                            Message::VerificationTermination => {
                                assert!(next_trace);
                                next_termination = true;
                            }
                            _ => {}
                        }
                    }
                    assert!(next_trace && next_termination);
                    silicon.stop().unwrap();
                }
                struct RejectTimeoutTrace(std::sync::atomic::AtomicUsize);
                impl silver::reporter::reporter::Reporter for RejectTimeoutTrace {
                    fn name(&self) -> &str {
                        "reject-timeout-trace"
                    }
                    fn report(
                        &self,
                        message: Message,
                    ) -> Result<(), silver::reporter::reporter::ReportError> {
                        if matches!(message, Message::ExecutionTrace { .. }) {
                            self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                            Err(silver::reporter::reporter::ReportError::Unsupported(
                                "timeout trace rejected",
                            ))
                        } else {
                            Ok(())
                        }
                    }
                }
                let config = Config::parse(&[
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    z3,
                    "--timeout".into(),
                    "1".into(),
                    "--assertTimeout".into(),
                    "0".into(),
                    "--checkTimeout".into(),
                    "0".into(),
                    "timeout.vpr".into(),
                ])
                .unwrap();
                let root = Arc::new(NativeSymbExLogger::Enabled(SymbExLog::new(
                    LogConfig::default(),
                )));
                let owner =
                    RunLogOwner::new(root.clone(), Some(|value| value.to_string()), true).unwrap();
                let reporter = Arc::new(RejectTimeoutTrace(std::sync::atomic::AtomicUsize::new(0)));
                let mut backend = NativeBackend::new(config);
                backend.logging = Some(owner);
                backend.reporter = Some(reporter.clone());
                let mut silicon = Silicon::new(backend);
                silicon.configure(&[]).unwrap();
                silicon.start().unwrap();
                let error = silicon
                    .verify(&program, &[])
                    .err()
                    .expect("trace rejection must propagate");
                assert!(format!("{error:?}").contains("timeout trace rejected"));
                assert_eq!(reporter.0.load(std::sync::atomic::Ordering::SeqCst), 1);
                assert!(
                    root.logs()
                        .unwrap()
                        .iter()
                        .all(|log| log.is_closed().unwrap())
                );
                silicon.stop().unwrap();
                let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
                let config = Config::parse(&[
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    z3,
                    "--numberOfParallelVerifiers".into(),
                    "2".into(),
                    "--timeout".into(),
                    "1".into(),
                    "--assertTimeout".into(),
                    "0".into(),
                    "--checkTimeout".into(),
                    "0".into(),
                    "timeout.vpr".into(),
                ])
                .unwrap();
                let root = Arc::new(NativeSymbExLogger::Enabled(SymbExLog::new(
                    LogConfig::default(),
                )));
                let owner =
                    RunLogOwner::new(root.clone(), Some(|value| value.to_string()), true).unwrap();
                let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                let mut backend = NativeBackend::new(config);
                backend.logging = Some(owner);
                backend.reporter = Some(reporter.clone());
                let mut silicon = Silicon::new(backend);
                silicon.configure(&[]).unwrap();
                silicon.start().unwrap();
                let pool = match silicon.backend().context.as_ref().unwrap() {
                    OwnedContext::ParallelStdio(context) => context.pool.as_ref().unwrap().clone(),
                    _ => panic!("parallel context expected"),
                };
                let error = silicon
                    .verify(&program, &[])
                    .err()
                    .expect("outstanding worker pool must block trace");
                assert!(format!("{error:?}").contains("still borrowed"));
                while reporter.has_new_message() {
                    assert!(!matches!(
                        reporter.get_new_message().unwrap(),
                        Message::ExecutionTrace { .. }
                    ));
                }
                assert!(
                    root.logs()
                        .unwrap()
                        .iter()
                        .all(|log| !log.is_closed().unwrap())
                );
                drop(pool);
                // Interrupted workers can report BrokenPipe while still joining successfully.
                let _cleanup = silicon.stop();
                assert!(
                    root.logs()
                        .unwrap()
                        .iter()
                        .all(|log| log.is_closed().unwrap())
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn logger_cleanup_keeps_primary_and_cleanup_failures() {
        let primary = FerrumError::Execution("solver stop".into());
        let cleanup = FerrumError::Execution("logger close".into());
        assert!(
            matches!(combine_logger_cleanup(Err(primary), Err(cleanup)), Err(FerrumError::Cleanup { primary, cleanup }) if primary.to_string() == "solver stop" && cleanup.to_string() == "logger close")
        );
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn run_owned_logger_reaches_main_and_method_workers() {
        std::thread::Builder::new()
            .stack_size(VERIFICATION_STACK_SIZE)
            .spawn(|| {
                let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
                for workers in [1, 2] {
                    let config = Config::parse(&[
                        "--ignoreFile".into(),
                        "--z3Exe".into(),
                        z3.clone(),
                        "--numberOfParallelVerifiers".into(),
                        workers.to_string(),
                        "injected.vpr".into(),
                    ])
                    .unwrap();
                    let root = Arc::new(NativeSymbExLogger::Enabled(SymbExLog::new(
                        LogConfig::default(),
                    )));
                    // Explicit test formatter: production activation must supply a source-compatible one.
                    let owner = silicon::logger::run_owner::RunLogOwner::new(
                        root.clone(),
                        Some(|value| value.to_string()),
                        true,
                    )
                    .unwrap();
                    let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                    let mut backend = NativeBackend::new(config);
                    backend.logging = Some(owner);
                    backend.reporter = Some(reporter.clone());
                    let mut silicon = Silicon::new(backend);
                    silicon.configure(&[]).unwrap();
                    silicon.start().unwrap();
                    let mut phases = SilFrontendPhases::new(
                        "injected.vpr".into(),
                        silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                    );
                    let parsed = phases
                        .parse("method first() {} method second() {}")
                        .unwrap();
                    let checked = phases.analyze(parsed).unwrap();
                    let program = phases.translate(checked).unwrap();
                    assert!(matches!(
                        silicon.verify(&program, &[]).unwrap(),
                        SiliconOutcome::BackendResult(VerificationResult::Success)
                    ));
                    let names: Vec<_> = root
                        .logs()
                        .unwrap()
                        .iter()
                        .map(|log| log.records().unwrap().len())
                        .collect();
                    assert_eq!(
                        names.len(),
                        2,
                        "both methods must contribute to the shared root"
                    );
                    assert!(names.iter().all(|count| *count > 0));
                    let mut trace = None;
                    let mut terminated = false;
                    while reporter.has_new_message() {
                        match reporter.get_new_message().unwrap() {
                            message @ Message::ExecutionTrace { .. } => {
                                assert!(!terminated);
                                trace = Some(message);
                            }
                            Message::VerificationTermination => {
                                assert!(trace.is_some());
                                terminated = true;
                            }
                            _ => {}
                        }
                    }
                    assert!(trace.is_some() && terminated);
                    struct RejectTrace(std::sync::atomic::AtomicUsize);
                    impl silver::reporter::reporter::Reporter for RejectTrace {
                        fn name(&self) -> &str {
                            "reject-trace"
                        }
                        fn report(
                            &self,
                            message: Message,
                        ) -> Result<(), silver::reporter::reporter::ReportError>
                        {
                            if matches!(message, Message::ExecutionTrace { .. }) {
                                Err(silver::reporter::reporter::ReportError::Unsupported(
                                    "test trace rejection",
                                ))
                            } else {
                                if matches!(message, Message::VerificationTermination) {
                                    self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                                }
                                Ok(())
                            }
                        }
                    }
                    let reject = Arc::new(RejectTrace(std::sync::atomic::AtomicUsize::new(0)));
                    silicon.backend_mut().reporter = Some(reject.clone());
                    assert!(silicon.verify(&program, &[]).is_err());
                    assert_eq!(reject.0.load(std::sync::atomic::Ordering::SeqCst), 0);
                    if workers == 2 {
                        let retained_pool = match silicon.backend().context.as_ref().unwrap() {
                            OwnedContext::ParallelStdio(context) => {
                                context.pool.as_ref().unwrap().clone()
                            }
                            _ => panic!("parallel context expected"),
                        };
                        assert!(silicon.stop().is_err());
                        assert!(
                            root.logs()
                                .unwrap()
                                .iter()
                                .all(|log| !log.is_closed().unwrap())
                        );
                        drop(retained_pool);
                    }
                    silicon.stop().unwrap();
                    silicon.stop().unwrap();
                    assert!(
                        root.logs()
                            .unwrap()
                            .iter()
                            .all(|log| log.is_closed().unwrap())
                    );
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

#[cfg(test)]
mod direct_session_reporter_tests {
    use super::*;
    use silver::{
        frontend::frontend::FrontendPhases,
        reporter::{
            message::Message,
            reporter::{NoopReporter, PollingReporter, ReportError, Reporter},
        },
    };

    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn direct_session_reports_events_and_propagates_reporter_failure() {
        struct RejectEntity;
        impl Reporter for RejectEntity {
            fn name(&self) -> &str {
                "reject-entity"
            }
            fn report(&self, message: Message) -> Result<(), ReportError> {
                if matches!(message, Message::EntitySuccess { .. }) {
                    Err(ReportError::Unsupported("entity rejected"))
                } else {
                    Ok(())
                }
            }
        }
        std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
            let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
            let mut phases = SilFrontendPhases::new("injected.vpr".into(), silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            let parsed = phases.parse("method m() { assert true; }").unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            for workers in [1, 2] {
                let config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "--numberOfParallelVerifiers".into(), workers.to_string(), "injected.vpr".into()]).unwrap();
                let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                let mut session = Session::new_with_reporter(config.clone(), reporter.clone()).unwrap();
                assert!(matches!(session.verify(&program, &[]).unwrap(), VerificationResult::Success));
                assert!(matches!(reporter.get_new_message().unwrap(), Message::EntitySuccess { concerning, .. } if concerning.name() == "m"));
                assert!(matches!(reporter.get_new_message().unwrap(), Message::VerificationTermination));
                session.stop().unwrap();
                let mut session = Session::new_with_reporter(config.clone(), Arc::new(RejectEntity)).unwrap();
                assert!(session.verify(&program, &[]).is_err());
                session.stop().unwrap();
                let mut unsupported = config;
                unsupported.enable_debugging = true;
                assert!(Session::new_with_reporter(unsupported, Arc::new(NoopReporter)).is_err());
            }
        }).unwrap().join().unwrap();
    }
}

#[cfg(test)]
mod configured_logging_setup_tests {
    use super::*;
    use silver::{
        frontend::frontend::FrontendPhases,
        reporter::{
            message::Message,
            reporter::{NoopReporter, PollingReporter},
        },
    };

    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn configured_logger_uses_start_reporter_and_requires_reporter() {
        std::thread::Builder::new()
            .stack_size(VERIFICATION_STACK_SIZE)
            .spawn(|| {
                let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
                let mut phases = SilFrontendPhases::new(
                    "injected.vpr".into(),
                    silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                );
                let parsed = phases
                    .parse("method first() {} method second() {}")
                    .unwrap();
                let checked = phases.analyze(parsed).unwrap();
                let program = phases.translate(checked).unwrap();
                for workers in [1, 2] {
                    let config = Config::parse(&[
                        "--ignoreFile".into(),
                        "--z3Exe".into(),
                        z3.clone(),
                        "--numberOfParallelVerifiers".into(),
                        workers.to_string(),
                        "--ideModeAdvanced".into(),
                        "injected.vpr".into(),
                    ])
                    .unwrap();
                    assert!(Session::new(config.clone()).is_err());
                    let earlier = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                    let current = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                    let mut backend = NativeBackend::new(config);
                    backend.reporter = Some(earlier.clone());
                    backend.reporter = Some(current.clone());
                    let mut silicon = Silicon::new(backend);
                    silicon.configure(&[]).unwrap();
                    silicon.start().unwrap();
                    for _ in 0..2 {
                        assert!(matches!(
                            silicon.verify(&program, &[]).unwrap(),
                            SiliconOutcome::BackendResult(VerificationResult::Success)
                        ));
                        let mut trace = false;
                        let mut terminated = false;
                        while current.has_new_message() {
                            match current.get_new_message().unwrap() {
                                Message::ExecutionTrace { member_traces, .. } => {
                                    assert_eq!(member_traces.len(), 2);
                                    trace = true;
                                }
                                Message::VerificationTermination => {
                                    assert!(trace);
                                    terminated = true;
                                }
                                _ => {}
                            }
                        }
                        assert!(trace && terminated);
                    }
                    assert!(!earlier.has_new_message());
                    silicon.stop().unwrap();
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn configured_state_reporting_preserves_callback_failures_in_warning_sink() {
        use silicon::{
            decider::z3_prover_std_io, logger::records::data::data_record::FullStateRecordFactory,
            supporters::method_supporter::MethodVerificationServices,
            verifier::verification_pool_manager::native_method_worker,
        };
        use silver::{
            ast::program::{Method, MethodData},
            reporter::reporter::{ReportError, Reporter},
        };
        struct RejectState(std::sync::mpsc::Sender<()>);
        impl Reporter for RejectState {
            fn name(&self) -> &str {
                "reject-state"
            }
            fn report(&self, message: Message) -> Result<(), ReportError> {
                if matches!(message, Message::VerifierState { .. }) {
                    let _ = self.0.send(());
                    Err(ReportError::Unsupported("state callback rejected"))
                } else {
                    Ok(())
                }
            }
        }
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let mut config = Config::default();
        config.report_state_after = Some(1);
        let (tx, rx) = std::sync::mpsc::channel();
        let warnings = Arc::new(Mutex::new(Vec::new()));
        let owner = configured_run_log_owner(
            &config,
            Some(Arc::new(RejectState(tx))),
            factory.clone(),
            warnings.clone(),
        )
        .unwrap();
        let prover = z3_prover_std_io::new(
            "test".into(),
            z3_prover_std_io::settings("z3".into()),
            factory.clone(),
            |_| {},
        );
        let identifiers = prover.identifier_factory();
        let worker_config = Config::default();
        let mut worker = native_method_worker(
            "test".into(),
            prover,
            identifiers,
            factory,
            NativeOptions::from_config(&worker_config).unwrap(),
            &worker_config,
        );
        owner
            .attachment()
            .attach(&mut worker.context, Rc::new(FullStateRecordFactory));
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: Default::default(),
        });
        worker.context.open_method_log(&method).unwrap();
        rx.recv_timeout(std::time::Duration::from_secs(3)).unwrap();
        let limit = std::time::Instant::now() + std::time::Duration::from_secs(2);
        while !warnings
            .lock()
            .unwrap()
            .iter()
            .any(|warning| warning.contains("state callback rejected"))
        {
            assert!(
                std::time::Instant::now() < limit,
                "scheduler error was lost"
            );
            std::thread::yield_now();
        }
        owner.close().unwrap();
    }
    #[test]
    fn configured_logging_exposes_bad_log_config_warning() {
        let mut config = Config::default();
        config.frontend.ide_mode_advanced = true;
        config.log_config = Some(format!("/nonexistent-ferrum-config-{}", std::process::id()));
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let warnings = Arc::new(Mutex::new(Vec::new()));
        let owner = configured_run_log_owner(
            &config,
            Some(Arc::new(NoopReporter)),
            factory,
            warnings.clone(),
        )
        .unwrap();
        assert!(
            warnings
                .lock()
                .unwrap()
                .iter()
                .any(|warning| warning.contains("default configuration will be used"))
        );
        owner.close().unwrap();
    }
    #[test]
    fn configured_logging_requires_reporter_and_does_not_bypass_debug() {
        let mut config = Config::default();
        config.frontend.ide_mode_advanced = true;
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        assert!(
            configured_run_log_owner(&config, None, factory, Arc::new(Mutex::new(vec![]))).is_err()
        );
        config.enable_debugging = true;
        let mut backend = NativeBackend::new(config);
        backend.reporter = Some(Arc::new(NoopReporter));
        assert!(backend.start().is_err());
    }
}

#[cfg(test)]
mod postcondition_owner_tests {
    use super::*;
    use silver::frontend::frontend::FrontendPhases;

    #[test]
    fn startup_configuration_report_failure_stops_before_solver_spawn() {
        struct Reject;
        impl silver::reporter::reporter::Reporter for Reject {
            fn name(&self) -> &str {
                "reject"
            }
            fn report(
                &self,
                message: silver::reporter::message::Message,
            ) -> Result<(), silver::reporter::reporter::ReportError> {
                if matches!(
                    message,
                    silver::reporter::message::Message::Simple {
                        kind:
                            silver::reporter::message::SimpleMessageKind::ConfigurationConfirmation,
                        ..
                    }
                ) {
                    return Err(silver::reporter::reporter::ReportError::Unsupported(
                        "configuration rejected",
                    ));
                }
                Ok(())
            }
        }
        let config = Config::parse(&[
            "--ignoreFile".into(),
            "--z3Exe".into(),
            "/missing-solver".into(),
            "test.vpr".into(),
        ])
        .unwrap();
        let mut backend = NativeBackend::new(config);
        backend.reporter = Some(Arc::new(Reject));
        let error = silicon::silicon::SiliconBackend::start(&mut backend).unwrap_err();
        assert!(
            format!("{error:?}").contains("configuration rejected"),
            "{error:?}"
        );
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn function_postcondition_vector_survives_native_context_reset() {
        std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
            let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
            let mut phases = SilFrontendPhases::new("post.vpr".into(), silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            let parsed = phases.parse("function f(x: Int): Int ensures result == x { x } method m() { assert f(1) == 1; }").unwrap();
            let checked = phases.analyze(parsed).unwrap(); let program = phases.translate(checked).unwrap();
            for workers in [1, 2] {
                let config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "--numberOfParallelVerifiers".into(), workers.to_string(), "post.vpr".into()]).unwrap();
                struct Capture(Mutex<Vec<String>>);
                impl silicon::logger::general::Sink for Capture { fn write(&self, message: &str) { self.0.lock().unwrap().push(format!("log: {message}")); } }
                impl silver::reporter::reporter::Reporter for Capture {
                    fn name(&self) -> &str { "capture" }
                    fn report(&self, message: silver::reporter::message::Message) -> Result<(), silver::reporter::reporter::ReportError> {
                        if let silver::reporter::message::Message::Simple { kind: silver::reporter::message::SimpleMessageKind::ConfigurationConfirmation, text } = message { self.0.lock().unwrap().push(format!("report: {text}")); }
                        Ok(())
                    }
                }
                let sink = Arc::new(Capture(Default::default()));
                let mut backend = NativeBackend::new(config); backend.reporter = Some(sink.clone());
                let mut named = std::collections::BTreeMap::new();
                named.insert("viper.silicon.verifier.DefaultMainVerifier-00".into(), "DEBUG".into());
                named.insert("viper.silicon.decider".into(), "DEBUG".into());
                if workers == 2 { named.insert("viper.silicon.verifier.WorkerVerifier-01".into(), "DEBUG".into()); named.insert("viper.silicon.verifier.WorkerVerifier-02".into(), "DEBUG".into()); }
                backend.general_logger = Some(silicon::logger::general::GeneralLogger::new(Some("INFO"), &named, sink.clone()));
                backend.config.prover_config_args.insert("smt.qi.eager_threshold".into(), "10".into());
                let mut silicon = Silicon::new(backend); silicon.configure(&[]).unwrap(); silicon.start().unwrap();
                assert!(matches!(silicon.verify(&program, &[]).unwrap(), SiliconOutcome::BackendResult(VerificationResult::Success)));
                let first = silicon.backend().postcondition_axioms.borrow().len(); assert!(first > 0);
                assert!(matches!(silicon.verify(&program, &[]).unwrap(), SiliconOutcome::BackendResult(VerificationResult::Success)));
                assert_eq!(silicon.backend().postcondition_axioms.borrow().len(), first * 2);
                let events = sink.0.lock().unwrap();
                let config_events: Vec<_> = events.iter().filter(|e| e.contains("Additional prover configuration options")).collect();
                let starts_reported = events.iter().filter(|e| e.starts_with("report: Starting prover at location")).count();
                let starts_logged = events.iter().filter(|e| e.starts_with("log: Starting prover at location")).count();
                assert!(starts_reported >= 2 && starts_reported == starts_logged, "{events:?}");
                let version_reports = events.iter().filter(|e| e.starts_with("report: Using Z3 ")).count();
                let version_logs = events.iter().filter(|e| e.starts_with("log: Using Z3 ")).count();
                let expected_provers = if workers == 1 { 1 } else { workers + 1 };
                assert_eq!(version_reports, expected_provers, "{events:?}");
                assert_eq!(version_logs, expected_provers, "{events:?}");
                assert_eq!(config_events.len(), 4, "report then log once per verification");
                assert!(config_events[0].starts_with("report: ") && config_events[1].starts_with("log: ") && config_events[2].starts_with("report: ") && config_events[3].starts_with("log: "));
                assert!(events.iter().any(|e| e.contains("EVAL ")), "recursive evaluation debug event missing: {events:?}");
                assert!(events.iter().any(|e| e.contains("EXECUTE ")), "statement debug event missing: {events:?}");
                assert!(events.iter().any(|e| e.contains("PRODUCE ")), "production debug event missing: {events:?}");
                assert!(events.iter().any(|e| e.contains("CONSUME ")), "consumption debug event missing: {events:?}");
                assert!(events.iter().any(|e| e.contains("Store: ") && e.contains("Heap: ")), "evaluation state missing: {events:?}");
                assert!(events.iter().any(|e| e.contains("----- Well-definedness of specifications -----")));
                assert!(events.iter().any(|e| e.contains("----- Verification of function body and postcondition -----")));
                if workers == 2 { assert!(events.iter().any(|e| e.contains("---------- METHOD m----------")), "worker debug logger was not attached: {events:?}"); }
                drop(events);
                let parsed = phases.parse("function bad(x: Int): Int ensures result == x + 1 { x }").unwrap();
                let checked = phases.analyze(parsed).unwrap();
                let invalid = phases.translate(checked).unwrap();
                assert!(matches!(silicon.verify(&invalid, &[]).unwrap(), SiliconOutcome::BackendResult(VerificationResult::Failure(_))));
                let events = sink.0.lock().unwrap();
                assert!(events.iter().any(|e| e.contains("Silicon finished verification of function `f`") && e.contains("Verification successful.")), "{events:?}");
                assert!(events.iter().any(|e| e.contains("Silicon finished verification of function `bad`") && e.contains("Verification failed with")), "{events:?}");
                drop(events);
                assert_eq!(silicon.backend().postcondition_axioms.borrow().len(), first * 3, "postcondition is retained when phase two fails");
                silicon.stop().unwrap();
            }
        }).unwrap().join().unwrap();
    }
}

#[cfg(unix)]
#[test]
#[ignore = "requires real Z3, Python 3; set FERRUM_TEST_Z3"]
fn public_session_delivers_stalled_state_and_preserves_reporter_error() {
    use silver::frontend::frontend::FrontendPhases;
    use silver::reporter::message::Message;
    use silver::reporter::reporter::{ReportError, Reporter};
    struct RejectState {
        sent: std::sync::mpsc::Sender<()>,
        held: std::path::PathBuf,
        resume: std::path::PathBuf,
    }
    impl Reporter for RejectState {
        fn name(&self) -> &str {
            "reject-state"
        }
        fn report(&self, message: Message) -> Result<(), ReportError> {
            if matches!(message, Message::VerifierState { .. }) {
                assert!(
                    self.held.exists(),
                    "state report arrived before the held verifier query"
                );
                std::fs::write(&self.resume, b"resume").unwrap();
                let _ = self.sent.send(());
                Err(ReportError::Unsupported("state rejected"))
            } else {
                Ok(())
            }
        }
    }
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let n = 14;
            let vars = (0..n).map(|i| format!("x{i}: Int")).collect::<Vec<_>>();
            let mut clauses = (0..n)
                .map(|i| format!("(0 <= x{i} && x{i} < {})", n - 1))
                .collect::<Vec<_>>();
            for i in 0..n {
                for j in i + 1..n {
                    clauses.push(format!("x{i} != x{j}"));
                }
            }
            let source = format!(
                "method hard({}) {{ assert !({}); }}",
                vars.join(", "),
                clauses.join(" && ")
            );
            let mut phases = SilFrontendPhases::new(
                "state.vpr".into(),
                silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
            );
            let parsed = phases.parse(&source).unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            use std::os::unix::fs::PermissionsExt;
            struct ProxyDir(std::path::PathBuf);
            impl Drop for ProxyDir {
                fn drop(&mut self) {
                    let _ = std::fs::remove_dir_all(&self.0);
                }
            }
            let stamp = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let dir = ProxyDir(
                std::env::temp_dir()
                    .join(format!("ferrum-state-proxy-{}-{stamp}", std::process::id())),
            );
            std::fs::create_dir(&dir.0).unwrap();
            let proxy = dir.0.join("z3-proxy");
            let held = dir.0.join("held");
            let resume = dir.0.join("resume");
            let timeout = dir.0.join("timeout");
            let reaped = dir.0.join("reaped");
            // The first check is preamble setup; the third reaches the nested
            // member evaluation. Hold that Z3 query until its state report.
            // A timeout prevents a broken reporter from deadlocking the test.
            let script = format!(
                r#"#!/usr/bin/env python3
import os, pathlib, subprocess, sys, time
child = subprocess.Popen([os.environ['FERRUM_TEST_Z3'], *sys.argv[1:]], stdin=subprocess.PIPE)
held = pathlib.Path({held:?})
resume = pathlib.Path({resume:?})
timeout = pathlib.Path({timeout:?})
reaped = pathlib.Path({reaped:?})
checks = 0
try:
    for line in sys.stdin.buffer:
        if line.lstrip().startswith(b'(check-sat'):
            checks += 1
            if checks == 3:
                held.write_text('held')
                deadline = time.monotonic() + 15
                while not resume.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                if not resume.exists():
                    timeout.write_text('timeout')
        child.stdin.write(line)
        child.stdin.flush()
        if line.strip() == b'(exit)':
            break
finally:
    child.stdin.close()
    try:
        child.wait(timeout=5)
    except subprocess.TimeoutExpired:
        child.kill()
        child.wait(timeout=5)
    reaped.write_text('reaped')
"#,
                held = held.to_str().unwrap(),
                resume = resume.to_str().unwrap(),
                timeout = timeout.to_str().unwrap()
            );
            std::fs::write(&proxy, script).unwrap();
            std::fs::set_permissions(&proxy, std::fs::Permissions::from_mode(0o700)).unwrap();
            let z3 = proxy.to_string_lossy().into_owned();
            let config = Config::parse(&[
                "--ignoreFile".into(),
                "--z3Exe".into(),
                z3,
                "--assertTimeout".into(),
                "5000".into(),
                "--checkTimeout".into(),
                "0".into(),
                "--reportStateAfter".into(),
                "1".into(),
                "state.vpr".into(),
            ])
            .unwrap();
            let (reports_tx, reports_rx) = std::sync::mpsc::channel();
            let reporter = Arc::new(RejectState {
                sent: reports_tx,
                held: held.clone(),
                resume,
            });
            let mut session = Session::new_with_reporter(config, reporter).unwrap();
            let outcome = session.verify(&program, &[]);
            assert!(
                outcome.is_ok(),
                "verification execution failed: {outcome:?}"
            );
            reports_rx
                .recv_timeout(std::time::Duration::from_secs(2))
                .expect("stalled state report");
            assert!(
                session
                    .take_warnings()
                    .iter()
                    .any(|warning| warning.contains("state rejected"))
            );
            assert!(
                !timeout.exists(),
                "held query timed out before a state report"
            );
            // Stop the real solver through the proxy and observe it being reaped
            // before the stdio prover terminates the proxy process.
            let Some(OwnedContext::Stdio(context)) = session.silicon.backend_mut().context.as_mut()
            else {
                panic!("expected single stdio context")
            };
            context.base.decider.prover.write_line("(exit)").unwrap();
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
            while !reaped.exists() && std::time::Instant::now() < deadline {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            assert!(reaped.exists(), "proxy did not reap the real solver");
            session.stop().unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}

#[cfg(test)]
mod public_logging_tests {
    use super::*;
    use silver::{
        frontend::frontend::FrontendPhases,
        reporter::{
            message::Message,
            reporter::{NoopReporter, PollingReporter},
        },
    };

    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn public_state_reporting_allows_session_reuse() {
        std::thread::Builder::new()
            .stack_size(VERIFICATION_STACK_SIZE)
            .spawn(|| {
                let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
                let mut phases = SilFrontendPhases::new(
                    "state.vpr".into(),
                    silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                );
                for workers in [1, 2] {
                    let config = Config::parse(&[
                        "--ignoreFile".into(),
                        "--z3Exe".into(),
                        z3.clone(),
                        "--numberOfParallelVerifiers".into(),
                        workers.to_string(),
                        "--reportStateAfter".into(),
                        "1".into(),
                        "state.vpr".into(),
                    ])
                    .unwrap();
                    let mut session =
                        Session::new_with_reporter(config, Arc::new(NoopReporter)).unwrap();
                    for (source, expected) in [
                        ("method m() { assert true; }", true),
                        ("method m() { assert false; }", false),
                        ("method m() { assert true; }", true),
                    ] {
                        let parsed = phases.parse(source).unwrap();
                        let checked = phases.analyze(parsed).unwrap();
                        let program = phases.translate(checked).unwrap();
                        assert_eq!(
                            matches!(
                                session.verify(&program, &[]).unwrap(),
                                VerificationResult::Success
                            ),
                            expected
                        );
                    }
                    session.stop().unwrap();
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn public_advanced_trace_renders_domain_function_predicate_and_quantified_permissions() {
        std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
            let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
            let prefix = "domain D { function value(): Int axiom fixed { value() == 1 } } field fld: Int predicate P(r: Ref) { acc(r.fld) } function f(x: Int): Int ensures result == x { x }";
            for workers in [1, 2] {
                for (assertion, expected) in [("f(value()) == 1", true), ("f(value()) == 2", false)] {
                    let source = format!("{prefix} method m() requires forall x: Ref :: x != null ==> acc(x.fld) {{ assert {assertion}; }}");
                    let mut phases = SilFrontendPhases::new("trace.vpr".into(), silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
                    let parsed = phases.parse(&source).unwrap(); let checked = phases.analyze(parsed).unwrap(); let program = phases.translate(checked).unwrap();
                    let config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "--numberOfParallelVerifiers".into(), workers.to_string(), "--ideModeAdvanced".into(), "trace.vpr".into()]).unwrap();
                    let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                    let mut session = Session::new_with_reporter(config, reporter.clone()).unwrap();
                    let outcome = session.verify(&program, &[]).unwrap();
                    assert_eq!(matches!(outcome, VerificationResult::Success), expected, "{assertion}, workers={workers}");
                    let mut traces = 0; let mut ended = false;
                    while reporter.has_new_message() { match reporter.get_new_message().unwrap() {
                        trace @ Message::ExecutionTrace { .. } => { let text = trace.render_source().unwrap(); assert!(text.contains("axioms=List(")); traces += 1; },
                        Message::VerificationTermination => { assert_eq!(traces, 1); ended = true; }, _ => {}
                    }}
                    assert_eq!(traces, 1); assert!(ended); session.stop().unwrap();
                }
            }
        }).unwrap().join().unwrap();
    }

    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn public_trace_preserves_postcondition_axioms_across_resets_and_phase_two_failure() {
        std::thread::Builder::new()
            .stack_size(VERIFICATION_STACK_SIZE)
            .spawn(|| {
                let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
                let mut phases = SilFrontendPhases::new(
                    "post.vpr".into(),
                    silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                );
                let parsed = phases
                    .parse("function f(x: Int): Int ensures result == x { x }")
                    .unwrap();
                let checked = phases.analyze(parsed).unwrap();
                let good = phases.translate(checked).unwrap();
                let parsed = phases
                    .parse("function bad(x: Int): Int ensures result == x + 1 { x }")
                    .unwrap();
                let checked = phases.analyze(parsed).unwrap();
                let bad = phases.translate(checked).unwrap();
                for workers in [1, 2] {
                    let config = Config::parse(&[
                        "--ignoreFile".into(),
                        "--z3Exe".into(),
                        z3.clone(),
                        "--numberOfParallelVerifiers".into(),
                        workers.to_string(),
                        "--ideModeAdvanced".into(),
                        "post.vpr".into(),
                    ])
                    .unwrap();
                    let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                    let mut session = Session::new_with_reporter(config, reporter.clone()).unwrap();
                    let mut counts = Vec::new();
                    for (program, success) in [(&good, true), (&good, true), (&bad, false)] {
                        assert_eq!(
                            matches!(
                                session.verify(program, &[]).unwrap(),
                                VerificationResult::Success
                            ),
                            success
                        );
                        while reporter.has_new_message() {
                            if let Message::ExecutionTrace {
                                function_post_axioms,
                                ..
                            } = reporter.get_new_message().unwrap()
                            {
                                counts.push(function_post_axioms.len());
                            }
                        }
                    }
                    assert!(counts[0] > 0);
                    assert_eq!(counts, vec![counts[0], counts[0] * 2, counts[0] * 3]);
                    session.stop().unwrap();
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn injected_api_advanced_trace_and_source_disabled_log_config_policy() {
        std::thread::Builder::new()
            .stack_size(VERIFICATION_STACK_SIZE)
            .spawn(|| {
                let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
                let args = vec![
                    "--z3Exe".into(),
                    z3.clone(),
                    "--disableDefaultPlugins".into(),
                    "--ideModeAdvanced".into(),
                ];
                let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                let mut api = NativeFrontendApi::new(&args, reporter.clone(), false).unwrap();
                let mut phases = SilFrontendPhases::new(
                    "injected.vpr".into(),
                    silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                );
                let parsed = phases.parse("method m() { assert true; }").unwrap();
                let checked = phases.analyze(parsed).unwrap();
                let program = phases.translate(checked).unwrap();
                assert!(matches!(
                    api.verify(&program).unwrap(),
                    VerificationResult::Success
                ));
                let mut saw_trace = false;
                while reporter.has_new_message() {
                    match reporter.get_new_message().unwrap() {
                        trace @ Message::ExecutionTrace { .. } => {
                            trace.render_source().unwrap();
                            saw_trace = true;
                        }
                        Message::VerificationTermination => assert!(saw_trace),
                        _ => {}
                    }
                }
                assert!(saw_trace);
                api.stop().unwrap();
                let unused_config = std::env::temp_dir()
                    .join(format!("ferrum-unused-log-config-{}", std::process::id()));
                std::fs::write(&unused_config, "invalid json").unwrap();
                let config = Config::parse(&[
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    z3,
                    "--logConfig".into(),
                    unused_config.to_string_lossy().into_owned(),
                    "injected.vpr".into(),
                ])
                .unwrap();
                let mut session = Session::new(config).unwrap();
                assert!(matches!(
                    session.verify(&program, &[]).unwrap(),
                    VerificationResult::Success
                ));
                assert!(session.take_warnings().is_empty());
                session.stop().unwrap();
                std::fs::remove_file(unused_config).unwrap();
                assert!(
                    Config::parse(&[
                        "--ignoreFile".into(),
                        "--reportStateAfter".into(),
                        "0".into(),
                        "injected.vpr".into()
                    ])
                    .is_err()
                );
                assert!(
                    Config::parse(&[
                        "--ignoreFile".into(),
                        "--ideModeAdvanced".into(),
                        "--parallelizeBranches".into(),
                        "injected.vpr".into()
                    ])
                    .is_err()
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
