//! Ferrum trigger-warning regression assembly described in PLAN.md.
//! Source: Silicon Evaluator.scala trigger fallback reports the Silver expression.
use ferrum::{
    Session, VERIFICATION_STACK_SIZE,
    silicon::config::Config,
    silver::{
        frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
        plugin::silver_plugin_manager::SilverPluginManager,
        reporter::{
            message::Message,
            reporter::{ReportError, Reporter},
        },
        verifier::verification_result::{FrontendErrorKind, VerificationResult},
    },
};
use std::sync::{Arc, Mutex};

#[derive(Default)]
struct Capture {
    warnings: Mutex<Vec<String>>,
    positions: Mutex<Vec<String>>,
    batch_sizes: Mutex<Vec<usize>>,
    threads: Mutex<Vec<std::thread::ThreadId>>,
    reject: bool,
}
impl Reporter for Capture {
    fn name(&self) -> &str {
        "trigger warning capture"
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        if let Message::WarningsDuringVerification { warnings } = message {
            if self.reject {
                return Err(ReportError::Unsupported("rejected trigger warning"));
            }
            self.batch_sizes.lock().unwrap().push(warnings.len());
            self.threads
                .lock()
                .unwrap()
                .push(std::thread::current().id());
            for warning in warnings {
                self.positions
                    .lock()
                    .unwrap()
                    .push(warning.position.to_string());
                if let FrontendErrorKind::VerifierWarning(text) = warning.kind {
                    self.warnings.lock().unwrap().push(text);
                }
            }
        }
        Ok(())
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn trigger_fallback_renders_source_and_delivers_worker_warning_errors() {
    std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
        let mut phases = SilFrontendPhases::new("trigger.vpr".into(), SilverPluginManager::new(vec![]));
        let parsed = phases.parse("function f(x: Int): Int requires x != 0 { x }\nmethod m() { inhale forall x: Int :: { f(x) } x != 0 }").unwrap();
        let checked = phases.analyze(parsed).unwrap();
        let program = phases.translate(checked).unwrap();
        for workers in [1, 2] {
            let args = vec!["--ignoreFile".into(), "--z3Exe".into(), std::env::var("FERRUM_TEST_Z3").unwrap(), "--numberOfParallelVerifiers".into(), workers.to_string(), "trigger.vpr".into()];
            let config = Config::parse(&args).unwrap();
            let reporter = Arc::new(Capture::default());
            let mut session = Session::new_with_reporter(config.clone(), reporter.clone()).unwrap();
            assert!(matches!(session.verify(&program, &[]).unwrap(), VerificationResult::Success));
            assert_eq!(*reporter.warnings.lock().unwrap(), ["Might not be able to use trigger f(x), since it is not evaluated while evaluating the body of the quantifier"]);
            assert_eq!(*reporter.positions.lock().unwrap(), ["trigger.vpr@2.40--2.44"]);
            assert_eq!(session.take_warnings().len(), 1);
            assert!(session.take_warnings().is_empty());
            session.stop().unwrap();
            let reporter = Arc::new(Capture { reject: true, ..Capture::default() });
            let mut session = Session::new_with_reporter(config, reporter).unwrap();
            let error = session.verify(&program, &[]).expect_err("warning delivery must propagate failure");
            assert!(format!("{error:?}").contains("Reporter(Unsupported(") && format!("{error:?}").contains("rejected trigger warning"), "{error:?}");
            assert_eq!(session.take_warnings().len(), 1);
            session.stop().unwrap();
        }
    }).unwrap().join().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn trigger_warnings_report_individually_in_source_order_across_resets() {
    std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
        let source = "function f(x: Int): Int requires x != 0 { x }\nfunction g(x: Int): Int requires x != 0 { x }\nmethod m() { inhale forall x: Int :: { f(x) } x == x; inhale forall y: Int :: { g(y) } y == y }";
        let mut phases = SilFrontendPhases::new("trigger.vpr".into(), SilverPluginManager::new(vec![]));
        let parsed = phases.parse(source).unwrap();
        let checked = phases.analyze(parsed).unwrap();
        let program = phases.translate(checked).unwrap();
        for workers in [1, 2] {
            let args = vec!["--ignoreFile".into(), "--z3Exe".into(), std::env::var("FERRUM_TEST_Z3").unwrap(), "--numberOfParallelVerifiers".into(), workers.to_string(), "trigger.vpr".into()];
            let reporter = Arc::new(Capture::default());
            let mut session = Session::new_with_reporter(Config::parse(&args).unwrap(), reporter.clone()).unwrap();
            for round in 1..=2 {
                assert!(matches!(session.verify(&program, &[]).unwrap(), VerificationResult::Success));
                let warnings = reporter.warnings.lock().unwrap();
                assert_eq!(warnings.len(), round * 2, "{warnings:?}");
                assert!(warnings[(round - 1) * 2].contains("trigger f(x),"));
                assert!(warnings[(round - 1) * 2 + 1].contains("trigger g(y),"));
                assert_eq!(session.take_warnings().len(), 2);
                assert!(session.take_warnings().is_empty());
            }
            assert_eq!(*reporter.batch_sizes.lock().unwrap(), [1, 1, 1, 1]);
            session.stop().unwrap();
        }
    }).unwrap().join().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn trigger_warnings_on_workers_with_parallel_branches_enabled() {
    std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
        let owner = std::thread::current().id();
        let source = "function f(x: Int): Int requires x != 0 { x }\nfunction g(x: Int): Int requires x != 0 { x }\nmethod m(b: Bool) { if (b) { inhale forall x: Int :: { f(x) } x == x } else { inhale forall y: Int :: { g(y) } y == y } }";
        let mut phases = SilFrontendPhases::new("trigger.vpr".into(), SilverPluginManager::new(vec![]));
        let parsed = phases.parse(source).unwrap();
        let checked = phases.analyze(parsed).unwrap();
        let program = phases.translate(checked).unwrap();
        let args = vec!["--ignoreFile".into(), "--z3Exe".into(), std::env::var("FERRUM_TEST_Z3").unwrap(), "--parallelizeBranches".into(), "--numberOfParallelVerifiers".into(), "2".into(), "trigger.vpr".into()];
        let reporter = Arc::new(Capture::default());
        let mut session = Session::new_with_reporter(Config::parse(&args).unwrap(), reporter.clone()).unwrap();
        for _ in 0..2 {
            let before = reporter.warnings.lock().unwrap().len();
            let thread_before = reporter.threads.lock().unwrap().len();
            assert!(matches!(session.verify(&program, &[]).unwrap(), VerificationResult::Success));
            let warnings = reporter.warnings.lock().unwrap();
            assert_eq!(warnings.len() - before, 2, "{warnings:?}");
            let batch = &warnings[before..];
            assert!(batch.iter().any(|w| w.contains("trigger f(x),")));
            assert!(batch.iter().any(|w| w.contains("trigger g(y),")));
            drop(warnings);
            let threads = reporter.threads.lock().unwrap();
            assert!(threads[thread_before..].iter().any(|thread| *thread != owner), "no worker-origin warning: {threads:?}");
            assert_eq!(session.take_warnings().len(), 2);
            assert!(session.take_warnings().is_empty());
        }
        session.stop().unwrap();
    }).unwrap().join().unwrap();
}

#[test]
fn trigger_reporter_failure_keeps_structural_error() {
    use ferrum::silicon::{
        config::JoinMode,
        decider::{prover_std_io::ProverStdIo, z3_prover_std_io},
        rules::evaluator::TriggerEvaluationContext,
        state::terms::{TermFactory, TermOptions},
        supporters::predicate_verification_unit::PredicateData,
        verifier::{
            native_context::{
                NativeError, NativeFunctionData, NativeOptions, NativeVerifierContext,
            },
            verification_pool_manager::native_method_worker,
        },
    };
    use ferrum::silver::verifier::verification_error::VerificationError;
    let config = Config::default();
    let factory = TermFactory::new(TermOptions {
        use_flyweight: config.use_flyweight(),
        use_old_axiomatization: config.use_old_axiomatization,
        mask_heap_mode: config.mask_heap_mode,
    });
    let prover = z3_prover_std_io::new(
        "structural-test".into(),
        z3_prover_std_io::settings("unused".into()),
        factory.clone(),
        |_| {},
    );
    let identifiers = prover.identifier_factory();
    let mut worker = native_method_worker(
        "structural-test".into(),
        prover,
        identifiers,
        factory,
        NativeOptions::from_config(&config).unwrap(),
        &config,
    );
    worker
        .context
        .set_preprocessing_reporter(Some(Arc::new(Capture {
            reject: true,
            ..Capture::default()
        })));
    let mut phases = SilFrontendPhases::new("trigger.vpr".into(), SilverPluginManager::new(vec![]));
    let parsed = phases.parse("function f(i: Int): Int { i }").unwrap();
    let checked = phases.analyze(parsed).unwrap();
    let program = phases.translate(checked).unwrap();
    let expression = program.functions[0].body.as_ref().unwrap();
    let error = <NativeVerifierContext<ProverStdIo, PredicateData, NativeFunctionData> as TriggerEvaluationContext<PredicateData, NativeFunctionData, JoinMode, VerificationError>>::warn_trigger(&mut worker.context, expression).unwrap_err();
    assert!(matches!(
        error,
        NativeError::Reporter(ReportError::Unsupported("rejected trigger warning"))
    ));
    assert_eq!(worker.context.reported_source_warnings.len(), 1);
}
