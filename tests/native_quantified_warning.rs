//! Ferrum quantified-trigger warning regression assembly described in PLAN.md.
//! Source: Silicon QuantifiedChunkSupport reports an internal warning and logs WARN.
use ferrum::{
    Session, VERIFICATION_STACK_SIZE,
    silicon::config::Config,
    silver::{
        frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
        plugin::silver_plugin_manager::SilverPluginManager,
        reporter::{
            message::{Message, SimpleMessageKind},
            reporter::{ReportError, Reporter},
        },
        verifier::verification_result::VerificationResult,
    },
};
use std::sync::{Arc, Mutex};

#[derive(Default)]
struct Capture {
    messages: Mutex<Vec<String>>,
    threads: Mutex<Vec<std::thread::ThreadId>>,
    generic: Mutex<usize>,
    reject: bool,
}
impl Reporter for Capture {
    fn name(&self) -> &str {
        "quantified warning capture"
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        match message {
            Message::Simple {
                kind: SimpleMessageKind::InternalWarning,
                text,
            } => {
                if self.reject {
                    return Err(ReportError::Unsupported("rejected quantified warning"));
                }
                self.messages.lock().unwrap().push(text);
                self.threads
                    .lock()
                    .unwrap()
                    .push(std::thread::current().id());
            }
            Message::WarningsDuringVerification { .. } => *self.generic.lock().unwrap() += 1,
            _ => {}
        }
        Ok(())
    }
}
const SOURCE: &str =
    "field f: Int\nmethod m(a: Ref) { inhale forall i: Int :: i == 0 ==> acc(a.f) }";

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn quantified_warning_reports_position_and_preserves_worker_sink() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let owner = std::thread::current().id();
            let mut phases =
                SilFrontendPhases::new("quantified.vpr".into(), SilverPluginManager::new(vec![]));
            let parsed = phases.parse(SOURCE).unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            for workers in [1, 2] {
                let args = vec![
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    std::env::var("FERRUM_TEST_Z3").unwrap(),
                    "--numberOfParallelVerifiers".into(),
                    workers.to_string(),
                    "--logLevel".into(),
                    "ERROR".into(),
                    "quantified.vpr".into(),
                ];
                let config = Config::parse(&args).unwrap();
                let reporter = Arc::new(Capture::default());
                let mut session =
                    Session::new_with_reporter(config.clone(), reporter.clone()).unwrap();
                for round in 1..=2 {
                    assert!(matches!(
                        session.verify(&program, &[]).unwrap(),
                        VerificationResult::Success
                    ));
                    let events = reporter.messages.lock().unwrap();
                    assert_eq!(events.len(), round);
                    assert!(
                        events[round - 1].starts_with(
                            "No triggers available for quantifier at quantified.vpr@2.27"
                        ),
                        "{events:?}"
                    );
                    let warnings = session.take_warnings();
                    assert_eq!(warnings, [events[round - 1].clone()]);
                    assert_eq!(*reporter.generic.lock().unwrap(), 0);
                    if workers == 2 {
                        assert!(
                            reporter
                                .threads
                                .lock()
                                .unwrap()
                                .iter()
                                .any(|id| *id != owner)
                        );
                    }
                    assert!(session.take_warnings().is_empty());
                }
                session.stop().unwrap();
                let reporter = Arc::new(Capture {
                    reject: true,
                    ..Capture::default()
                });
                let mut session = Session::new_with_reporter(config, reporter).unwrap();
                let error = session
                    .verify(&program, &[])
                    .expect_err("reporter rejection must fail");
                let detail = format!("{error:?}");
                assert!(
                    detail.contains("Reporter(Unsupported(")
                        && detail.contains("rejected quantified warning"),
                    "{detail}"
                );
                assert_eq!(session.take_warnings().len(), 1);
                session.stop().unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn quantified_warning_respects_warn_threshold() {
    let file = std::env::temp_dir().join(format!(
        "ferrum-quantified-warning-{}.vpr",
        std::process::id()
    ));
    std::fs::write(&file, SOURCE).unwrap();
    for (level, expect) in [("INFO", true), ("ERROR", false)] {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_ferrum"))
            .args([
                "--z3Exe",
                &std::env::var("FERRUM_TEST_Z3").unwrap(),
                "--logLevel",
                level,
            ])
            .arg(&file)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stdout)
                .contains("No triggers available for quantifier at "),
            expect
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stderr)
                .matches("No triggers available for quantifier at ")
                .count(),
            1
        );
    }
    std::fs::remove_file(file).unwrap();
}

#[test]
fn quantified_warning_reporter_failure_keeps_structural_error() {
    use ferrum::silicon::{
        config::JoinMode,
        decider::{prover_std_io::ProverStdIo, z3_prover_std_io},
        rules::quantified_chunk_support::GeneralQuantifiedProduction,
        state::terms::{TermFactory, TermOptions},
        supporters::predicate_verification_unit::PredicateData,
        verifier::{
            native_context::{
                NativeError, NativeFunctionData, NativeOptions, NativeVerifierContext,
            },
            verification_pool_manager::native_method_worker,
        },
    };
    use ferrum::silver::{
        ast::position::Position, verifier::verification_error::VerificationError,
    };
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
    let error = <NativeVerifierContext<ProverStdIo, PredicateData, NativeFunctionData> as GeneralQuantifiedProduction<PredicateData, NativeFunctionData, JoinMode, VerificationError>>::warn_missing_quantified_triggers(&mut worker.context, &Position::NoPosition).unwrap_err();
    assert!(matches!(
        error,
        NativeError::Reporter(ReportError::Unsupported("rejected quantified warning"))
    ));
    assert_eq!(worker.context.reported_source_warnings.len(), 1);
}
