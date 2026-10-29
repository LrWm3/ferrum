//! Ferrum internal warning regression assembly described in PLAN.md.
//! Source: Silicon HeapAccessReplacingExpressionTranslator reports InternalWarningMessage and logs WARN.
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
    internal: Mutex<Vec<String>>,
    threads: Mutex<Vec<std::thread::ThreadId>>,
    generic: Mutex<usize>,
    reject: bool,
    reject_worker_of: Option<std::thread::ThreadId>,
}
impl Reporter for Capture {
    fn name(&self) -> &str {
        "internal warning capture"
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        match message {
            Message::Simple {
                kind: SimpleMessageKind::InternalWarning,
                text,
            } => {
                if self.reject
                    || self
                        .reject_worker_of
                        .is_some_and(|owner| owner != std::thread::current().id())
                {
                    return Err(ReportError::Unsupported("rejected internal warning"));
                }
                self.internal.lock().unwrap().push(text);
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

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn unresolved_warning_uses_internal_category_and_survives_reset() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let mut phases =
                SilFrontendPhases::new("unresolved.vpr".into(), SilverPluginManager::new(vec![]));
            let parsed = phases
                .parse(
                    "function f(i: Int): Int { true ? 0 : f(i) }\nmethod m() { assert f(0) == 0 }",
                )
                .unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            for workers in [1, 2] {
                let args = vec![
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    std::env::var("FERRUM_TEST_Z3").unwrap(),
                    "--logLevel".into(),
                    "ERROR".into(),
                    "--numberOfParallelVerifiers".into(),
                    workers.to_string(),
                    "unresolved.vpr".into(),
                ];
                let config = Config::parse(&args).unwrap();
                let reporter = Arc::new(Capture::default());
                let mut session =
                    Session::new_with_reporter(config.clone(), reporter.clone()).unwrap();
                for expected in 1..=2 {
                    assert!(matches!(
                        session.verify(&program, &[]).unwrap(),
                        VerificationResult::Success
                    ));
                    let warnings = session.take_warnings();
                    assert_eq!(warnings.len(), 1, "{warnings:?}");
                    assert!(
                        warnings[0].contains("Could not resolve expression f(i)"),
                        "{warnings:?}"
                    );
                    assert_eq!(reporter.internal.lock().unwrap().len(), expected);
                    assert_eq!(*reporter.generic.lock().unwrap(), 0);
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
                    .expect_err("internal warning reporter rejection must fail verification");
                let detail = format!("{error:?}");
                assert!(
                    detail.contains("Reporter(Unsupported(")
                        && detail.contains("rejected internal warning"),
                    "{error:?}"
                );
                let warnings = session.take_warnings();
                assert_eq!(warnings.len(), 1, "{warnings:?}");
                session.stop().unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn unresolved_warning_uses_warn_log_level() {
    let file = std::env::temp_dir().join(format!(
        "ferrum-internal-warning-{}.vpr",
        std::process::id()
    ));
    std::fs::write(
        &file,
        "function f(i: Int): Int { true ? 0 : f(i) }\nmethod m() { assert f(0) == 0 }",
    )
    .unwrap();
    for (level, expected) in [("INFO", true), ("ERROR", false)] {
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
            String::from_utf8_lossy(&output.stdout).contains("Could not resolve expression f(i)"),
            expected
        );
        assert_eq!(
            String::from_utf8_lossy(&output.stderr)
                .matches("Could not resolve expression f(i)")
                .count(),
            1
        );
    }
    std::fs::remove_file(file).unwrap();
}

#[test]
fn unresolved_reporter_failure_keeps_structural_error() {
    use ferrum::silicon::{
        decider::z3_prover_std_io,
        state::terms::{TermFactory, TermOptions},
        supporters::functions::heap_access_replacing_expression_translator::HeapExpressionServices,
        verifier::{
            native_context::{NativeError, NativeOptions},
            verification_pool_manager::native_method_worker,
        },
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
    let mut phases =
        SilFrontendPhases::new("unresolved.vpr".into(), SilverPluginManager::new(vec![]));
    let parsed = phases.parse("function f(i: Int): Int { i }").unwrap();
    let checked = phases.analyze(parsed).unwrap();
    let program = phases.translate(checked).unwrap();
    let function = &program.functions[0];
    let expression = function.body.as_ref().unwrap();
    let error = worker
        .context
        .warn_unresolved(expression, function)
        .unwrap_err();
    assert!(matches!(
        error,
        NativeError::Reporter(ReportError::Unsupported("rejected internal warning"))
    ));
    assert_eq!(worker.context.reported_source_warnings.len(), 1);
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn mask_frame_warnings_transfer_from_workers_without_leaking() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let owner = std::thread::current().id();
            let mut phases =
                SilFrontendPhases::new("mask-warning.vpr".into(), SilverPluginManager::new(vec![]));
            let parsed = phases
                .parse(
                    r#"field f: Int
function get(r: Ref): Ref { r }
function foo(r: Ref, n: Int): Bool
  requires (true ? acc(r.f) : acc(get(r).f))
{ forall i: Int :: {foo(r, i)} foo(r, i) == foo(r, i) }
method test(r: Ref, b: Bool) requires acc(r.f) {
  if (b) { assert forall i: Int :: { foo(r, i) } foo(r, i) == foo(r, i) }
  else { assert forall i: Int :: { foo(r, i) } foo(r, i) == foo(r, i) }
}"#,
                )
                .unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            let args = vec![
                "--ignoreFile".into(),
                "--z3Exe".into(),
                std::env::var("FERRUM_TEST_Z3").unwrap(),
                "--logLevel".into(),
                "ERROR".into(),
                "--maskHeapMode".into(),
                "--numberOfParallelVerifiers".into(),
                "2".into(),
                "mask-warning.vpr".into(),
            ];
            let reporter = Arc::new(Capture::default());
            let mut session =
                Session::new_with_reporter(Config::parse(&args).unwrap(), reporter.clone())
                    .unwrap();
            for _ in 0..2 {
                let before = reporter.internal.lock().unwrap().len();
                let thread_before = reporter.threads.lock().unwrap().len();
                assert!(matches!(
                    session.verify(&program, &[]).unwrap(),
                    VerificationResult::Success
                ));
                let warnings = session.take_warnings();
                let internal = reporter.internal.lock().unwrap();
                assert_eq!(
                    warnings.len(),
                    internal.len() - before,
                    "warnings {warnings:?}; events {internal:?}"
                );
                assert!(
                    warnings
                        .iter()
                        .all(|w| w.contains("Could not resolve expression get(r)")),
                    "{warnings:?}"
                );
                drop(internal);
                let threads = reporter.threads.lock().unwrap();
                assert!(
                    threads[thread_before..]
                        .iter()
                        .any(|thread| *thread != owner),
                    "no worker-origin warning: {threads:?}"
                );
                assert_eq!(*reporter.generic.lock().unwrap(), 0);
                assert!(session.take_warnings().is_empty());
            }
            session.stop().unwrap();
            let reporter = Arc::new(Capture {
                reject_worker_of: Some(owner),
                ..Capture::default()
            });
            let mut session =
                Session::new_with_reporter(Config::parse(&args).unwrap(), reporter).unwrap();
            let error = session
                .verify(&program, &[])
                .expect_err("worker warning reporter rejection must propagate");
            let detail = format!("{error:?}");
            assert!(
                detail.contains("Reporter(Unsupported(")
                    && detail.contains("rejected internal warning"),
                "{error:?}"
            );
            let warnings = session.take_warnings();
            assert!(warnings.len() >= 2, "{warnings:?}");
            assert!(session.take_warnings().is_empty());
            session.stop().unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}
