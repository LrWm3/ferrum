//! Ferrum injected-AST assembly regression checks described in PLAN.md.
//! These exercise the native provider and Silicon session against real Z3.
use ferrum::{
    NativeFrontendApi, VERIFICATION_STACK_SIZE,
    silver::{
        ast::program::Program,
        frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
        plugin::silver_plugin_manager::SilverPluginManager,
        reporter::reporter::NoopReporter,
        verifier::verification_result::VerificationResult,
    },
};
use std::sync::Arc;

fn parsed_program(source: &str) -> Program {
    let mut phases =
        SilFrontendPhases::new("injected.vpr".into(), SilverPluginManager::new(vec![]));
    let parsed = phases.parse(source).unwrap();
    let checked = phases.analyze(parsed).unwrap();
    phases.translate(checked).unwrap()
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn configured_injected_api_verifies_reuses_and_stops() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
            let mut args = vec![
                "--prover".into(),
                prover.clone(),
                "--disableDefaultPlugins".into(),
            ];
            if prover == "Z3" {
                args.extend([
                    "--z3Exe".into(),
                    std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"),
                ]);
            }
            let mut api = NativeFrontendApi::new(&args, Arc::new(NoopReporter), false).unwrap();
            for (source, success) in [
                ("method m() { assert true; }", true),
                ("method m() { assert false; }", false),
                ("method m() { assert true; }", true),
                ("method m() { var p: Perm := epsilon; }", false),
            ] {
                let result = api.verify(&parsed_program(source)).unwrap();
                assert_eq!(
                    matches!(result, VerificationResult::Success),
                    success,
                    "{source}"
                );
            }
            let _warnings = api.take_warnings();
            api.stop().unwrap();
            assert!(
                api.verify(&parsed_program("method m() { assert true; }"))
                    .is_err()
            );
            api.stop().unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}

#[cfg(target_os = "linux")]
#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn failed_initialization_retains_warnings_and_reaps_solver() {
    use std::{os::unix::fs::PermissionsExt, sync::Mutex};
    std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
        let dir = std::env::temp_dir().join(format!("ferrum-api-init-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let script = dir.join("solver");
        let pid_file = dir.join("pid");
        std::fs::write(&script, format!("#!/bin/sh\nprintf 'WARNING injected-startup-warning\\n'\nprintf '%s' $$ > '{}'\nexec \"$FERRUM_TEST_Z3\" \"$@\"\n", pid_file.display())).unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o700)).unwrap();
        let warnings = Arc::new(Mutex::new(Vec::new()));
        let args = vec!["--z3Exe".into(), script.to_string_lossy().into_owned(), "--disableDefaultPlugins".into(), "--plugin".into(), "unknown.Plugin".into()];
        assert!(NativeFrontendApi::new_with_warning_sink(&args, Arc::new(NoopReporter), false, warnings.clone()).is_err());
        assert!(warnings.lock().unwrap().iter().any(|warning| warning.contains("injected-startup-warning")));
        let pid = std::fs::read_to_string(&pid_file).unwrap();
        assert!(!std::path::Path::new("/proc").join(pid).exists(), "solver was not reaped");
        std::fs::write(&script, "#!/bin/sh\nprintf 'WARNING failing-startup-warning\\ninvalid-response\\n'\n").unwrap();
        let warnings = Arc::new(Mutex::new(Vec::new()));
        let args = vec!["--z3Exe".into(), script.to_string_lossy().into_owned(), "--disableDefaultPlugins".into()];
        assert!(NativeFrontendApi::new_with_warning_sink(&args, Arc::new(NoopReporter), false, warnings.clone()).is_err());
        assert!(warnings.lock().unwrap().iter().any(|warning| warning.contains("failing-startup-warning")));
        std::fs::remove_dir_all(dir).unwrap();
    }).unwrap().join().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn injected_reporter_gets_ordered_events_and_failures_propagate() {
    use ferrum::silver::reporter::{
        message::Message,
        reporter::{PollingReporter, ReportError, Reporter},
    };
    struct FailOn {
        trigger: bool,
    }
    impl Reporter for FailOn {
        fn name(&self) -> &str {
            "fail-on-event"
        }
        fn report(&self, message: Message) -> Result<(), ReportError> {
            if (self.trigger && matches!(message, Message::QuantifierChosenTriggers { .. }))
                || (!self.trigger && matches!(message, Message::EntitySuccess { .. }))
            {
                Err(ReportError::Unsupported("injected reporter failure"))
            } else {
                Ok(())
            }
        }
    }
    struct FailTermination;
    impl Reporter for FailTermination {
        fn name(&self) -> &str {
            "fail-termination"
        }
        fn report(&self, message: Message) -> Result<(), ReportError> {
            if matches!(message, Message::VerificationTermination) {
                Err(ReportError::Unsupported("termination"))
            } else {
                Ok(())
            }
        }
    }
    std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
        let source = "function f(x:Int):Int { x } predicate P(r:Ref) { true } method m() { assert forall y:Int :: {f(y)} f(y) == y; }";
        let program = parsed_program(source);
        for workers in [1, 2] {
            let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
            let mut args = vec!["--prover".into(), prover.clone(), "--disableDefaultPlugins".into(), "--numberOfParallelVerifiers".into(), workers.to_string()];
            if prover == "Z3" { args.extend(["--z3Exe".into(), std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3")]); }
            let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
            let mut api = NativeFrontendApi::new(&args, reporter.clone(), false).unwrap();
            assert!(matches!(api.verify(&program).unwrap(), VerificationResult::Success));
            let mut events = Vec::new();
            while reporter.has_new_message() { events.push(reporter.get_new_message().unwrap()); }
            let trigger = events.iter().position(|m| matches!(m, Message::QuantifierChosenTriggers { .. })).expect("trigger event");
            let entities: Vec<_> = events.iter().enumerate().filter_map(|(i,m)| matches!(m, Message::EntitySuccess { .. }).then_some(i)).collect();
            let terminations: Vec<_> = events.iter().enumerate().filter_map(|(i,m)| matches!(m, Message::VerificationTermination).then_some(i)).collect();
            assert_eq!(entities.len(), 3, "events: {events:?}");
            let names = entities.iter().map(|index| match &events[*index] { Message::EntitySuccess { concerning, .. } => concerning.name(), _ => unreachable!() }).collect::<Vec<_>>();
            assert_eq!(names, vec!["f", "P", "m"]);
            assert_eq!(terminations.len(), 1, "events: {events:?}");
            assert!(trigger < entities[0] && entities[2] < terminations[0], "events: {events:?}");
            assert!(matches!(api.verify(&parsed_program("method bad() { assert false; }")).unwrap(), VerificationResult::Failure(_)));
            let mut failed_events = Vec::new();
            while reporter.has_new_message() { failed_events.push(reporter.get_new_message().unwrap()); }
            assert!(matches!(failed_events.first(), Some(Message::EntityFailure { concerning, .. }) if concerning.name() == "bad"));
            assert!(matches!(failed_events.last(), Some(Message::VerificationTermination)));
            api.stop().unwrap();
            for trigger in [true, false] {
                let mut api = NativeFrontendApi::new(&args, Arc::new(FailOn { trigger }), false).unwrap();
                assert!(api.verify(&program).is_err());
                api.stop().unwrap();
            }
            let mut api = NativeFrontendApi::new(&args, Arc::new(FailTermination), false).unwrap();
            assert!(api.verify(&program).is_err());
            api.stop().unwrap();
        }
    }).unwrap().join().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn reporter_warning_failure_retains_warning_sink() {
    use ferrum::silver::reporter::{
        message::Message,
        reporter::{PollingReporter, ReportError, Reporter},
    };
    use std::sync::Mutex;
    struct FailWarning;
    impl Reporter for FailWarning {
        fn name(&self) -> &str {
            "fail-warning"
        }
        fn report(&self, message: Message) -> Result<(), ReportError> {
            if matches!(message, Message::WarningsDuringVerification { .. }) {
                Err(ReportError::Unsupported("warning delivery"))
            } else {
                Ok(())
            }
        }
    }
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            for workers in [1, 2] {
                let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
                let mut args = vec!["--prover".into(), prover.clone(), "--disableDefaultPlugins".into(), "--numberOfParallelVerifiers".into(), workers.to_string()];
                if prover == "Z3" { args.extend(["--z3Exe".into(), std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3")]); }
                for source in ["@proverConfigArgs(\"bad\") method m() { assert true; }", "@proverConfigArgs(\"bad\") function f(): Int { 1 }"] {
                let program = parsed_program(source);
                let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                let mut success_api = NativeFrontendApi::new(&args, reporter.clone(), false).unwrap();
                assert!(matches!(success_api.verify(&program).unwrap(), VerificationResult::Success));
                assert!(matches!(reporter.get_new_message().unwrap(), Message::WarningsDuringVerification { warnings } if !warnings.is_empty()));
                assert!(matches!(reporter.get_new_message().unwrap(), Message::EntitySuccess { .. }));
                assert!(matches!(reporter.get_new_message().unwrap(), Message::VerificationTermination));
                success_api.stop().unwrap();
                let sink = Arc::new(Mutex::new(Vec::new()));
                let mut api = NativeFrontendApi::new_with_warning_sink(
                    &args,
                    Arc::new(FailWarning),
                    false,
                    sink.clone(),
                )
                .unwrap();
                assert!(api.verify(&program).is_err());
                assert!(
                    sink.lock()
                        .unwrap()
                        .iter()
                        .any(|w| w.contains("Invalid proverConfigArgs"))
                );
                api.stop().unwrap();
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn injected_builtin_refute_maps_entity_and_final_results() {
    use ferrum::silver::{
        frontend::{
            sil_front_end_config::SilFrontendConfig, sil_frontend::standard_plugin_manager,
        },
        reporter::{message::Message, reporter::PollingReporter},
    };
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let plugin = "viper.silver.plugin.standard.refute.RefutePlugin";
            let parse_args = vec![
                "--ignoreFile".into(),
                "--disableDefaultPlugins".into(),
                "--plugin".into(),
                plugin.into(),
                "injected.vpr".into(),
            ];
            let config = SilFrontendConfig::parse_shared("test", &parse_args);
            let mut phases = SilFrontendPhases::new(
                "injected.vpr".into(),
                standard_plugin_manager(&config).unwrap(),
            );
            let parsed = phases
                .parse("method disproved() { refute false; } method true_refute() { refute true; }")
                .unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            for workers in [1, 2] {
                let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
                let mut args = vec![
                    "--prover".into(),
                    prover.clone(),
                    "--disableDefaultPlugins".into(),
                    "--plugin".into(),
                    plugin.into(),
                    "--numberOfParallelVerifiers".into(),
                    workers.to_string(),
                ];
                if prover == "Z3" {
                    args.extend([
                        "--z3Exe".into(),
                        std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"),
                    ]);
                }
                let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                let mut api = NativeFrontendApi::new(&args, reporter.clone(), false).unwrap();
                let VerificationResult::Failure(errors) = api.verify(&program).unwrap() else {
                    panic!("true refute must fail")
                };
                assert_eq!(
                    errors
                        .iter()
                        .map(|error| error.full_id())
                        .collect::<Vec<_>>(),
                    vec!["refute.failed:refutation.true"]
                );
                let mut success = false;
                let mut failure = false;
                while reporter.has_new_message() {
                    match reporter.get_new_message().unwrap() {
                        Message::EntitySuccess { concerning, .. }
                            if concerning.name() == "disproved" =>
                        {
                            success = true
                        }
                        Message::EntityFailure {
                            concerning, errors, ..
                        } if concerning.name() == "true_refute" => {
                            assert_eq!(
                                errors
                                    .iter()
                                    .map(|error| error.full_id())
                                    .collect::<Vec<_>>(),
                                vec!["refute.failed:refutation.true"]
                            );
                            failure = true;
                        }
                        _ => {}
                    }
                }
                assert!(
                    success && failure,
                    "missing mapped entity outcomes for {workers} workers"
                );
                api.stop().unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn public_parallel_branches_session_reuses_worker_pool() {
    std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
        let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
        for workers in ["1", "2", "4"] {
        for enabled in [false, true] {
            let mut args = vec!["--ignoreFile".into(), "--prover".into(), prover.clone(), "--numberOfParallelVerifiers".into(), workers.into()];
            if enabled { args.push("--parallelizeBranches".into()); }
            if prover == "Z3" { args.extend(["--z3Exe".into(), std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3")]); }
            args.push("injected.vpr".into());
            let config = ferrum::silicon::config::Config::parse(&args).unwrap();
            let mut session = ferrum::Session::new(config).unwrap();
            for (source, expected) in [("method m(b: Bool) returns (r: Int) ensures r > 0 { if (b) { r := 1; } else { r := 2; } }", true), ("method m(b: Bool) returns (r: Int) ensures r > 0 { if (b) { r := 1; } else { r := 0; } }", false), ("method m() { assert true; }", true)] {
                assert_eq!(matches!(session.verify(&parsed_program(source), &[]).unwrap(), VerificationResult::Success), expected);
            }
            session.stop().unwrap();
        }
        }
    }).unwrap().join().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn separate_method_solver_preserves_function_axioms_and_session_reuse() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
            let programs = [
                ("function f(x: Int): Int ensures result == x + 1 { x + 1 } method m(x: Int) { assert f(x) > x; }", true),
                ("function f(x: Int): Int ensures result == x + 1 { x + 1 } method m(x: Int) { assert f(x) == x; }", false),
                ("function f(x: Int): Int ensures result == x + 2 { x + 1 } method m() { assert true; }", false),
                ("function f(x: Int): Int ensures result == x + 2 { x + 2 } method m(x: Int) { assert f(x) == x + 2; }", true),
                ("method m() { assert false; }", false),
                ("method m() { assert true; }", true),
            ].map(|(source, success)| (parsed_program(source), success));
            let mut outcomes = Vec::new();
            for separate in [false, true] {
                let mut args = vec![
                    "--prover".into(), prover.clone(), "--disableDefaultPlugins".into(),
                    "--numberOfParallelVerifiers=1".into(), "--parallelizeBranches=false".into(),
                    format!("--separateMethodSolver={separate}"),
                ];
                if prover == "Z3" {
                    args.extend(["--z3Exe".into(), std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3")]);
                }
                let mut api = NativeFrontendApi::new(&args, Arc::new(NoopReporter), false).unwrap();
                let mut errors = Vec::new();
                for (program, success) in &programs {
                    let result = api.verify(program).unwrap();
                    assert_eq!(matches!(result, VerificationResult::Success), *success);
                    errors.push(match result {
                        VerificationResult::Success => Vec::new(),
                        VerificationResult::Failure(errors) => errors.iter().map(|error| (error.full_id(), error.position().to_string())).collect(),
                    });
                }
                api.stop().unwrap();
                api.stop().unwrap();
                assert!(api.verify(&programs[0].0).is_err());
                outcomes.push(errors);
            }
            assert_eq!(outcomes[0], outcomes[1]);
        })
        .unwrap()
        .join()
        .unwrap();
}
