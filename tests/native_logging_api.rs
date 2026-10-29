//! Ferrum native reporting API regression checks described in PLAN.md.
//! Requires real Z3 or a linked Z3 4.16 build.
use ferrum::{
    Session, VERIFICATION_STACK_SIZE,
    silicon::config::Config,
    silver::{
        frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
        plugin::silver_plugin_manager::SilverPluginManager,
        reporter::{
            message::Message,
            reporter::{NoopReporter, PollingReporter},
        },
        verifier::verification_result::VerificationResult,
    },
};
use std::sync::Arc;

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn configured_logging_verifies_and_reuses_session() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
            for workers in [1, 2] {
                for advanced in [false, true] {
                    let mut args = vec![
                        "--ignoreFile".into(),
                        "--prover".into(),
                        prover.clone(),
                        "--numberOfParallelVerifiers".into(),
                        workers.to_string(),
                    ];
                    if prover == "Z3" {
                        args.extend([
                            "--z3Exe".into(),
                            std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"),
                        ]);
                    }
                    if advanced {
                        args.push("--ideModeAdvanced".into());
                    } else {
                        args.extend(["--reportStateAfter".into(), "1".into()]);
                    }
                    args.push("test.vpr".into());
                    let config = Config::parse(&args).unwrap();
                    let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                    let mut session = Session::new_with_reporter(config, reporter.clone()).unwrap();
                    let mut phases =
                        SilFrontendPhases::new("test.vpr".into(), SilverPluginManager::new(vec![]));
                    for (source, expected) in [
                        ("method m() { assert true; }", true),
                        ("method m() { assert false; }", false),
                        ("method m() { assert true; }", true),
                    ] {
                        let parsed = phases.parse(source).unwrap();
                        let analyzed = phases.analyze(parsed).unwrap();
                        let program = phases.translate(analyzed).unwrap();
                        assert_eq!(
                            matches!(
                                session.verify(&program, &[]).unwrap(),
                                VerificationResult::Success
                            ),
                            expected
                        );
                        let mut traces = 0;
                        while reporter.has_new_message() {
                            if let Ok(trace @ Message::ExecutionTrace { .. }) =
                                reporter.get_new_message()
                            {
                                trace.render_source().unwrap();
                                traces += 1;
                            }
                        }
                        assert_eq!(traces, usize::from(advanced));
                    }
                    session.stop().unwrap();
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn cli_emits_requested_logging_without_duplicate_results() {
    let path = std::env::temp_dir().join(format!("ferrum-logging-cli-{}.vpr", std::process::id()));
    let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
    for (source, success) in [
        ("method m() { assert true; }", true),
        ("method m() { assert false; }", false),
    ] {
        std::fs::write(&path, source).unwrap();
        for options in [
            &[][..],
            &["--ideModeAdvanced"][..],
            &["--reportStateAfter", "1"][..],
        ] {
            let mut cmd = std::process::Command::new(env!("CARGO_BIN_EXE_ferrum"));
            cmd.arg("--prover").arg(&prover);
            if prover == "Z3" {
                cmd.arg("--z3Exe")
                    .arg(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"));
            }
            let output = cmd.args(options).arg(&path).output().unwrap();
            assert_eq!(
                output.status.success(),
                success,
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert_eq!(
                stdout.matches("Execution trace for the last run:").count(),
                usize::from(options == ["--ideModeAdvanced"])
            );
            if !success {
                assert_eq!(
                    String::from_utf8_lossy(&output.stderr)
                        .matches("assert.failed")
                        .count(),
                    1
                );
            }
        }
    }
    std::fs::remove_file(path).unwrap();
}
