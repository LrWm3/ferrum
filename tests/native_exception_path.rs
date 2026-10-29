//! Ferrum exception-path regressions; see [PLAN.md](../PLAN.md).
#![cfg(unix)]
use std::{fs, os::unix::fs::PermissionsExt, process::Command};

#[test]
#[ignore = "requires real Z3 and python3; set FERRUM_TEST_Z3"]
fn solver_protocol_exception_is_reported_or_propagated_by_option() {
    let dir = std::env::temp_dir().join(format!("ferrum-exception-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let solver = dir.join("solver.py");
    fs::write(&solver, r##"#!/usr/bin/env python3
import os, subprocess, sys, threading
p = subprocess.Popen([os.environ['FERRUM_TEST_Z3'], *sys.argv[1:]], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
def forward():
    for line in sys.stdin:
        try:
            p.stdin.write(line); p.stdin.flush()
        except BrokenPipeError:
            break
    p.stdin.close()
threading.Thread(target=forward, daemon=True).start()
for line in p.stdout:
    sys.stdout.write('bogus\n' if line.strip() in ('sat', 'unsat', 'unknown') else line)
    sys.stdout.flush()
p.wait()
"##).unwrap();
    fs::set_permissions(&solver, fs::Permissions::from_mode(0o755)).unwrap();
    let program = dir.join("case.vpr");
    fs::write(&program, "method m(x: Int) { assert x > 0 }").unwrap();
    for (workers, disabled) in [(1, false), (1, true), (2, false), (2, true)] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_ferrum"));
        cmd.args([
            "--z3Exe",
            solver.to_str().unwrap(),
            "--logLevel",
            "DEBUG",
            "--numberOfParallelVerifiers",
            &workers.to_string(),
        ]);
        if disabled {
            cmd.arg("--disableCatchingExceptions");
        }
        let out = cmd.arg(&program).output().unwrap();
        let output = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(
            output.contains("An exception was thrown while verifying method `m`."),
            "{output}"
        );
        assert!(
            output
                .contains("Unexpected output of prover while trying to refute an assertion: bogus"),
            "{output}"
        );
        if disabled {
            assert!(!output.contains("An exception occurred:"), "{output}");
        } else {
            assert!(
                output.contains("Verification aborted exceptionally:"),
                "{output}"
            );
            assert!(output.contains("An exception occurred:"), "{output}");
            assert!(
                output.contains("Interaction with prover (instance"),
                "{output}"
            );
        }
    }
    let solver_path = solver.to_string_lossy().into_owned();
    std::thread::Builder::new()
        .stack_size(ferrum::VERIFICATION_STACK_SIZE)
        .spawn(move || {
            use ferrum::silver::{
                frontend::frontend::FrontendPhases,
                reporter::{
                    message::Message,
                    reporter::{ReportError, Reporter},
                },
            };
            use std::sync::{
                Arc,
                atomic::{AtomicUsize, Ordering},
            };
            struct Capture {
                count: AtomicUsize,
                reject: bool,
            }
            impl Reporter for Capture {
                fn name(&self) -> &str {
                    "exception-capture"
                }
                fn report(&self, message: Message) -> Result<(), ReportError> {
                    if let Message::Exception { details, .. } = message {
                        assert!(details.unwrap().display.contains("ProverInteractionFailed"));
                        self.count.fetch_add(1, Ordering::SeqCst);
                        if self.reject {
                            return Err(ReportError::Unsupported("exception report rejected"));
                        }
                    }
                    Ok(())
                }
            }
            let mut phases = ferrum::silver::frontend::sil_frontend::SilFrontendPhases::new(
                "case.vpr".into(),
                ferrum::silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
            );
            let parsed = phases.parse("method m(x: Int) { assert x > 0 }").unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            for reject in [false, true] {
                let config = ferrum::silicon::config::Config::parse(&[
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    solver_path.clone(),
                    "case.vpr".into(),
                ])
                .unwrap();
                let reporter = Arc::new(Capture {
                    count: AtomicUsize::new(0),
                    reject,
                });
                let mut session =
                    ferrum::Session::new_with_reporter(config, reporter.clone()).unwrap();
                let result = session.verify(&program, &[]);
                assert_eq!(reporter.count.load(Ordering::SeqCst), 1);
                if reject {
                    assert!(result.is_err());
                } else {
                    assert!(matches!(
                        result.unwrap(),
                        ferrum::silver::verifier::verification_result::VerificationResult::Failure(
                            _
                        )
                    ));
                }
                session.stop().unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn startup_external_tool_exception_obeys_catching_and_frontend_logger_levels() {
    let dir = std::env::temp_dir().join(format!("ferrum-startup-exception-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let program = dir.join("case.vpr");
    fs::write(&program, "method m() {}\n").unwrap();
    let nonexec = dir.join("not-executable");
    fs::write(&nonexec, "not executable").unwrap();
    fs::set_permissions(&nonexec, fs::Permissions::from_mode(0o644)).unwrap();
    for solver in [dir.join("missing"), nonexec] {
        let detail = if solver.exists() {
            "file is not executable"
        } else {
            "not a file"
        };
        for (workers, disabled, debug) in [
            (1, false, true),
            (2, false, true),
            (1, true, true),
            (1, false, false),
        ] {
            let mut cmd = Command::new(env!("CARGO_BIN_EXE_ferrum"));
            cmd.args([
                "--z3Exe",
                solver.to_str().unwrap(),
                "--logLevel",
                "DEBUG",
                "--numberOfParallelVerifiers",
                &workers.to_string(),
            ]);
            if disabled {
                cmd.arg("--disableCatchingExceptions");
            }
            if !debug {
                cmd.arg("-LSiliconFrontend=OFF");
            }
            let out = cmd.arg(&program).output().unwrap();
            let output = format!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            assert!(!out.status.success(), "{output}");
            assert!(output.contains(detail), "{output}");
            assert_eq!(
                output.contains("Verification aborted exceptionally:"),
                !disabled,
                "{output}"
            );
            assert_eq!(
                output.contains("An exception occurred:"),
                !disabled && debug,
                "{output}"
            );
            assert!(!output.contains("Verification failed with"), "{output}");
        }
    }
    {
        use ferrum::silver::reporter::{
            message::Message,
            reporter::{ReportError, Reporter},
        };
        use std::sync::{
            Arc,
            atomic::{AtomicUsize, Ordering},
        };
        struct Reject(AtomicUsize);
        impl Reporter for Reject {
            fn name(&self) -> &str {
                "reject-startup-exception"
            }
            fn report(&self, message: Message) -> Result<(), ReportError> {
                if matches!(message, Message::Exception { .. }) {
                    self.0.fetch_add(1, Ordering::SeqCst);
                    return Err(ReportError::Unsupported(
                        "startup exception report rejected",
                    ));
                }
                Ok(())
            }
        }
        let config = ferrum::silicon::config::Config::parse(&[
            "--ignoreFile".into(),
            "--z3Exe".into(),
            dir.join("missing").to_string_lossy().into_owned(),
            "case.vpr".into(),
        ])
        .unwrap();
        let reporter = Arc::new(Reject(AtomicUsize::new(0)));
        let error = match ferrum::Session::new_with_reporter(config, reporter.clone()) {
            Ok(_) => panic!("startup unexpectedly succeeded"),
            Err(error) => error,
        };
        assert!(
            error
                .to_string()
                .contains("startup exception report rejected"),
            "{error}"
        );
        assert!(error.to_string().contains("not a file"), "{error}");
        assert_eq!(reporter.0.load(Ordering::SeqCst), 1);
    }
    fs::remove_dir_all(dir).unwrap();
}

#[cfg(feature = "native-z3")]
#[test]
#[ignore = "requires linked Z3 4.16"]
fn linked_z3_dynamic_member_option_is_a_source_exception() {
    let dir = std::env::temp_dir().join(format!("ferrum-api-exception-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let program = dir.join("case.vpr");
    fs::write(
        &program,
        "@proverConfigArgs(\"smt.random_seed=1\") method m() { assert true }",
    )
    .unwrap();
    for (workers, disabled) in [(1, false), (1, true), (2, false), (2, true)] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_ferrum"));
        cmd.args([
            "--prover",
            "Z3-API",
            "--logLevel",
            "DEBUG",
            "--numberOfParallelVerifiers",
            &workers.to_string(),
        ]);
        if disabled {
            cmd.arg("--disableCatchingExceptions");
        }
        let out = cmd.arg(&program).output().unwrap();
        let output = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(!out.status.success(), "{output}");
        assert!(
            output.contains(
                "Dynamically setting prover options via Z3 API is currently not supported."
            ),
            "{output}"
        );
        assert_eq!(
            output.contains("An exception occurred:"),
            !disabled,
            "{output}"
        );
        if !disabled {
            assert!(
                output.contains("Interaction with prover (instance"),
                "{output}"
            );
        }
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
#[ignore = "requires real Z3 and python3; set FERRUM_TEST_Z3"]
fn solver_eof_becomes_the_source_prover_interaction_failure() {
    let dir = std::env::temp_dir().join(format!("ferrum-eof-exception-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let solver = dir.join("solver.py");
    fs::write(&solver, r##"#!/usr/bin/env python3
import os, subprocess, sys, threading
p = subprocess.Popen([os.environ['FERRUM_TEST_Z3'], *sys.argv[1:]], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
def forward():
    for line in sys.stdin:
        try:
            p.stdin.write(line); p.stdin.flush()
        except BrokenPipeError:
            break
threading.Thread(target=forward, daemon=True).start()
for line in p.stdout:
    if line.strip() in ('sat', 'unsat', 'unknown'):
        p.kill(); p.wait(); break
    sys.stdout.write(line); sys.stdout.flush()
"##).unwrap();
    fs::set_permissions(&solver, fs::Permissions::from_mode(0o755)).unwrap();
    let program = dir.join("case.vpr");
    fs::write(&program, "method m(x: Int) { assert x > 0 }").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ferrum"))
        .args([
            "--z3Exe",
            solver.to_str().unwrap(),
            "--logLevel",
            "DEBUG",
            "--numberOfParallelVerifiers",
            "1",
        ])
        .arg(&program)
        .output()
        .unwrap();
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        text.contains(
            "Interaction with prover yielded null. This might indicate that the prover crashed."
        ),
        "{text}"
    );
    assert!(
        text.contains("Verification aborted exceptionally:"),
        "{text}"
    );
    assert!(text.contains("An exception occurred:"), "{text}");
    fs::remove_dir_all(dir).unwrap();
}

#[cfg(feature = "native-z3")]
#[test]
#[ignore = "requires linked Z3 4.16"]
fn linked_z3_assertion_failure_has_the_source_tool_error_type() {
    use ferrum::silicon::{
        decider::{
            native_z3::{LinkedProverError, LinkedProverOptions, LinkedZ3Prover},
            z3_prover_api::ApiTimeoutSettings,
        },
        interfaces::decider::prover::Prover,
        state::terms::{TermFactory, TermOptions},
    };
    let factory = TermFactory::new(TermOptions {
        use_flyweight: false,
        use_old_axiomatization: false,
        mask_heap_mode: false,
    });
    let options = LinkedProverOptions {
        timeout: ApiTimeoutSettings {
            default_timeout_ms: 0,
            use_time_bounds: true,
            resources_per_millisecond: 1,
        },
        counterexamples: false,
        report_reason_unknown: false,
        debug: false,
        soft_assertions: false,
        custom_options: vec![],
        disable_nonlinear: false,
    };
    let mut prover = LinkedZ3Prover::new("test", factory.clone(), options);
    prover.start(None).unwrap();
    use ferrum::silicon::state::{
        identifiers::Identifier,
        terms::{Quantifier, Sort, Trigger},
    };
    let x = factory.var(Identifier::new("x"), Sort::Int, false);
    let q = factory.quantification_without_triggers(
        Quantifier::Forall,
        vec![x.clone()],
        factory.greater(x, factory.int_literal(0)),
        "bad-trigger".into(),
        false,
        None,
    );
    let bad = factory
        .quantification_with_raw_triggers(
            &q,
            vec![Trigger {
                terms: vec![factory.int_literal(1)],
            }],
        )
        .unwrap();
    let error = prover.assert_goal(&bad, None).unwrap_err();
    assert!(
        matches!(error, LinkedProverError::SourceToolError(ref message) if message.starts_with("Z3 error: ")),
        "{error:?}"
    );
    prover.stop().unwrap();
}

#[test]
#[ignore = "requires real Z3 and python3; set FERRUM_TEST_Z3"]
fn invalid_solver_version_is_reported_at_startup() {
    let dir = std::env::temp_dir().join(format!("ferrum-version-exception-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let solver = dir.join("solver.py");
    fs::write(&solver, r##"#!/usr/bin/env python3
import os, subprocess, sys, threading
p = subprocess.Popen([os.environ['FERRUM_TEST_Z3'], *sys.argv[1:]], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
def forward():
    for line in sys.stdin:
        try: p.stdin.write(line); p.stdin.flush()
        except BrokenPipeError: break
    p.stdin.close()
threading.Thread(target=forward, daemon=True).start()
for line in p.stdout:
    sys.stdout.write('bogus\n' if line.startswith('(:version') else line); sys.stdout.flush()
p.wait()
"##).unwrap();
    fs::set_permissions(&solver, fs::Permissions::from_mode(0o755)).unwrap();
    let program = dir.join("case.vpr");
    fs::write(&program, "method m() {}\n").unwrap();
    for workers in [1, 2] {
        let output = Command::new(env!("CARGO_BIN_EXE_ferrum"))
            .args([
                "--z3Exe",
                solver.to_str().unwrap(),
                "--logLevel",
                "DEBUG",
                "--numberOfParallelVerifiers",
                &workers.to_string(),
            ])
            .arg(&program)
            .output()
            .unwrap();
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            text.contains("Unexpected output of prover while getting version: bogus"),
            "{text}"
        );
        assert!(
            text.contains("Verification aborted exceptionally:"),
            "{text}"
        );
        assert!(text.contains("An exception occurred:"), "{text}");
        assert!(!text.contains("Verification failed with"), "{text}");
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
#[ignore = "requires real Z3 and python3; set FERRUM_TEST_Z3"]
fn malformed_quantifier_profile_is_a_caught_native_ordinary_exception() {
    let dir = std::env::temp_dir().join(format!("ferrum-quant-exception-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let solver = dir.join("solver.py");
    fs::write(&solver, r##"#!/usr/bin/env python3
import os, subprocess, sys, threading
p = subprocess.Popen([os.environ['FERRUM_TEST_Z3'], *sys.argv[1:]], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
def forward():
    for line in sys.stdin:
        try: p.stdin.write(line); p.stdin.flush()
        except BrokenPipeError: break
    p.stdin.close()
threading.Thread(target=forward, daemon=True).start()
for line in p.stdout:
    if line.strip() in ('sat', 'unsat', 'unknown'): sys.stdout.write('[quantifier_instances] q : abc : 1 : 2\n')
    sys.stdout.write(line); sys.stdout.flush()
p.wait()
"##).unwrap();
    fs::set_permissions(&solver, fs::Permissions::from_mode(0o755)).unwrap();
    let program = dir.join("case.vpr");
    fs::write(&program, "method m(x: Int) { assert x > 0 }").unwrap();
    for disabled in [false, true] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_ferrum"));
        cmd.args([
            "--z3Exe",
            solver.to_str().unwrap(),
            "--logLevel",
            "DEBUG",
            "--numberOfParallelVerifiers",
            "1",
        ]);
        if disabled {
            cmd.arg("--disableCatchingExceptions");
        }
        let output = cmd.arg(&program).output().unwrap();
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(!output.status.success(), "{text}");
        assert!(
            text.contains("native integer parse error: invalid digit found in string"),
            "{text}"
        );
        assert_eq!(text.contains("An exception occurred:"), !disabled, "{text}");
        if !disabled {
            assert!(
                text.contains("Verification aborted exceptionally"),
                "{text}"
            );
        }
    }
    let solver_path = solver.to_string_lossy().into_owned();
    std::thread::Builder::new()
        .stack_size(ferrum::VERIFICATION_STACK_SIZE)
        .spawn(move || {
            use ferrum::silver::{
                frontend::frontend::FrontendPhases,
                reporter::{
                    message::Message,
                    reporter::{ReportError, Reporter},
                },
            };
            use std::sync::{
                Arc,
                atomic::{AtomicUsize, Ordering},
            };
            struct Reject(AtomicUsize);
            impl Reporter for Reject {
                fn name(&self) -> &str {
                    "reject-ordinary"
                }
                fn report(&self, message: Message) -> Result<(), ReportError> {
                    if let Message::Exception {
                        details: Some(details),
                        ..
                    } = message
                    {
                        assert!(details.display.contains("native integer parse error"));
                        assert!(details.stack_trace.contains("prover_std_io"));
                        self.0.fetch_add(1, Ordering::SeqCst);
                        return Err(ReportError::Unsupported(
                            "ordinary exception report rejected",
                        ));
                    }
                    Ok(())
                }
            }
            let mut phases = ferrum::silver::frontend::sil_frontend::SilFrontendPhases::new(
                "case.vpr".into(),
                ferrum::silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
            );
            let parsed = phases.parse("method m(x: Int) { assert x > 0 }").unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            let config = ferrum::silicon::config::Config::parse(&[
                "--ignoreFile".into(),
                "--z3Exe".into(),
                solver_path,
                "case.vpr".into(),
            ])
            .unwrap();
            let reporter = Arc::new(Reject(AtomicUsize::new(0)));
            let mut session = ferrum::Session::new_with_reporter(config, reporter.clone()).unwrap();
            let error = session.verify(&program, &[]).unwrap_err();
            assert!(
                error
                    .to_string()
                    .contains("ordinary exception report rejected"),
                "{error}"
            );
            assert!(
                error.to_string().contains("native integer parse error"),
                "{error}"
            );
            assert_eq!(reporter.0.load(Ordering::SeqCst), 1);
            session.stop().unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
    fs::remove_dir_all(dir).unwrap();
}

#[cfg(feature = "native-z3")]
#[test]
#[ignore = "requires linked Z3 4.16"]
fn linked_z3_failed_assumption_retry_is_native_ordinary_exception() {
    use ferrum::silicon::{
        decider::{
            native_z3::{LinkedProverError, LinkedProverOptions, LinkedZ3Prover},
            z3_prover_api::ApiTimeoutSettings,
        },
        interfaces::decider::prover::{Prover, ProverLike},
        state::{
            identifiers::Identifier,
            terms::{Quantifier, Sort, TermFactory, TermOptions, Trigger},
        },
    };
    let factory = TermFactory::new(TermOptions {
        use_flyweight: false,
        use_old_axiomatization: false,
        mask_heap_mode: false,
    });
    let options = LinkedProverOptions {
        timeout: ApiTimeoutSettings {
            default_timeout_ms: 0,
            use_time_bounds: true,
            resources_per_millisecond: 1,
        },
        counterexamples: false,
        report_reason_unknown: false,
        debug: false,
        soft_assertions: false,
        custom_options: vec![],
        disable_nonlinear: false,
    };
    let mut prover = LinkedZ3Prover::new("test", factory.clone(), options);
    prover.start(None).unwrap();
    let x = factory.var(Identifier::new("x"), Sort::Int, false);
    let q = factory.quantification_without_triggers(
        Quantifier::Forall,
        vec![x.clone()],
        factory.greater(x, factory.int_literal(0)),
        "bad-trigger".into(),
        false,
        None,
    );
    let bad = factory
        .quantification_with_raw_triggers(
            &q,
            vec![Trigger {
                terms: vec![factory.int_literal(1)],
            }],
        )
        .unwrap();
    let error = prover.assume(&bad).unwrap_err();
    assert!(
        matches!(error, LinkedProverError::SourceOrdinary { ref message, ref stack_trace } if message.starts_with("Z3 error: ") && stack_trace.len() > 1),
        "{error:?}"
    );
    prover.stop().unwrap();
}
