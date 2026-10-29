//! Ferrum prover-version lifecycle regression assembly described in PLAN.md.
//! Source Decider.createProver version events across recreated native contexts.
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
    events: Mutex<Vec<String>>,
    reject_version: bool,
}
impl Reporter for Capture {
    fn name(&self) -> &str {
        "capture"
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        if let Message::Simple {
            kind: SimpleMessageKind::ConfigurationConfirmation,
            text,
        } = message
        {
            if text.starts_with("Using ") && self.reject_version {
                return Err(ReportError::Unsupported("rejected version"));
            }
            self.events.lock().unwrap().push(text);
        }
        Ok(())
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
#[cfg(unix)]
fn version_queried_once_per_prover_across_resets_and_report_failure() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            use std::os::unix::fs::PermissionsExt;
            let directory =
                std::env::temp_dir().join(format!("ferrum-version-{}", std::process::id()));
            std::fs::create_dir_all(&directory).unwrap();
            let transcript = directory.join("commands");
            let wrapper = directory.join("z3-wrapper");
            let quote = |s: &str| format!("'{}'", s.replace('\'', "'\\''"));
            let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
            std::fs::write(
                &wrapper,
                format!(
                    "#!/bin/sh\ntee -a {} | {} \"$@\"\n",
                    quote(transcript.to_str().unwrap()),
                    quote(&z3)
                ),
            )
            .unwrap();
            std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).unwrap();
            let mut phases =
                SilFrontendPhases::new("test.vpr".into(), SilverPluginManager::new(vec![]));
            let parsed = phases.parse("method m() { assert true; }").unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            for count in [1, 2] {
                std::fs::write(&transcript, "").unwrap();
                let args = vec![
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    wrapper.to_string_lossy().into_owned(),
                    "--numberOfParallelVerifiers".into(),
                    count.to_string(),
                    "test.vpr".into(),
                ];
                let config = Config::parse(&args).unwrap();
                let reporter = Arc::new(Capture::default());
                let mut session =
                    Session::new_with_reporter(config.clone(), reporter.clone()).unwrap();
                for _ in 0..3 {
                    assert!(matches!(
                        session.verify(&program, &[]).unwrap(),
                        VerificationResult::Success
                    ));
                }
                session.stop().unwrap();
                let expected = if count == 1 { 1 } else { count + 1 };
                let events = reporter.events.lock().unwrap();
                assert_eq!(
                    events.iter().filter(|s| s.starts_with("Using Z3 ")).count(),
                    expected,
                    "{events:?}"
                );
                let commands = std::fs::read_to_string(&transcript).unwrap();
                assert_eq!(
                    commands.matches("(get-info :version)").count(),
                    expected,
                    "{commands}"
                );
                drop(events);
                let reject = Arc::new(Capture {
                    reject_version: true,
                    ..Capture::default()
                });
                let error = match Session::new_with_reporter(config, reject) {
                    Ok(_) => panic!("reporter error ignored"),
                    Err(e) => e,
                };
                assert!(
                    format!("{error:?}").contains("rejected version"),
                    "{error:?}"
                );
            }
            std::fs::remove_dir_all(directory).unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}

#[cfg(feature = "native-z3")]
#[test]
#[ignore = "requires linked Z3 4.16"]
fn linked_version_event_is_once_per_prover_across_resets() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let mut phases =
                SilFrontendPhases::new("test.vpr".into(), SilverPluginManager::new(vec![]));
            let parsed = phases.parse("method m() { assert true; }").unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            for count in [1, 2] {
                let config = Config::parse(&[
                    "--ignoreFile".into(),
                    "--prover".into(),
                    "Z3-API".into(),
                    "--numberOfParallelVerifiers".into(),
                    count.to_string(),
                    "test.vpr".into(),
                ])
                .unwrap();
                let reporter = Arc::new(Capture::default());
                let mut session = Session::new_with_reporter(config, reporter.clone()).unwrap();
                for _ in 0..3 {
                    assert!(matches!(
                        session.verify(&program, &[]).unwrap(),
                        VerificationResult::Success
                    ));
                }
                session.stop().unwrap();
                let events = reporter.events.lock().unwrap();
                let expected = if count == 1 { 1 } else { count + 1 };
                assert_eq!(
                    events
                        .iter()
                        .filter(|s| s.starts_with("Using Z3-API ")
                            && s.ends_with(" located at No Path"))
                        .count(),
                    expected,
                    "{events:?}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
#[cfg(unix)]
fn old_version_warning_reaches_reporter_and_failure_is_propagated() {
    use std::os::unix::fs::PermissionsExt;
    struct WarningReporter {
        warnings: Mutex<Vec<String>>,
        reject: bool,
    }
    impl Reporter for WarningReporter {
        fn name(&self) -> &str {
            "warning capture"
        }
        fn report(&self, message: Message) -> Result<(), ReportError> {
            if let Message::Simple {
                kind: SimpleMessageKind::InternalWarning,
                text,
            } = message
            {
                if self.reject {
                    return Err(ReportError::Unsupported("rejected warning"));
                }
                self.warnings.lock().unwrap().push(text);
            }
            Ok(())
        }
    }
    let directory =
        std::env::temp_dir().join(format!("ferrum-version-warning-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let wrapper = directory.join("z3-wrapper");
    let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
    let quoted = format!("'{}'", z3.replace('\'', "'\\''"));
    std::fs::write(
        &wrapper,
        format!(
            "#!/bin/sh\n{quoted} \"$@\" | sed -u 's/:version \"[^\"]*\"/:version \"4.0.0\"/'\n"
        ),
    )
    .unwrap();
    std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o755)).unwrap();
    let config = Config::parse(&[
        "--ignoreFile".into(),
        "--z3Exe".into(),
        wrapper.to_string_lossy().into_owned(),
        "test.vpr".into(),
    ])
    .unwrap();
    let reporter = Arc::new(WarningReporter {
        warnings: Mutex::new(Vec::new()),
        reject: false,
    });
    let mut session = Session::new_with_reporter(config.clone(), reporter.clone()).unwrap();
    assert_eq!(
        *reporter.warnings.lock().unwrap(),
        ["Expected at least Z3 version 4.5.0, but found 4.0.0"]
    );
    session.stop().unwrap();
    let reject = Arc::new(WarningReporter {
        warnings: Mutex::new(Vec::new()),
        reject: true,
    });
    let error = match Session::new_with_reporter(config, reject) {
        Ok(_) => panic!("warning reporter error ignored"),
        Err(e) => e,
    };
    assert!(
        format!("{error:?}").contains("rejected warning"),
        "{error:?}"
    );
    std::fs::remove_dir_all(directory).unwrap();
}
