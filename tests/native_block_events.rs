//! Ferrum block-event ownership regressions described in PLAN.md.
use ferrum::{
    NativeFrontendApi, VERIFICATION_STACK_SIZE,
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
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn block_events_report_reached_failure_and_processed() {
    let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(move || {
            for workers in [1, 2] {
                let mut phases =
                    SilFrontendPhases::new("block.vpr".into(), SilverPluginManager::new(vec![]));
                let parsed = phases
                    .parse("method m() { label here; assert false; }")
                    .unwrap();
                let checked = phases.analyze(parsed).unwrap();
                let program = phases.translate(checked).unwrap();
                let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
                let mut api = NativeFrontendApi::new(
                    &[
                        "--z3Exe".into(),
                        z3.clone(),
                        "--generateBlockMessages".into(),
                        "--numberOfParallelVerifiers".into(),
                        workers.to_string(),
                    ],
                    reporter.clone(),
                    false,
                )
                .unwrap();
                assert!(matches!(
                    api.verify(&program).unwrap(),
                    VerificationResult::Failure(_)
                ));
                api.stop().unwrap();
                let mut events = Vec::new();
                while reporter.has_new_message() {
                    match reporter.get_new_message().unwrap() {
                        Message::BlockReached {
                            method_name,
                            label,
                            path_id,
                        } => events.push(("reached", method_name, label, path_id)),
                        Message::BlockFailure {
                            method_name,
                            label,
                            path_id,
                        } => events.push(("failure", method_name, label, path_id)),
                        Message::PathProcessed {
                            method_name,
                            path_id,
                            result,
                        } => {
                            assert_eq!(result, "Failure");
                            events.push(("processed", method_name, "here".into(), path_id));
                        }
                        _ => (),
                    }
                }
                assert_eq!(events.len(), 3, "{events:?}");
                assert_eq!(
                    events.iter().map(|event| event.0).collect::<Vec<_>>(),
                    ["reached", "failure", "processed"]
                );
                assert!(
                    events
                        .iter()
                        .all(|event| event.1 == "m" && event.2 == "here" && event.3 == events[0].3)
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn branched_block_events_and_reuse() {
    let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
    std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(move || {
        for workers in [1,2] {
            let mut phases = SilFrontendPhases::new("branch.vpr".into(), SilverPluginManager::new(vec![]));
            let parsed = phases.parse("method m(b: Bool) { label entry; if (b) { label yes; assert false; } else { label no; assert true; } }").unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
            let mut api = NativeFrontendApi::new(&["--z3Exe".into(), z3.clone(), "--generateBlockMessages".into(), "--parallelizeBranches".into(), "--numberOfParallelVerifiers".into(), workers.to_string()], reporter.clone(), false).unwrap();
            for _ in 0..2 {
                assert!(matches!(api.verify(&program).unwrap(), VerificationResult::Failure(_)));
                let mut reached = Vec::new(); let mut failures = Vec::new(); let mut processed = Vec::new();
                while reporter.has_new_message() { match reporter.get_new_message().unwrap() {
                    Message::BlockReached { method_name,label,path_id } => { assert_eq!(method_name,"m"); reached.push((label,path_id)); },
                    Message::BlockFailure { method_name,label,path_id } => { assert_eq!(method_name,"m"); failures.push((label,path_id)); },
                    Message::PathProcessed { method_name,path_id,result } => { assert_eq!(method_name,"m"); processed.push((path_id,result)); },
                    _ => (),
                }}
                assert!(reached.iter().any(|(label,_)| label=="entry"),"{reached:?}");
                assert!(reached.iter().any(|(label,_)| label=="yes"),"{reached:?}");
                assert!(reached.iter().any(|(label,_)| label=="no"),"{reached:?}");
                assert!(failures.iter().any(|(label,_)| label=="yes"),"{failures:?}");
                assert!(processed.iter().any(|(_,result)| result=="Failure"),"{processed:?}");
                assert!(processed.iter().any(|(_,result)| result=="Success"),"{processed:?}");
            }
            api.stop().unwrap();
        }
    }).unwrap().join().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn each_block_reporter_error_is_propagated() {
    use ferrum::silver::reporter::reporter::{ReportError, Reporter};
    struct Reject(&'static str);
    impl Reporter for Reject {
        fn name(&self) -> &str {
            "reject"
        }
        fn report(&self, message: Message) -> Result<(), ReportError> {
            let reject = matches!(
                (&message, self.0),
                (Message::BlockReached { .. }, "reached")
                    | (Message::BlockFailure { .. }, "failure")
                    | (Message::PathProcessed { .. }, "processed")
            );
            if reject {
                Err(ReportError::Unsupported("injected block reporter failure"))
            } else {
                Ok(())
            }
        }
    }
    let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(move || {
            for kind in ["reached", "failure", "processed"] {
                let mut phases =
                    SilFrontendPhases::new("block.vpr".into(), SilverPluginManager::new(vec![]));
                let parsed = phases
                    .parse("method m() { label here; assert false; }")
                    .unwrap();
                let checked = phases.analyze(parsed).unwrap();
                let program = phases.translate(checked).unwrap();
                let mut api = NativeFrontendApi::new(
                    &[
                        "--z3Exe".into(),
                        z3.clone(),
                        "--generateBlockMessages".into(),
                    ],
                    Arc::new(Reject(kind)),
                    false,
                )
                .unwrap();
                let error = api.verify(&program).unwrap_err();
                assert!(
                    format!("{error:?}").contains("injected block reporter failure"),
                    "{error:?}"
                );
                api.stop().unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
