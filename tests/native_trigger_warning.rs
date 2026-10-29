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
            for warning in warnings {
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
            session.stop().unwrap();
            let reporter = Arc::new(Capture { reject: true, ..Capture::default() });
            let mut session = Session::new_with_reporter(config, reporter).unwrap();
            let error = session.verify(&program, &[]).expect_err("warning delivery must propagate failure");
            assert!(format!("{error:?}").contains("rejected trigger warning"), "{error:?}");
            session.stop().unwrap();
        }
    }).unwrap().join().unwrap();
}
