//! Ferrum domain-axiom closure regression described in PLAN.md.
use ferrum::{
    NativeFrontendApi, VERIFICATION_STACK_SIZE,
    silver::{
        frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
        plugin::silver_plugin_manager::SilverPluginManager,
        reporter::reporter::NoopReporter,
        verifier::verification_result::VerificationResult,
    },
};
use std::sync::Arc;

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn axioms_in_indirectly_referenced_domain_are_emitted() {
    let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
    std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(move || {
        for (comparison, expected_success) in [("dec(1, 2)",true),("dec(2, 1)",false)] {
            let source = format!("domain W[T] {{ function dec(x: T, y: T): Bool }}\ndomain A {{ axiom ax {{ forall x: Int, y: Int :: {{ dec(x, y) }} x < y ==> dec(x, y) }} }}\nmethod m() {{ assert {comparison} }}");
            let mut phases=SilFrontendPhases::new("closure.vpr".into(),SilverPluginManager::new(vec![]));
            let parsed=phases.parse(&source).unwrap(); let checked=phases.analyze(parsed).unwrap(); let program=phases.translate(checked).unwrap();
            let mut api=NativeFrontendApi::new(&["--z3Exe".into(),z3.clone()],Arc::new(NoopReporter),false).unwrap();
            let result=api.verify(&program).unwrap();
            assert_eq!(matches!(result,VerificationResult::Success),expected_success,"{comparison}: {result:?}");
            api.stop().unwrap();
        }
    }).unwrap().join().unwrap();
}
