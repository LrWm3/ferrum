//! Preserve heap-dependent trigger proofs while pruning other summary triggers.
//! The CC0 fixture is linked-list-qp-append.vpr from Silver at
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/resources/quantifiedpermissions/sequences/linked-list-qp-append.vpr
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

fn program(source: &str) -> Program {
    let mut phases = SilFrontendPhases::new(
        "snapshot-summary-append.vpr".into(),
        SilverPluginManager::new(vec![]),
    );
    let parsed = phases.parse(source).unwrap();
    let checked = phases.analyze(parsed).unwrap();
    phases.translate(checked).unwrap()
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn heap_dependent_summary_triggers_verify_reject_and_reuse() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let source = include_str!("fixtures/snapshot_summary_append.vpr");
            assert_eq!(source.matches("n.val := elem").count(), 1);
            let valid = program(source);
            let invalid = program(&source.replace("n.val := elem", "n.val := elem + 1"));
            let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
            for summary_only in [false, true] {
                let mut args = vec![
                    "--prover".into(),
                    prover.clone(),
                    "--disableDefaultPlugins".into(),
                    "--numberOfParallelVerifiers=1".into(),
                    "--parallelizeBranches=false".into(),
                    "--timeout=30".into(),
                    // Match the provable upstream comparison configuration. Retained
                    // solvers and internal caches still time out with both policies.
                    "--separateMethodSolver".into(),
                    "--disableCaches".into(),
                    format!("--snapshotSummaryOnlyTriggers={summary_only}"),
                ];
                if prover == "Z3" {
                    args.extend([
                        "--z3Exe".into(),
                        std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"),
                    ]);
                }
                let mut api = NativeFrontendApi::new(&args, Arc::new(NoopReporter), false).unwrap();
                for (input, success) in [(&valid, true), (&invalid, false), (&valid, true)] {
                    let result = api.verify(input).unwrap();
                    if !success {
                        let VerificationResult::Failure(errors) = result else {
                            panic!("incorrect appended value must fail ({summary_only})")
                        };
                        assert_eq!(
                            errors
                                .iter()
                                .map(|error| error.full_id())
                                .collect::<Vec<_>>(),
                            vec!["postcondition.violated:assertion.false"],
                            "summary_only={summary_only}"
                        );
                    } else {
                        assert!(
                            matches!(result, VerificationResult::Success),
                            "append must verify (summary_only={summary_only}): {result:?}"
                        );
                    }
                }
                api.stop().unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
