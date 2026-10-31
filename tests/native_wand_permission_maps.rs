//! Permission-map definitions used by wand residual heaps must survive packaging.
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
        "wand-permission-maps.vpr".into(),
        SilverPluginManager::new(vec![]),
    );
    let parsed = phases.parse(source).unwrap();
    let checked = phases.analyze(parsed).unwrap();
    phases.translate(checked).unwrap()
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn wand_permission_definitions_preserve_frames_without_leaking_assumptions() {
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            let source = include_str!("fixtures/wand_permission_branch.vpr");
            let valid = program(source);
            let consumed = program(&source.replace("ensures b ==> acc(y.f)", "ensures acc(y.f)"));
            let macro_permissions = program(include_str!("fixtures/wand_permission_macro.vpr"));
            let nested = program(include_str!("fixtures/wand_permission_nested.vpr"));
            let lhs_assumption = program(
                "field f: Int method m(x: Ref, b: Bool) {
                  package (b && (forall r: Ref :: r == x ==> acc(r.f))) --* true {
                    if (perm(x.f) > none) { assert b }
                  }
                  assert b
                }",
            );
            let snapshot_dependent = program(
                "field f: Int field flag: Bool
                method m(x: Ref, y: Ref) requires acc(y.f) ensures acc(y.f) {
                  package (acc(x.flag) &&
                    (forall r: Ref :: r == x && x.flag ==> acc(r.f))) --* true {
                    exhale acc(x.f, x.flag ? 1/2 : none)
                    if (perm(x.f) == none) { exhale acc(y.f) }
                  }
                }",
            );
            for caches in [false, true] {
                let args = vec![
                    "--z3Exe".into(),
                    std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"),
                    "--disableDefaultPlugins".into(),
                    "--numberOfParallelVerifiers=1".into(),
                    "--parallelizeBranches=false".into(),
                    "--enableMoreCompleteExhale".into(),
                    "--timeout=15".into(),
                    format!("--disableCaches={}", !caches),
                ];
                let mut api = NativeFrontendApi::new(&args, Arc::new(NoopReporter), false).unwrap();
                for (input, expected) in [
                    (&valid, None),
                    (
                        &consumed,
                        Some("postcondition.violated:insufficient.permission"),
                    ),
                    (&nested, None),
                    (&macro_permissions, None),
                    (&lhs_assumption, Some("assert.failed:assertion.false")),
                    (
                        &snapshot_dependent,
                        Some("postcondition.violated:insufficient.permission"),
                    ),
                    (&valid, None),
                ] {
                    let result = api.verify(input).unwrap();
                    match (result, expected) {
                        (VerificationResult::Success, None) => (),
                        (VerificationResult::Failure(errors), Some(id)) => {
                            assert_eq!(
                                errors
                                    .iter()
                                    .map(|error| error.full_id())
                                    .collect::<Vec<_>>(),
                                vec![id],
                                "caches={caches}"
                            );
                        }
                        (result, expected) => {
                            panic!("caches={caches}: expected {expected:?}, got {result:?}")
                        }
                    }
                }
                api.stop().unwrap();
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
