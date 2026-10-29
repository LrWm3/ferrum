//! Ferrum solver declaration configuration regression assembly described in PLAN.md.
use ferrum::{Session, silicon::config::Config};

#[test]
fn direct_session_rejects_disabled_global_declarations_before_solver_start() {
    for key in ["global-decls", "global-declarations"] {
        let mut config = Config::default();
        config.prover_config_args.insert(key.into(), "false".into());
        let error = match Session::new(config) {
            Ok(_) => panic!("disabled global declarations accepted"),
            Err(error) => error,
        };
        assert!(
            error.to_string().contains("global declarations required"),
            "{error}"
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn explicit_enabled_global_declarations_allows_verification() {
    use ferrum::silver::{
        frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
        plugin::silver_plugin_manager::SilverPluginManager,
        verifier::verification_result::VerificationResult,
    };
    let args = vec![
        "--ignoreFile".into(),
        "--z3Exe".into(),
        std::env::var("FERRUM_TEST_Z3").unwrap(),
        "--proverConfigArgs".into(),
        "global-decls=true smt.random_seed=1".into(),
        "--logLevel".into(),
        "ERROR".into(),
        "test.vpr".into(),
    ];
    let mut session = Session::new(Config::parse(&args).unwrap()).unwrap();
    let mut phases = SilFrontendPhases::new("test.vpr".into(), SilverPluginManager::new(vec![]));
    let parsed = phases.parse("method m() { assert true; }").unwrap();
    let checked = phases.analyze(parsed).unwrap();
    let program = phases.translate(checked).unwrap();
    assert!(matches!(
        session.verify(&program, &[]).unwrap(),
        VerificationResult::Success
    ));
    session.stop().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn member_annotations_cannot_disable_global_declarations() {
    use ferrum::{
        VERIFICATION_STACK_SIZE,
        silver::{
            frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
            plugin::silver_plugin_manager::SilverPluginManager,
            verifier::verification_result::VerificationResult,
        },
    };
    std::thread::Builder::new()
        .stack_size(VERIFICATION_STACK_SIZE)
        .spawn(|| {
            for workers in [1, 2] {
                for (key, value, accepted) in [
                    ("global-decls", "true", true),
                    ("global-decls", "false", false),
                    ("global-declarations", "true", true),
                    ("global-declarations", "false", false),
                ] {
                    let args = vec![
                        "--ignoreFile".into(),
                        "--z3Exe".into(),
                        std::env::var("FERRUM_TEST_Z3").unwrap(),
                        "--numberOfParallelVerifiers".into(),
                        workers.to_string(),
                        "--logLevel".into(),
                        "ERROR".into(),
                        "test.vpr".into(),
                    ];
                    let mut session = Session::new(Config::parse(&args).unwrap()).unwrap();
                    let mut phases =
                        SilFrontendPhases::new("test.vpr".into(), SilverPluginManager::new(vec![]));
                    let source = format!(
                        "@proverConfigArgs(\"{key}={value}\") method m() {{ assert true; }}"
                    );
                    let parsed = phases.parse(&source).unwrap();
                    let checked = phases.analyze(parsed).unwrap();
                    let program = phases.translate(checked).unwrap();
                    let result = session.verify(&program, &[]);
                    if accepted {
                        match result {
                            Ok(result) => assert!(matches!(result, VerificationResult::Success)),
                            Err(error) => {
                                let detail = format!("{error:?}");
                                assert!(
                                    detail.contains("Protocol")
                                        && !detail.contains("UnsupportedConfiguration"),
                                    "{error:?}"
                                );
                            }
                        }
                    } else {
                        let error = result.expect_err("disabling globals must fail");
                        assert!(
                            format!("{error:?}").contains("UnsupportedConfiguration"),
                            "{error:?}"
                        );
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
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn rejected_function_option_does_not_leak_into_next_run() {
    use ferrum::{
        VERIFICATION_STACK_SIZE,
        silver::{
            frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
            plugin::silver_plugin_manager::SilverPluginManager,
            verifier::verification_result::VerificationResult,
        },
    };
    std::thread::Builder::new().stack_size(VERIFICATION_STACK_SIZE).spawn(|| {
        for workers in [1, 2] {
            let args = vec!["--ignoreFile".into(), "--z3Exe".into(), std::env::var("FERRUM_TEST_Z3").unwrap(), "--numberOfParallelVerifiers".into(), workers.to_string(), "--logLevel".into(), "ERROR".into(), "test.vpr".into()];
            let mut session = Session::new(Config::parse(&args).unwrap()).unwrap();
            let mut phases = SilFrontendPhases::new("test.vpr".into(), SilverPluginManager::new(vec![]));
            for (source, accepted) in [("@proverConfigArgs(\"global-decls=false\") function f(): Int { 1 } method m() { assert f() == 1 }", false), ("function f(): Int { 1 } method m() { assert f() == 1 }", true)] {
                let parsed = phases.parse(source).unwrap();
                let checked = phases.analyze(parsed).unwrap();
                let program = phases.translate(checked).unwrap();
                let result = session.verify(&program, &[]);
                if accepted { assert!(matches!(result.unwrap(), VerificationResult::Success)); }
                else { let error = result.expect_err("disabling globals must fail"); assert!(format!("{error:?}").contains("UnsupportedConfiguration"), "{error:?}"); }
            }
            session.stop().unwrap();
        }
    }).unwrap().join().unwrap();
}
