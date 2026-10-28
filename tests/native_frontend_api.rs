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
