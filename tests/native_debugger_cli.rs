//! Ferrum public debugger validation assembly described in PLAN.md.
//! Public debugger CLI and stream regressions.
use ferrum::{
    RunOutcome, run_file,
    silicon::{
        config::Config,
        debugger::native_session,
        state::terms::{TermFactory, TermOptions},
        verifier::native_context::NativeOptions,
    },
    silver::verifier::verification_result::{AbstractError, VerificationResult},
};
use std::{
    io::{self, Cursor, Write},
    path::PathBuf,
    process::{Command, Stdio},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Temp(PathBuf);
impl Temp {
    fn new(ext: &str) -> Self {
        Self(std::env::temp_dir().join(format!(
            "ferrum-debug-public-{}-{}.{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
            ext
        )))
    }
}
impl Drop for Temp {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}
fn config(path: &std::path::Path, z3: &std::path::Path) -> Config {
    Config::parse(&[
        "--enableDebugging".into(),
        "--numberOfParallelVerifiers".into(),
        "1".into(),
        "--numberOfErrorsToReport".into(),
        "0".into(),
        "--z3Exe".into(),
        z3.to_string_lossy().into_owned(),
        path.to_string_lossy().into_owned(),
    ])
    .unwrap()
}
fn failures(config: Config) -> Vec<AbstractError> {
    match run_file(config).unwrap().outcome {
        RunOutcome::Verified(VerificationResult::Failure(errors)) => errors,
        other => panic!("expected verification failure: {other:?}"),
    }
}
fn streams(
    config: &Config,
    errors: &[AbstractError],
    input: &[u8],
    output: &mut impl Write,
) -> Result<(), String> {
    let options = NativeOptions::from_config(config).unwrap();
    let factory = TermFactory::new(TermOptions {
        use_flyweight: config.use_flyweight(),
        use_old_axiomatization: config.use_old_axiomatization,
        mask_heap_mode: false,
    });
    native_session::run_failures(
        config,
        options,
        factory,
        errors,
        &mut Cursor::new(input),
        output,
    )
}
fn run_cli(path: &std::path::Path, z3: &std::path::Path, input: &[u8]) -> std::process::Output {
    run_cli_with_options(path, z3, input, "1", &[])
}
fn run_cli_with_options(
    path: &std::path::Path,
    z3: &std::path::Path,
    input: &[u8],
    workers: &str,
    options: &[&str],
) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ferrum"))
        .args([
            "--enableDebugging",
            "--numberOfParallelVerifiers",
            workers,
            "--z3Exe",
        ])
        .arg(z3)
        .args(options)
        .arg(path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    child.wait_with_output().unwrap()
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3; native-z3 requires the pinned library"]
fn public_debugger_replays_worker_and_reporting_configurations() {
    let z3 = PathBuf::from(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"));
    let file = Temp::new("vpr");
    std::fs::write(
        &file.0,
        "field f: Int method m(r: Ref) requires acc(r.f) { assert r.f > 0 }",
    )
    .unwrap();
    let check = |workers: &str, options: &[&str]| {
        let out = run_cli_with_options(&file.0, &z3, b"p\naf\nr.f > 0\np\nq\n", workers, options);
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert_eq!(
            out.status.code(),
            Some(1),
            "stdout={stdout} stderr={}",
            String::from_utf8_lossy(&out.stderr)
        );
        let proofs: Vec<_> = stdout
            .lines()
            .filter(|line| line.starts_with("PASS: Proving") || line.starts_with("FAIL: Proving"))
            .collect();
        assert_eq!(
            proofs,
            [
                "FAIL: Proving obligation failed.",
                "PASS: Proving obligation was successful."
            ],
            "{stdout}"
        );
        assert!(!stdout.contains("Error while"), "{stdout}");
    };
    check("1", &["--ideModeAdvanced"]);
    check("2", &["--parallelizeBranches"]);
    #[cfg(feature = "native-z3")]
    {
        check("1", &["--prover", "Z3-API"]);
        check("2", &["--prover", "Z3-API", "--parallelizeBranches"]);
    }
}
#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn public_cli_success_and_failing_session() {
    let z3 = PathBuf::from(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"));
    let good = Temp::new("vpr");
    std::fs::write(&good.0, "method m() { assert true }").unwrap();
    let out = run_cli(&good.0, &z3, b"");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(out.status.code(), Some(0), "{out:?}");
    assert!(
        stdout.contains("No failures found. Debugging mode terminated."),
        "{stdout}"
    );
    assert!(stdout.contains("Verification succeeded"), "{stdout}");
    let bad = Temp::new("vpr");
    std::fs::write(
        &bad.0,
        "function f(x: Int): Int { x } method m(x: Int) requires x > 0 { assert f(x) > 1 }",
    )
    .unwrap();
    let out = run_cli(&bad.0, &z3, b"p\naf\nx +\naf\nf(x) > 1\np\nq\n");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(
        out.status.code(),
        Some(1),
        "stdout={stdout} stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        stdout.contains("FAIL: Proving obligation failed."),
        "{stdout}"
    );
    assert!(
        stdout.contains("Error while parsing x +: Parse Error, Position 1:4, found \"\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("Unexpected error: Parse Error, Position 1:4, found \"\"."),
        "{stdout}"
    );
    assert!(
        stdout.contains("Assumption was added successfully!"),
        "{stdout}"
    );
    assert!(
        stdout.contains("PASS: Proving obligation was successful."),
        "{stdout}"
    );
}
#[cfg(target_os = "linux")]
#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn stream_selection_eof_independent_sessions_and_cleanup() {
    std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
        use std::os::unix::fs::PermissionsExt;
        let z3 = PathBuf::from(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"));
        let source = Temp::new("vpr");
        std::fs::write(&source.0, "method first(x: Int) requires x > 0 { assert x > 1 } method second(y: Int) requires y > 0 { assert y > 2 }").unwrap();
        let pidfile = Temp::new("pids"); let wrapper = Temp::new("sh");
        // The script records every solver PID then replaces itself with the real solver.
        fn quote(path: &std::path::Path) -> String {
            format!("'{}'", path.to_string_lossy().replace('\'', "'\\''"))
        }
        std::fs::write(&wrapper.0, format!("#!/bin/sh\nprintf '%s\\n' $$ >> {}\nexec {} \"$@\"\n", quote(&pidfile.0), quote(&z3))).unwrap();
        std::fs::set_permissions(&wrapper.0, std::fs::Permissions::from_mode(0o755)).unwrap();
        let config = config(&source.0, &wrapper.0);
        let errors = failures(config.clone());
        assert_eq!(errors.len(), 2, "{errors:?}");
        let mut output = Vec::new();
        streams(&config, &errors, b"bad\n1\nq\nq\n", &mut output).unwrap();
        let text = String::from_utf8(output).unwrap();
        assert!(text.contains("Which verification result do you want to debug next [0 - 1]"), "{text}");
        assert!(text.contains("Debug mode for this obligation are not available"), "{text}");
        assert!(text.contains("Verification result 1:"), "{text}");
        let mut output = Vec::new();
        streams(&config, &errors, b"", &mut output).unwrap();
        let text = String::from_utf8(output).unwrap();
        assert!(text.contains("Which verification result do you want to debug next"), "{text}");
        assert!(!text.contains("Initializing prover..."), "{text}");
        let one = &errors[..1];
        let mut output = Vec::new();
        streams(&config, one, b"af\nfalse\np\nq\n", &mut output).unwrap();
        let text = String::from_utf8(output).unwrap();
        assert!(text.contains("PASS: Proving obligation was successful."), "{text}");
        let mut output = Vec::new();
        streams(&config, one, b"not-a-command\np\n", &mut output).unwrap();
        let text = String::from_utf8(output).unwrap();
        assert!(text.contains("Invalid input!"), "{text}");
        assert!(text.contains("FAIL: Proving obligation failed."), "{text}");
        struct FailOnProgress(Vec<u8>);
        impl Write for FailOnProgress {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                self.0.extend_from_slice(bytes);
                if self.0.windows(b"Initializing prover...".len()).any(|w| w == b"Initializing prover...") { return Err(io::Error::other("intentional writer failure")); }
                Ok(bytes.len())
            }
            fn flush(&mut self) -> io::Result<()> { Ok(()) }
        }
        let before = std::fs::read_to_string(&pidfile.0).unwrap().lines().count();
        let error = streams(&config, one, b"q\n", &mut FailOnProgress(Vec::new())).unwrap_err();
        assert!(error.contains("intentional writer failure"), "{error}");
        let all = std::fs::read_to_string(&pidfile.0).unwrap();
        assert!(all.lines().count() > before, "failure occurred before replay solver started");
        for pid in all.lines() { assert!(!PathBuf::from(format!("/proc/{pid}")).exists(), "solver process {pid} was not reaped"); }
    }).unwrap().join().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn public_cli_replays_field_expression() {
    let z3 = PathBuf::from(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"));
    let file = Temp::new("vpr");
    std::fs::write(
        &file.0,
        "field f: Int method m(r: Ref) requires acc(r.f) { assert r.f > 0 }",
    )
    .unwrap();
    let out = run_cli(&file.0, &z3, b"af\nr.f > 0\np\nq\n");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert_eq!(
        out.status.code(),
        Some(1),
        "stdout={stdout} stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        stdout.contains("Assumption was added successfully!"),
        "{stdout}"
    );
    assert!(
        stdout.contains("PASS: Proving obligation was successful."),
        "{stdout}"
    );
}
