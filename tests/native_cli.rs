//! Ferrum native runner regression checks described in PLAN.md.
//! These checks require real Z3 and run explicitly with FERRUM_TEST_Z3 for stdio,
//! or FERRUM_TEST_PROVER=Z3-API and the native-z3 feature for linked Z3 4.16.

use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
struct Input(PathBuf);
impl Drop for Input {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}
fn run(source: &str, args: &[&str]) -> std::process::Output {
    let prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
    let path = std::env::temp_dir().join(format!(
        "ferrum-branch-{}-{}.vpr",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let input = Input(path);
    std::fs::write(&input.0, source).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_ferrum"));
    command.arg("--prover").arg(&prover);
    if prover == "Z3" {
        command.arg("--z3Exe").arg(
            std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3 to the Z3 executable"),
        );
    }
    command.args(args).arg(&input.0).output().unwrap()
}
fn check(source: &str, expected: i32) {
    let output = run(source, &[]);
    assert_eq!(
        output.status.code(),
        Some(expected),
        "source: {source}\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    if expected == 1 {
        assert!(String::from_utf8_lossy(&output.stderr).contains("assert.failed"));
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn sif_inactive_inhale_false_cannot_hide_a_failed_assertion() {
    for (guard, expected) in [("false", 1), ("true", 0)] {
        let source = format!("method m() {{ if ({guard}) {{ inhale false; }} assert false; }}");
        let output = run(&source, &["--plugin", "viper.silver.plugin.sif.SIFPlugin"]);
        assert_eq!(
            output.status.code(),
            Some(expected),
            "{source}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if expected == 1 {
            assert!(String::from_utf8_lossy(&output.stderr).contains("assert.failed"));
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn nested_predicate_chain_uses_the_source_launcher_stack() {
    let mut source = String::from("field value: Int predicate P0(r: Ref) { acc(r.value) }\n");
    for level in 1..32 {
        source.push_str(&format!(
            "predicate P{level}(r: Ref) {{ acc(P{}(r)) }}\n",
            level - 1
        ));
    }
    source.push_str("method m(r: Ref) requires acc(r.value) && r.value == 7 {\n");
    for level in 0..32 {
        source.push_str(&format!("fold acc(P{level}(r));\n"));
    }
    for level in (0..32).rev() {
        source.push_str(&format!("unfold acc(P{level}(r));\n"));
    }
    check(&format!("{source} assert r.value == 7; }}"), 0);
    check(&format!("{source} assert r.value == 8; }}"), 1);
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn complete_exhale_and_cfg_joins_preserve_conditional_permissions() {
    let prefix = "field f: Int method m(x: Ref, y: Ref, b: Bool)
        requires acc(x.f, 1/2) && acc(y.f, 1/2) {
        assume x == y;
        if (b) { exhale acc(x.f, 1/4); } else { exhale acc(x.f, 1/2); }";
    for mode in ["1", "2"] {
        for (amount, expected) in [("1/2", 0), ("3/4", 1)] {
            let source = format!("{prefix} assert acc(x.f, {amount}); }}");
            let output = run(&source, &["--exhaleMode", mode, "--moreJoins", "2"]);
            assert_eq!(
                output.status.code(),
                Some(expected),
                "{source}\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
            if expected == 1 {
                assert!(String::from_utf8_lossy(&output.stderr).contains("assert.failed"));
            }
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn try_plugin_preserves_fallback_and_later_failures() {
    let plugin = ["--plugin", "viper.silicon.extensions.TryBlockParserPlugin"];
    for (source, expected) in [
        ("method m() { try { assert false; } assert true; }", 0),
        ("method m() { try { assert false; } assert false; }", 1),
        (
            "method n() {} method m() { try { assume true; n(); } assert false; }",
            1,
        ),
        (
            "field f: Int method m(x: Ref) requires acc(x.f) && x.f == 7 { try { exhale acc(x.f); assert false; } assert x.f == 7; }",
            0,
        ),
    ] {
        let output = run(source, &plugin);
        assert_eq!(
            output.status.code(),
            Some(expected),
            "{source}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if expected == 1 {
            assert!(String::from_utf8_lossy(&output.stderr).contains("assert.failed"));
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn wand_packaging_transfers_permissions_and_application_consumes_the_wand() {
    let prefix = "field first: Int field second: Int
        method test(r: Ref)
            requires acc(r.first) && acc(r.second) && r.second == 3
        { package acc(r.first) --* acc(r.second) {}";
    check(
        &format!("{prefix} apply acc(r.first) --* acc(r.second); assert r.second == 3; }}"),
        0,
    );
    check(&format!("{prefix} assert acc(r.second); }}"), 1);
    let output = run(
        "field value: Int method test(r: Ref) requires acc(r.value) {
            package acc(r.value) --* acc(r.value) {}
            apply acc(r.value) --* acc(r.value);
            apply acc(r.value) --* acc(r.value);
        }",
        &[],
    );
    let errors = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{errors}");
    assert!(errors.contains("wand.not.found"), "{errors}");
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn heap_havoc_forgets_selected_values_and_preserves_frames() {
    let prefix = "field value: Int
        method test(r: Ref, s: Ref)
            requires r != s && acc(r.value) && acc(s.value)
            requires r.value == 1 && s.value == 2
        { quasihavocall x: Ref :: x == r ==> x.value;";
    check(
        &format!("{prefix} assert acc(r.value) && s.value == 2; }}"),
        0,
    );
    check(&format!("{prefix} assert r.value == 1; }}"), 1);
    check(
        "field value: Int
        method test(r: Ref, s: Ref)
            requires r == s && acc(r.value) && r.value == 1
        { quasihavoc s.value; assert r.value == 1; }",
        1,
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn quantified_permissions_preserve_frames_and_consumption() {
    let prefix = "field value: Int
        method test(r: Ref, s: Ref)
            requires r != null && s != null && r != s
            requires forall x: Ref :: x != null ==> acc(x.value)
        { r.value := 1; s.value := 2;";
    check(
        &format!("{prefix} assert r.value == 1 && s.value == 2; }}"),
        0,
    );
    check(&format!("{prefix} assert r.value == s.value; }}"), 1);
    check(
        &format!(
            "{prefix} exhale forall x: Ref :: x != null ==> acc(x.value); assert acc(r.value); }}"
        ),
        1,
    );
    check(
        "field value: Int
        method test(r: Ref) requires r != null
            requires forall x: Ref :: x != null ==> acc(x.value, 1/2)
        { assert acc(r.value); }",
        1,
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn final_report_groups_duplicate_branch_failures() {
    let output = run(
        "method test(b: Bool) { if (b) { } else { } assert false; }",
        &["--numberOfErrorsToReport", "0", "--no-timing"],
    );
    let errors = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{errors}");
    assert_eq!(errors.matches("assert.failed").count(), 1, "{errors}");
    assert!(
        errors.contains("Verification failed with 1 error(s)."),
        "{errors}"
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn function_calls_use_the_current_heap_snapshot() {
    let prefix = "field value: Int
        function read(x: Ref): Int requires acc(x.value) { x.value }
        method test() {
            var x: Ref := new(value);
            x.value := 1;
            var previous: Int := read(x);
            x.value := 2;";
    check(
        &format!("{prefix} assert previous == 1; assert read(x) == 2; }}"),
        0,
    );
    check(&format!("{prefix} assert read(x) == previous; }}"), 1);
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn repeated_session_runs_discard_previous_axioms() {
    use ferrum::{
        Session,
        silicon::config::Config,
        silver::{
            frontend::{
                frontend::FrontendPhases,
                sil_frontend::{SilFrontendPhases, standard_plugin_manager},
            },
            verifier::verification_result::VerificationResult,
        },
    };
    let mut config = Config::default();
    config.prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
    if config.prover == "Z3" {
        config.z3_exe = Some(std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"));
    }
    let mut session = Session::new(config.clone()).unwrap();
    for (source, success) in [
        (
            "domain D { function value(): Int axiom fixed { value() == 1 } } method test() { assert value() == 1; }",
            true,
        ),
        (
            "domain D { function value(): Int } method test() { assert value() == 1; }",
            false,
        ),
        ("method test() { assert true; }", true),
    ] {
        let plugins = standard_plugin_manager(&config.frontend).unwrap();
        let mut frontend = SilFrontendPhases::new("session.vpr".into(), plugins);
        frontend.configure_consistency(&config.frontend);
        let parsed = frontend.parse(source).unwrap();
        let analyzed = frontend.analyze(parsed).unwrap();
        let translated = frontend.translate(analyzed).unwrap();
        let program = frontend.check_consistency(translated).unwrap();
        let program = frontend.prepare_verification(program).unwrap();
        let result = session.verify(&program, &[]).unwrap();
        assert_eq!(
            matches!(result, VerificationResult::Success),
            success,
            "{source}"
        );
    }
    session.stop().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn symbolic_expression_branches_keep_source_order() {
    check(
        "method test(b: Bool) { assert ((b ? 1 : 2) == 1) ==> b; }",
        0,
    );
    check("method test(b: Bool) { assert b ==> false; }", 1);
    check(
        "method test(b: Bool) { var x: Int := b ? 1 : 2; if (b) { assert x == 1; } else { assert x == 2; } }",
        0,
    );
    check(
        "method test(b: Bool) { var x: Int := b ? 1 : 2; if (b) { assert x == 2; } else { assert x == 1; } }",
        1,
    );
}
