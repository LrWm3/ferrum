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
fn method_cfg_output_obeys_selection_and_propagates_io_failures() {
    let directory = std::env::temp_dir().join(format!(
        "ferrum-cfg-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let source = "method selected(x: Int) { if (x > 0) { assert x >= 0; } } method skipped() {}";
    let output = run(
        source,
        &[
            "--printMethodCFGs",
            "--tempDirectory",
            directory.to_str().unwrap(),
            "--includeMethods",
            "selected",
            "--numberOfParallelVerifiers",
            "2",
        ],
    );
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let dot = std::fs::read_to_string(directory.join("selected.dot")).unwrap();
    assert!(dot.starts_with("digraph {\n"));
    assert!(dot.contains("assert x \\>= 0"));
    assert!(dot.contains("x \\> 0"));
    assert!(!directory.join("skipped.dot").exists());
    std::fs::remove_dir_all(&directory).unwrap();

    std::fs::write(&directory, "parent is a file").unwrap();
    let output = run(
        "method m() {}",
        &[
            "--printMethodCFGs",
            "--tempDirectory",
            directory.to_str().unwrap(),
        ],
    );
    std::fs::remove_file(&directory).unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("CFG output"));
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn parallel_counterexamples_retain_variable_and_heap_values() {
    let source = "field f: Int
        method m(x: Int, r: Ref) requires x == 3 && acc(r.f) && r.f == 1 {
            assert r.f == 2;
        }";
    let output = run(
        source,
        &[
            "--counterexample",
            "mapped",
            "--exhaleMode",
            "1",
            "--numberOfParallelVerifiers",
            "2",
        ],
    );
    let text = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{text}");
    assert!(text.contains("counterexample:"), "{text}");
    assert!(text.contains("x <- 3"), "{text}");
    assert!(text.contains("f(perm: 1/1) <- 1"), "{text}");
    assert!(!text.contains("variable not found"), "{text}");
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn quantified_wand_transfers_preserve_permissions_and_values() {
    let source = "field f: Int
        method m(x: Ref) requires (forall y: Ref :: y == x ==> acc(y.f)) && x.f == 7 {
            package acc(x.f, 1/2) --* (forall y: Ref :: y == x ==> acc(y.f)) {}
            apply acc(x.f, 1/2) --* (forall y: Ref :: y == x ==> acc(y.f))
            assert x.f == 7;
        }";
    for mode in ["0", "1", "2"] {
        for (source, expected) in [
            (source.to_owned(), 0),
            (source.replace("assert x.f == 7", "assert x.f == 8"), 1),
            (
                source.replace(
                    "            apply acc",
                    "            assert acc(x.f, 3/4); apply acc",
                ),
                1,
            ),
        ] {
            let output = run(&source, &["--exhaleModeQP", mode]);
            assert_eq!(
                output.status.code(),
                Some(expected),
                "mode {mode}, source {source}\nstderr: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn parallel_workers_share_preambles_and_report_real_failures() {
    let source = "field value: Int
        predicate P(r: Ref) { acc(r.value) }
        function inc(x: Int): Int { x + 1 }
        method first() { assert inc(1) == 2; }
        method second(r: Ref) requires acc(r.value) && r.value == 7 {
            fold acc(P(r)); unfold acc(P(r)); assert r.value == 7;
        }
        method third() { assert |Seq(1, 2)| == 2; }
        method last() { assert inc(2) == 3; }";
    for (source, expected) in [
        (source.to_owned(), 0),
        (source.replace("inc(2) == 3", "inc(2) == 4"), 1),
    ] {
        let output = run(
            &source,
            &["--numberOfParallelVerifiers", "2", "--no-timing"],
        );
        let errors = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(expected), "{errors}");
        if expected == 1 {
            assert!(
                errors.contains("Verification failed with 1 error(s)."),
                "{errors}"
            );
            assert_eq!(errors.matches("assert.failed").count(), 1, "{errors}");
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn sif_loops_and_dependent_predicates_preserve_relational_obligations() {
    let predicate = "field f: Int
        predicate Q(r: Ref) { acc(r.f) && low(r.f) }
        predicate P(r: Ref) { acc(Q(r)) }
        method m(r: Ref) requires acc(r.f) && low(r) && low(r.f) {
            fold acc(Q(r)); fold acc(P(r)); unfold acc(P(r)); unfold acc(Q(r));
            assert low(r.f);
        }";
    let loop_source = "method m(n: Int) requires low(n) {
        var x: Int := n;
        while (x > 0) invariant low(x) { x := x - 1; }
        assert low(x);
    }";
    for (source, expected) in [
        (predicate.to_owned(), 0),
        (predicate.replace(" && low(r.f) {", " {"), 1),
        (loop_source.to_owned(), 0),
        (loop_source.replace(" requires low(n)", ""), 1),
    ] {
        let output = run(&source, &["--plugin", "viper.silver.plugin.sif.SIFPlugin"]);
        assert_eq!(
            output.status.code(),
            Some(expected),
            "{source}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
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
        { package acc(r.first) --* acc(r.second) {
            assert acc(r.second); assert r.second == 3;
        }";
    check(
        &format!("{prefix} apply acc(r.first) --* acc(r.second); assert r.second == 3; }}"),
        0,
    );
    check(&format!("{prefix} assert acc(r.second); }}"), 1);
    check(
        &format!(
            "{} }}",
            prefix.replace("assert r.second == 3", "assert r.second == 4")
        ),
        1,
    );
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
fn quantified_wildcard_removal_preserves_permission_constraints() {
    // Repeated wildcard consumption may choose smaller positive fractions.
    // An unrelated receiver must not gain permission from those constraints.
    let prefix = "field value: Int
        method test(xs: Set[Ref], r: Ref)
            requires r != null && r in xs
            requires forall x: Ref :: x in xs ==> acc(x.value, wildcard)
        { exhale forall x: Ref :: x in xs ==> acc(x.value, wildcard);
          exhale forall x: Ref :: x in xs ==> acc(x.value, wildcard);";
    check(&format!("{prefix} assert acc(r.value, wildcard); }}"), 0);
    check(&format!("{prefix} assert acc(r.value); }}"), 1);
    check(
        "field value: Int
        method test(xs: Set[Ref], r: Ref)
            requires r != null && !(r in xs)
            requires forall x: Ref :: x in xs ==> acc(x.value, wildcard)
        { exhale forall x: Ref :: x in xs ==> acc(x.value, wildcard);
          assert acc(r.value, wildcard); }",
        1,
    );
    check(
        "predicate Q(r: Ref)
        predicate P(xs: Set[Ref]) {
            forall x: Ref :: x in xs ==> acc(Q(x), wildcard)
        }
        method test(xs: Set[Ref]) requires acc(P(xs), wildcard) {
            unfold acc(P(xs), wildcard);
            fold acc(P(xs), wildcard);
            unfold acc(P(xs), wildcard);
        }",
        0,
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn user_sort_names_do_not_rewrite_snapshot_wrapper_templates() {
    let domains = "domain $T$_ { function f(x: $T$_): Int }
        domain $S$_ { function g(x: $S$_): Int }
        domain $T0$_ { function h(x: $T0$_): Int }
        domain $T1$_ { function i(x: $T1$_): Int }
        domain $T$_$T0$_$T1$ { function j(x: $T$_$T0$_$T1$): Int }";
    check(domains, 0);
    check(&format!("{domains} method bad() {{ assert false; }}"), 1);
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
    for count in [1, 2] {
        let mut config = Config::parse(&[
            "--numberOfParallelVerifiers".into(),
            count.to_string(),
            "--ignoreFile".into(),
            "session.vpr".into(),
        ])
        .unwrap();
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

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn timed_out_session_can_be_reused() {
    std::thread::Builder::new().stack_size(ferrum::VERIFICATION_STACK_SIZE).spawn(|| {
    use ferrum::{
        Session,
        silicon::config::Config,
        silver::{
            frontend::{
                frontend::FrontendPhases,
                sil_frontend::{SilFrontendPhases, standard_plugin_manager},
            },
            verifier::verification_result::{AbstractError, FrontendErrorKind, VerificationResult},
        },
    };
    // Integer pigeonhole keeps frontend construction compact while making the
    // verification phase exceed the deadline on both pinned solver transports.
    let n = 25;
    let vars = (0..n).map(|i| format!("x{i}: Int")).collect::<Vec<_>>();
    let mut clauses = (0..n)
        .map(|i| format!("(0 <= x{i} && x{i} < {})", n - 1))
        .collect::<Vec<_>>();
    for i in 0..n {
        for j in i + 1..n {
            clauses.push(format!("x{i} != x{j}"));
        }
    }
    let hard = format!(
        "method m({}) {{ assert !({}); }}",
        vars.join(", "),
        clauses.join(" && ")
    );
    for count in [1, 2] {
        let mut config = Config::parse(&[
            "--numberOfParallelVerifiers".into(),
            count.to_string(),
            "--timeout".into(),
            "1".into(),
            "--assertTimeout".into(),
            "0".into(),
            "--checkTimeout".into(),
            "0".into(),
            "--ignoreFile".into(),
            "session.vpr".into(),
        ])
        .unwrap();
        config.prover = std::env::var("FERRUM_TEST_PROVER").unwrap_or_else(|_| "Z3".into());
        if config.prover == "Z3" { config.z3_exe = Some(std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3")); }
        let prepare = |source: &str| {
            let plugins = standard_plugin_manager(&config.frontend).unwrap();
            let mut frontend = SilFrontendPhases::new("session.vpr".into(), plugins);
            frontend.configure_consistency(&config.frontend);
            let parsed = frontend.parse(source).unwrap();
            let analyzed = frontend.analyze(parsed).unwrap();
            let translated = frontend.translate(analyzed).unwrap();
            let program = frontend.check_consistency(translated).unwrap();
            frontend.prepare_verification(program).unwrap()
        };
        let hard = prepare(&hard);
        let simple = prepare("method m() { assert true; }");
        let mut session = Session::new(config.clone()).unwrap();
        let result = session.verify(&hard, &[]).unwrap();
        assert!(
            matches!(result, VerificationResult::Failure(ref errors) if matches!(&errors[0], AbstractError::Frontend(e) if matches!(e.kind, FrontendErrorKind::TimeoutOccurred { .. })))
        );
        assert!(matches!(
            session.verify(&simple, &[]).unwrap(),
            VerificationResult::Success
        ));
        session.stop().unwrap();
    }
    }).unwrap().join().unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn cached_predicates_preserve_branch_values_and_permission_amounts() {
    let source = "field f: Int
        field g: Int
        predicate P(x: Ref, b: Bool) {
            b ? (acc(x.f) && x.f == 7) : (acc(x.g) && x.g == 8)
        }
        method m(x: Ref, b: Bool) requires acc(P(x, b)) {
            unfold acc(P(x, b), 1/2);
            assert b ? (acc(x.f, 1/2) && x.f == 7) : (acc(x.g, 1/2) && x.g == 8);
        }";
    for (source, expected) in [
        (source.to_owned(), 0),
        (
            source.replace("assert b ? (acc(x.f, 1/2)", "assert b ? (acc(x.f, write)"),
            1,
        ),
        (source.replace("&& x.g == 8);", "&& x.g == 9);"), 1),
    ] {
        let output = run(
            &source,
            &[
                "--enableSimplifiedUnfolds",
                "--moreJoins",
                "1",
                "--numberOfParallelVerifiers",
                "2",
            ],
        );
        assert_eq!(
            output.status.code(),
            Some(expected),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if expected == 1 {
            assert!(String::from_utf8_lossy(&output.stderr).contains("assert.failed"));
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn domain_axioms_can_call_precondition_free_functions() {
    let source = "function interp(i: Int): Int { i + 1 }
        domain D {
            function unint(i: Int): Int
            axiom { forall i: Int :: {unint(i)} unint(i) == interp(i) + 1 }
        }
        method m() { assert unint(4) == 6; }";
    check(source, 0);
    check(&source.replace("unint(4) == 6", "unint(4) == 7"), 1);
    let invalid = source.replace("Int { i + 1 }", "Int requires i >= 0 { i + 1 }");
    let output = run(&invalid, &[]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("FunctionPreconditionInDomainAxiom"));
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn domain_axioms_allow_typed_adt_accesses_but_reject_heap_locations() {
    let source = r#"
        adt Box[T] { Boxed(elem: T) }
        domain D {
            function value(b: Box[Int]): Int
            function valid(b: Box[Int]): Bool
            axiom { forall b: Box[Int] :: {value(b)} value(b) == b.elem }
            axiom { forall b: Box[Int] :: {valid(b)} valid(b) == b.isBoxed }
            axiom { forall x: Int :: {value(Boxed(x))} value(Boxed(x)) == Boxed(x).elem }
        }
        method good() { assert value(Boxed(7)) == 7; assert valid(Boxed(7)); }
    "#;
    check(source, 0);
    check(
        &source.replace("value(Boxed(7)) == 7", "value(Boxed(7)) == 8"),
        1,
    );
    for invalid in [
        "field f: Int domain D { function f_of(x: Ref): Int axiom { forall x: Ref :: {f_of(x)} f_of(x) == x.f } }",
        "adt Box[T] { Boxed(elem: T) } domain D { axiom { forall x: Int :: x.elem == 3 } }",
        "adt Box[T] { Boxed(elem: T) } adt Other { Othered() } domain D { axiom { forall b: Box[Int] :: b.isOthered } }",
        "adt Box[T] { Boxed(elem: T) } field elem: Int domain D { axiom { forall x: Ref :: x.elem == 3 } }",
        "field f: Int domain D { axiom { forall x: Ref :: acc(x.f) } }",
    ] {
        let output = run(invalid, &[]);
        assert_eq!(
            output.status.code(),
            Some(2),
            "unexpected result for invalid axiom {invalid}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn mask_heaps_preserve_unfolding_frames_and_wand_values() {
    let cases = [
        (
            r#"field f: Int predicate p(x: Ref) { acc(x.f) } function read(x: Ref): Int requires acc(p(x)) { unfolding acc(p(x)) in x.f } method test() { var x: Ref := new(f); x.f := 2; fold acc(p(x)); assert read(x)==2; }"#,
            0,
        ),
        (
            r#"field f: Int predicate p(x: Ref) { acc(x.f) } function read(x: Ref): Int requires acc(p(x)) { unfolding acc(p(x)) in x.f } method test() { var x: Ref := new(f); x.f := 2; fold acc(p(x)); assert read(x)==3; }"#,
            1,
        ),
        (
            r#"field f: Int
method m(x: Ref, z: Ref) requires x != z && (forall y: Ref :: y == x || y == z ==> acc(y.f)) && x.f == 1 && z.f == 2 {
  package acc(x.f) --* (forall y: Ref :: y == x || y == z ==> acc(y.f)) {}
  apply acc(x.f) --* (forall y: Ref :: y == x || y == z ==> acc(y.f))
  assert x.f == 1 && z.f == 2
}
"#,
            0,
        ),
        (
            r#"field f: Int
method m(x: Ref, z: Ref) requires x != z && (forall y: Ref :: y == x || y == z ==> acc(y.f)) && x.f == 1 && z.f == 2 {
  package acc(x.f) --* (forall y: Ref :: y == x || y == z ==> acc(y.f)) {}
  apply acc(x.f) --* (forall y: Ref :: y == x || y == z ==> acc(y.f))
  assert x.f == 2 && z.f == 2
}
"#,
            1,
        ),
        (
            r#"field f: Int
function foo(r: Ref, n: Int): Bool
  requires acc(r.f)
{ forall i: Int :: {foo(r, i)} foo(r, i) == foo(r, i) }
method test(r: Ref) requires acc(r.f) { assert foo(r, 0) }
"#,
            0,
        ),
        (
            r#"field f: Int
function foo(r: Ref, n: Int): Bool
  requires acc(r.f)
{ forall i: Int :: {foo(r, i)} foo(r, i) == foo(r, i) }
method test(r: Ref) requires acc(r.f) { assert !foo(r, 0) }
"#,
            1,
        ),
    ];
    for workers in ["1", "2"] {
        for simplify in [false, true] {
            let mut args = vec!["--maskHeapMode", "--numberOfParallelVerifiers", workers];
            if simplify {
                args.push("--simplifyOnConsume");
            }
            for (source, expected) in cases {
                let output = run(source, &args);
                assert_eq!(
                    output.status.code(),
                    Some(expected),
                    "workers={workers}, simplify={simplify}, source={source}\n{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                if expected == 1 {
                    assert!(String::from_utf8_lossy(&output.stderr).contains("assert.failed"));
                }
            }
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3 or FERRUM_TEST_PROVER=Z3-API"]
fn public_parallel_branches_verify_terminal_paths() {
    let source = "field f: Int method good(x: Ref, b: Bool) returns (r: Int) requires acc(x.f) ensures acc(x.f) && r > 0 { if (b) { x.f := 1; } else { x.f := 2; } r := x.f; } method bad(x: Ref, b: Bool) returns (r: Int) requires acc(x.f) ensures acc(x.f) && r > 0 { if (b) { x.f := 1; } else { x.f := 0; } r := x.f; }";
    for workers in ["1", "2", "4"] {
        for enabled in [false, true] {
            let mut args = vec!["--numberOfParallelVerifiers", workers, "--no-timing"];
            if enabled {
                args.push("--parallelizeBranches");
            }
            let output = run(source, &args);
            assert_eq!(
                output.status.code(),
                Some(1),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("postcondition"), "{stderr}");
        }
    }
}

#[test]
fn backend_type_interpretation_is_checked_before_solver_start() {
    let path = std::env::temp_dir().join(format!(
        "ferrum-interpretation-{}-{}.vpr",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let input = Input(path);
    std::fs::write(&input.0, "domain myBV interpretation (FantasyBackend: \"bv32\") { function f(x: Int): myBV interpretation \"f\" }").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ferrum"))
        .arg(&input.0)
        .output()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(2),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Domain myBV has no interpretation for backend SMTLIB."),
        "{stderr}"
    );
    assert!(stderr.contains("@1.1"), "{stderr}");
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn singleton_quantified_wand_resource_properties_verify() {
    let source = r#"
        field f: Int
        method mWand(r: Ref)
            requires acc(r.f) --* false
        {
            assume exists x: Ref :: { acc(x.f) --* false } perm(acc(x.f) --* false) > none
        }
    "#;
    check(source, 0);
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn forperm_matches_nonquantified_magic_wand_chunks() {
    let prefix = r#"
        field f: Int
        method m(x: Ref, y: Ref, z: Ref) {
            inhale acc(x.f)
            inhale acc(y.f)
            inhale acc(z.f)
            inhale acc(x.f) --* acc(y.f)
            inhale acc(z.f) --* acc(y.f)
            inhale forperm a: Ref, b: Ref [acc(a.f) --* acc(b.f)] :: a.f > 0 && b.f < 0
    "#;
    check(&format!("{prefix} assert x.f > 0; assert y.f < 0; }}"), 0);
    check(
        &format!("{prefix} assert forperm a: Ref, b: Ref [acc(a.f) --* acc(b.f)] :: false; }}"),
        1,
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn wand_proof_cfg_executes_conditional_branches_and_uses_their_footprints() {
    let prefix = r#"
        field f: Int
        method m(x: Ref, y: Ref, b: Bool)
          requires acc(x.f) && acc(y.f)
        {
          package true --* true {
            if (b) { exhale acc(x.f) } else { exhale acc(y.f) }
          }
    "#;
    let positive = format!("{prefix} if (b) {{ assert acc(y.f) }} else {{ assert acc(x.f) }} }}");
    let negative = format!("{prefix} if (b) {{ assert acc(x.f) }} }}");
    let false_proof = "method m(b: Bool) { package true --* true { if (b) { assert false } } }";
    for workers in ["1", "2"] {
        for (source, expected) in [(&positive as &str, 0), (&negative, 1), (false_proof, 1)] {
            let output = run(source, &["--numberOfParallelVerifiers", workers]);
            assert_eq!(
                output.status.code(),
                Some(expected),
                "workers={workers}; {}",
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
fn unresolved_function_warning_uses_source_expression_and_position() {
    let output = run(
        "function f(i: Int): Int { true ? 0 : f(i) }\nmethod m() { assert f(0) == 0 }\n",
        &[],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{stderr}");
    assert!(
        stderr.contains("Could not resolve expression f(i) ("),
        "{stderr}"
    );
    assert!(
        stderr.contains("@1.38--1.42) during the axiomatisation of function f."),
        "{stderr}"
    );
    assert!(
        stderr.contains("a fresh symbol, i.e. an arbitrary value."),
        "{stderr}"
    );
    assert!(
        !stderr.contains("ExpNode") && !stderr.contains("PNode"),
        "{stderr}"
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn loop_termination_diagnostic_uses_decreases_clause_span() {
    let source = "import <decreases/int.vpr>\nmethod m(x: Int) {\n  while (x >= 0)\n    decreases x\n  { }\n}\n";
    let output = run(source, &[]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.contains("termination.failed:tuple.false"),
        "{stderr}"
    );
    assert!(stderr.contains("@4.15--4.16"), "{stderr}");
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn termination_specification_order_preserves_source_failures() {
    for source in [
        include_str!("fixtures/termination_function_spec_order.vpr"),
        include_str!("fixtures/termination_method_spec_order.vpr"),
    ] {
        let output = run(
            source,
            &["--disableCaches", "--numberOfParallelVerifiers", "1"],
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(1), "{stderr}");
        assert_eq!(
            stderr.matches("termination.failed:tuple.false").count(),
            3,
            "{stderr}"
        );
        assert_eq!(
            stderr
                .matches("termination.failed:tuple.condition.false")
                .count(),
            3,
            "{stderr}"
        );
    }
    let output = run(
        include_str!("fixtures/termination_multiple_decreases.vpr"),
        &["--disableCaches", "--numberOfParallelVerifiers", "1"],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert_eq!(
        stderr.matches("Multiple decreases tuple.").count(),
        3,
        "{stderr}"
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn heap_trigger_failed_argument_does_not_hide_later_assertion_failure() {
    let output = run(
        include_str!("fixtures/heap_trigger_failed_argument.vpr"),
        &["--disableCaches", "--numberOfParallelVerifiers", "1"],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(stderr.contains("assert.failed:assertion.false"), "{stderr}");
    assert!(stderr.contains("3 + 8 == 38"), "{stderr}");
    assert!(
        !stderr.contains("heap trigger argument verification failure"),
        "{stderr}"
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn sif_relational_conditions_preserve_branch_and_loop_failures() {
    for source in [
        include_str!("fixtures/sif_branch_condition.vpr"),
        include_str!("fixtures/sif_branch_issue_903.vpr"),
        include_str!("fixtures/sif_loop_condition.vpr"),
        "method m(t: Int) requires lowEvent { if (!low(t)) { assert false } }",
    ] {
        let output = run(
            source,
            &[
                "--plugin",
                "viper.silver.plugin.sif.SIFPlugin",
                "--disableCaches",
                "--numberOfParallelVerifiers",
                "1",
            ],
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(1), "{stderr}");
        assert_eq!(
            stderr.matches("assert.failed:assertion.false").count(),
            1,
            "{stderr}"
        );
        assert!(
            stderr.contains("Assertion false might not hold"),
            "{stderr}"
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn sif_relational_condition_respects_active_executions() {
    let source = "method m(t: Int) requires lowEvent { if (low(t)) { assert low(t) } else { assert !low(t) } } method n(t: Int) requires !lowEvent { if (low(t)) { assert true } else { assert false } }";
    let output = run(
        source,
        &[
            "--plugin",
            "viper.silver.plugin.sif.SIFPlugin",
            "--disableCaches",
            "--numberOfParallelVerifiers",
            "1",
        ],
    );
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn sif_invalid_function_and_domain_reports_all_structured_diagnostics() {
    let source = "function bad(x: Int): Int requires low(x) ensures lowEvent { x }\ndomain D { function f(): Int axiom { low(f()) } axiom { lowEvent } }\n";
    let output = run(
        source,
        &[
            "--plugin",
            "viper.silver.plugin.sif.SIFPlugin",
            "--disableCaches",
            "--numberOfParallelVerifiers",
            "1",
        ],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    let lines: Vec<_> = stderr.lines().collect();
    assert_eq!(lines.len(), 4, "{stderr}");
    for (line, expected, position) in lines
        .iter()
        .zip([
            "low(x) is not supported. Relational assertions are not allowed in functions.",
            "lowEvent is not supported. Relational assertions are not allowed in functions.",
            "low(f()) is not supported. Relational assertions are not allowed in domains.",
            "lowEvent is not supported. Relational assertions are not allowed in domains.",
        ])
        .zip([
            "@1.36--1.42)",
            "@1.51--1.59)",
            "@2.38--2.46)",
            "@2.57--2.65)",
        ])
        .map(|((line, expected), position)| (line, expected, position))
    {
        assert!(
            line.contains("internal:feature.unsupported")
                && line.contains(expected)
                && line.contains(position),
            "{stderr}"
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn sif_unsupported_goto_reports_source_error() {
    let source = "method m() {\n  goto end\n  label end\n}";
    let output = run(source, &["--plugin", "viper.silver.plugin.sif.SIFPlugin"]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(
        stderr.contains("internal:feature.unsupported")
            && stderr.contains(
                "goto end is not supported. Goto statements are currently not supported."
            )
            && stderr.contains("@2.3--2.11)"),
        "{stderr}"
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn sif_plugin_errors_preserve_typechecking_warnings_and_exit_status() {
    let source =
        "field f: Int\nfunction bad(r: Ref): Int requires acc(r.f, 1/2) requires low(r) { r.f }\n";
    let output = run(source, &["--plugin", "viper.silver.plugin.sif.SIFPlugin"]);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    let warning = stderr
        .find("Function contains specific permission amount")
        .expect("typechecking warning");
    let error = stderr
        .find("internal:feature.unsupported")
        .expect("SIF error");
    assert!(
        warning < error && stderr.contains("@2.45--2.48)") && stderr.contains("@2.59--2.65)"),
        "{stderr}"
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn arp_invalid_uses_report_all_source_errors_and_positions() {
    let options = [
        "--plugin",
        "viper.silver.plugin.standard.arp.ARPPlugin",
        "--disableCaches",
        "--numberOfParallelVerifiers",
        "1",
    ];
    let output = run(
        include_str!("fixtures/arp_unsupported_expressions.vpr"),
        &options,
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    let errors: Vec<_> = stderr
        .lines()
        .filter(|line| {
            line.contains("Consistency error: Unsupported use of abstract read permission rd:")
        })
        .collect();
    assert_eq!(errors.len(), 15, "{stderr}");
    for (line, position) in errors.iter().zip([
        "13.27", "15.20", "19.25", "23.18", "31.23", "33.22", "35.18", "37.8", "39.13", "41.34",
        "43.20", "45.23", "53.31", "59.34", "66.14",
    ]) {
        assert!(line.contains(&format!("@{position}--")), "{stderr}");
    }
    assert!(errors[13].contains("rd cannot be used inside magic wands."));
    assert!(errors[14].contains("rd cannot be used inside magic wands."));
    let output = run(
        include_str!("fixtures/arp_unsupported_members.vpr"),
        &options,
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    let errors: Vec<_> = stderr
        .lines()
        .filter(|line| {
            line.contains("Consistency error: Unsupported use of abstract read permission rd:")
        })
        .collect();
    assert_eq!(errors.len(), 4, "{stderr}");
    for (line, position) in errors.iter().zip(["31.12", "10.21", "18.3", "23.12"]) {
        assert!(line.contains(&format!("@{position}--")), "{stderr}");
    }
    assert!(
        stderr.contains("Function contains specific permission amount"),
        "{stderr}"
    );
    let output = run(include_str!("fixtures/arp_quantified.vpr"), &options);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert_eq!(
        stderr
            .matches("call.precondition:insufficient.permission")
            .count(),
        1,
        "{stderr}"
    );
    assert!(stderr.contains("@36.3--36.15)"), "{stderr}");
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn arp_wand_and_indirect_use_emit_independent_source_errors() {
    let source = "field f: Int\nmethod m(x: Ref) requires acc(x.f) --* acc(x.f, rd * 2)\n";
    let output = run(
        source,
        &["--plugin", "viper.silver.plugin.standard.arp.ARPPlugin"],
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    let lines: Vec<_> = stderr.lines().collect();
    assert_eq!(lines.len(), 2, "{stderr}");
    assert!(
        lines[0].contains("rd cannot be used inside magic wands.")
            && lines[0].contains("@2.49--2.51)"),
        "{stderr}"
    );
    assert!(
        lines[1].contains("rd can only be used directly as the permission amount")
            && lines[1].contains("@2.49--2.51)"),
        "{stderr}"
    );
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn deep_statement_execution_keeps_success_and_failure_obligations() {
    let statements = "x := x + 1;\n".repeat(1200);
    let source = format!(
        "method good() {{ var x: Int := 0; {statements} assert x == 1200; }}\nmethod bad() {{ var x: Int := 0; {statements} assert x == 1201; }}"
    );
    for workers in ["1", "2"] {
        let output = run(
            &source,
            &["--disableCaches", "--numberOfParallelVerifiers", workers],
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(1), "{stderr}");
        assert_eq!(
            stderr.matches("assert.failed:assertion.false").count(),
            1,
            "{stderr}"
        );
        assert!(stderr.contains("x == 1201"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn adt_signature_errors_collect_positions_across_members() {
    let options = ["--plugin", "viper.silver.plugin.standard.adt.AdtPlugin"];
    let output = run(include_str!("fixtures/adt_declarations_7.vpr"), &options);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert!(
        stderr.contains("undeclared adt field `Leaf3`, expected field in containing adt"),
        "{stderr}"
    );
    assert!(stderr.contains("@8.22--8.27"), "{stderr}");
    assert!(
        stderr.contains("undeclared adt field `hello`, expected field in containing adt"),
        "{stderr}"
    );
    assert!(stderr.contains("@16.37--16.42"), "{stderr}");
    let output = run(
        include_str!("fixtures/adt_variable_declarations_2.vpr"),
        &options,
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(2), "{stderr}");
    assert_eq!(
        stderr.matches("wrong number of type arguments").count(),
        3,
        "{stderr}"
    );
    for pos in ["@9.16--9.30", "@12.16--12.20", "@25.75--25.92"] {
        assert!(stderr.contains(pos), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn adt_discriminator_shadow_reports_constructor_and_shadow_positions() {
    let options = ["--plugin", "viper.silver.plugin.standard.adt.AdtPlugin"];
    for (source, shadow) in [
        (include_str!("fixtures/adt_discriminators_5.vpr"), "@8.7"),
        (include_str!("fixtures/adt_discriminators_6.vpr"), "@7.10"),
    ] {
        let output = run(source, &options);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(2), "{stderr}");
        assert!(
            stderr.contains("corresponding adt discriminator identifier `isNil`"),
            "{stderr}"
        );
        assert!(
            stderr.contains("@3.5--3.8") && stderr.contains(shadow),
            "{stderr}"
        );
    }
}
