//! Ferrum owned return-stack regression assembly described in PLAN.md.
//! Source-order regression for an owned asserting value nested on the right of addition.
use std::sync::atomic::{AtomicUsize, Ordering};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn run(source: &str, workers: &str) -> std::process::Output {
    run_with_limit(source, workers, None)
}
fn run_with_limit(source: &str, workers: &str, limit: Option<&str>) -> std::process::Output {
    let path = std::env::temp_dir().join(format!(
        "ferrum-return-order-{}-{}.vpr",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source).unwrap();
    let mut command = std::process::Command::new(env!("CARGO_BIN_EXE_ferrum"));
    if let Some(limit) = limit {
        command.args(["--numberOfErrorsToReport", limit]);
    }
    let output = command
        .arg("--z3Exe")
        .arg(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"))
        .args([
            "--parallelizeBranches",
            "--numberOfParallelVerifiers",
            workers,
        ])
        .arg(&path)
        .output()
        .unwrap();
    std::fs::remove_file(path).unwrap();
    output
}
#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn left_operand_failure_precedes_nested_assertion() {
    let source = r#"field f: Int
method bad(x: Ref, b: Bool) returns (r: Int) {
    r := x.f + -(old(asserting (b ? false : false) in 1));
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(
            !output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn failing_left_assertion_precedes_right_assertion() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Int)
  requires x != y
{
    label L;
    r := -(old(asserting (b ? acc(x.f) : acc(y.f)) in 1) + old[L](asserting (c ? false : false) in 2));
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(
            !output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn strict_left_failure_precedes_right_assertion() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Bool)
  requires x != y
{
    r := !((asserting (b ? acc(x.f) : acc(y.f)) in 1) < (asserting (c ? false : false) in 2));
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn strict_right_failure_skips_tail() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, w: Ref, b: Bool, c: Bool) returns (r: Int)
  requires w != x && w != y && acc(x.f) && acc(y.f)
{
    r := (asserting (b ? acc(x.f) : acc(y.f)) in 7) - (asserting (c ? acc(w.f) : acc(w.f)) in 4);
    assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn outer_assertion_failure_precedes_nested_body() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Int)
  requires x != y
{
    r := asserting (b ? acc(x.f) : acc(y.f)) in (asserting (c ? false : false) in 1);
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn inner_assertion_failure_skips_caller_tail() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, w: Ref, b: Bool, c: Bool) returns (r: Int)
  requires w != x && w != y && acc(x.f) && acc(y.f)
{
    r := asserting (b ? acc(x.f) : acc(y.f)) in -(asserting (c ? acc(w.f) : acc(w.f)) in 1);
    assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn let_value_failure_precedes_body_assertion() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Int)
  requires x != y
{
  r := (let v == (asserting (b ? acc(x.f) : acc(y.f)) in 1) in (asserting (c ? false : false) in v));
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn let_body_failure_skips_caller_tail() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, w: Ref, b: Bool, c: Bool) returns (r: Int)
  requires w != x && w != y && acc(x.f) && acc(y.f)
{
  r := (let v == (asserting (b ? acc(x.f) : acc(y.f)) in 1) in (asserting (c ? acc(w.f) : acc(w.f)) in v));
  assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn necmp_value_failure_precedes_right_assertion() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Bool)
  requires x != y
{
  r := (asserting (b ? acc(x.f) : acc(y.f)) in 1) != (asserting (c ? false : false) in 2);
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn divmod_left_permission_failure_precedes_divisor_check() {
    for operator in ["/", "%"] {
        let source = format!(
            r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool) returns (r: Int)
 requires x != y
{{ r := (asserting (b ? acc(x.f) : acc(y.f)) in 1) {operator} 0; }}
"#
        );
        for workers in ["1", "2"] {
            let output = run(&source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("insufficient.permission"), "{stderr}");
            assert!(!stderr.contains("division.by.zero"), "{stderr}");
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn divmod_zero_failure_prevents_tail_at_default_limit() {
    for operator in ["/", "%"] {
        let source = format!(
            r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int)
 requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
{{ r := (asserting (b ? acc(x.f) : acc(y.f)) in 1) {operator} (asserting (c ? acc(z.f) : acc(w.f)) in 0); assert false; }}
"#
        );
        for workers in ["1", "2"] {
            let output = run(&source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("division.by.zero"), "{stderr}");
            assert!(
                stderr.contains("Divisor (asserting"),
                "divisor attribution missing: {stderr}"
            );
            assert!(!stderr.contains("assertion.false"), "{stderr}");
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn divmod_report_further_errors_keeps_tail_failure() {
    for operator in ["/", "%"] {
        let source = format!(
            r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref, d: Int) returns (r: Int)
 requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
{{ r := (asserting (b ? acc(x.f) : acc(y.f)) in 1) {operator} (asserting (c ? acc(z.f) : acc(w.f)) in d); assert false; }}
"#
        );
        for workers in ["1", "2"] {
            let output = run_with_limit(&source, workers, Some("0"));
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("division.by.zero"), "{stderr}");
            assert!(
                stderr.contains("Divisor (asserting"),
                "divisor attribution missing: {stderr}"
            );
            assert!(stderr.contains("assertion.false"), "{stderr}");
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn necmp_right_permission_failure_skips_caller_tail() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, w: Ref, b: Bool, c: Bool) returns (r: Bool)
 requires w != x && w != y && acc(x.f) && acc(y.f)
{ r := (asserting (b ? acc(x.f) : acc(y.f)) in 1) != (asserting (c ? acc(w.f) : acc(w.f)) in 2); assert false; }
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn field_receiver_failure_precedes_read_and_tail() {
    let source = r#"field f: Int
method bad(x: Ref, b: Bool) returns (r: Int) {
  r := (asserting (b ? false : false) in x).f;
  assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("assertion.false"), "{stderr}");
        assert!(!stderr.contains("insufficient.permission"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn field_read_failure_skips_caller_tail() {
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, z: Ref, b: Bool) returns (r: Int)
 requires x != z && y != z && acc(x.f) && acc(y.f)
{
  r := (asserting (b ? acc(x.f) : acc(y.f)) in z).f;
  assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn domain_argument_failure_order_and_tail() {
    for (declaration, name) in [
        ("domain D { function f(a: Int, b: Int): Int }", "f"),
        (
            "domain Ops { function sum(a: Int, b: Int): Int interpretation \"+\" }",
            "sum",
        ),
    ] {
        let first = format!(
            r#"{declaration}
field val: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Int) requires x != y
{{ r := {name}((asserting (b ? acc(x.val) : acc(y.val)) in 1), (asserting (c ? false : false) in 2)); }}
"#
        );
        let later = format!(
            r#"{declaration}
field val: Int
method bad(x: Ref, y: Ref, w: Ref, b: Bool, c: Bool) returns (r: Int)
 requires w != x && w != y && acc(x.val) && acc(y.val)
{{ r := {name}((asserting (b ? acc(x.val) : acc(y.val)) in 1), (asserting (c ? acc(w.val) : acc(w.val)) in 2)); assert false; }}
"#
        );
        for source in [&first, &later] {
            for workers in ["1", "2"] {
                let output = run(source, workers);
                assert!(!output.status.success());
                let stderr = String::from_utf8_lossy(&output.stderr);
                assert!(stderr.contains("insufficient.permission"), "{stderr}");
                assert!(!stderr.contains("assertion.false"), "{stderr}");
            }
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn current_permission_arguments_failure_order_and_tail() {
    let first = r#"field val: Int
predicate P(a: Ref, b: Ref) { true }
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Perm) requires x != y
{ r := perm(P((asserting (b ? acc(x.val) : acc(y.val)) in x), (asserting (c ? false : false) in y))); }
"#;
    let later = r#"field val: Int
predicate P(a: Ref, b: Ref) { true }
method bad(x: Ref, y: Ref, w: Ref, b: Bool, c: Bool) returns (r: Perm)
 requires w != x && w != y && acc(x.val) && acc(y.val)
{ r := perm(P((asserting (b ? acc(x.val) : acc(y.val)) in x), (asserting (c ? acc(w.val) : acc(w.val)) in w))); assert false; }
"#;
    for source in [first, later] {
        for workers in ["1", "2"] {
            let output = run(source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("insufficient.permission"), "{stderr}");
            assert!(!stderr.contains("assertion.false"), "{stderr}");
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn current_permission_mask_heap_parallel_arguments() {
    let source = r#"field val: Int
predicate P(a: Ref, b: Ref) { true }
method field_case(b: Bool, x: Ref, y: Ref) returns (r: Perm)
 requires acc(x.val) && acc(y.val) ensures r == write && acc(x.val) && acc(y.val)
{ r := perm((asserting (b ? acc(x.val) : acc(y.val)) in x).val); }
method pred_case(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Perm)
 requires acc(x.val) && acc(y.val) && acc(z.val) && acc(w.val) && acc(P(x, z))
 ensures r == write && acc(P(x, z))
{ r := perm(P((asserting (b ? acc(x.val) : acc(y.val)) in x), (asserting (c ? acc(z.val) : acc(w.val)) in z))); }
"#;
    let path = std::env::temp_dir().join(format!(
        "ferrum-permission-mask-{}-{}.vpr",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source).unwrap();
    for workers in ["1", "2"] {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_ferrum"))
            .arg("--z3Exe")
            .arg(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"))
            .args([
                "--parallelizeBranches",
                "--numberOfParallelVerifiers",
                workers,
                "--maskHeapMode",
            ])
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    std::fs::remove_file(path).unwrap();
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn function_argument_failure_precedes_precondition() {
    let source = r#"field val: Int
function f(a: Int, b: Int): Int requires a > 0 { a + b }
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Int) requires x != y
{ r := f((asserting (b ? acc(x.val) : acc(y.val)) in -1), (asserting (c ? false : false) in 2)); }
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
        assert!(!stderr.contains("application.precondition"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn function_precondition_failure_skips_caller_tail() {
    let source = r#"field val: Int
function f(a: Int, b: Int): Int requires a > 0 { a + b }
method bad(x: Ref, y: Ref, z: Ref, w: Ref, b: Bool, c: Bool) returns (r: Int)
 requires acc(x.val) && acc(y.val) && acc(z.val) && acc(w.val)
{ r := f((asserting (b ? acc(x.val) : acc(y.val)) in -1), (asserting (c ? acc(z.val) : acc(w.val)) in 2)); assert false; }
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("application.precondition"), "{stderr}");
        assert!(
            !stderr.contains("[assert.failed:assertion.false]"),
            "{stderr}"
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn permission_division_zero_and_left_failure_order() {
    for (left, zero) in [("1", "0"), ("write", "0"), ("write", "none")] {
        let source = format!(
            r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Perm)
 requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
{{ r := (asserting (b ? acc(x.f) : acc(y.f)) in {left}) / (asserting (c ? acc(z.f) : acc(w.f)) in {zero}); assert false; }}
"#
        );
        for workers in ["1", "2"] {
            let output = run(&source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                stderr.contains("division.by.zero") && stderr.contains("Divisor (asserting"),
                "{stderr}"
            );
            assert!(!stderr.contains("assertion.false"), "{stderr}");
        }
    }
    let source = r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool) returns (r: Perm)
 requires x != y
{ r := (asserting (b ? acc(x.f) : acc(y.f)) in write) / 0; }
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("division.by.zero"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn permission_division_report_further_errors_keeps_tail() {
    for (left, typ) in [("1", "Int"), ("write", "Int"), ("write", "Perm")] {
        let source = format!(
            r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref, d: {typ}) returns (r: Perm)
 requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
{{ r := (asserting (b ? acc(x.f) : acc(y.f)) in {left}) / (asserting (c ? acc(z.f) : acc(w.f)) in d); assert false; }}
"#
        );
        for workers in ["1", "2"] {
            let output = run_with_limit(&source, workers, Some("0"));
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                stderr.contains("division.by.zero") && stderr.contains("Divisor (asserting"),
                "{stderr}"
            );
            assert!(stderr.contains("assertion.false"), "{stderr}");
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn explicit_collection_element_failure_order_and_tail() {
    for kind in ["Seq", "Set", "Multiset"] {
        let first = format!(
            r#"field val: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: {kind}[Int]) requires x != y
{{ r := {kind}((asserting (b ? acc(x.val) : acc(y.val)) in 1), (asserting (c ? false : false) in 2)); }}
"#
        );
        let later = format!(
            r#"field val: Int
method bad(x: Ref, y: Ref, w: Ref, b: Bool, c: Bool) returns (r: {kind}[Int])
 requires w != x && w != y && acc(x.val) && acc(y.val)
{{ r := {kind}((asserting (b ? acc(x.val) : acc(y.val)) in 1), (asserting (c ? acc(w.val) : acc(w.val)) in 2)); assert false; }}
"#
        );
        for source in [&first, &later] {
            for workers in ["1", "2"] {
                let output = run(source, workers);
                assert!(!output.status.success());
                let stderr = String::from_utf8_lossy(&output.stderr);
                assert!(stderr.contains("insufficient.permission"), "{stderr}");
                assert!(!stderr.contains("assertion.false"), "{stderr}");
            }
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn indexed_collection_checks_and_tail() {
    let cases = [
        (
            "(asserting (b ? acc(x.val) : acc(y.val)) in Seq(3))[(asserting (c ? acc(z.val) : acc(w.val)) in -1)]",
            "seq.index.negative",
        ),
        (
            "(asserting (b ? acc(x.val) : acc(y.val)) in Seq(3))[(asserting (c ? acc(z.val) : acc(w.val)) in 2)]",
            "seq.index.length",
        ),
        (
            "(asserting (b ? acc(x.val) : acc(y.val)) in Map(1 := 3))[(asserting (c ? acc(z.val) : acc(w.val)) in 0)]",
            "map.key.contains",
        ),
    ];
    for (expression, reason) in cases {
        let source = format!(
            r#"field val: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int)
 requires acc(x.val) && acc(y.val) && acc(z.val) && acc(w.val)
{{ r := {expression}; assert false; }}
"#
        );
        for workers in ["1", "2"] {
            let output = run(&source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains(reason), "{stderr}");
            assert!(
                !stderr.contains("[assert.failed:assertion.false]"),
                "{stderr}"
            );
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn sequence_update_value_failure_precedes_bounds_check() {
    let source = r#"field val: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Seq[Int])
 requires acc(x.val) && acc(y.val) && acc(z.val) && acc(w.val)
{ r := (asserting (b ? acc(x.val) : acc(y.val)) in Seq(3))[(asserting (c ? acc(z.val) : acc(w.val)) in 2) := (asserting (false) in 9)]; }
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("assertion.false"), "{stderr}");
        assert!(!stderr.contains("seq.index.length"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn indexed_collection_report_further_preserves_tail() {
    let cases = [
        (
            "(asserting (b ? acc(x.val) : acc(y.val)) in Seq(3))[(asserting (c ? acc(z.val) : acc(w.val)) in i)]",
            "seq.index.negative",
        ),
        (
            "(asserting (b ? acc(x.val) : acc(y.val)) in Map(1 := 3))[(asserting (c ? acc(z.val) : acc(w.val)) in i)]",
            "map.key.contains",
        ),
    ];
    for (expression, reason) in cases {
        let source = format!(
            r#"field val: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref, i: Int) returns (r: Int)
 requires acc(x.val) && acc(y.val) && acc(z.val) && acc(w.val)
{{ r := {expression}; assert false; }}
"#
        );
        for workers in ["1", "2"] {
            let output = run_with_limit(&source, workers, Some("0"));
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains(reason), "{stderr}");
            assert!(
                stderr.contains("[assert.failed:assertion.false]"),
                "{stderr}"
            );
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn boolean_head_failure_precedes_branch_and_tail() {
    let head = "(asserting (b ? acc(x.f) : acc(y.f)) in b)";
    let branch_bool = "(asserting (false) in true)";
    let cases = [
        (
            format!("{head} ? (asserting (false) in 1) : (asserting (false) in 2)"),
            "Int",
        ),
        (format!("{head} ==> {branch_bool}"), "Bool"),
        (format!("{head} && {branch_bool}"), "Bool"),
        (format!("{head} || {branch_bool}"), "Bool"),
    ];
    for (expression, typ) in cases {
        let source = format!(
            r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool) returns (r: {typ}) requires x != y
{{ r := {expression}; assert false; }}
"#
        );
        for workers in ["1", "2"] {
            let output = run(&source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                stderr.contains("insufficient.permission"),
                "{expression}: {stderr}"
            );
            assert!(
                !stderr.contains("assertion.false"),
                "{expression}: {stderr}"
            );
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn boolean_short_circuit_skips_unreachable_failure() {
    let head = |value: &str| format!("(asserting (b ? acc(x.f) : acc(y.f)) in {value})");
    let cases = [
        format!("{} ? 1 : (asserting (false) in 2)", head("true")),
        format!("{} ==> (asserting (false) in true)", head("false")),
        format!("{} && (asserting (false) in true)", head("false")),
        format!("{} || (asserting (false) in true)", head("true")),
    ];
    for (index, expression) in cases.into_iter().enumerate() {
        let typ = if index == 0 { "Int" } else { "Bool" };
        let source = format!(
            r#"field f: Int
method good(x: Ref, y: Ref, b: Bool) returns (r: {typ}) requires acc(x.f) && acc(y.f)
{{ r := {expression}; }}
"#
        );
        for workers in ["1", "2"] {
            let output = run(&source, workers);
            assert!(
                output.status.success(),
                "{expression}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn boolean_strict_mode_evaluates_right_operand() {
    for (operator, value) in [("&&", "false"), ("||", "true")] {
        let source = format!(
            r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool) returns (r: Bool) requires acc(x.f) && acc(y.f)
{{ r := (asserting (b ? acc(x.f) : acc(y.f)) in {value}) {operator} (asserting (false) in true); }}
"#
        );
        let path = std::env::temp_dir().join(format!(
            "ferrum-boolean-strict-{}-{}.vpr",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::write(&path, source).unwrap();
        for workers in ["1", "2"] {
            let output = std::process::Command::new(env!("CARGO_BIN_EXE_ferrum"))
                .arg("--z3Exe")
                .arg(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"))
                .args([
                    "--parallelizeBranches",
                    "--numberOfParallelVerifiers",
                    workers,
                    "--disableShortCircuitingEvaluations",
                ])
                .arg(&path)
                .output()
                .unwrap();
            assert!(!output.status.success());
            assert!(
                String::from_utf8_lossy(&output.stderr).contains("assertion.false"),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        std::fs::remove_file(path).unwrap();
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn collection_operator_failure_order_and_tail() {
    let unary = r#"field val: Int
method bad(x: Ref, y: Ref, b: Bool) returns (r: Int) requires x != y
{ r := |(asserting (b ? acc(x.val) : acc(y.val)) in Seq(1))|; assert false; }
"#;
    let binary = r#"field val: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Seq[Int]) requires x != y
{ r := (asserting (b ? acc(x.val) : acc(y.val)) in Seq(1)) ++ (asserting (c ? false : false) in Seq(2)); }
"#;
    for source in [unary, binary] {
        for workers in ["1", "2"] {
            let output = run(source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("insufficient.permission"), "{stderr}");
            assert!(
                !stderr.contains("[assert.failed:assertion.false]"),
                "{stderr}"
            );
            assert!(
                !stderr.contains("assignment.failed:assertion.false"),
                "{stderr}"
            );
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn explicit_map_entry_order_and_tail() {
    let first = r#"field val: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Map[Int, Int]) requires x != y
{ r := Map((asserting (b ? acc(x.val) : acc(y.val)) in 1) := (asserting (c ? false : false) in 2)); }
"#;
    let later = r#"field val: Int
method bad(x: Ref, y: Ref, w: Ref, b: Bool, c: Bool) returns (r: Map[Int, Int])
 requires w != x && w != y && acc(x.val) && acc(y.val)
{ r := Map((asserting (b ? acc(x.val) : acc(y.val)) in 1) := (asserting (c ? acc(w.val) : acc(w.val)) in 2)); assert false; }
"#;
    for source in [first, later] {
        for workers in ["1", "2"] {
            let output = run(source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("insufficient.permission"), "{stderr}");
            assert!(!stderr.contains("assertion.false"), "{stderr}");
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn anyset_operator_failure_order_and_tail() {
    for kind in ["Set", "Multiset"] {
        let first = format!(
            r#"field val: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: {kind}[Int]) requires x != y
{{ r := (asserting (b ? acc(x.val) : acc(y.val)) in {kind}(1)) union (asserting (c ? false : false) in {kind}(2)); }}
"#
        );
        let unary = format!(
            r#"field val: Int
method bad(x: Ref, y: Ref, b: Bool) returns (r: Int) requires x != y
{{ r := |(asserting (b ? acc(x.val) : acc(y.val)) in {kind}(1))|; assert false; }}
"#
        );
        for source in [&first, &unary] {
            for workers in ["1", "2"] {
                let output = run(source, workers);
                assert!(!output.status.success());
                let stderr = String::from_utf8_lossy(&output.stderr);
                assert!(stderr.contains("insufficient.permission"), "{stderr}");
                assert!(!stderr.contains("assertion.false"), "{stderr}");
            }
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn sequence_membership_evaluates_sequence_before_element() {
    let source = r#"field val: Int
method bad(x: Ref, y: Ref, b: Bool) returns (r: Bool) requires x != y
{ r := (asserting (false) in 1) in (asserting (b ? acc(x.val) : acc(y.val)) in Seq(1)); }
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn joined_asserting_failure_skips_assignment_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref) returns (r: Int)
 requires b && x != y
{ r := b ? (asserting (c ? acc(x.f) : acc(y.f)) in 1) : 2; assert false; }
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn field_assignment_receiver_failure_precedes_value_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref) requires x != y {
 (asserting (b ? acc(x.f) : acc(y.f)) in x).f := (asserting (c ? false : false) in 1);
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn field_assignment_value_failure_precedes_write_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref) requires acc(x.f) && acc(y.f) && z != x && z != y {
 (asserting (b ? acc(x.f) : acc(y.f)) in z).f := (asserting (c ? false : false) in 1);
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("assertion.false"), "{stderr}");
        assert!(!stderr.contains("insufficient.permission"), "{stderr}");
        assert!(
            !stderr.contains("[assert.failed:assertion.false]"),
            "{stderr}"
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn field_assignment_write_failure_skips_tail() {
    let source = r#"field f: Int
method bad(b: Bool, x: Ref, y: Ref, z: Ref) requires acc(x.f) && acc(y.f) && z != x && z != y {
 z.f := (asserting (b ? acc(x.f) : acc(y.f)) in 1);
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn call_argument_failure_precedes_later_argument_and_precondition() {
    let source = r#"field f: Int
method callee(a: Int, b: Int) requires a > 0
method bad(b: Bool, c: Bool, x: Ref, y: Ref) requires x != y {
 callee((asserting (b ? acc(x.f) : acc(y.f)) in -1), (asserting (c ? false : false) in 1));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
        assert!(!stderr.contains("call.precondition"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn call_precondition_failure_skips_tail_after_owned_arguments() {
    let source = r#"field f: Int
method callee(a: Int, b: Int) requires a > 0
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref)
 requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
{
 callee((asserting (b ? acc(x.f) : acc(y.f)) in -1), (asserting (c ? acc(z.f) : acc(w.f)) in 1));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("call.precondition"), "{stderr}");
        assert!(
            !stderr.contains("[assert.failed:assertion.false]"),
            "{stderr}"
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn boolean_tail_failure_and_skipping() {
    for (op, required, literal) in [("&&", "b", "false"), ("||", "!b", "true")] {
        let reached = format!(
            r#"field f: Int
method bad(x: Ref, y: Ref, b: Bool, c: Bool) returns (r: Bool) requires {required} && x != y
{{ r := b {op} (asserting (c ? acc(x.f) : acc(y.f)) in b); assert false; }}
"#
        );
        let skipped = format!(
            r#"field f: Int
method good(x: Ref, y: Ref, c: Bool) returns (r: Bool)
{{ r := {literal} {op} (asserting (c ? acc(x.f) : acc(y.f)) in true); }}
"#
        );
        for workers in ["1", "2"] {
            let output = run(&reached, workers);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                !output.status.success() && stderr.contains("insufficient.permission"),
                "{stderr}"
            );
            assert!(!stderr.contains("assertion.false"), "{stderr}");
            let output = run(&skipped, workers);
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn cfg_guard_permission_failure_skips_branches_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref) requires x != y
{ if (asserting (c ? acc(x.f) : acc(y.f)) in b) { assert false; } else { assert false; } assert false; }
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success() && stderr.contains("insufficient.permission"),
            "{stderr}"
        );
        assert!(!stderr.contains("assertion.false"), "{stderr}");
        assert!(stderr.contains("if.failed"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn loop_guard_well_definedness_failure_precedes_body_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref) requires x != y
{ var go: Bool; go := b;
  while (asserting (c ? acc(x.f) : acc(y.f)) in go) { assert false; go := false; }
  assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success() && stderr.contains("insufficient.permission"),
            "{stderr}"
        );
        assert!(!stderr.contains("assertion.false"), "{stderr}");
        assert!(stderr.contains("while.failed"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn consumption_guard_failure_skips_branches_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref) requires x != y && x != z && y != z {
 exhale (asserting (b ? acc(x.f) : acc(y.f)) in c) ? acc(z.f) : acc(z.f);
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
        assert!(!stderr.contains("z.f"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn pure_consumption_inner_failure_precedes_outer_assertion() {
    let source = r#"field f: Int
method bad(b: Bool, x: Ref, y: Ref) requires x != y {
 assert (asserting (b ? acc(x.f) : acc(y.f)) in false);
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn pure_consumption_false_skips_tail_after_owned_assertion() {
    let source = r#"field f: Int
method bad(b: Bool, x: Ref, y: Ref, z: Ref)
 requires acc(x.f) && acc(y.f) && z != x && z != y
{
 assert (asserting (b ? acc(x.f) : acc(y.f)) in false);
 exhale acc(z.f);
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("assertion.false"), "{stderr}");
        assert!(!stderr.contains("insufficient.permission"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn pure_consumption_reports_later_failure_when_enabled() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref)
 requires acc(x.f) && acc(y.f) && z != x && z != y
{
 assert (asserting (b ? acc(x.f) : acc(y.f)) in c);
 exhale acc(z.f);
}
"#;
    for workers in ["1", "2"] {
        let output = run_with_limit(source, workers, Some("0"));
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("assertion.false"), "{stderr}");
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn access_argument_failure_precedes_permission_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref) requires x != y && x != z && y != z {
 exhale acc((asserting (b ? acc(x.f) : acc(y.f)) in z).f, (asserting (c ? false : false) in write));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn access_permission_failure_precedes_resource_consumption_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref)
 requires acc(x.f) && acc(y.f) && z != x && z != y
{
 exhale acc((asserting (b ? acc(x.f) : acc(y.f)) in z).f, (asserting (c ? false : false) in write));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("assertion.false"), "{stderr}");
        assert!(!stderr.contains("insufficient.permission"), "{stderr}");
        assert!(
            !stderr.contains("[assert.failed:assertion.false]"),
            "{stderr}"
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn access_negative_permission_precedes_resource_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref)
 requires acc(x.f) && acc(y.f) && z != x && z != y
{
 exhale acc((asserting (b ? acc(x.f) : acc(y.f)) in z).f, (asserting (c ? acc(x.f) : acc(y.f)) in -write));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("negative.permission"), "{stderr}");
        assert!(!stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn consumption_let_first_failure_precedes_later_binding_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) requires x != y {
 exhale (let a == (asserting (b ? acc(x.f) : acc(y.f)) in z) in (let q == (asserting (c ? false : false) in w) in acc(q.f)));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn consumption_let_later_failure_precedes_body_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref)
 requires acc(x.f) && acc(y.f) && w != x && w != y
{
 exhale (let a == (asserting (b ? acc(x.f) : acc(y.f)) in z) in (let q == (asserting (c ? false : false) in w) in acc(q.f)));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("assertion.false"), "{stderr}");
        assert!(!stderr.contains("insufficient.permission"), "{stderr}");
        assert!(
            !stderr.contains("[assert.failed:assertion.false]"),
            "{stderr}"
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn production_guard_failure_precedes_branch_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) requires x != y {
 inhale (asserting (b ? acc(x.f) : acc(y.f)) in c) ? acc(z.f) : acc(w.f);
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn production_pure_inner_failure_skips_assumption_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, x: Ref, y: Ref) requires x != y {
 inhale (asserting (b ? acc(x.f) : acc(y.f)) in false);
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn production_access_argument_failure_precedes_permission_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref) requires x != y {
 inhale acc((asserting (b ? acc(x.f) : acc(y.f)) in z).f, (asserting (c ? false : false) in write));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn production_access_negative_permission_precedes_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref)
 requires acc(x.f) && acc(y.f) && z != x && z != y
{
 inhale acc((asserting (b ? acc(x.f) : acc(y.f)) in z).f, (asserting (c ? acc(x.f) : acc(y.f)) in -write));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("negative.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn production_let_first_failure_precedes_later_binding_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) requires x != y {
 inhale (let a == (asserting (b ? acc(x.f) : acc(y.f)) in z) in (let q == (asserting (c ? false : false) in w) in acc(q.f)));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn production_let_later_failure_precedes_body_and_tail() {
    let source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) requires acc(x.f) && acc(y.f) {
 inhale (let a == (asserting (b ? acc(x.f) : acc(y.f)) in z) in (let q == (asserting (c ? false : false) in w) in acc(q.f)));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("assertion.false"), "{stderr}");
        assert!(
            !stderr.contains("[assert.failed:assertion.false]"),
            "{stderr}"
        );
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn predicate_statement_argument_failure_precedes_permission_and_tail() {
    for operation in ["fold", "unfold"] {
        let source = format!(
            r#"field f: Int
predicate P(a: Ref, d: Ref) {{ acc(a.f) }}
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref) requires x != y {{
 {operation} acc(P((asserting (b ? acc(x.f) : acc(y.f)) in z), x), (asserting (c ? false : false) in write));
 assert false;
}}
"#
        );
        for workers in ["1", "2"] {
            let output = run(&source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("insufficient.permission"), "{stderr}");
            assert!(!stderr.contains("assertion.false"), "{stderr}");
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn predicate_statement_nonpositive_permission_precedes_body_and_tail() {
    for operation in ["fold", "unfold"] {
        let source = format!(
            r#"field f: Int
predicate P(a: Ref, d: Ref) {{ acc(a.f) }}
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref) requires acc(x.f) && acc(y.f) {{
 {operation} acc(P((asserting (b ? acc(x.f) : acc(y.f)) in z), x), (asserting (c ? acc(x.f) : acc(y.f)) in -write));
 assert false;
}}
"#
        );
        for workers in ["1", "2"] {
            let output = run(&source, workers);
            assert!(!output.status.success());
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(stderr.contains("permission.not.positive"), "{stderr}");
            assert!(!stderr.contains("assertion.false"), "{stderr}");
        }
    }
}

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn production_wand_argument_failure_skips_wand_and_tail() {
    let source = r#"field f: Int
method bad(a: Ref, b: Ref, c: Bool) requires a != b {
 inhale (acc(old(asserting (c ? acc(a.f) : acc(b.f)) in a).f) --* acc(a.f));
 assert false;
}
"#;
    for workers in ["1", "2"] {
        let output = run(source, workers);
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("insufficient.permission"), "{stderr}");
        assert!(!stderr.contains("assertion.false"), "{stderr}");
    }
}
