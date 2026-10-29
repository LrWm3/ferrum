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
