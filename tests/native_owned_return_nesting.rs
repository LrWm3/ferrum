//! Ferrum owned return-stack regression assembly described in PLAN.md.
//! Source-order regression for an owned asserting value nested on the right of addition.
use std::sync::atomic::{AtomicUsize, Ordering};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn run(source: &str, workers: &str) -> std::process::Output {
    let path = std::env::temp_dir().join(format!(
        "ferrum-return-order-{}-{}.vpr",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source).unwrap();
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_ferrum"))
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
