//! Ferrum native runner regression checks described in PLAN.md.
//! These checks require a real Z3 process and are run explicitly with FERRUM_TEST_Z3.

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
    let solver =
        std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3 to the Z3 executable");
    let path = std::env::temp_dir().join(format!(
        "ferrum-branch-{}-{}.vpr",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let input = Input(path);
    std::fs::write(&input.0, source).unwrap();
    Command::new(env!("CARGO_BIN_EXE_ferrum"))
        .arg("--z3Exe")
        .arg(solver)
        .args(args)
        .arg(&input.0)
        .output()
        .unwrap()
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
fn final_report_groups_duplicate_branch_failures() {
    let output = run(
        "method test(b: Bool) { if (b) { } else { } assert false; }",
        &["--numberOfErrorsToReport", "0"],
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
