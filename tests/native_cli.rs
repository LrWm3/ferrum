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
fn check(source: &str, expected: i32) {
    let solver =
        std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3 to the Z3 executable");
    let path = std::env::temp_dir().join(format!(
        "ferrum-branch-{}-{}.vpr",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let input = Input(path);
    std::fs::write(&input.0, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_ferrum"))
        .arg("--z3Exe")
        .arg(solver)
        .arg(&input.0)
        .output()
        .unwrap();
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
