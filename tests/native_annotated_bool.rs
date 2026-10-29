//! Ferrum annotated Boolean overload regression; see [PLAN.md](../PLAN.md).
use std::{fs, process::Command};

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn annotated_boolean_overloads_resolve_without_accepting_invalid_operands() {
    let path = std::env::temp_dir().join(format!("ferrum-annotated-bool-{}.vpr", std::process::id()));
    let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
    let run = |source: &str| {
        fs::write(&path, source).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_ferrum")).args(["--z3Exe", &z3, "--numberOfParallelVerifiers", "1"]).arg(&path).output().unwrap();
        (out.status.code(), format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr)))
    };
    let (status, text) = run("function f(): Int requires @error(\"x\") (true && true) requires @error(\"x\") (true ==> true)\n");
    assert_eq!(status, Some(0), "{text}");
    let (status, text) = run("function f(): Int requires @error(\"x\") (true && 1)\n");
    assert_eq!(status, Some(2), "{text}");
    assert!(text.contains("incompatible type"), "{text}");
    fs::remove_file(path).unwrap();
}
