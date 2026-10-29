//! Ferrum function permission warning regression; see [PLAN.md](../PLAN.md).
use std::{fs, process::Command};

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn function_permission_warnings_follow_source_flag_and_spans() {
    let path = std::env::temp_dir().join(format!("ferrum-function-permission-{}.vpr", std::process::id()));
    let source = "field f: Int\nfunction read(r: Ref): Int\n  requires acc(r.f, write)\n  requires acc(r.f, wildcard)\n  requires acc(r.f, none)\n  requires forall x: Ref :: x == r ==> acc(x.f, write)\n  requires let x == (r) in acc(x.f, write)\nmethod m(r: Ref) requires acc(r.f, write) {}\n";
    fs::write(&path, source).unwrap();
    let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
    for enabled in [false, true] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_ferrum"));
        cmd.args(["--z3Exe", &z3]);
        if enabled { cmd.arg("--respectFunctionPrePermAmounts"); }
        let out = cmd.arg(&path).output().unwrap();
        let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
        assert!(out.status.success(), "{text}");
        assert_eq!(text.matches("Function contains specific permission amount").count(), usize::from(!enabled), "{text}");
        if !enabled { assert!(text.contains("@3.21--3.26"), "{text}"); }
    }
    fs::remove_file(path).unwrap();
}
