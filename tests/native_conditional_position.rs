//! Conditional permission rewriting must retain the source access span.
//! Regression for pinned Silicon conditionalizePermissions/silicon_0008.vpr.

use std::process::Command;

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn conditional_postcondition_reports_access_span() {
    let input = std::env::temp_dir().join(format!(
        "ferrum-conditional-position-{}.vpr",
        std::process::id()
    ));
    std::fs::write(
        &input,
        "field f: Int\nmethod deAlias(x: Ref, y: Ref, k: Perm)\n  requires k >= none\n  requires acc(x.f, k) && acc(y.f, k)\n  ensures x == y ==> acc(x.f, 2 * k)\n{}\n",
    )
    .unwrap();
    for workers in ["1", "2"] {
        let output = Command::new(env!("CARGO_BIN_EXE_ferrum"))
            .arg("--z3Exe")
            .arg(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"))
            .args([
                "--conditionalizePermissions",
                "--numberOfParallelVerifiers",
                workers,
                "--parallelizeBranches",
            ])
            .arg(&input)
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(1), "{stderr}");
        assert!(
            stderr.contains("postcondition.violated:insufficient.permission"),
            "{stderr}"
        );
        assert!(stderr.contains("@5.22--5.37"), "{stderr}");
        assert!(!stderr.contains("@5.11--5.37"), "{stderr}");
    }
    std::fs::remove_file(input).unwrap();
}
