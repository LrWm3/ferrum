//! Ferrum source logging event regression; see [PLAN.md](../PLAN.md).
use std::{fs, process::Command};

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn predicate_fold_reports_missing_snapshot_domain_only_at_debug() {
    let path = std::env::temp_dir().join(format!("ferrum-domain-event-{}.vpr", std::process::id()));
    fs::write(&path, "field f: Int\npredicate p(r: Ref) { acc(r.f) && (forall x: Ref :: {x.f} x == r ==> x.f >= 0) }\nmethod m(r: Ref) requires acc(r.f) && r.f >= 0 { fold p(r) }\n").unwrap();
    let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
    for (level, expected) in [("DEBUG", 1), ("INFO", 0)] {
        let output = Command::new(env!("CARGO_BIN_EXE_ferrum"))
            .args([
                "--z3Exe",
                &z3,
                "--logLevel",
                level,
                "--numberOfParallelVerifiers",
                "1",
            ])
            .arg(&path)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(
            stdout
                .matches("Axiomatisation of an SM domain missing!")
                .count(),
            expected,
            "{stdout}"
        );
    }
    fs::remove_file(path).unwrap();
}
