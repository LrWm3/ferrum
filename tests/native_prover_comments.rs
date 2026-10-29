//! Ferrum prover comment regression assembly described in PLAN.md.
//! Regression for Silicon rule comments in the stdio prover log.
#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn rule_comments_do_not_depend_on_general_logging() {
    let base = std::env::temp_dir().join(format!("ferrum-prover-comments-{}", std::process::id()));
    let input = base.with_extension("vpr");
    std::fs::write(&input, "method m() { assert 1 + 1 == 2; }").unwrap();
    for workers in ["1", "2"] {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_ferrum"))
            .arg("--z3Exe")
            .arg(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"))
            .args(["--numberOfParallelVerifiers", workers, "--proverLogFile"])
            .arg(&base)
            .arg(&input)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let ids: &[&str] = if workers == "1" {
            &["main"]
        } else {
            &["main", "worker_0", "worker_1"]
        };
        let mut text = String::new();
        for id in ids {
            let path = std::path::PathBuf::from(format!("{}-{id}.smt2", base.display()));
            let log = std::fs::read_to_string(&path).unwrap();
            if workers == "2" && *id == "main" {
                assert!(!log.contains("[exec]"), "method executed on main: {log}");
                assert!(
                    !log.contains("[eval] 1 + 1 == 2"),
                    "method evaluation broadcast to main: {log}"
                );
            }
            text.push_str(&log);
            std::fs::remove_file(path).unwrap();
        }
        assert!(text.contains("[exec]"), "{text}");
        assert!(text.contains("[eval] 1 + 1 == 2"), "{text}");
    }
    std::fs::remove_file(input).unwrap();
}
