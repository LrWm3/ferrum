//! Ferrum function permission warning regression; see [PLAN.md](../PLAN.md).
use std::{fs, process::Command};

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn function_permission_warnings_follow_source_flag_and_spans() {
    let path = std::env::temp_dir().join(format!(
        "ferrum-function-permission-{}.vpr",
        std::process::id()
    ));
    let source = "field f: Int\nfunction read(r: Ref): Int\n  requires acc(r.f, write)\n  requires acc(r.f, wildcard)\n  requires acc(r.f, none)\n  requires forall x: Ref :: x == r ==> acc(x.f, write)\n  requires let x == (r) in acc(x.f, write)\nmethod m(r: Ref) requires acc(r.f, write) {}\n";
    fs::write(&path, source).unwrap();
    let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
    for enabled in [false, true] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_ferrum"));
        cmd.args(["--z3Exe", &z3]);
        if enabled {
            cmd.arg("--respectFunctionPrePermAmounts");
        }
        let out = cmd.arg(&path).output().unwrap();
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(out.status.success(), "{text}");
        assert_eq!(
            text.matches("Function contains specific permission amount")
                .count(),
            usize::from(!enabled),
            "{text}"
        );
        if !enabled {
            assert!(text.contains("@3.21--3.26"), "{text}");
        }
    }
    for (source, warning) in [
        (
            "field f: Int\nfunction read(r: Ref): Int requires acc(r.f, write) && bad\n",
            true,
        ),
        (
            "function read(r: Ref): Int requires acc(r.missing, write)\n",
            false,
        ),
    ] {
        fs::write(&path, source).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_ferrum"))
            .args(["--z3Exe", &z3])
            .arg(&path)
            .output()
            .unwrap();
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(!out.status.success(), "{text}");
        assert_eq!(
            text.contains("Function contains specific permission amount"),
            warning,
            "{text}"
        );
        if warning {
            assert!(
                text.find("Type checker warning:") < text.find("undeclared identifier"),
                "{text}"
            );
        }
        if warning {
            let config = ferrum::silicon::config::Config::parse(&[
                "--z3Exe".into(),
                z3.clone(),
                path.to_string_lossy().into_owned(),
            ])
            .unwrap();
            let error = ferrum::run_file(config).unwrap_err();
            assert!(
                matches!(error, ferrum::FerrumError::DiagnosticsWithWarnings { ref errors, ref warnings } if !errors.is_empty() && warnings.len() == 1)
            );
        }
    }
    fs::remove_file(path).unwrap();
}
