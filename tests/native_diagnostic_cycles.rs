//! Ferrum source diagnostic ordering regression; see [PLAN.md](../PLAN.md).
use std::{fs, process::Command};

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn cycle_diagnostic_members_follow_rooted_source_probe_order() {
    let dir = std::env::temp_dir().join(format!("ferrum-cycle-order-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
    for (source, expected) in [
        (
            "function a(): Bool requires b()\nfunction b(): Bool requires c()\nfunction c(): Bool requires a()\n",
            [
                "function(s) a, b, c",
                "function(s) b, c, a",
                "function(s) c, a, b",
            ],
        ),
        (
            "function a(): Bool requires b() && c()\nfunction b(): Bool requires a()\nfunction c(): Bool requires a()\n",
            [
                "function(s) a, c, b",
                "function(s) b, a, c",
                "function(s) c, a, b",
            ],
        ),
    ] {
        let file = dir.join("cycle.vpr");
        fs::write(&file, source).unwrap();
        let out = Command::new(env!("CARGO_BIN_EXE_ferrum"))
            .args(["--z3Exe", &z3])
            .arg(&file)
            .output()
            .unwrap();
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(!out.status.success());
        for item in expected {
            assert!(text.contains(item), "{text}");
        }
    }
    fs::remove_dir_all(dir).unwrap();
}
