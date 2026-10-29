//! Ferrum ADT trigger regression assembly described in PLAN.md.
//! End-to-end source trigger validation for ADT extension expressions.
use std::sync::atomic::{AtomicUsize, Ordering};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn run(source: &str) -> std::process::Output {
    let path = std::env::temp_dir().join(format!(
        "ferrum-adt-trigger-{}-{}.vpr",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, source).unwrap();
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_ferrum"))
        .arg("--z3Exe")
        .arg(std::env::var_os("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"))
        .arg(&path)
        .output()
        .unwrap();
    std::fs::remove_file(path).unwrap();
    output
}
#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn adt_triggers_allow_constructors_and_destructors_but_reject_forbidden_descendants() {
    let valid = run(r#"
        adt A { C(v: Int) }
        domain D {
            function f(a: A): Int
            axiom { forall x: Int :: { f(C(x)) } f(C(x)) == x }
        }
        method m() {
            assert f(C(2)) == 2;
            assert forall a: A :: { f(C(a.v)) } f(C(a.v)) == a.v;
        }
    "#);
    assert!(
        valid.status.success(),
        "{}",
        String::from_utf8_lossy(&valid.stderr)
    );
    for source in [
        r#"
        adt A { C(v: Int) }
        domain D { function f(a: A): Int
            axiom { forall x: Int :: { f(C(x + 1)) } f(C(x + 1)) == x }
        }
    "#,
        r#"
        adt A { C(v: Int) }
        domain D { function g(b: Bool): Int }
        method m() { assert forall a: A :: { g(a.isC) } g(a.isC) == 1; }
    "#,
    ] {
        let output = run(source);
        assert!(
            !output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("not a valid Trigger"),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
