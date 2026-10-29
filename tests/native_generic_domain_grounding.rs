//! Ferrum generic-domain grounding regression; see [PLAN.md](../PLAN.md).
use std::{fs, process::Command};

#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn generic_domain_axiom_uses_each_instantiation_and_keeps_false_assertions() {
    let path = std::env::temp_dir().join(format!("ferrum-generic-domain-{}.vpr", std::process::id()));
    let source = r#"domain Option[T] {
  axiom { Option_discr(Option_None()) == 0 }
  function Option_discr(Option[T]): Int
  function Option_None(): Option[T]
  function Option_Some(T): Option[T]
}
method m() {
  assert Option_discr((Option_None(): Option[Bool])) == 0
  assert Option_discr((Option_None(): Option[Ref])) == 0
  assert Option_discr((Option_None(): Option[Perm])) == 1
}
domain Option2[T] {
  axiom { forall o: Option2[T] :: Option2_discr(o) >= 0 && Option2_discr(Option2_None()) == 0 }
  function Option2_discr(Option2[T]): Int
  function Option2_None(): Option2[T]
}
method m2() {
  assert Option2_discr((Option2_None(): Option2[Bool])) == 0
  assert Option2_discr((Option2_None(): Option2[Bool])) == 1
}
"#;
    fs::write(&path, source).unwrap();
    let out = Command::new(env!("CARGO_BIN_EXE_ferrum")).args(["--z3Exe", &std::env::var("FERRUM_TEST_Z3").unwrap(), "--numberOfParallelVerifiers", "1"]).arg(&path).output().unwrap();
    let text = format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    assert_eq!(out.status.code(), Some(1), "{text}");
    assert_eq!(text.matches("[assert.failed:assertion.false]").count(), 2, "{text}");
    assert!(text.contains("Option[Perm]"), "{text}");
    assert!(text.contains("Option2[Bool]"), "{text}");
    assert!(!text.contains("unconstrained type parameter"), "{text}");
    assert!(!text.contains("Option[Ref])): Int) == 0 might not hold"), "{text}");
    assert!(!text.contains("Option[Bool])): Int) == 0 might not hold"), "{text}");
    fs::remove_file(path).unwrap();
}
