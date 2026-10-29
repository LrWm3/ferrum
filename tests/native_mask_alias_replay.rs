//! Ferrum assembly regression described in PLAN.md for replaying shared mask aliases.
#[test]
#[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
fn parallel_mask_aliases_replay_across_workers() {
    let path = std::env::temp_dir().join(format!("ferrum-mask-alias-replay-{}.vpr", std::process::id()));
    std::fs::write(&path, r#"field f: Int
function get(r: Ref): Ref { r }
function foo(r: Ref, n: Int): Bool
  requires (true ? acc(r.f) : acc(get(r).f))
{ forall i: Int :: {foo(r, i)} foo(r, i) == foo(r, i) }
method test(r: Ref, b: Bool) requires acc(r.f) {
  if (b) { assert forall i: Int :: { foo(r, i) } foo(r, i) == foo(r, i) }
  else { assert forall i: Int :: { foo(r, i) } foo(r, i) == foo(r, i) }
}
"#).unwrap();
    for workers in ["1", "2"] {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_ferrum"))
            .args(["--z3Exe", &std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3"), "--logLevel", "ERROR", "--maskHeapMode", "--parallelizeBranches", "--numberOfParallelVerifiers", workers])
            .arg(&path).output().unwrap();
        assert!(output.status.success(), "workers={workers}: {}", String::from_utf8_lossy(&output.stderr));
    }
    std::fs::remove_file(path).unwrap();
}
