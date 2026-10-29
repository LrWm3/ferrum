//! Ferrum exception-path regressions; see [PLAN.md](../PLAN.md).
#![cfg(unix)]
use ferrum::silicon::{
    decider::{
        prover_std_io::{ProverError, ProverSettings, ProverStdIo},
        z3_prover_std_io,
    },
    interfaces::decider::prover::Prover,
    state::terms::{TermFactory, TermOptions},
};
use std::{fs, os::unix::fs::PermissionsExt};

#[test]
fn empty_statistics_response_keeps_source_exception_type_and_message() {
    let path = std::env::temp_dir().join(format!("ferrum-empty-statistics-{}", std::process::id()));
    fs::write(&path, "#!/usr/bin/env python3\nimport sys\nfor line in sys.stdin:\n if '(get-info :all-statistics)' in line:\n  print('', flush=True)\n").unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    let factory = TermFactory::new(TermOptions {
        use_flyweight: false,
        use_old_axiomatization: false,
        mask_heap_mode: false,
    });
    let settings = ProverSettings::new(path.clone(), 1);
    let mut prover = ProverStdIo::new(
        "test".into(),
        settings,
        z3_prover_std_io::profile(),
        factory,
        |_| {},
    );
    prover.start(None).unwrap();
    let error = prover.statistics().unwrap_err();
    assert!(
        matches!(error, ProverError::SourceProtocol { ref prover_id, ref message } if prover_id == "test" && message == "Unexpected output of prover while reading statistics: ")
    );
    prover.stop().unwrap();
    fs::remove_file(path).unwrap();
}
