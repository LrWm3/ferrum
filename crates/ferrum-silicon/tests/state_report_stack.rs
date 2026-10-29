//! Ferrum state-reporting verification integration regression described in PLAN.md.

use ferrum_silicon::{
    config::Config,
    decider::z3_prover_std_io,
    logger::{
        records::data::data_record::FullStateRecordFactory, symb_ex_logger::NativeSymbExLogger,
    },
    state::terms::{TermFactory, TermOptions},
    verifier::{native_context::NativeOptions, verification_pool_manager::native_method_worker},
};
use ferrum_silver::{
    frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases},
    plugin::silver_plugin_manager::SilverPluginManager,
    reporter::{
        message::Message,
        reporter::{ReportError, Reporter},
    },
};
use std::{rc::Rc, sync::Arc};

#[cfg(unix)]
#[test]
#[ignore = "requires real Z3, Python 3; set FERRUM_TEST_Z3"]
fn scheduler_renders_real_stalled_verification_with_source_stack_bound() {
    struct RejectState {
        sent: std::sync::mpsc::Sender<()>,
        held: std::path::PathBuf,
        resume: std::path::PathBuf,
    }
    impl Reporter for RejectState {
        fn name(&self) -> &str {
            "reject-state"
        }
        fn report(&self, message: Message) -> Result<(), ReportError> {
            if matches!(message, Message::VerifierState { .. }) {
                assert!(
                    self.held.exists(),
                    "state report arrived before the held verifier query"
                );
                std::fs::write(&self.resume, b"resume").unwrap();
                let _ = self.sent.send(());
                Err(ReportError::Unsupported("state rejected"))
            } else {
                Ok(())
            }
        }
    }
    std::thread::Builder::new()
        .stack_size(128 * 1024 * 1024)
        .spawn(|| {
            let n = 14;
            let vars = (0..n).map(|i| format!("x{i}: Int")).collect::<Vec<_>>();
            let mut clauses = (0..n)
                .map(|i| format!("(0 <= x{i} && x{i} < {})", n - 1))
                .collect::<Vec<_>>();
            for i in 0..n {
                for j in i + 1..n {
                    clauses.push(format!("x{i} != x{j}"));
                }
            }
            let source = format!(
                "method hard({}) {{ assert !({}); }}",
                vars.join(", "),
                clauses.join(" && ")
            );
            let mut phases =
                SilFrontendPhases::new("state.vpr".into(), SilverPluginManager::new(vec![]));
            let parsed = phases.parse(&source).unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            use std::os::unix::fs::PermissionsExt;
            struct ProxyDir(std::path::PathBuf);
            impl Drop for ProxyDir {
                fn drop(&mut self) {
                    let _ = std::fs::remove_dir_all(&self.0);
                }
            }
            let stamp = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let dir = ProxyDir(
                std::env::temp_dir()
                    .join(format!("ferrum-state-proxy-{}-{stamp}", std::process::id())),
            );
            std::fs::create_dir(&dir.0).unwrap();
            let proxy = dir.0.join("z3-proxy");
            let held = dir.0.join("held");
            let resume = dir.0.join("resume");
            let timeout = dir.0.join("timeout");
            let reaped = dir.0.join("reaped");
            // The first check is preamble setup; the third reaches the nested
            // member evaluation. Hold that Z3 query until its state report.
            // A timeout prevents a broken reporter from deadlocking the test.
            let script = format!(
                r#"#!/usr/bin/env python3
import os, pathlib, subprocess, sys, time
child = subprocess.Popen([os.environ['FERRUM_TEST_Z3'], *sys.argv[1:]], stdin=subprocess.PIPE)
held = pathlib.Path({held:?})
resume = pathlib.Path({resume:?})
timeout = pathlib.Path({timeout:?})
reaped = pathlib.Path({reaped:?})
checks = 0
try:
    for line in sys.stdin.buffer:
        if line.lstrip().startswith(b'(check-sat'):
            checks += 1
            if checks == 3:
                held.write_text('held')
                deadline = time.monotonic() + 15
                while not resume.exists() and time.monotonic() < deadline:
                    time.sleep(0.01)
                if not resume.exists():
                    timeout.write_text('timeout')
        child.stdin.write(line)
        child.stdin.flush()
        if line.strip() == b'(exit)':
            break
finally:
    child.stdin.close()
    try:
        child.wait(timeout=5)
    except subprocess.TimeoutExpired:
        child.kill()
        child.wait(timeout=5)
    reaped.write_text('reaped')
"#,
                held = held.to_str().unwrap(),
                resume = resume.to_str().unwrap(),
                timeout = timeout.to_str().unwrap()
            );
            std::fs::write(&proxy, script).unwrap();
            std::fs::set_permissions(&proxy, std::fs::Permissions::from_mode(0o700)).unwrap();
            let z3 = proxy.to_string_lossy().into_owned();
            let config = Config::parse(&[
                "--ignoreFile".into(),
                "--z3Exe".into(),
                z3,
                "--assertTimeout".into(),
                "5000".into(),
                "--checkTimeout".into(),
                "0".into(),
                "state.vpr".into(),
            ])
            .unwrap();
            let factory = TermFactory::new(TermOptions {
                use_flyweight: config.use_flyweight(),
                use_old_axiomatization: config.use_old_axiomatization,
                mask_heap_mode: config.mask_heap_mode,
            });
            let (reports_tx, reports_rx) = std::sync::mpsc::channel();
            let (errors_tx, errors_rx) = std::sync::mpsc::channel();
            let mut logging_config = config.clone();
            logging_config.report_state_after = Some(1);
            let root = Arc::new(
                NativeSymbExLogger::of_config(
                    &logging_config,
                    Arc::new(RejectState {
                        sent: reports_tx,
                        held: held.clone(),
                        resume,
                    }),
                    factory.clone(),
                    |_| {},
                    move |error| {
                        let _ = errors_tx.send(format!("{error:?}"));
                    },
                )
                .unwrap(),
            );
            let prover = z3_prover_std_io::new(
                "state-stack".into(),
                config.prover_settings("state-stack").unwrap(),
                factory.clone(),
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker(
                "state-stack".into(),
                prover,
                identifiers,
                factory,
                NativeOptions::from_config(&config).unwrap(),
                &config,
            );
            worker
                .context
                .set_logging_root(Some(root.clone()), Some(Rc::new(FullStateRecordFactory)));
            worker
                .context
                .set_decider_logging_formatter(Some(|value| value.to_string()));
            worker
                .context
                .start(config.prover_args.as_deref(), &[])
                .unwrap();
            let outcome = worker.context.verify_program(&program, &[]);
            assert!(
                outcome.is_ok(),
                "verification execution failed: {outcome:?}"
            );
            reports_rx
                .recv_timeout(std::time::Duration::from_secs(2))
                .expect("stalled state report");
            assert!(
                errors_rx
                    .recv_timeout(std::time::Duration::from_secs(2))
                    .unwrap()
                    .contains("state rejected")
            );
            assert!(
                !timeout.exists(),
                "held query timed out before a state report"
            );
            // Stop the real solver through the proxy and observe it being reaped
            // before the stdio prover terminates the proxy process.
            worker
                .context
                .base
                .decider
                .prover
                .write_line("(exit)")
                .unwrap();
            let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
            while !reaped.exists() && std::time::Instant::now() < deadline {
                std::thread::sleep(std::time::Duration::from_millis(10));
            }
            assert!(reaped.exists(), "proxy did not reap the real solver");
            worker.context.stop().unwrap();
            root.close().unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}
