//! Ferrum debugger runtime assembly described in PLAN.md.
//! Native stream-driven failure selection and debugger sessions.
//! Source: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/SiliconDebugger.scala
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{
    debug_typechecker::DebugSourceScope,
    native_debugger::{
        NativeDebuggerServices, NativeInputError, NativeProofObligation, NativeReplayVerifier,
    },
    native_failure::NativeDebugFailureContext,
    native_presentation::NativeDebuggerPresentation,
    silicon_debugger::{DebuggerPresentation, SiliconDebugger},
};
use crate::{
    config::Config,
    state::terms::TermFactory,
    supporters::predicate_verification_unit::PredicateData,
    verifier::native_context::{NativeFunctionData, NativeOptions},
};
use ferrum_silver::verifier::verification_result::{
    AbstractError, DiagnosticError, VerificationDiagnostic,
};
use std::{
    any::Any,
    io::{BufRead, Write},
};

type CapturedFailure = NativeDebugFailureContext<PredicateData, NativeFunctionData>;

fn message(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

/// The caller owns these streams and invokes the debugger on its verifier
/// thread. Failure contexts contain detached data, never a live solver.
pub fn run_failures<R: BufRead, W: Write>(
    config: &Config,
    options: NativeOptions,
    factory: TermFactory,
    errors: &[AbstractError],
    input: &mut R,
    output: &mut W,
) -> Result<(), String> {
    if !config.enable_debugging {
        writeln!(output, "Debugging mode is disabled").map_err(message)?;
        return Ok(());
    }
    let failures: Vec<&dyn VerificationDiagnostic> = errors
        .iter()
        .filter_map(|e| match e {
            AbstractError::Verification(e) => Some(e.as_ref()),
            _ => None,
        })
        .collect();
    if failures.is_empty() {
        writeln!(output, "No failures found. Debugging mode terminated.").map_err(message)?;
        return Ok(());
    }
    loop {
        for (index, failure) in failures.iter().enumerate() {
            let reason = failure.reason().map_err(message)?;
            let readable = reason
                .readable_message(&|node| {
                    ferrum_silver::ast::pretty::pretty_printer::pretty_node(node)
                        .map_err(|_| DiagnosticError::Unsupported("debugger reason rendering"))
                })
                .map_err(message)?;
            writeln!(
                output,
                "[{index}]: {readable} ({})\n",
                reason.position().map_err(message)?
            )
            .map_err(message)?;
        }
        let index = if failures.len() == 1 {
            Some(0)
        } else {
            writeln!(
                output,
                "Which verification result do you want to debug next [0 - {}] (or q to quit):",
                failures.len() - 1
            )
            .map_err(message)?;
            output.flush().map_err(message)?;
            let mut line = String::new();
            if input.read_line(&mut line).map_err(message)? == 0 {
                return Ok(());
            }
            let line = line.trim_end_matches(['\r', '\n']);
            if line.eq_ignore_ascii_case("q") || line.eq_ignore_ascii_case("quit") {
                return Ok(());
            }
            line.parse::<usize>().ok().filter(|i| *i < failures.len())
        };
        if let Some(index) = index {
            writeln!(output, "\nVerification result {index}:").map_err(message)?;
            let contexts = failures[index].failure_contexts().map_err(message)?;
            let captured = contexts.iter().find_map(|context| {
                (context.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>()
            });
            if let Some(captured) = captured {
                run_obligation(
                    config,
                    options.clone(),
                    factory.clone(),
                    captured,
                    input,
                    output,
                )?;
            } else {
                writeln!(output, "Debugging results are not available. No failure context found.\nDebug mode for this obligation are not available").map_err(message)?;
            }
        } else {
            writeln!(output, "Debug mode for this obligation are not available")
                .map_err(message)?;
        }
        if failures.len() == 1 {
            return Ok(());
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn cancelled_inflight_failure_capture_is_detached_and_replay_is_isolated() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{config::Config, decider::{decider::DefaultDecider, z3_prover_std_io}, state::terms::TermOptions, verifier::{base_verifier::BaseVerifier, native_context::NativeVerifierContext, verification_pool_manager::{native_method_worker, verify_native_parallel_with_reporting, BroadcastingProver, CancellationController, ThreadVerificationPool, DEBUG_TEST_METHOD_EXECUTIONS, DEBUG_TEST_METHOD_SUBMISSIONS}}};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{cell::RefCell, io::Cursor, rc::Rc, sync::{atomic::Ordering, mpsc, Arc, Mutex}};
            for workers in [1, 2] {
                let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
                let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
                let options = NativeOptions::from_config(&config).unwrap();
                config.enable_debugging = true;
                let factory = TermFactory::new(TermOptions { use_flyweight: false, use_old_axiomatization: false, mask_heap_mode: false });
                let cancellation = CancellationController::default();
                let (arrived_tx, arrived_rx) = mpsc::channel();
                let (release_tx, release_rx) = mpsc::channel();
                let release_rx = Arc::new(Mutex::new(release_rx));
                let captures: Arc<Mutex<Vec<Arc<CapturedFailure>>>> = Arc::new(Mutex::new(Vec::new()));
                let handles = Arc::new(Mutex::new(Vec::new()));
                let worker_factory = factory.clone();
                let worker_options = options.clone();
                let worker_config = config.clone();
                let worker_cancel = cancellation.clone();
                let worker_arrived = arrived_tx;
                let worker_release = release_rx;
                let worker_captures = captures.clone();
                let worker_handles = handles.clone();
                let pool = ThreadVerificationPool::start_with_cancellation(workers, 128 * 1024 * 1024, cancellation.clone(), move |id| {
                    let mut settings = z3_prover_std_io::settings(z3.clone().into()); settings.debug = true;
                    let prover = z3_prover_std_io::new(format!("detached-{id}"), settings, worker_factory.clone(), |_| {});
                    let handle = prover.cancellation_handle();
                    worker_handles.lock().unwrap().push(handle.clone());
                    worker_cancel.register(move || handle.cancel().map(|_| ()).map_err(|e| e.to_string()));
                    let ids = prover.identifier_factory();
                    let mut worker = native_method_worker(format!("detached-{id}"), prover, ids, worker_factory.clone(), worker_options.clone(), &worker_config);
                    worker.set_cancellation(worker_cancel.clone());
                    let arrived = worker_arrived.clone(); let release = worker_release.clone(); let captures = worker_captures.clone();
                    worker.context.set_debug_failure_factory(Arc::new(move |state, record, owners| {
                        let captured = Arc::new(CapturedFailure::capture_native(state, record, owners)?);
                        captures.lock().unwrap().push(captured.clone());
                        arrived.send(()).map_err(|e| format!("capture barrier: {e}"))?;
                        release.lock().unwrap().recv().map_err(|e| format!("capture release: {e}"))?;
                        Ok(captured)
                    }));
                    Ok(worker)
                }).unwrap();
                let child_ids: Vec<_> = handles.lock().unwrap().iter().map(|handle| handle.child_id().expect("started worker solver")).collect();
                assert_eq!(child_ids.len(), workers);
                let pool = Rc::new(RefCell::new(pool));
                let mut settings = z3_prover_std_io::settings(std::env::var("FERRUM_TEST_Z3").unwrap().into()); settings.debug = true;
                let prover = z3_prover_std_io::new("main".into(), settings, factory.clone(), |_| {});
                let identifiers = prover.identifier_factory();
                let decider = DefaultDecider::new(BroadcastingProver::new(prover, pool.clone()), false, None, None, None);
                let base = BaseVerifier::new_with_identifiers("main".into(), decider, factory.clone(), false, crate::config::StateConsolidationMode::Default, identifiers);
                let mut context = NativeVerifierContext::new(base, factory.clone(), options.clone());
                context.set_cancellation(cancellation.clone());
                context.start(None, &[]).unwrap();
                let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
                phases.retain_source_program = true;
                let source = if workers == 1 { "method first(x: Int) { assert x > 0; }" } else { "method first(x: Int) { assert x > 0; } method second(x: Int) { assert x > 1; }" };
                let parsed = phases.parse(source).unwrap();
                let analyzed = phases.analyze(parsed).unwrap();
                let program = phases.translate(analyzed).unwrap();
                let submitted = DEBUG_TEST_METHOD_SUBMISSIONS.load(Ordering::SeqCst);
                let executed = DEBUG_TEST_METHOD_EXECUTIONS.load(Ordering::SeqCst);
                let cancel = cancellation.clone();
                let coordinator = std::thread::spawn(move || {
                    let reached = (0..workers).all(|_| arrived_rx.recv_timeout(std::time::Duration::from_secs(30)).is_ok());
                    cancel.cancel();
                    for _ in 0..workers { let _ = release_tx.send(()); }
                    reached
                });
                let outcome = verify_native_parallel_with_reporting(&mut context, &program, &[], None, None, None);
                assert!(coordinator.join().unwrap(), "failure capture did not reach barrier");
                use crate::verifier::verification_pool_manager::{NativeParallelError, ThreadPoolError};
                use crate::verifier::native_context::NativeError;
                use crate::decider::{decider::DeciderError, prover_std_io::ProverError};
                let error = outcome.expect_err("cancelled capture unexpectedly completed");
                match error {
                    NativeParallelError::Worker(ThreadPoolError::Worker(NativeError::Cleanup(detail))) => {
                        assert!(detail.contains("Service(Cancelled)") && detail.contains("SourceProtocol") && detail.contains("BrokenPipe"), "unexpected cleanup provenance: {detail}");
                    }
                    other => panic!("unexpected cancellation result: {other:?}"),
                }
                assert!(DEBUG_TEST_METHOD_SUBMISSIONS.load(Ordering::SeqCst) > submitted, "no member task submitted");
                assert!(DEBUG_TEST_METHOD_EXECUTIONS.load(Ordering::SeqCst) > executed, "no member task executed");
                context.stop().expect("main verifier cleanup"); drop(context);
                let pool = Rc::try_unwrap(pool).ok().unwrap().into_inner();
                match pool.shutdown() {
                    Err(ThreadPoolError::Cleanup { primary, errors }) => {
                        assert!(matches!(*primary, ThreadPoolError::Stopped));
                        assert!(!errors.is_empty());
                        for error in errors {
                            match error {
                                ThreadPoolError::Stopped => (),
                                ThreadPoolError::Worker(NativeError::Decider(DeciderError::Prover(ProverError::Io(error)))) if error.kind() == std::io::ErrorKind::BrokenPipe => (),
                                other => panic!("unexpected pool cleanup: {other:?}"),
                            }
                        }
                    }
                    other => panic!("unexpected pool shutdown result: {other:?}"),
                }
                for handle in handles.lock().unwrap().iter() { assert!(!handle.has_child_handle(), "solver child handle retained after pool shutdown"); }
                #[cfg(target_os = "linux")]
                for pid in child_ids { assert!(!std::path::Path::new(&format!("/proc/{pid}")).exists(), "solver process {pid} was not reaped"); }
                let captured = captures.lock().unwrap();
                assert_eq!(captured.len(), workers, "capture collector leaked or lost a job");
                let worker_ids = captured.iter().map(|failure| failure.obligation.verifier.worker_id.clone()).collect::<std::collections::HashSet<_>>();
                assert_eq!(worker_ids.len(), workers, "captured failures did not execute on distinct workers");
                assert!(worker_ids.iter().all(|id| id.starts_with("detached-")));
                let mut first = Vec::new();
                run_obligation(&config, options.clone(), factory.clone(), &captured[0], &mut Cursor::new(b"af\nfalse\np\nq\n"), &mut first).unwrap();
                assert!(String::from_utf8(first).unwrap().contains("PASS: Proving obligation was successful."));
                let mut second = Vec::new();
                run_obligation(&config, options, factory, &captured[0], &mut Cursor::new(b"p\nq\n"), &mut second).unwrap();
                assert!(String::from_utf8(second).unwrap().contains("FAIL: Proving obligation failed."), "detached sessions shared assumptions");
            }
        }).unwrap().join().unwrap();
    }
    use super::*;
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_function_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("function f(x: Int): Int { x } method m(x: Int) requires x > 0 { assert f(x) > 1; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            let mut output = Vec::new();
            let mut input = Cursor::new(b"af\nx +\naf\nmissing > 0\nt\n1000\np\naf\nf(x) > 1\np\nr\np\ns\nZ3\n\np\nq\n");
            run_obligation(&config, options.clone(), factory.clone(), captured, &mut input, &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert_eq!(transcript.matches("PASS: Proving obligation was successful.").count(), 2, "{transcript}");
            assert_eq!(transcript.matches("FAIL: Proving obligation failed.").count(), 2, "{transcript}");
            assert!(transcript.contains("Assumption was added successfully!"), "{transcript}");
            assert_eq!(transcript.matches("Error while parsing x +:").count(), 1, "{transcript}");
            assert!(transcript.contains("FastMessage(undeclared identifier `missing`,userInput@1.1--1.8,true)"), "{transcript}");
            assert_eq!(transcript.matches("Unexpected error:").count(), 2, "{transcript}");
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "independent replay changed: {transcript}");
            assert!(!transcript.contains("PASS:"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_quantified_negative_production_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(p: Perm) requires p < none { inhale forall x: Ref :: x != null ==> acc(x.f, p); }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_quantified_negative_consumption_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(p: Perm) requires p < none { exhale forall x: Ref :: x != null ==> acc(x.f, p); }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_nonpositive_unfold_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("predicate P() { true } method m() { assert unfolding acc(P(), none) in true; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_quantified_read_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(r: Ref) requires r != null && (forall x: Ref :: x != null && x != r ==> acc(x.f)) { assert r.f == 0; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_map_lookup_failure_session_replays_after_verifier_drop() {
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(|| {
                use crate::{
                    decider::z3_prover_std_io, interfaces::verification::ResultKind,
                    state::terms::TermOptions,
                    verifier::verification_pool_manager::native_method_worker,
                };
                use ferrum_silver::frontend::{
                    frontend::FrontendPhases, sil_frontend::SilFrontendPhases,
                };
                use std::{io::Cursor, sync::Arc};
                let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
                let mut config = Config::parse(&[
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    z3.clone(),
                    "debug.vpr".into(),
                ])
                .unwrap();
                // Exercise capture independently of the CLI.
                let options = NativeOptions::from_config(&config).unwrap();
                config.enable_debugging = true;
                let factory = TermFactory::new(TermOptions {
                    use_flyweight: config.use_flyweight(),
                    use_old_axiomatization: config.use_old_axiomatization,
                    mask_heap_mode: false,
                });
                let mut settings = z3_prover_std_io::settings(z3.into());
                settings.debug = true;
                let prover = z3_prover_std_io::new(
                    "session_capture".into(),
                    settings,
                    factory.clone(),
                    |_| {},
                );
                let identifiers = prover.identifier_factory();
                let mut worker = native_method_worker(
                    "session_capture".into(),
                    prover,
                    identifiers,
                    factory.clone(),
                    options.clone(),
                    &config,
                );
                let mut phases = SilFrontendPhases::new(
                    "debug.vpr".into(),
                    ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                );
                phases.retain_source_program = true;
                let parsed = phases
                    .parse("method m(table: Map[Int, Int]) { assert table[0] == 1; }")
                    .unwrap();
                let analyzed = phases.analyze(parsed).unwrap();
                let program = phases.translate(analyzed).unwrap();
                worker.context.start(None, &[]).unwrap();
                worker
                    .context
                    .set_debug_failure_factory(Arc::new(|state, record, owners| {
                        Ok(Arc::new(CapturedFailure::capture_native(
                            state, record, owners,
                        )?))
                    }));
                let results = worker.context.verify_program(&program, &[]).unwrap();
                worker.context.stop().unwrap();
                drop(worker);
                let failure = results
                    .iter()
                    .find_map(|result| {
                        result.with_kind(|kind| match kind {
                            ResultKind::Failure(error) => error.failure_contexts.first().cloned(),
                            _ => None,
                        })
                    })
                    .expect("captured failure");
                let captured = (failure.as_ref() as &dyn Any)
                    .downcast_ref::<CapturedFailure>()
                    .unwrap();
                assert!(matches!(
                    captured
                        .obligation
                        .assertion_exp
                        .final_exp()
                        .unwrap()
                        .kind(),
                    ferrum_silver::ast::expression::ExpKind::MapContains(..)
                ));
                let mut output = Vec::new();
                run_obligation(
                    &config,
                    options,
                    factory,
                    captured,
                    &mut Cursor::new(b"p\nq\n"),
                    &mut output,
                )
                .unwrap();
                let transcript = String::from_utf8(output).unwrap();
                assert!(
                    transcript.contains("FAIL: Proving obligation failed."),
                    "{transcript}"
                );
                assert!(!transcript.contains("Error while"), "{transcript}");
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_division_failure_session_replays_after_verifier_drop() {
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(|| {
                use crate::{
                    decider::z3_prover_std_io, interfaces::verification::ResultKind,
                    state::terms::TermOptions,
                    verifier::verification_pool_manager::native_method_worker,
                };
                use ferrum_silver::frontend::{
                    frontend::FrontendPhases, sil_frontend::SilFrontendPhases,
                };
                use std::{io::Cursor, sync::Arc};
                let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
                let mut config = Config::parse(&[
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    z3.clone(),
                    "debug.vpr".into(),
                ])
                .unwrap();
                // Exercise capture independently of the CLI.
                let options = NativeOptions::from_config(&config).unwrap();
                config.enable_debugging = true;
                let factory = TermFactory::new(TermOptions {
                    use_flyweight: config.use_flyweight(),
                    use_old_axiomatization: config.use_old_axiomatization,
                    mask_heap_mode: false,
                });
                let mut settings = z3_prover_std_io::settings(z3.into());
                settings.debug = true;
                let prover = z3_prover_std_io::new(
                    "session_capture".into(),
                    settings,
                    factory.clone(),
                    |_| {},
                );
                let identifiers = prover.identifier_factory();
                let mut worker = native_method_worker(
                    "session_capture".into(),
                    prover,
                    identifiers,
                    factory.clone(),
                    options.clone(),
                    &config,
                );
                let mut phases = SilFrontendPhases::new(
                    "debug.vpr".into(),
                    ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                );
                phases.retain_source_program = true;
                let parsed = phases
                    .parse("method m(x: Int) { assert 10 / x > 0; }")
                    .unwrap();
                let analyzed = phases.analyze(parsed).unwrap();
                let program = phases.translate(analyzed).unwrap();
                worker.context.start(None, &[]).unwrap();
                worker
                    .context
                    .set_debug_failure_factory(Arc::new(|state, record, owners| {
                        Ok(Arc::new(CapturedFailure::capture_native(
                            state, record, owners,
                        )?))
                    }));
                let results = worker.context.verify_program(&program, &[]).unwrap();
                worker.context.stop().unwrap();
                drop(worker);
                let failure = results
                    .iter()
                    .find_map(|result| {
                        result.with_kind(|kind| match kind {
                            ResultKind::Failure(error) => error.failure_contexts.first().cloned(),
                            _ => None,
                        })
                    })
                    .expect("captured failure");
                let captured = (failure.as_ref() as &dyn Any)
                    .downcast_ref::<CapturedFailure>()
                    .unwrap();
                assert!(matches!(
                    captured
                        .obligation
                        .assertion_exp
                        .final_exp()
                        .unwrap()
                        .kind(),
                    ferrum_silver::ast::expression::ExpKind::NeCmp(..)
                ));
                let mut output = Vec::new();
                run_obligation(
                    &config,
                    options,
                    factory,
                    captured,
                    &mut Cursor::new(b"p\nq\n"),
                    &mut output,
                )
                .unwrap();
                let transcript = String::from_utf8(output).unwrap();
                assert!(
                    transcript.contains("FAIL: Proving obligation failed."),
                    "{transcript}"
                );
                assert!(!transcript.contains("Error while"), "{transcript}");
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_sequence_bounds_failure_session_replays_after_verifier_drop() {
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(|| {
                use crate::{
                    decider::z3_prover_std_io, interfaces::verification::ResultKind,
                    state::terms::TermOptions,
                    verifier::verification_pool_manager::native_method_worker,
                };
                use ferrum_silver::frontend::{
                    frontend::FrontendPhases, sil_frontend::SilFrontendPhases,
                };
                use std::{io::Cursor, sync::Arc};
                let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
                let mut config = Config::parse(&[
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    z3.clone(),
                    "debug.vpr".into(),
                ])
                .unwrap();
                // Exercise capture independently of the CLI.
                let options = NativeOptions::from_config(&config).unwrap();
                config.enable_debugging = true;
                let factory = TermFactory::new(TermOptions {
                    use_flyweight: config.use_flyweight(),
                    use_old_axiomatization: config.use_old_axiomatization,
                    mask_heap_mode: false,
                });
                let mut settings = z3_prover_std_io::settings(z3.into());
                settings.debug = true;
                let prover = z3_prover_std_io::new(
                    "session_capture".into(),
                    settings,
                    factory.clone(),
                    |_| {},
                );
                let identifiers = prover.identifier_factory();
                let mut worker = native_method_worker(
                    "session_capture".into(),
                    prover,
                    identifiers,
                    factory.clone(),
                    options.clone(),
                    &config,
                );
                let mut phases = SilFrontendPhases::new(
                    "debug.vpr".into(),
                    ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                );
                phases.retain_source_program = true;
                let parsed = phases
                    .parse("method m(s: Seq[Int], i: Int) { assert s[i] == 0; }")
                    .unwrap();
                let analyzed = phases.analyze(parsed).unwrap();
                let program = phases.translate(analyzed).unwrap();
                worker.context.start(None, &[]).unwrap();
                worker
                    .context
                    .set_debug_failure_factory(Arc::new(|state, record, owners| {
                        Ok(Arc::new(CapturedFailure::capture_native(
                            state, record, owners,
                        )?))
                    }));
                let results = worker.context.verify_program(&program, &[]).unwrap();
                worker.context.stop().unwrap();
                drop(worker);
                let failure = results
                    .iter()
                    .find_map(|result| {
                        result.with_kind(|kind| match kind {
                            ResultKind::Failure(error) => error.failure_contexts.first().cloned(),
                            _ => None,
                        })
                    })
                    .expect("captured failure");
                let captured = (failure.as_ref() as &dyn Any)
                    .downcast_ref::<CapturedFailure>()
                    .unwrap();
                assert!(matches!(
                    captured
                        .obligation
                        .assertion_exp
                        .final_exp()
                        .unwrap()
                        .kind(),
                    ferrum_silver::ast::expression::ExpKind::GeCmp(..)
                        | ferrum_silver::ast::expression::ExpKind::LtCmp(..)
                ));
                let mut output = Vec::new();
                run_obligation(
                    &config,
                    options,
                    factory,
                    captured,
                    &mut Cursor::new(b"p\nq\n"),
                    &mut output,
                )
                .unwrap();
                let transcript = String::from_utf8(output).unwrap();
                assert!(
                    transcript.contains("PASS: Proving obligation was successful."),
                    "{transcript}"
                );
                assert!(!transcript.contains("Error while"), "{transcript}");
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_complete_lookup_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "--exhaleMode".into(), "1".into(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(r: Ref, s: Ref) requires acc(r.f, 1/2) && acc(s.f, 1/2) { assert r.f == 0; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            fn has_snapshot(debug: &crate::debugger::debug_exp::DebugExp) -> bool {
                debug.description() == Some("Snapshot") || debug.children().iter().any(has_snapshot)
            }
            assert!(captured.obligation.assumptions.iter().any(has_snapshot), "missing complete lookup snapshot definition");
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_singleton_quantified_production_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(r: Ref) requires r != null && (forall x: Ref :: x != null && x != r ==> acc(x.f)) { inhale acc(r.f); assert false; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            fn has_definition(debug: &crate::debugger::debug_exp::DebugExp) -> bool {
                debug.description() == Some("Definitional axioms for singleton-SM's value") || debug.children().iter().any(has_definition)
            }
            assert!(captured.obligation.assumptions.iter().any(has_definition), "missing singleton snapshot definition");
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_resource_trigger_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(r: Ref) requires r != null && (forall x: Ref :: x != null ==> acc(x.f)) { inhale forall x: Ref :: { x.f } true; exhale acc(r.f); assert false; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            fn has_resource_trigger(debug: &crate::debugger::debug_exp::DebugExp) -> bool {
                debug.description().is_some_and(|description| description.starts_with("Resource trigger(f(")) || debug.children().iter().any(has_resource_trigger)
            }
            assert!(captured.obligation.assumptions.iter().any(has_resource_trigger), "missing resource-trigger debug assumption");
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_assignment_trigger_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(r: Ref) requires r != null && (forall x: Ref :: x != null ==> acc(x.f)) { inhale forall x: Ref :: { x.f } true; r.f := 0; assert r.f == 1; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            fn has_resource_trigger(debug: &crate::debugger::debug_exp::DebugExp) -> bool {
                debug.description().is_some_and(|description| description.starts_with("Resource trigger(f(")) || debug.children().iter().any(has_resource_trigger)
            }
            assert!(captured.obligation.assumptions.iter().any(has_resource_trigger), "missing resource-trigger debug assumption");
            fn has_field_trigger(debug: &crate::debugger::debug_exp::DebugExp) -> bool {
                debug.description().is_some_and(|description| description.starts_with("FieldTrigger(")) || debug.children().iter().any(has_field_trigger)
            }
            assert!(captured.obligation.assumptions.iter().any(has_field_trigger), "missing field-trigger debug assumption");
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_quantified_successful_assignment_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(r: Ref) requires r != null && (forall x: Ref :: x != null ==> acc(x.f)) { r.f := 0; assert r.f == 1; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            fn has_snapshot_definition(debug: &crate::debugger::debug_exp::DebugExp) -> bool {
                debug.description() == Some("Definitional axioms for singleton-FVF's value") || debug.children().iter().any(has_snapshot_definition)
            }
            assert!(captured.obligation.assumptions.iter().any(has_snapshot_definition), "missing assignment snapshot definition");
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_quantified_current_permission_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(r: Ref) requires r != null && (forall x: Ref :: x != null && x != r ==> acc(x.f)) { assert perm(r.f) == write; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            fn has_permission_bound(debug: &crate::debugger::debug_exp::DebugExp) -> bool {
                use ferrum_silver::ast::expression::ExpKind;
                let found = debug.original_exp().is_some_and(|expression| match expression.kind() {
                    ExpKind::PermLeCmp(old, _) => matches!(old.kind(), ExpKind::DebugLabelledOld(current, _) if matches!(current.kind(), ExpKind::CurrentPerm(_))),
                    _ => false,
                });
                found || debug.children().iter().any(has_permission_bound)
            }
            assert!(captured.obligation.assumptions.iter().any(has_permission_bound), "missing quantified current-permission debug bound");
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_new_allocation_session_replays_after_verifier_drop() {
        std::thread::Builder::new()
            .stack_size(128 * 1024 * 1024)
            .spawn(|| {
                use crate::{
                    decider::z3_prover_std_io, interfaces::verification::ResultKind,
                    state::terms::TermOptions,
                    verifier::verification_pool_manager::native_method_worker,
                };
                use ferrum_silver::frontend::{
                    frontend::FrontendPhases, sil_frontend::SilFrontendPhases,
                };
                use std::{io::Cursor, sync::Arc};
                let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
                let mut config = Config::parse(&[
                    "--ignoreFile".into(),
                    "--z3Exe".into(),
                    z3.clone(),
                    "debug.vpr".into(),
                ])
                .unwrap();
                // Exercise capture independently of the CLI.
                let options = NativeOptions::from_config(&config).unwrap();
                config.enable_debugging = true;
                let factory = TermFactory::new(TermOptions {
                    use_flyweight: config.use_flyweight(),
                    use_old_axiomatization: config.use_old_axiomatization,
                    mask_heap_mode: false,
                });
                let mut settings = z3_prover_std_io::settings(z3.into());
                settings.debug = true;
                let prover = z3_prover_std_io::new(
                    "session_capture".into(),
                    settings,
                    factory.clone(),
                    |_| {},
                );
                let identifiers = prover.identifier_factory();
                let mut worker = native_method_worker(
                    "session_capture".into(),
                    prover,
                    identifiers,
                    factory.clone(),
                    options.clone(),
                    &config,
                );
                let mut phases = SilFrontendPhases::new(
                    "debug.vpr".into(),
                    ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]),
                );
                phases.retain_source_program = true;
                let parsed = phases
                    .parse("field f: Int method m() { var r: Ref := new(f); assert false; }")
                    .unwrap();
                let analyzed = phases.analyze(parsed).unwrap();
                let program = phases.translate(analyzed).unwrap();
                worker.context.start(None, &[]).unwrap();
                worker
                    .context
                    .set_debug_failure_factory(Arc::new(|state, record, owners| {
                        Ok(Arc::new(CapturedFailure::capture_native(
                            state, record, owners,
                        )?))
                    }));
                let results = worker.context.verify_program(&program, &[]).unwrap();
                worker.context.stop().unwrap();
                drop(worker);
                let failure = results
                    .iter()
                    .find_map(|result| {
                        result.with_kind(|kind| match kind {
                            ResultKind::Failure(error) => error.failure_contexts.first().cloned(),
                            _ => None,
                        })
                    })
                    .expect("captured failure");
                let captured = (failure.as_ref() as &dyn Any)
                    .downcast_ref::<CapturedFailure>()
                    .unwrap();
                let mut output = Vec::new();
                run_obligation(
                    &config,
                    options,
                    factory,
                    captured,
                    &mut Cursor::new(b"p\nq\n"),
                    &mut output,
                )
                .unwrap();
                let transcript = String::from_utf8(output).unwrap();
                assert!(
                    transcript.contains("FAIL: Proving obligation failed."),
                    "{transcript}"
                );
                assert!(!transcript.contains("Error while"), "{transcript}");
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_more_joins_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "--moreJoins".into(), "2".into(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("method m(b: Bool) { if (b) { inhale true; } else { inhale true; } assert false; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_quantified_assign_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(r: Ref) requires r != null && (forall x: Ref :: x != null && x != r ==> acc(x.f)) { r.f := 0; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_complete_wildcard_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "--exhaleMode".into(), "1".into(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let mut settings = z3_prover_std_io::settings(z3.into()); settings.debug = true;
            let prover = z3_prover_std_io::new("session_capture".into(), settings, factory.clone(), |_| {});
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("field f: Int method m(r: Ref) requires acc(r.f, 1/2) { exhale acc(r.f, wildcard); assert false; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
        }).unwrap().join().unwrap();
    }
    #[cfg(feature = "native-z3")]
    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn captured_linked_z3_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::{native_z3::{LinkedZ3Prover, LinkedProverOptions}, z3_prover_api::ApiTimeoutSettings}, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // This fixture also exercises capture independently of the CLI.
            config.prover_randomize_seeds = true;
            config.prover_config_args.insert("smt.qi.eager_threshold".into(), "10.0".into());
            config.prover_config_args.insert("random_seed".into(), "-1".into());
            config.prover_config_args.insert("timeout".into(), "5000".into());
            config.prover_config_args.insert("smt.string_solver".into(), "seq".into());
            config.prover_config_args.insert("smt.mbqi".into(), "false".into());
            config.prover_config_args.insert("smt.ferrum_unknown_option".into(), "true".into());
            let options = NativeOptions::from_config(&config).unwrap();
            config.enable_debugging = true;
            let factory = TermFactory::new(TermOptions { use_flyweight: config.use_flyweight(), use_old_axiomatization: config.use_old_axiomatization, mask_heap_mode: false });
            let settings = LinkedProverOptions { timeout: ApiTimeoutSettings { default_timeout_ms: 0, use_time_bounds: true, resources_per_millisecond: 1 }, counterexamples: false, report_reason_unknown: false, debug: true, soft_assertions: false, custom_options: config.prover_config_args.iter().map(|(k,v)| (k.clone(),v.clone())).collect(), disable_nonlinear: false };
            let prover = LinkedZ3Prover::new("session_capture", factory.clone(), settings);
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker("session_capture".into(), prover, identifiers, factory.clone(), options.clone(), &config);
            let mut phases = SilFrontendPhases::new("debug.vpr".into(), ferrum_silver::plugin::silver_plugin_manager::SilverPluginManager::new(vec![]));
            phases.retain_source_program = true;
            let parsed = phases.parse("function f(x: Int): Int { x } method m(x: Int) requires x > 0 { assert f(x) > 1; }").unwrap();
            let analyzed = phases.analyze(parsed).unwrap();
            let program = phases.translate(analyzed).unwrap();
            worker.context.start(None, &[]).unwrap();
            let warnings = worker.context.base.decider.prover.take_warnings();
            assert!(warnings.iter().any(|w| w.contains("ferrum_unknown_option")), "{warnings:?}");
            worker.context.set_debug_failure_factory(Arc::new(|state, record, owners| Ok(Arc::new(CapturedFailure::capture_native(state, record, owners)?))));
            let results = worker.context.verify_program(&program, &[]).unwrap();
            worker.context.stop().unwrap();
            drop(worker);
            let failure = results.iter().find_map(|result| result.with_kind(|kind| match kind {
                ResultKind::Failure(error) => error.failure_contexts.first().cloned(), _ => None,
            })).expect("captured failure");
            let captured = (failure.as_ref() as &dyn Any).downcast_ref::<CapturedFailure>().unwrap();
            use crate::interfaces::decider::prover::{DebugReplayEvent, DebugZ3OptionValue};
            let events = captured.obligation.verifier.api_replay_events.as_ref().unwrap();
            assert!(events.iter().any(|e| matches!(e, DebugReplayEvent::Z3Option { name, value: DebugZ3OptionValue::Double(v) } if name == "qi.eager_threshold" && *v == 10.0)));
            let seeds = events.iter().filter_map(|e| match e { DebugReplayEvent::Z3Option { name, value: DebugZ3OptionValue::Unsigned(seed) } if name == "random_seed" => Some(*seed), _ => None }).collect::<Vec<_>>();
            assert_eq!(seeds.len(), 2, "{seeds:?}");
            assert_eq!(seeds[0], u32::MAX);
            assert!(seeds[1] < 10_000);
            assert!(events.iter().any(|e| matches!(e, DebugReplayEvent::Z3Option { name, value: DebugZ3OptionValue::Unsigned(5000) } if name == "timeout")));
            assert!(events.iter().any(|e| matches!(e, DebugReplayEvent::Z3Option { name, value: DebugZ3OptionValue::Boolean(false) } if name == "mbqi")));
            assert!(!events.iter().any(|e| matches!(e, DebugReplayEvent::Z3Option { name, .. } if name == "string_solver")));
            assert!(warnings.iter().any(|w| w.contains("string_solver")), "{warnings:?}");
            assert!(!events.iter().any(|e| matches!(e, DebugReplayEvent::Z3Option { name, .. } if name.contains("ferrum_unknown_option"))));
            let mut nonlinear_disabled = config.clone();
            nonlinear_disabled.disable_nl = true;
            let mut output = Vec::new();
            run_obligation(&nonlinear_disabled, options.clone(), factory.clone(), captured, &mut Cursor::new(b"p\nq\n"), &mut output).unwrap();
            assert!(String::from_utf8(output).unwrap().contains("FAIL: Proving obligation failed."));
            let mut output = Vec::new();
            let mut input = Cursor::new(b"t\n1000\np\naf\nf(x) > 1\np\nr\np\ns\nZ3\n\np\nq\n");
            run_obligation(&config, options.clone(), factory.clone(), captured, &mut input, &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            let proof_results = transcript.lines().filter(|line| line.starts_with("PASS: Proving") || line.starts_with("FAIL: Proving")).collect::<Vec<_>>();
            assert_eq!(proof_results, vec!["FAIL: Proving obligation failed.", "PASS: Proving obligation was successful.", "PASS: Proving obligation was successful.", "FAIL: Proving obligation failed."], "{transcript}");
            assert_eq!(transcript.matches("PASS: Proving obligation was successful.").count(), 2, "{transcript}");
            assert_eq!(transcript.matches("FAIL: Proving obligation failed.").count(), 2, "{transcript}");
            assert!(transcript.contains("Assumption was added successfully!"), "{transcript}");
            assert!(!transcript.contains("Error while"), "{transcript}");
            let mut output = Vec::new();
            run_obligation(&config, options, factory, captured, &mut Cursor::new(b"p\n"), &mut output).unwrap();
            let transcript = String::from_utf8(output).unwrap();
            assert!(transcript.contains("FAIL: Proving obligation failed."), "independent replay changed: {transcript}");
            assert!(!transcript.contains("PASS:"), "{transcript}");
        }).unwrap().join().unwrap();
    }
}

fn run_obligation<R: BufRead, W: Write>(
    config: &Config,
    options: NativeOptions,
    factory: TermFactory,
    captured: &CapturedFailure,
    input: &mut R,
    output: &mut W,
) -> Result<(), String> {
    let saved = &captured.obligation;
    let mut scope = DebugSourceScope::new(&saved.state.program, saved.assertion_exp.final_exp())
        .map_err(message)?;
    if !scope.has_scope() {
        writeln!(output, "Could not determine the scope for typechecking.").map_err(message)?;
    }
    let program = saved.state.program.clone();
    let types = saved
        .verifier
        .debug_variable_types
        .iter()
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect();
    let mut services = NativeDebuggerServices::new(
        config.clone(),
        options,
        factory.clone(),
        move |input: &str| {
            scope
                .translate_boolean(input, &program, &types)
                .map_err(|error| NativeInputError {
                    prelude: error.prelude(input),
                    message: error.to_string(),
                })
        },
        |context: &mut crate::verifier::native_context::NativeContext,
         state: &crate::verifier::native_context::NativeState| {
            captured.prepare_runtime_with_state(context, state)
        },
    );
    let obligation = NativeProofObligation {
        state: saved.state.clone(),
        verifier: NativeReplayVerifier::captured(saved.verifier.clone()),
        prover_emits: saved.prover_emits.clone(),
        preamble_assumptions: saved.preamble_assumptions.clone(),
        branch_conditions: saved.branch_conditions.clone(),
        branch_condition_exps: saved.branch_condition_exps.clone(),
        assumptions: saved.assumptions.clone(),
        assertion: saved.assertion.clone(),
        assertion_exp: saved.assertion_exp.clone(),
        timeout: saved.timeout,
        print_config: saved.print_config.clone(),
        original_error_reason: saved.original_error_reason.clone(),
    };
    let mut presentation = NativeDebuggerPresentation {
        factory: factory.clone(),
    };
    let result = (|| -> Result<(), String> {
        writeln!(
            output,
            "Current obligation:\n{}",
            presentation.obligation(&obligation).map_err(message)?
        )
        .map_err(message)?;
        let mut debugger = SiliconDebugger::default();
        let initialized = debugger
            .initialize_with_output(
                &factory,
                &mut services,
                &obligation,
                "Z3",
                config.prover_args.as_deref(),
                output,
            )
            .map_err(message)?;
        debugger
            .run_obligation(
                &factory,
                &mut services,
                &mut presentation,
                initialized.clone(),
                input,
                output,
            )
            .map_err(message)
    })();
    let cleanup = services.close();
    match (result, cleanup) {
        (Ok(()), Ok(())) => Ok(()),
        (Err(error), Ok(())) | (Ok(()), Err(error)) => Err(error),
        (Err(primary), Err(cleanup)) => Err(format!("{primary}; debugger cleanup: {cleanup}")),
    }
}
