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
            // Keep the public configuration gate until all failure sites are
            // connected; this fixture exercises the internal assembled path.
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
            // Keep the public configuration gate until all failure sites are
            // connected; this fixture exercises the internal assembled path.
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
            // Keep the public configuration gate until all failure sites are
            // connected; this fixture exercises the internal assembled path.
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
            // Keep the public configuration gate until all failure sites are
            // connected; this fixture exercises the internal assembled path.
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
            // Keep the public configuration gate until all failure sites are
            // connected; this fixture exercises the internal assembled path.
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
                // Keep the public configuration gate until all failure sites are
                // connected; this fixture exercises the internal assembled path.
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
    fn captured_quantified_assign_session_replays_after_verifier_drop() {
        std::thread::Builder::new().stack_size(128 * 1024 * 1024).spawn(|| {
            use crate::{decider::z3_prover_std_io, interfaces::verification::ResultKind, state::terms::TermOptions, verifier::verification_pool_manager::native_method_worker};
            use ferrum_silver::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
            use std::{io::Cursor, sync::Arc};
            let z3 = std::env::var("FERRUM_TEST_Z3").unwrap();
            let mut config = Config::parse(&["--ignoreFile".into(), "--z3Exe".into(), z3.clone(), "debug.vpr".into()]).unwrap();
            // Keep the public configuration gate until all failure sites are
            // connected; this fixture exercises the internal assembled path.
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
            // Keep the public configuration gate until all failure sites are
            // connected; this fixture exercises the internal assembled path.
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
