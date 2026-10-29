//! Ferrum debugger runtime assembly described in PLAN.md.
//! Native owner-thread services for the pinned Silicon debugger protocol.
//! Source: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/SiliconDebugger.scala
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::{
    debug_exp::{DebugAxiom, DebugExp},
    native_failure::NativeDebugVerifierSnapshot,
    silicon_debugger::{DebuggerServices, EvaluatedAssumption, ProofObligation},
};
use crate::{
    config::Config,
    decider::{decider::DefaultDecider, prover_std_io::ProverStdIo},
    interfaces::{
        decider::prover::{Prover, ProverLike, TextEmitter},
        verification::VerificationResult,
    },
    state::terms::{Term, TermFactory},
    verifier::{
        base_verifier::BaseVerifier,
        native_context::{NativeContext, NativeOptions, NativeState},
    },
};
use ferrum_silver::{
    ast::expression::Exp,
    verifier::verification_error::{ErrorReason, PartialVerificationError, VerificationErrorKind},
};
use std::{
    cell::RefCell,
    collections::HashSet,
    rc::{Rc, Weak},
};

/// Every cloned handle shares a single owner-thread runtime. No live prover is
/// stored in a failure context or transferred to another thread.
#[derive(Clone)]
pub struct NativeReplayVerifier {
    pub snapshot: NativeDebugVerifierSnapshot,
    runtime: Rc<RefCell<Option<ReplayRuntime>>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        config::JoinMode,
        debugger::silicon_debugger::SiliconDebugger,
        state::{
            identifiers::Identifier,
            terms::{Sort, TermOptions},
        },
    };
    use ferrum_silver::ast::{ast::Metadata, expression::ExpKind, program::Program};
    use std::sync::{Arc, Mutex};

    #[test]
    #[ignore = "requires real Z3; set FERRUM_TEST_Z3"]
    fn replay_proves_removes_assumptions_and_closes_shared_worker() {
        let z3 = std::env::var("FERRUM_TEST_Z3").expect("set FERRUM_TEST_Z3");
        let config = Config::parse(&[
            "--ignoreFile".into(),
            "--z3Exe".into(),
            z3,
            "test.vpr".into(),
        ])
        .unwrap();
        let options = NativeOptions::from_config(&config).unwrap();
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let state = NativeState::new(
            program,
            Default::default(),
            Default::default(),
            JoinMode::Off,
            &factory,
            true,
            false,
        );
        let x = factory.var(Identifier::new("replay_x"), Sort::Int, false);
        let initial = factory.greater(x.clone(), factory.int_literal(0));
        let goal = factory.greater(x, factory.int_literal(1));
        let exp = Exp::new(ExpKind::FalseLit, Metadata::default());
        let debug =
            DebugExp::group("initial assumption".into(), Default::default()).with_term(initial);
        let obligation = ProofObligation {
            state,
            verifier: NativeReplayVerifier::captured(NativeDebugVerifierSnapshot {
                worker_id: "captured".into(),
                prover_name: "Z3".into(),
                macro_declarations: vec![],
                function_declarations: vec![],
                debug_variable_types: Default::default(),
            }),
            prover_emits: vec![
                "(set-option :print-success true)".into(),
                "(declare-const replay_x Int)".into(),
            ],
            preamble_assumptions: vec![],
            branch_conditions: vec![],
            branch_condition_exps: vec![],
            assumptions: [debug].into_iter().collect(),
            assertion: goal.clone(),
            assertion_exp: DebugExp::group("goal".into(), Default::default())
                .with_term(goal.clone()),
            timeout: None,
            print_config: Arc::new(Mutex::new(Default::default())),
            original_error_reason: ErrorReason::AssertionFalse(exp),
        };
        let mut services = NativeDebuggerServices::new(
            config,
            options,
            factory.clone(),
            |_: &str| Err("unused parser".into()),
            |_: &mut NativeContext, state: &NativeState| Ok(state.clone()),
        );
        let mut debugger = SiliconDebugger::default();
        let mut live = debugger
            .initialize(&factory, &mut services, &obligation, "Z3", None)
            .unwrap();
        assert!(!debugger.prove(&mut services, &mut live).unwrap());
        services
            .debugger_assume(&mut live.verifier, &[goal], None)
            .unwrap();
        assert!(debugger.prove(&mut services, &mut live).unwrap());
        let mut removed = debugger
            .remove(&factory, &mut services, &live, &[])
            .unwrap();
        assert!(
            !debugger.prove(&mut services, &mut removed).unwrap(),
            "replacement must replay only recorded assumptions"
        );
        assert!(
            debugger.prove(&mut services, &mut live).unwrap(),
            "replacement must not mutate earlier worker"
        );
        let clone = removed.verifier.clone();
        removed.verifier.close().unwrap();
        assert!(clone.with_runtime(|_| Ok(())).is_err());
        live.verifier.close().unwrap();
    }
}

struct ReplayRuntime {
    context: NativeContext,
    assumed: HashSet<Term>,
    stopped: bool,
    cleanup_errors: Rc<RefCell<Vec<String>>>,
}
impl Drop for ReplayRuntime {
    fn drop(&mut self) {
        // Explicit close reports errors; this guard also handles partial
        // initialization, command errors, EOF and replacement of an obligation.
        if !self.stopped {
            self.stopped = true;
            if let Err(error) = self.context.stop() {
                self.cleanup_errors.borrow_mut().push(display(error));
            }
        }
    }
}
impl NativeReplayVerifier {
    pub fn captured(snapshot: NativeDebugVerifierSnapshot) -> Self {
        Self {
            snapshot,
            runtime: Rc::new(RefCell::new(None)),
        }
    }
    pub fn close(&mut self) -> Result<(), String> {
        let runtime = self.runtime.borrow_mut().take();
        if let Some(mut runtime) = runtime {
            runtime.stopped = true;
            runtime.context.stop().map_err(display)?;
        }
        Ok(())
    }
    fn with_runtime<T>(
        &self,
        f: impl FnOnce(&mut ReplayRuntime) -> Result<T, String>,
    ) -> Result<T, String> {
        let mut runtime = self
            .runtime
            .try_borrow_mut()
            .map_err(|_| "debugger worker is already in use".to_owned())?;
        f(runtime
            .as_mut()
            .ok_or("debugger prover has not been initialized")?)
    }
}

pub type NativeProofObligation = ProofObligation<NativeState, NativeReplayVerifier, ErrorReason>;

/// A command translation failure may include the source phase message emitted
/// before the command loop's retry diagnostic.
#[derive(Debug)]
pub struct NativeInputError {
    pub message: String,
    pub prelude: Option<String>,
}
impl From<String> for NativeInputError {
    fn from(message: String) -> Self {
        Self {
            message,
            prelude: None,
        }
    }
}
impl From<&str> for NativeInputError {
    fn from(message: &str) -> Self {
        message.to_owned().into()
    }
}

/// The parser adapter owns the retained source program and captured scope.
/// Runtime restoration installs the captured function/predicate registries;
/// both are explicit dependencies, so replay cannot silently use empty state.
pub struct NativeDebuggerServices<T, R> {
    config: Config,
    options: NativeOptions,
    factory: TermFactory,
    translate: T,
    restore: R,
    workers: Vec<Weak<RefCell<Option<ReplayRuntime>>>>,
    cleanup_errors: Rc<RefCell<Vec<String>>>,
    evaluation_failure: Option<String>,
    input_prelude: RefCell<Option<String>>,
}
impl<T, R> NativeDebuggerServices<T, R> {
    pub fn new(
        config: Config,
        options: NativeOptions,
        factory: TermFactory,
        translate: T,
        restore: R,
    ) -> Self {
        Self {
            config,
            options,
            factory,
            translate,
            restore,
            workers: vec![],
            cleanup_errors: Rc::new(RefCell::new(vec![])),
            evaluation_failure: None,
            input_prelude: RefCell::new(None),
        }
    }
    /// Close all owner-thread workers, including handles retained by reset, and
    /// report cleanup failures from discarded workers as well as live workers.
    pub fn close(&mut self) -> Result<(), String> {
        for worker in self.workers.drain(..).filter_map(|weak| weak.upgrade()) {
            drop(worker.borrow_mut().take());
        }
        let errors = std::mem::take(&mut *self.cleanup_errors.borrow_mut());
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors.join("; "))
        }
    }
}
impl<T, R> Drop for NativeDebuggerServices<T, R> {
    fn drop(&mut self) {
        let _ = self.close();
    }
}
fn display(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

impl<T, R> DebuggerServices<NativeState, NativeReplayVerifier> for NativeDebuggerServices<T, R>
where
    T: FnMut(&str) -> Result<Exp, NativeInputError>,
    R: FnMut(&mut NativeContext, &NativeState) -> Result<NativeState, String>,
{
    type Error = String;
    fn error_message(&self, error: &String) -> String {
        error.clone()
    }
    fn error_prelude(&self, _: &String) -> Option<String> {
        self.input_prelude.borrow_mut().take()
    }
    fn evaluation_failure_message(&self) -> Option<String> {
        self.evaluation_failure.clone()
    }
    fn solver_name(&self, verifier: &NativeReplayVerifier) -> String {
        verifier
            .runtime
            .borrow()
            .as_ref()
            .map(|r| r.context.base.decider.prover.name().to_owned())
            .unwrap_or_else(|| verifier.snapshot.prover_name.clone())
    }
    fn fresh_worker(&mut self, old: &NativeReplayVerifier) -> Result<NativeReplayVerifier, String> {
        Ok(NativeReplayVerifier::captured(old.snapshot.clone()))
    }
    fn start_worker(&mut self, _: &mut NativeReplayVerifier) -> Result<(), String> {
        // Native worker components are created with the selected prover below;
        // there is no redundant default solver process to start and replace.
        Ok(())
    }
    fn create_prover(
        &mut self,
        verifier: &mut NativeReplayVerifier,
        solver: &str,
        args: Option<&str>,
    ) -> Result<(), String> {
        let profile = match solver {
            "Z3" => crate::decider::z3_prover_std_io::profile(),
            "cvc5" => crate::decider::cvc5_prover_std_io::profile(),
            _ => return Err(format!("Unsupported debugger solver {solver}")),
        };
        verifier.close()?;
        let mut config = self.config.clone();
        config.prover = solver.into();
        config.enable_debugging = true;
        let id = verifier.snapshot.worker_id.clone();
        let settings = config.prover_settings(&id).map_err(display)?;
        let prover = ProverStdIo::new(id.clone(), settings, profile, self.factory.clone(), |_| {});
        let identifiers = prover.identifier_factory();
        let decider = DefaultDecider::new(
            prover,
            true,
            config.assert_timeout,
            Some(config.check_timeout),
            Some(config.push_timeout),
        );
        let base = BaseVerifier::new_with_identifiers(
            id,
            decider,
            self.factory.clone(),
            false,
            config.state_consolidation_mode,
            identifiers,
        );
        let mut context = NativeContext::new(base, self.factory.clone(), self.options.clone());
        // Starting only the base avoids duplicating the captured preamble: the
        // generic debugger subsequently emits it in the recorded order.
        context.base.start(args).map_err(display)?;
        let mut runtime = ReplayRuntime {
            context,
            assumed: HashSet::new(),
            stopped: false,
            cleanup_errors: self.cleanup_errors.clone(),
        };
        runtime.context.base.decider.debug_variable_types =
            verifier.snapshot.debug_variable_types.clone();
        runtime.context.base.decider.fresh_functions = verifier
            .snapshot
            .function_declarations
            .iter()
            .cloned()
            .collect();
        runtime.context.base.decider.fresh_macros = verifier.snapshot.macro_declarations.clone();
        // Raw SMT replay still needs converter metadata for macro applications.
        // Register it locally without emitting duplicate declarations.
        for declaration in &verifier.snapshot.macro_declarations {
            runtime
                .context
                .base
                .decider
                .prover
                .converter
                .convert_declaration(declaration)
                .map_err(display)?;
        }
        *verifier.runtime.borrow_mut() = Some(runtime);
        self.workers.push(Rc::downgrade(&verifier.runtime));
        Ok(())
    }
    fn prepare_state(
        &mut self,
        state: &NativeState,
        verifier: &mut NativeReplayVerifier,
    ) -> Result<NativeState, String> {
        verifier.with_runtime(|r| (self.restore)(&mut r.context, state))
    }
    fn emit(
        &mut self,
        verifier: &mut NativeReplayVerifier,
        commands: &[String],
    ) -> Result<(), String> {
        verifier.with_runtime(|r| {
            r.context
                .base
                .decider
                .prover
                .emit_all(commands)
                .map_err(display)
        })
    }
    fn assume_axioms(
        &mut self,
        verifier: &mut NativeReplayVerifier,
        axiom: &DebugAxiom,
    ) -> Result<(), String> {
        verifier.with_runtime(|r| {
            r.context
                .base
                .decider
                .prover
                .assume_axioms(&axiom.terms, &axiom.description)
                .map_err(display)
        })
    }
    fn debugger_assume(
        &mut self,
        verifier: &mut NativeReplayVerifier,
        terms: &[Term],
        _: Option<&DebugExp>,
    ) -> Result<(), String> {
        verifier.with_runtime(|runtime| {
            for term in terms {
                if !runtime.assumed.contains(term) {
                    runtime
                        .context
                        .base
                        .decider
                        .prover
                        .assume(term)
                        .map_err(display)?;
                    runtime.assumed.insert(term.clone());
                }
            }
            Ok(())
        })
    }
    fn translate_boolean(&mut self, input: &str) -> Result<Exp, String> {
        *self.input_prelude.borrow_mut() = None;
        (self.translate)(input).map_err(|error| {
            *self.input_prelude.borrow_mut() = error.prelude;
            error.message
        })
    }
    fn evaluate_assumption(
        &mut self,
        state: &NativeState,
        expression: &Exp,
        verifier: &NativeReplayVerifier,
    ) -> Result<Option<EvaluatedAssumption<NativeState, NativeReplayVerifier>>, String> {
        self.evaluation_failure = None;
        verifier.with_runtime(|runtime| {
            let mark = runtime.context.base.decider.mark();
            let partial = PartialVerificationError::for_kind(VerificationErrorKind::ContractNotWellformed(expression.clone()));
            let mut evaluated = None;
            let outcome = crate::rules::evaluator::evaluate(&mut runtime.context, state.clone(), expression, &partial, &mut |context, state, term, rewritten| {
                let assumptions = context.base.decider.pcs.after(mark).map_err(|e| crate::rules::evaluator::EvaluationError::Context(crate::verifier::native_context::NativeError::Diagnostic(display(e))))?.assumption_exps();
                evaluated = Some((state, term, rewritten, assumptions));
                Ok(VerificationResult::success())
            }).map_err(display)?;
            if outcome.is_fatal() {
                self.evaluation_failure = Some(outcome.with_kind(|kind| {
                    match kind {
                        crate::interfaces::verification::ResultKind::Failure(error) => error.message_with_contexts(&|node| {
                            ferrum_silver::ast::pretty::pretty_printer::pretty_node(node).map_err(|_| ferrum_silver::verifier::verification_result::DiagnosticError::Unsupported("debugger evaluation error rendering"))
                        }).map_err(display),
                        _ => unreachable!("fatal result has a failure"),
                    }
                })?);
                return Ok(None);
            }
            if outcome.with_kind(|kind| matches!(kind, crate::interfaces::verification::ResultKind::Unreachable)) {
                self.evaluation_failure = Some("Unreachable".into());
                return Ok(None);
            }
            let Some((state, term, rewritten, introduced_assumptions)) = evaluated else { return Ok(None); };
            let expression = rewritten.ok_or("debugger evaluation did not retain a rewritten expression")?;
            Ok(Some(EvaluatedAssumption { state, verifier: verifier.clone(), term, expression, introduced_assumptions }))
        })
    }
    fn assert_term(
        &mut self,
        verifier: &mut NativeReplayVerifier,
        term: &Term,
        timeout: Option<i32>,
    ) -> Result<bool, String> {
        verifier.with_runtime(|r| {
            r.context
                .base
                .decider
                .prover
                .assert_goal(term, timeout)
                .map_err(display)
        })
    }
    fn make_debug_expression(
        &mut self,
        original: &Exp,
        evaluated: &Exp,
    ) -> Result<DebugExp, String> {
        DebugExp::create(
            None,
            Some(original.clone()),
            Some(evaluated.clone()),
            None,
            false,
            Default::default(),
            false,
            &|e| {
                ferrum_silver::ast::utility::simplifier::simplify(e, true, &|_| {
                    Ok::<_, std::convert::Infallible>(true)
                })
            },
        )
        .map_err(display)
    }
}
