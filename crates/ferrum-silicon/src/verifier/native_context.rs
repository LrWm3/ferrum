// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

//! Ferrum assembly described in PLAN.md.
//! Native verifier context connecting source rule algorithms to a real owned prover.
//! Upstream service composition:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/BaseVerifier.scala
//! Status: initial evaluator/decider connections; branches, heap, quantifiers, production,
//! consumption and member verification are not yet connected and return explicit errors.

use crate::rules::producer::{ProductionError, QuantifiedProductionData};
use crate::{
    config::JoinMode,
    decider::decider::DeciderError,
    interfaces::{decider::prover::Prover, verification::VerificationResult},
    rules::evaluator::{
        EvaluationContext, EvaluationError, ForPermCondition, QuantifiedExpressionData,
    },
    state::{
        heap::ListBackedHeap,
        state::State,
        terms::{Term, TermFactory},
    },
    verifier::base_verifier::BaseVerifier,
};
use ferrum_silver::{
    ast::expression::Exp,
    verifier::verification_error::{ErrorReason, PartialVerificationError, VerificationError},
};
use std::{
    marker::PhantomData,
    sync::{Arc, atomic::Ordering},
};

#[derive(Clone, Debug)]
pub struct NativeOptions {
    pub unsafe_wildcard_optimization: bool,
    pub disable_short_circuiting: bool,
    pub error_limit: usize,
    pub respect_function_pre_permission_amounts: bool,
}
#[derive(Debug)]
pub enum NativeError<E> {
    Decider(DeciderError<E>),
    Sort(crate::state::symbol_converter::SymbolConversionError),
    HeapDependency(String),
    Diagnostic(String),
    Evaluation(String),
    ContinuationAbort,
    State(crate::state::state::StateMergeError),
    BranchTraversal(String),
    Resource(std::io::Error),
    StartCleanup {
        primary: Box<NativeError<E>>,
        cleanup: DeciderError<E>,
    },
    Unsupported(&'static str),
}
pub struct NativeVerifierContext<S: Prover, PD, FD> {
    pub base: BaseVerifier<S>,
    pub factory: TermFactory,
    pub options: NativeOptions,
    pub warnings: Vec<String>,
    _state_types: PhantomData<(PD, FD)>,
}
impl<S: Prover, PD, FD> NativeVerifierContext<S, PD, FD> {
    pub fn new(base: BaseVerifier<S>, factory: TermFactory, options: NativeOptions) -> Self {
        Self {
            base,
            factory,
            options,
            warnings: Vec::new(),
            _state_types: PhantomData,
        }
    }
    /// Start the owned solver and install the source static settings and base preamble.
    /// Contributor-specific declarations and axioms must be installed separately after analysis.
    pub fn start(
        &mut self,
        user_args: Option<&str>,
        config_options: &[String],
    ) -> Result<(), NativeError<S::Error>> {
        use crate::interfaces::preamble::PreambleReader;
        self.base.start(user_args).map_err(NativeError::Decider)?;
        let reader = crate::decider::smt_lib2_preamble_reader::SmtLib2PreambleReader::default();
        let resource = self.base.decider.prover.static_preamble().to_string();
        let result = (|| {
            let settings = reader
                .read_preamble(&resource)
                .map_err(NativeError::Resource)?;
            self.base
                .decider
                .prover
                .emit_settings(&settings)
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            if !config_options.is_empty() {
                self.base
                    .decider
                    .prover
                    .emit_settings(config_options)
                    .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            }
            let commands = reader
                .read_preamble("/preamble.smt2")
                .map_err(NativeError::Resource)?;
            self.base
                .decider
                .prover
                .emit_all(&commands)
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            Ok(())
        })();
        match result {
            Ok(()) => Ok(()),
            Err(primary) => match self.base.stop() {
                Ok(()) => Err(primary),
                Err(cleanup) => Err(NativeError::StartCleanup {
                    primary: Box::new(primary),
                    cleanup,
                }),
            },
        }
    }
    pub fn stop(&mut self) -> Result<(), NativeError<S::Error>> {
        self.base.stop().map_err(NativeError::Decider)
    }
    fn assume_term(&mut self, term: &Term) -> Result<(), NativeError<S::Error>> {
        self.base
            .decider
            .assume([(term.clone(), None)], false, false)
            .map_err(NativeError::Decider)
    }
    fn failure(
        &mut self,
        partial: &PartialVerificationError,
        reason: ErrorReason,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        let error = partial
            .due_to(reason)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        self.base.errors_reported.fetch_add(1, Ordering::SeqCst);
        Ok(VerificationResult::failure(
            error,
            self.base.report_further_errors(self.options.error_limit),
        ))
    }
}
#[allow(unused_variables)]
impl<S: Prover, PD, FD> EvaluationContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
{
    type Error = NativeError<S::Error>;
    type PartialError = PartialVerificationError;
    fn factory(&self) -> &TermFactory {
        &self.factory
    }
    fn debugging(&self) -> bool {
        false
    }
    fn verifier_unique_id(&self) -> &str {
        &self.base.unique_id
    }
    fn to_sort(
        &mut self,
        typ: &ferrum_silver::ast::r#type::Type,
    ) -> Result<crate::state::terms::Sort, Self::Error> {
        self.base
            .symbol_converter
            .to_sort(typ)
            .map_err(NativeError::Sort)
    }
    fn disable_short_circuiting(&self) -> bool {
        self.options.disable_short_circuiting
    }
    fn is_short_circuit_implies(&self, expression: &Exp) -> bool {
        false
    }
    fn open_evaluation(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        expression: &Exp,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn close_evaluation(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn eval_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        if state.exhale_ext {
            Err(NativeError::Unsupported("wand evaluation heap"))
        } else {
            Ok(state.h.clone())
        }
    }
    fn record_possible_trigger(
        &mut self,
        state: &mut State<PD, FD, JoinMode>,
        expression: &Exp,
        term: &Term,
    ) -> Result<(), Self::Error> {
        Err(NativeError::Unsupported("record_possible_trigger"))
    }
    fn assert_goal(&mut self, goal: &Term) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check(goal, self.base.decider.assert_timeout)
            .map_err(NativeError::Decider)
    }
    fn report_further_errors(&self) -> bool {
        self.base.report_further_errors(self.options.error_limit)
    }
    fn assume_generated(
        &mut self,
        term: &Term,
        original: Option<&Exp>,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.assume_term(term)
    }
    fn assume_nonzero(
        &mut self,
        term: &Term,
        original: Option<&Exp>,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.assume_term(term)
    }
    fn division_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        partial: &Self::PartialError,
        divisor: &Exp,
        assertion: &Term,
        rewritten_assertion: Option<&Exp>,
    ) -> Result<VerificationResult<VerificationError>, Self::Error> {
        self.failure(partial, ErrorReason::DivisionByZero(divisor.clone()))
    }
    fn sequence_bounds_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        partial: &Self::PartialError,
        sequence: &Exp,
        index: &Exp,
        negative: bool,
        goal: &Term,
        rewritten: Option<&Exp>,
    ) -> Result<VerificationResult<VerificationError>, Self::Error> {
        self.failure(
            partial,
            if negative {
                ErrorReason::SeqIndexNegative {
                    sequence: sequence.clone(),
                    index: index.clone(),
                }
            } else {
                ErrorReason::SeqIndexExceedsLength {
                    sequence: sequence.clone(),
                    index: index.clone(),
                }
            },
        )
    }
    fn map_key_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        partial: &Self::PartialError,
        base: &Exp,
        key: &Exp,
        assertion: &Term,
        rewritten_assertion: Option<&Exp>,
    ) -> Result<VerificationResult<VerificationError>, Self::Error> {
        self.failure(
            partial,
            ErrorReason::MapKeyNotContained {
                map: base.clone(),
                key: key.clone(),
            },
        )
    }
    fn fresh_arp(&mut self) -> Result<(Term, Term, Option<Exp>), Self::Error> {
        {
            let (v, c) = self
                .base
                .decider
                .fresh_arp(&self.factory, "arp", None)
                .map_err(NativeError::Decider)?;
            Ok((v, c, None))
        }
    }
    fn assume_arp_definition(
        &mut self,
        constraint: &Term,
        debug_variable: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.base
            .decider
            .assume([(constraint.clone(), None)], false, true)
            .map_err(NativeError::Decider)
    }
    fn consolidate_old(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Err(NativeError::Unsupported("consolidate_old"))
    }
    fn is_heap_dependent(
        &mut self,
        expression: &Exp,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<bool, Self::Error> {
        ferrum_silver::ast::utility::expressions::is_heap_dependent(expression, program)
            .map_err(|e| NativeError::HeapDependency(format!("{e:?}")))
    }
    fn missing_label_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        partial: &Self::PartialError,
        original: &Exp,
        label: &str,
    ) -> Result<VerificationResult<VerificationError>, Self::Error> {
        self.failure(
            partial,
            ErrorReason::LabelledStateNotReached(original.clone()),
        )
    }
    fn fresh_let_application(
        &mut self,
        typ: &ferrum_silver::ast::r#type::Type,
        variables: &[Term],
    ) -> Result<(Term, crate::state::terms::ApplicationTarget), Self::Error> {
        let sort = self
            .base
            .symbol_converter
            .to_sort(typ)
            .map_err(NativeError::Sort)?;
        let sorts = variables
            .iter()
            .map(|value| value.sort().clone())
            .collect::<Vec<_>>();
        let (target, _) = self
            .base
            .decider
            .fresh(&self.factory, "letvar", &sorts, &sort)
            .map_err(NativeError::Decider)?;
        let term = match &target {
            crate::state::terms::ApplicationTarget::Function(function) => {
                self.factory.app(function.clone(), variables.to_vec())
            }
            crate::state::terms::ApplicationTarget::Variable(variable) if variables.is_empty() => {
                variable.clone()
            }
            _ => return Err(NativeError::Unsupported("fresh let application target")),
        };
        Ok((term, target))
    }
    fn assume_let_definition(
        &mut self,
        equality: &Term,
        variable: &ferrum_silver::ast::expression::LocalVar,
        original: &Exp,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.base
            .decider
            .assume([(equality.clone(), None)], false, true)
            .map_err(NativeError::Decider)
    }
    fn merge_evaluation_states(
        &mut self,
        first: State<PD, FD, JoinMode>,
        second: &State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        first
            .merge_unconditional(second, &mut |message| self.warnings.push(message))
            .map_err(NativeError::State)
    }
    fn branch_join_evaluation(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        from_short_circuit_and: bool,
        yes: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                Term,
                Option<Exp>,
            ) -> Result<
                VerificationResult<VerificationError>,
                EvaluationError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
        no: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                Term,
                Option<Exp>,
            ) -> Result<
                VerificationResult<VerificationError>,
                EvaluationError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
        merge: &mut dyn FnMut(
            &mut Self,
            Vec<(State<PD, FD, JoinMode>, Term, Option<Exp>)>,
        ) -> Result<
            (State<PD, FD, JoinMode>, Term, Option<Exp>),
            EvaluationError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
            Option<Exp>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        use crate::rules::{
            brancher,
            joiner::{self, JoinDataEntry},
        };
        use ferrum_silver::ast::{ast::Metadata, expression::ExpKind};
        if state.retrying || state.exhale_ext {
            return Err(EvaluationError::Context(NativeError::Unsupported(
                "branch consolidation or wand reserve heap",
            )));
        }
        let factory = self.factory.clone();
        self.base
            .decider
            .push_scope()
            .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
        let mark = self.base.decider.pcs.mark();
        let mut joined_state = state.clone();
        joined_state.under_join = true;
        let quantified: Vec<_> = state
            .quantified_variables
            .iter()
            .map(|(v, _)| v.clone())
            .collect();
        let block = (|| {
            let decision = brancher::decide(
                &factory,
                &condition,
                &quantified,
                from_short_circuit_and,
                false,
                |term| {
                    self.base
                        .decider
                        .check(term, self.base.decider.check_timeout)
                },
            )
            .map_err(|e| match e {
                brancher::BranchError::Solver(e) => {
                    EvaluationError::Context(NativeError::Decider(e))
                }
                brancher::BranchError::Traversal(e) => {
                    EvaluationError::Context(NativeError::BranchTraversal(format!("{e:?}")))
                }
            })?;
            let mut entries = Vec::new();
            let mut run = |this: &mut Self,
                           active: bool,
                           positive: bool,
                           action: &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                &mut dyn FnMut(
                    &mut Self,
                    State<PD, FD, JoinMode>,
                    Term,
                    Option<Exp>,
                ) -> Result<
                    VerificationResult<VerificationError>,
                    EvaluationError<Self::Error>,
                >,
            ) -> Result<
                VerificationResult<VerificationError>,
                EvaluationError<Self::Error>,
            >|
             -> Result<
                VerificationResult<VerificationError>,
                EvaluationError<Self::Error>,
            > {
                if !active {
                    return Ok(VerificationResult::unreachable());
                }
                this.base
                    .decider
                    .push_scope()
                    .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
                let branch_term = if positive {
                    condition.clone()
                } else {
                    factory.not(condition.clone())
                };
                let branch_exp = if positive {
                    original.clone()
                } else {
                    Exp::new(ExpKind::Not(original.clone()), Metadata::default())
                };
                let rewritten_exp = if positive {
                    rewritten.cloned()
                } else {
                    rewritten.map(|e| Exp::new(ExpKind::Not(e.clone()), Metadata::default()))
                };
                let result = (|| {
                    this.base
                        .decider
                        .set_branch_condition(branch_term, (branch_exp, rewritten_exp), None)
                        .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
                    action(
                        this,
                        joined_state.clone(),
                        &mut |context, result_state, value, debug| {
                            let path = context
                                .base
                                .decider
                                .pcs
                                .after(mark)
                                .map_err(EvaluationError::Path)?;
                            entries.push(JoinDataEntry {
                                state: joiner::restore_state(result_state, &state),
                                data: (value, debug),
                                path_conditions: path,
                            });
                            Ok(VerificationResult::success())
                        },
                    )
                })();
                let cleanup = this.base.decider.pop_scope().map_err(NativeError::Decider);
                match (result, cleanup) {
                    (Ok(result), Ok(())) => Ok(result),
                    (Err(e), Err(cleanup)) => Err(EvaluationError::TriggerCleanup {
                        evaluation: Box::new(e),
                        cleanup,
                    }),
                    (Err(e), Ok(())) => Err(e),
                    (Ok(_), Err(cleanup)) => Err(EvaluationError::Context(cleanup)),
                }
            };
            // A synchronous source else future runs eagerly before the then branch.
            let else_result = run(self, decision.execute_else, false, no)?;
            let then_result = run(self, decision.execute_then, true, yes)?;
            let branch_result = then_result.combine(|| else_result, false);
            Ok((entries, branch_result))
        })();
        let cleanup = self.base.decider.pop_scope().map_err(NativeError::Decider);
        let (entries, result) = match (block, cleanup) {
            (Ok(value), Ok(())) => value,
            (Err(e), Err(cleanup)) => {
                return Err(EvaluationError::TriggerCleanup {
                    evaluation: Box::new(e),
                    cleanup,
                });
            }
            (Err(e), Ok(())) => return Err(e),
            (Ok(_), Err(cleanup)) => return Err(EvaluationError::Context(cleanup)),
        };
        let result = VerificationResult::success().and_then(|| result);
        if !result.continue_verification() {
            return Ok(result);
        }
        if entries.is_empty() {
            return Ok(result.combine(VerificationResult::success, false));
        }
        let (assumptions, feasible) = joiner::joined_conditions(&entries, &factory);
        let values = entries
            .into_iter()
            .map(|entry| (entry.state, entry.data.0, entry.data.1))
            .collect();
        let (merged, value, debug) = merge(self, values)?;
        for group in assumptions {
            for term in group {
                self.assume_term(&term).map_err(EvaluationError::Context)?;
            }
        }
        self.assume_term(&feasible)
            .map_err(EvaluationError::Context)?;
        let next = continuation(self, merged, value, debug)?;
        Ok(result.combine(|| next, false))
    }
    fn domain_function(
        &mut self,
        function: &ferrum_silver::ast::program::DomainFunc,
        program: &ferrum_silver::ast::program::Program,
        argument_sorts: &[crate::state::terms::Sort],
        result_sort: &crate::state::terms::Sort,
        backend: bool,
    ) -> Result<crate::state::terms::Applicable, Self::Error> {
        {
            if backend {
                self.base
                    .symbol_converter
                    .domain_function(function, program)
                    .map_err(NativeError::Sort)
            } else {
                let mut sorts = argument_sorts.to_vec();
                sorts.push(result_sort.clone());
                self.base
                    .symbol_converter
                    .domain_function_with_sorts(function, &sorts, program)
                    .map_err(NativeError::Sort)
            }
        }
    }
    fn consume_assertion(
        &mut self,
        state: State<PD, FD, JoinMode>,
        assertion: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        Err(EvaluationError::Context(NativeError::Unsupported(
            "consume_assertion",
        )))
    }
    fn eval_field_access(
        &mut self,
        state: State<PD, FD, JoinMode>,
        access: &ferrum_silver::ast::expression::FieldAccess,
        receiver: &Term,
        receiver_exp: Option<&Exp>,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        Err(EvaluationError::Context(NativeError::Unsupported(
            "eval_field_access",
        )))
    }
    fn record_intermediate_heap(
        &mut self,
        state: State<PD, FD, JoinMode>,
        expression: &Exp,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Err(NativeError::Unsupported("record_intermediate_heap"))
    }
    fn debug_old_label(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        position: &ferrum_silver::ast::position::Position,
    ) -> Result<String, Self::Error> {
        Err(NativeError::Unsupported("debug_old_label"))
    }
    fn eval_current_permission(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: Arc<ListBackedHeap>,
        access: &Exp,
        resource: &crate::state::terms::ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        Err(EvaluationError::Context(NativeError::Unsupported(
            "eval_current_permission",
        )))
    }
    fn annotation_warning(&mut self, message: String) -> Result<(), Self::Error> {
        {
            self.warnings.push(message);
            Ok(())
        }
    }
    fn evaluate_quantifier(
        &mut self,
        state: State<PD, FD, JoinMode>,
        expression: &Exp,
        name: &str,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Option<QuantifiedExpressionData>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        Err(EvaluationError::Context(NativeError::Unsupported(
            "evaluate_quantifier",
        )))
    }
    fn heap_independent_auxiliaries(&mut self, terms: &[Term]) -> Result<Vec<Term>, Self::Error> {
        Err(NativeError::Unsupported("heap_independent_auxiliaries"))
    }
    fn assume_quantifier_auxiliaries(
        &mut self,
        globals: &[Term],
        non_globals: &[Term],
        debug: Option<&(
            crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
                crate::debugger::debug_exp::DebugExp,
            >,
            crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
                crate::debugger::debug_exp::DebugExp,
            >,
        )>,
    ) -> Result<(), Self::Error> {
        Err(NativeError::Unsupported("assume_quantifier_auxiliaries"))
    }
    fn precondition_function(
        &mut self,
        function: &crate::state::terms::Applicable,
    ) -> Result<crate::state::terms::Applicable, Self::Error> {
        Err(NativeError::Unsupported("precondition_function"))
    }
    fn assume_existential_preconditions(
        &mut self,
        term: &Term,
        original: &Exp,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.assume_term(term)
    }
    fn check_smoke(&mut self) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check_smoke(false)
            .map_err(NativeError::Decider)
    }
    fn quantifier_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        expression: &Exp,
        error: &Self::PartialError,
    ) -> Result<VerificationResult<VerificationError>, Self::Error> {
        Err(NativeError::Unsupported("quantifier_failure"))
    }
    fn join_off(&self) -> JoinMode {
        JoinMode::Off
    }
    fn respect_function_pre_permission_amounts(&self) -> bool {
        self.options.respect_function_pre_permission_amounts
    }
    fn join_function_application(
        &mut self,
        state: State<PD, FD, JoinMode>,
        function: &ferrum_silver::ast::program::Function,
        args: &[Term],
        debug_exp: Option<&Exp>,
        block: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                Term,
                Option<Exp>,
            ) -> Result<
                VerificationResult<VerificationError>,
                EvaluationError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
            Option<Exp>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        Err(EvaluationError::Context(NativeError::Unsupported(
            "join_function_application",
        )))
    }
    fn consume_function_preconditions(
        &mut self,
        state: State<PD, FD, JoinMode>,
        function: &ferrum_silver::ast::program::Function,
        application: &Exp,
        arguments: &[Exp],
        preconditions: &[Exp],
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        Err(EvaluationError::Context(NativeError::Unsupported(
            "consume_function_preconditions",
        )))
    }
    fn function_snapshot_args(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        function: &ferrum_silver::ast::program::Function,
        arguments: &[Term],
        snapshot: &Term,
    ) -> Result<(Vec<Term>, Term), Self::Error> {
        Err(NativeError::Unsupported("function_snapshot_args"))
    }
    fn heap_function(
        &mut self,
        function: &ferrum_silver::ast::program::Function,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<crate::state::terms::Applicable, Self::Error> {
        Err(NativeError::Unsupported("heap_function"))
    }
    fn assume_function_precondition(
        &mut self,
        term: &Term,
        function: &ferrum_silver::ast::program::Function,
        debug_args: Option<&[Exp]>,
    ) -> Result<(), Self::Error> {
        self.assume_term(term)
    }
    fn branch_conditions(&self) -> Vec<Term> {
        self.base.decider.pcs.recorded().branch_conditions()
    }
    fn fresh_for_perm(
        &mut self,
        declaration: &ferrum_silver::ast::program::LocalVarDecl,
    ) -> Result<(Term, Option<Exp>), Self::Error> {
        Err(NativeError::Unsupported("fresh_for_perm"))
    }
    fn for_perm_conditions(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &crate::state::terms::ResourceKey,
        variables: &[(Term, Option<Exp>)],
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<Vec<ForPermCondition>, Self::Error> {
        Err(NativeError::Unsupported("for_perm_conditions"))
    }
    fn evaluate_special(
        &mut self,
        state: State<PD, FD, JoinMode>,
        expression: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
            Option<Exp>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        Err(EvaluationError::Context(NativeError::Unsupported(
            "evaluate_special",
        )))
    }
}

/// Source snapshot function: projects a snapshot to the requested sort.
pub type NativeSnapshot = Arc<dyn Fn(crate::state::terms::Sort) -> Term + Send + Sync>;
#[allow(unused_variables)]
impl<S: Prover, PD, FD>
    crate::rules::producer::ProductionContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    type PartialError = PartialVerificationError;
    type Snapshot = NativeSnapshot;
    fn adapt_snapshot(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        snapshot: Self::Snapshot,
        assertions: &[Exp],
    ) -> Result<Self::Snapshot, Self::Error> {
        Ok(snapshot)
    }
    fn split_snapshot(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        snapshot: &Self::Snapshot,
        first: &Exp,
        rest: &[Exp],
    ) -> Result<Option<(Self::Snapshot, Self::Snapshot)>, Self::Error> {
        {
            let snap = snapshot(crate::state::terms::Sort::Snap);
            if matches!(snap.kind(), crate::state::terms::TermKind::Unit) {
                return Ok(None);
            }
            let first = self.factory.first(snap.clone());
            let second = self.factory.second(snap.clone());
            let equality = self
                .factory
                .equals(snap, self.factory.combine(first.clone(), second.clone()));
            self.assume_term(&equality)?;
            let f = self.factory.clone();
            let left: NativeSnapshot = Arc::new(move |sort| f.sort_wrapper(first.clone(), sort));
            let f = self.factory.clone();
            let right: NativeSnapshot = Arc::new(move |sort| f.sort_wrapper(second.clone(), sort));
            Ok(Some((left, right)))
        }
    }
    fn assert_false(&mut self) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check(
                &self.factory.boolean(false),
                Some(self.base.decider.assert_timeout.unwrap_or(0)),
            )
            .map_err(NativeError::Decider)
    }
    fn open_produce(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        assertion: &Exp,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn close_produce(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn assume_empty_snapshot(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        snapshot: &Self::Snapshot,
    ) -> Result<(), Self::Error> {
        {
            let actual = snapshot(crate::state::terms::Sort::Snap);
            let equality = self.factory.equals(actual, self.factory.unit());
            self.assume_term(&equality)
        }
    }
    fn evaluate(
        &mut self,
        state: State<PD, FD, JoinMode>,
        expression: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
            Option<Exp>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ProductionError<Self::Error>> {
        {
            let mut callback_error = None;
            let result = crate::rules::evaluator::evaluate(
                self,
                state,
                expression,
                error,
                &mut |context, state, term, debug| match continuation(context, state, term, debug) {
                    Ok(value) => Ok(value),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(EvaluationError::Context(NativeError::ContinuationAbort))
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            result.map_err(|e| ProductionError::Context(NativeError::Evaluation(format!("{e:?}"))))
        }
    }
    fn assume(
        &mut self,
        term: &Term,
        original: &Exp,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.assume_term(term)
    }
    fn factory(&self) -> &crate::state::terms::TermFactory {
        &self.factory
    }
    fn debugging(&self) -> bool {
        false
    }
    fn unsafe_wildcard_optimization(&self) -> bool {
        self.options.unsafe_wildcard_optimization
    }
    fn snapshot_for_resource(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        snapshot: &Self::Snapshot,
        resource: &crate::state::terms::ResourceKey,
    ) -> Result<Term, Self::Error> {
        Err(NativeError::Unsupported("snapshot_for_resource"))
    }
    fn assert_not_negative(
        &mut self,
        state: State<PD, FD, JoinMode>,
        permission: &Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ProductionError<Self::Error>> {
        Err(ProductionError::Context(NativeError::Unsupported(
            "assert_not_negative",
        )))
    }
    fn produce_single(
        &mut self,
        state: State<PD, FD, JoinMode>,
        resource: &crate::state::terms::ResourceKey,
        arguments: &[Term],
        argument_expressions: Option<&[Exp]>,
        snapshot: Term,
        gain: Term,
        gain_exp: Option<Exp>,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ProductionError<Self::Error>> {
        Err(ProductionError::Context(NativeError::Unsupported(
            "produce_single",
        )))
    }
    fn branch_production(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        join: bool,
        consolidate_on_merge: bool,
        when_true: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ProductionError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
        when_false: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ProductionError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ProductionError<Self::Error>> {
        Err(ProductionError::Context(NativeError::Unsupported(
            "branch_production",
        )))
    }
    fn join_impure(&self, state: &State<PD, FD, JoinMode>) -> bool {
        matches!(state.more_joins, JoinMode::Impure | JoinMode::All)
    }
    fn handle_let(
        &mut self,
        state: State<PD, FD, JoinMode>,
        assertion: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            crate::state::store::MapBackedStore,
            Exp,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ProductionError<Self::Error>> {
        Err(ProductionError::Context(NativeError::Unsupported(
            "handle_let",
        )))
    }
    fn evaluate_quantified_permission(
        &mut self,
        state: State<PD, FD, JoinMode>,
        forall: &Exp,
        condition: &Exp,
        permission: &Exp,
        arguments: &[Exp],
        qid: &str,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Option<QuantifiedProductionData>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ProductionError<Self::Error>> {
        Err(ProductionError::Context(NativeError::Unsupported(
            "evaluate_quantified_permission",
        )))
    }
    fn produce_quantified(
        &mut self,
        state: State<PD, FD, JoinMode>,
        snapshot: &Self::Snapshot,
        forall: &Exp,
        resource: &crate::state::terms::ResourceKey,
        qid: &str,
        data: &QuantifiedProductionData,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ProductionError<Self::Error>> {
        Err(ProductionError::Context(NativeError::Unsupported(
            "produce_quantified",
        )))
    }
    fn produce_special(
        &mut self,
        state: State<PD, FD, JoinMode>,
        snapshot: &Self::Snapshot,
        assertion: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ProductionError<Self::Error>> {
        Err(ProductionError::Context(NativeError::Unsupported(
            "produce_special",
        )))
    }
}
