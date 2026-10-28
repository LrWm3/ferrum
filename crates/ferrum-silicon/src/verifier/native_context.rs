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

use crate::interfaces::decider::prover::ProverLike;
use crate::rules::chunk_supporter::ChunkExecutionError;
use crate::rules::consumer::ConsumptionError;
use crate::rules::executor::ExecutionError;
use crate::rules::producer::{ProductionError, QuantifiedProductionData};
use crate::state::store::StoreValue;
use crate::state::{
    chunks::{Chunk, ChunkIdentifier},
    terms::{ApplicationTarget, ResourceKey, Sort},
};
use crate::supporters::functions::function_recorder::FunctionRecorder;
use crate::supporters::method_supporter::MethodVerificationError;
use crate::supporters::predicate_verification_unit::{
    PredicateBranchResult, PredicateVerificationError,
};
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
use ferrum_silver::ast::expression::{ExpKind, LocalVar};
use ferrum_silver::ast::program::Predicate;
use ferrum_silver::ast::program::{LocalVarDecl, Method};
use ferrum_silver::ast::statement::Stmt;
use ferrum_silver::cfg::silver::silver_cfg::SilverCfg;
use ferrum_silver::verifier::verification_error::VerificationErrorKind;
use ferrum_silver::{
    ast::expression::Exp,
    verifier::verification_error::{ErrorReason, PartialVerificationError, VerificationError},
};
type TermValue = Term;
type SilverBlock = ferrum_silver::cfg::silver::silver_cfg::SilverBlock;
type SilverEdge = ferrum_silver::cfg::silver::silver_cfg::SilverEdge;
use std::{
    marker::PhantomData,
    sync::{Arc, atomic::Ordering},
};

#[derive(Clone, Debug)]
pub struct NativeOptions {
    pub unsafe_wildcard_optimization: bool,
    pub disable_subsumption: bool,
    pub join_mode: JoinMode,
    pub after_prelude_timeout: Option<i32>,
    pub after_contract_timeout: Option<i32>,
    pub before_repetition_timeout: Option<i32>,
    pub enable_simplified_unfolds: bool,
    pub disable_havoc_hack_407: bool,
    pub after_inhale_timeout: Option<i32>,
    pub enable_predicate_triggers_on_inhale: bool,
    pub disable_function_unfold_trigger: bool,
    pub exhale_mode: crate::config::ExhaleMode,
    pub exhale_mode_qp: crate::config::ExhaleMode,
    pub disable_short_circuiting: bool,
    pub error_limit: usize,
    pub respect_function_pre_permission_amounts: bool,
}
impl NativeOptions {
    /// Select only features for which the native execution and reporting context is connected.
    pub fn from_config(
        config: &crate::config::Config,
    ) -> Result<Self, NativeError<crate::decider::prover_std_io::ProverError>> {
        if config.enable_debugging
            || config.mask_heap_mode
            || config.parallelize_branches
            || config.enable_simplified_unfolds
            || config.conditionalize_permissions
            || config.prover_randomize_seeds
            || config.report_reason_unknown
            || config.frontend.counterexample.is_some()
            || config.frontend.ide_mode_advanced
            || config.generate_block_messages
            || config.print_method_cf_gs
            || config.print_translated_program
        {
            return Err(NativeError::Unsupported(
                "requested verifier configuration is not connected",
            ));
        }
        if config.timeout != 0
            || config.report_state_after.is_some()
            || config.log_config.is_some()
            || config.log_level.is_some()
            || !config.logger.is_empty()
            || config.state_consolidation_mode != crate::config::StateConsolidationMode::Default
            || config.set_axiomatization_file.is_some()
            || config.multiset_axiomatization_file.is_some()
            || config.sequence_axiomatization_file.is_some()
            || config.map_axiomatization_file.is_some()
            || config.enable_predicate_triggers_on_inhale
            || config.disable_value_map_caching
            || config.disable_isc_triggers
            || config.disable_chunk_order_heuristics
            || config.disable_caches
            || config.disable_function_unfold_trigger
            || config.simplify_on_consume
            || config.enable_branchcondition_reporting
            || config.alternative_function_verification_order
            || config.report_state_after.is_some()
            || config.prover == "Z3-API"
            || (config.is_supplied("numberOfParallelVerifiers")
                && config.number_of_parallel_verifiers != 1)
        {
            return Err(NativeError::Unsupported(
                "requested timeout, logging, solver, worker, cache or encoding policy is not connected",
            ));
        }
        if config.more_joins != JoinMode::Off {
            return Err(NativeError::Unsupported("CFG join mode"));
        }
        if config.include_methods != ".*" || !config.exclude_methods.is_empty() {
            return Err(NativeError::Unsupported(
                "method inclusion/exclusion filters",
            ));
        }
        if config.exhale_mode() != crate::config::ExhaleMode::Greedy {
            return Err(NativeError::Unsupported("more-complete exhale mode"));
        }
        let [prelude, contract, _, inhale, repetition] = config
            .saturation_weights
            .timeouts(config.prover_saturation_timeout);
        Ok(Self {
            unsafe_wildcard_optimization: config.unsafe_wildcard_optimization,
            disable_subsumption: config.disable_subsumption,
            join_mode: config.more_joins,
            after_prelude_timeout: prelude.map(|x| x.timeout_ms),
            after_contract_timeout: contract.map(|x| x.timeout_ms),
            before_repetition_timeout: repetition.map(|x| x.timeout_ms),
            enable_simplified_unfolds: config.enable_simplified_unfolds,
            disable_havoc_hack_407: config.disable_havoc_hack407,
            after_inhale_timeout: inhale.map(|x| x.timeout_ms),
            enable_predicate_triggers_on_inhale: config.enable_predicate_triggers_on_inhale,
            disable_function_unfold_trigger: config.disable_function_unfold_trigger,
            exhale_mode: config.exhale_mode(),
            exhale_mode_qp: config.exhale_mode_qp(),
            disable_short_circuiting: config.disable_short_circuiting_evaluations,
            error_limit: usize::try_from(config.number_of_errors_to_report)
                .map_err(|_| NativeError::Unsupported("negative error limit"))?,
            respect_function_pre_permission_amounts: config
                .frontend
                .respect_function_pre_perm_amounts,
        })
    }
}
#[derive(Debug)]
pub enum NativeError<E> {
    Decider(DeciderError<E>),
    Sort(crate::state::symbol_converter::SymbolConversionError),
    HeapDependency(String),
    Diagnostic(String),
    Evaluation(String),
    Consumption(String),
    Production(String),
    Execution(String),
    Cleanup(String),
    Snapshot(String),
    ResourceProperty(String),
    Preamble(String),
    Chunk(String),
    Consolidation(String),
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
/// Shared recursive function-data handle used by native states and recorders.
#[derive(Clone)]
pub struct NativeFunctionData(
    pub Arc<crate::supporters::functions::function_data::FunctionData<NativeFunctionData>>,
);
pub type NativeState = State<
    crate::supporters::predicate_verification_unit::PredicateData,
    NativeFunctionData,
    JoinMode,
>;
pub type NativeContext = NativeVerifierContext<
    crate::decider::prover_std_io::ProverStdIo,
    crate::supporters::predicate_verification_unit::PredicateData,
    NativeFunctionData,
>;
pub struct NativeVerifierContext<S: Prover, PD, FD> {
    pub base: BaseVerifier<S>,
    pub factory: TermFactory,
    pub options: NativeOptions,
    pub warnings: Vec<String>,
    havoc_counter: u64,
    config_options: Vec<String>,
    predicate_snapshots: crate::supporters::qps::predicate_snap_generator::PredicateSnapGenerator,
    active_program: Option<ferrum_silver::ast::program::Program>,
    _state_types: PhantomData<(PD, FD)>,
}
impl<S: Prover, PD, FD> NativeVerifierContext<S, PD, FD> {
    pub fn new(base: BaseVerifier<S>, factory: TermFactory, options: NativeOptions) -> Self {
        Self {
            base,
            factory,
            options,
            warnings: Vec::new(),
            havoc_counter: 0,
            config_options: Vec::new(),
            predicate_snapshots: Default::default(),
            active_program: None,
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
        self.base.start(user_args).map_err(NativeError::Decider)?;
        self.config_options = config_options.to_vec();
        self.install_preamble()
    }
    /// Reinitialize the solver and reinstall all static options before another verification run.
    pub fn reset(&mut self) -> Result<(), NativeError<S::Error>> {
        self.base.reset().map_err(NativeError::Decider)?;
        self.predicate_snapshots = Default::default();
        self.active_program = None;
        self.havoc_counter = 0;
        self.install_preamble()
    }
    fn install_preamble(&mut self) -> Result<(), NativeError<S::Error>> {
        use crate::interfaces::preamble::PreambleReader;
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
            if !self.config_options.is_empty() {
                self.base
                    .decider
                    .prover
                    .emit_settings(&self.config_options)
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
    fn consolidation_choice(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<crate::verifier::base_verifier::ConsolidatorChoice, NativeError<S::Error>> {
        use ferrum_silver::ast::program::Member;
        let member = match &state.current_member {
            Some(member) => member,
            None => return Ok(self.base.consolidator(None)),
        };
        let info = match member {
            Member::Domain(m) => &m.meta.info,
            Member::Field(m) => &m.meta.info,
            Member::Function(m) => &m.meta.info,
            Member::Predicate(m) => &m.meta.info,
            Member::Method(m) => &m.meta.info,
            Member::Extension(_) => {
                return Err(NativeError::Unsupported("extension member annotations"));
            }
        };
        let choice = crate::supporters::annotation_supporter::consolidation_mode(
            member.name(),
            info,
            |warning| {
                self.warnings.push(warning);
                Ok::<_, ()>(())
            },
        )
        .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        Ok(self.base.consolidator(choice))
    }
    fn call_partial(
        &self,
        call: &Stmt,
        method: &Method,
        precondition: bool,
    ) -> Result<PartialVerificationError, NativeError<S::Error>> {
        use ferrum_silver::ast::{expression::ExpKind, statement::StmtKind};
        let args = match call.kind() {
            StmtKind::MethodCall { args, .. } => args,
            _ => return Err(NativeError::Unsupported("call error context")),
        };
        let substitutions: Vec<_> = method
            .formal_args
            .iter()
            .zip(args)
            .map(|(formal, actual)| {
                (
                    Exp::new(ExpKind::LocalVar(formal.local_var()), formal.meta.clone()),
                    actual.clone(),
                )
            })
            .collect();
        let kind = if precondition {
            VerificationErrorKind::PreconditionInCallFalse(call.clone())
        } else {
            VerificationErrorKind::CallFailed(call.clone())
        };
        Ok(
            PartialVerificationError::for_kind(kind).with_reason_node_transformed(move |node| {
                ferrum_silver::ast::utility::nodes::replace_expressions(&node, &substitutions)
                    .map_err(|_| {
                        ferrum_silver::verifier::verification_result::DiagnosticError::Unsupported(
                            "method call error substitution",
                        )
                    })
            }),
        )
    }
    fn snapshot_term(
        &mut self,
        snapshot: &NativeSnapshot,
        sort: Sort,
    ) -> Result<Term, NativeError<S::Error>> {
        match snapshot {
            NativeSnapshot::Fresh => self
                .base
                .decider
                .fresh_variable(&self.factory, "snapshot", &sort, false, None)
                .map_err(NativeError::Decider),
            NativeSnapshot::Projection(value) => Ok(self.factory.sort_wrapper(value.clone(), sort)),
        }
    }
    fn assume_term(&mut self, term: &Term) -> Result<(), NativeError<S::Error>> {
        self.base
            .decider
            .assume([(term.clone(), None)], false, false)
            .map_err(NativeError::Decider)
    }
    fn failure_full(
        &mut self,
        error: VerificationError,
        retry_level: i32,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        if retry_level == 0
            && !error
                .is_expected()
                .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?
        {
            self.base.errors_reported.fetch_add(1, Ordering::SeqCst);
        }
        Ok(VerificationResult::failure(
            error,
            self.base.report_further_errors(self.options.error_limit),
        ))
    }
    fn failure(
        &mut self,
        partial: &PartialVerificationError,
        reason: ErrorReason,
        retry_level: i32,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        let error = partial
            .due_to(reason)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        if retry_level == 0
            && !error
                .is_expected()
                .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?
        {
            self.base.errors_reported.fetch_add(1, Ordering::SeqCst);
        }
        Ok(VerificationResult::failure(
            error,
            self.base.report_further_errors(self.options.error_limit),
        ))
    }
}
#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone> EvaluationContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
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
        let possible = expression.is_possible_trigger()
            || matches!(expression.kind(),
            ferrum_silver::ast::expression::ExpKind::FieldAccess(access) if state.qp_fields.contains(&access.field));
        if possible {
            state
                .possible_triggers
                .insert(expression.clone(), term.clone());
        }
        Ok(())
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
        self.failure(
            partial,
            ErrorReason::DivisionByZero(divisor.clone()),
            state.retry_level,
        )
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
            state.retry_level,
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
            state.retry_level,
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
        self.consolidate_optional(state)
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
            state.retry_level,
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
        if state.exhale_ext {
            return Err(EvaluationError::Context(NativeError::Unsupported(
                "wand reserve heap",
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
                    let branch_state = this
                        .consolidate_optional(joined_state.clone())
                        .map_err(EvaluationError::Context)?;
                    action(
                        this,
                        branch_state,
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
        let field_exp = Exp::new(ExpKind::FieldAccess(access.clone()), access.meta.clone());
        let full = error
            .due_to(ErrorReason::InsufficientPermission(
                ferrum_silver::ast::utility::nodes::Node::FieldAccess(access.clone()),
            ))
            .map_err(|e| EvaluationError::Context(NativeError::Diagnostic(format!("{e:?}"))))?;
        let resource = ResourceKey::Field(Arc::new(access.field.clone()));
        let mut callback_error = None;
        let result = crate::rules::heap_supporter::field_access(
            self,
            state,
            &field_exp,
            &resource,
            receiver,
            receiver_exp,
            &Some(full),
            &mut |ctx, state, value| match continuation(ctx, state, value) {
                Ok(v) => Ok(v),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ChunkExecutionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| EvaluationError::Context(NativeError::Chunk(format!("{e:?}"))))
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
#[derive(Clone, Debug)]
pub enum NativeSnapshot {
    Fresh,
    Projection(Term),
}
#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
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
            let snap = self.snapshot_term(snapshot, crate::state::terms::Sort::Snap)?;
            if matches!(snap.kind(), crate::state::terms::TermKind::Unit) {
                return Ok(None);
            }
            let first = self.factory.first(snap.clone());
            let second = self.factory.second(snap.clone());
            let equality = self
                .factory
                .equals(snap, self.factory.combine(first.clone(), second.clone()));
            self.assume_term(&equality)?;
            Ok(Some((
                NativeSnapshot::Projection(first),
                NativeSnapshot::Projection(second),
            )))
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
            let actual = self.snapshot_term(snapshot, crate::state::terms::Sort::Snap)?;
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
        use crate::state::terms::{ResourceKey, Sort};
        let sort = match resource {
            ResourceKey::Field(field) => self
                .base
                .symbol_converter
                .to_sort(&field.typ)
                .map_err(NativeError::Sort)?,
            ResourceKey::Predicate(predicate) => {
                if let Some(sort) = state.predicate_snap_map.get(&predicate.name) {
                    sort.clone()
                } else if let Some(body) = &predicate.body {
                    let supporter =
                        crate::supporters::snapshot_supporter::DefaultSnapshotSupporter {
                            symbols: &self.base.symbol_converter,
                            factory: &self.factory,
                        };
                    supporter
                        .optimal_snapshot_sort::<()>(body, &state.program)
                        .map_err(|e| NativeError::Snapshot(format!("{e:?}")))?
                        .0
                } else {
                    Sort::Snap
                }
            }
            ResourceKey::Wand(_) => Sort::MagicWandSnapFunction,
        };
        self.snapshot_term(snapshot, sort)
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
        let factory = self.factory.clone();
        let check = crate::rules::permission_supporter::assert_permission(
            &factory,
            permission,
            original,
            rewritten,
            state.constrainable_arps.iter().cloned(),
            false,
            |term| {
                self.base
                    .decider
                    .check(term, self.base.decider.assert_timeout)
                    .map_err(NativeError::Decider)
            },
            || None,
            |_, _, _, _| Some(()),
        )
        .map_err(ProductionError::Context)?;
        if check.is_none() {
            continuation(self, state)
        } else {
            self.failure(
                error,
                ErrorReason::NegativePermission(original.clone()),
                state.retry_level,
            )
            .map_err(ProductionError::Context)
        }
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
        use ferrum_silver::ast::{program::Member, utility::nodes::Node};
        let node = match resource {
            ResourceKey::Field(f) => Node::Member(Member::Field((**f).clone())),
            ResourceKey::Predicate(p) => Node::Member(Member::Predicate((**p).clone())),
            ResourceKey::Wand(w) => Node::Exp(w.ghost_free_wand.clone()),
        };
        let full = error
            .due_to(ErrorReason::InsufficientPermission(node))
            .map_err(|e| ProductionError::Context(NativeError::Diagnostic(format!("{e:?}"))))?;
        let mut callback_error = None;
        let result = crate::rules::heap_supporter::produce_single(
            self,
            state,
            resource,
            arguments,
            argument_expressions,
            snapshot,
            None,
            gain,
            gain_exp,
            &Some(full),
            true,
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(value) => Ok(value),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ChunkExecutionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| ProductionError::Context(NativeError::Chunk(format!("{e:?}"))))
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

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::rules::consumer::ConsumptionContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    type PartialError = PartialVerificationError;
    fn unit_snapshot(&self) -> Term {
        self.factory.unit()
    }
    fn combine_snapshots(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        first: Term,
        second: Term,
        assertion: &Exp,
        rest: &[Exp],
    ) -> Result<Term, Self::Error> {
        Ok(self.factory.combine(first, second))
    }
    fn finalize_snapshot(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        original_heap: &Arc<ListBackedHeap>,
        snapshot: Term,
        assertions: &[Exp],
    ) -> Result<Term, Self::Error> {
        Ok(snapshot)
    }
    fn consume_with_retry(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: Arc<ListBackedHeap>,
        assertion: &Exp,
        return_snapshot: bool,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
        let original_heap = state.h.clone();
        let mut working = state;
        working.h = heap;
        self.retry_consumption(
            working,
            &mut |ctx, mut state, done| {
                let heap = state.h.clone();
                state.h = original_heap.clone();
                crate::rules::consumer::consume_one(
                    ctx,
                    state,
                    heap,
                    assertion,
                    return_snapshot,
                    error,
                    &mut |ctx, state, heap, snapshot| done(ctx, state, (heap, snapshot)),
                )
            },
            &mut |ctx, state, (heap, snapshot)| continuation(ctx, state, heap, snapshot),
        )
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
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
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
            result.map_err(|e| ConsumptionError::Context(NativeError::Evaluation(format!("{e:?}"))))
        }
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
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
        let factory = self.factory.clone();
        let check = crate::rules::permission_supporter::assert_permission(
            &factory,
            permission,
            original,
            rewritten,
            state.constrainable_arps.iter().cloned(),
            false,
            |term| {
                self.base
                    .decider
                    .check(term, self.base.decider.assert_timeout)
                    .map_err(NativeError::Decider)
            },
            || None,
            |_, _, _, _| Some(()),
        )
        .map_err(ConsumptionError::Context)?;
        if check.is_none() {
            continuation(self, state)
        } else {
            self.failure(
                error,
                ErrorReason::NegativePermission(original.clone()),
                state.retry_level,
            )
            .map_err(ConsumptionError::Context)
        }
    }
    fn trigger_resource(
        &mut self,
        state: State<PD, FD, JoinMode>,
        assertion: &Exp,
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        if state.heap_dependent_triggers.is_empty() {
            Ok(state)
        } else {
            Err(NativeError::Unsupported("resource trigger summaries"))
        }
    }
    fn consume_single(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: Arc<ListBackedHeap>,
        resource: &crate::state::terms::ResourceKey,
        assertion: &Exp,
        args: &[Term],
        debug_args: Option<&[Exp]>,
        loss: Term,
        loss_exp: Option<Exp>,
        return_snapshot: bool,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
        let location = match assertion.kind() {
            ExpKind::FieldAccessPredicate(access, _) => {
                ferrum_silver::ast::utility::nodes::Node::FieldAccess(access.clone())
            }
            ExpKind::PredicateAccessPredicate(access) => {
                ferrum_silver::ast::utility::nodes::Node::PredicateAccess(access.location.clone())
            }
            _ => ferrum_silver::ast::utility::nodes::Node::Exp(assertion.clone()),
        };
        let full = error
            .due_to(ErrorReason::InsufficientPermission(location))
            .map_err(|e| ConsumptionError::Context(NativeError::Diagnostic(format!("{e:?}"))))?;
        let mut callback_error = None;
        let result = crate::rules::heap_supporter::consume_single(
            self,
            state,
            heap,
            resource,
            args,
            debug_args,
            &loss,
            loss_exp.as_ref(),
            return_snapshot,
            &Some(full),
            &mut |ctx, state, heap, snapshot| match continuation(ctx, state, heap, snapshot) {
                Ok(value) => Ok(value),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ChunkExecutionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| ConsumptionError::Context(NativeError::Chunk(format!("{e:?}"))))
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
    fn retry_pure(
        &mut self,
        state: State<PD, FD, JoinMode>,
        action: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ConsumptionError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
        self.retry_consumption(
            state,
            &mut |ctx, state, done| action(ctx, state, &mut |ctx, state| done(ctx, state, ())),
            &mut |ctx, state, ()| continuation(ctx, state),
        )
    }
    fn precondition_function(
        &mut self,
        function: &crate::state::terms::Applicable,
    ) -> Result<crate::state::terms::Applicable, Self::Error> {
        Ok(crate::rules::function_supporter::precondition_version(
            &self.factory,
            function,
        ))
    }
    fn assume_quantifier_precondition(
        &mut self,
        term: &Term,
        expression: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.assume_term(term)
    }
    fn assert_goal(&mut self, term: &Term) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check(term, self.base.decider.assert_timeout)
            .map_err(NativeError::Decider)
    }
    fn assume_assertion(
        &mut self,
        term: &Term,
        original: &Exp,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.assume_term(term)
    }
    fn assertion_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        error: &Self::PartialError,
        original: &Exp,
        goal: &Term,
        rewritten: Option<&Exp>,
    ) -> Result<VerificationResult<VerificationError>, Self::Error> {
        self.failure(
            error,
            ErrorReason::AssertionFalse(original.clone()),
            state.retry_level,
        )
    }
    fn report_further_errors(&self) -> bool {
        self.base.report_further_errors(self.options.error_limit)
    }
    fn join_impure(&self, state: &State<PD, FD, JoinMode>) -> bool {
        matches!(state.more_joins, JoinMode::Impure | JoinMode::All)
    }
    fn branch_consumption(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        join: bool,
        return_snapshot: bool,
        when_true: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                Arc<ListBackedHeap>,
                Option<Term>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ConsumptionError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
        when_false: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                Arc<ListBackedHeap>,
                Option<Term>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ConsumptionError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
        Err(ConsumptionError::Context(NativeError::Unsupported(
            "branch_consumption",
        )))
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
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
        Err(ConsumptionError::Context(NativeError::Unsupported(
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
            Option<crate::rules::producer::QuantifiedProductionData>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
        Err(ConsumptionError::Context(NativeError::Unsupported(
            "evaluate_quantified_permission",
        )))
    }
    fn consume_quantified(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: Arc<ListBackedHeap>,
        resource: &crate::state::terms::ResourceKey,
        assertion: &Exp,
        forall: &Exp,
        qid: &str,
        data: &crate::rules::producer::QuantifiedProductionData,
        return_snapshot: bool,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
        Err(ConsumptionError::Context(NativeError::Unsupported(
            "consume_quantified",
        )))
    }
    fn consume_special(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: Arc<ListBackedHeap>,
        assertion: &Exp,
        return_snapshot: bool,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<Self::Error>> {
        Err(ConsumptionError::Context(NativeError::Unsupported(
            "consume_special",
        )))
    }
}

impl<S: Prover, PD, FD> crate::rules::execution_flow_controller::ScopedContext
    for NativeVerifierContext<S, PD, FD>
{
    type Error = NativeError<S::Error>;
    fn push_scope(&mut self) -> Result<(), Self::Error> {
        self.base.decider.push_scope().map_err(NativeError::Decider)
    }
    fn pop_scope(&mut self) -> Result<(), Self::Error> {
        self.base.decider.pop_scope().map_err(NativeError::Decider)
    }
}
impl<S: Prover, PD, FD: Clone>
    crate::rules::execution_flow_controller::RetryContext<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Mark = crate::decider::path_conditions::Mark;
    fn mark(&mut self) -> Self::Mark {
        self.base.decider.mark()
    }
    fn rollback_to(&mut self, mark: Self::Mark) -> Result<(), Self::Error> {
        self.base
            .decider
            .pcs
            .pop_until_mark(mark)
            .map_err(|e| NativeError::Decider(DeciderError::Path(e)))
    }
    fn consolidate(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        let factory = self.factory.clone();
        let choice = self.consolidation_choice(&state)?;
        crate::rules::state_consolidator::consolidate(&factory, self, state, choice, false)
            .map_err(|e| NativeError::Consolidation(format!("{e:?}")))
    }
    fn retry_exhale_modes(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<(bool, bool), Self::Error> {
        use crate::config::ExhaleMode;
        use ferrum_silver::ast::program::Member;
        let modes = if let Some(member) = &state.current_member {
            let info = match member {
                Member::Domain(m) => &m.meta.info,
                Member::Field(m) => &m.meta.info,
                Member::Function(m) => &m.meta.info,
                Member::Predicate(m) => &m.meta.info,
                Member::Method(m) => &m.meta.info,
                Member::Extension(_) => {
                    return Err(NativeError::Unsupported("extension member annotations"));
                }
            };
            let get = |quantified, warnings: &mut Vec<String>| {
                crate::supporters::annotation_supporter::exhale_mode(
                    member.name(),
                    info,
                    quantified,
                    |message| {
                        warnings.push(message);
                        Ok::<_, ()>(())
                    },
                )
                .map_err(|_| NativeError::Unsupported("exhale annotation"))
            };
            (
                get(false, &mut self.warnings)?,
                get(true, &mut self.warnings)?,
            )
        } else {
            (None, None)
        };
        let select = |mode: Option<ExhaleMode>, configured: ExhaleMode| {
            !matches!(mode.unwrap_or(configured), ExhaleMode::Greedy)
        };
        Ok((
            select(modes.0, self.options.exhale_mode),
            select(modes.1, self.options.exhale_mode_qp),
        ))
    }
    fn open_retry_log(&mut self, _: &State<PD, FD, JoinMode>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn close_retry_log(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// Adapt the consumer's fallible continuation to the shared source retry algorithm.
struct ConsumerRetryAction<'a, S: Prover, PD, FD, T> {
    action: &'a mut dyn FnMut(
        &mut NativeVerifierContext<S, PD, FD>,
        State<PD, FD, JoinMode>,
        &mut dyn FnMut(
            &mut NativeVerifierContext<S, PD, FD>,
            State<PD, FD, JoinMode>,
            T,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<NativeError<S::Error>>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        ConsumptionError<NativeError<S::Error>>,
    >,
}
impl<S: Prover, PD, FD: Clone, T>
    crate::rules::execution_flow_controller::RetryAction<
        NativeVerifierContext<S, PD, FD>,
        PD,
        FD,
        JoinMode,
        T,
        VerificationError,
    > for ConsumerRetryAction<'_, S, PD, FD, T>
where
    S::Error: std::fmt::Debug,
{
    fn run(
        &mut self,
        context: &mut NativeVerifierContext<S, PD, FD>,
        state: State<PD, FD, JoinMode>,
        continuation: &mut dyn FnMut(
            &mut NativeVerifierContext<S, PD, FD>,
            State<PD, FD, JoinMode>,
            T,
        ) -> Result<
            VerificationResult<VerificationError>,
            NativeError<S::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        (self.action)(context, state, &mut |context, state, data| {
            continuation(context, state, data).map_err(ConsumptionError::Context)
        })
        .map_err(|e| NativeError::Consumption(format!("{e:?}")))
    }
}
impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn consolidate_optional(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, NativeError<S::Error>> {
        let choice = self.consolidation_choice(&state)?;
        let factory = self.factory.clone();
        crate::rules::state_consolidator::consolidate(&factory, self, state, choice, true)
            .map_err(|e| NativeError::Consolidation(format!("{e:?}")))
    }
    fn retry_consumption<T>(
        &mut self,
        state: State<PD, FD, JoinMode>,
        action: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                T,
            ) -> Result<
                VerificationResult<VerificationError>,
                ConsumptionError<NativeError<S::Error>>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<NativeError<S::Error>>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            T,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<NativeError<S::Error>>>
    {
        let mut bridge = ConsumerRetryAction { action };
        crate::rules::execution_flow_controller::try_or_fail(
            self,
            state,
            &mut bridge,
            &mut |ctx, state, data| {
                continuation(ctx, state, data)
                    .map_err(|e| NativeError::Consumption(format!("{e:?}")))
            },
        )
        .map_err(ConsumptionError::Context)
    }
}

impl<S: Prover, PD, FD> crate::rules::chunk_supporter::ChunkSolver<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn factory(&self) -> &TermFactory {
        &self.factory
    }
    fn check(&mut self, term: &Term, timeout_ms: i32) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check(term, Some(timeout_ms))
            .map_err(NativeError::Decider)
    }
    fn check_timeout(&self) -> i32 {
        self.base.decider.check_timeout.unwrap_or(0)
    }
    fn assert_timeout(&self) -> i32 {
        self.base.decider.assert_timeout.unwrap_or(0)
    }
    fn assume(&mut self, term: &Term, _: Option<&Exp>) -> Result<(), Self::Error> {
        self.assume_term(term)
    }
    fn assume_properties(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        chunk: &crate::state::chunks::Chunk,
    ) -> Result<(), Self::Error> {
        use crate::{
            interfaces::state::chunks::GeneralChunk,
            state::{chunks::Chunk, heap::Heap},
        };
        let id = match chunk {
            Chunk::Basic(c) => c.resource_id(),
            Chunk::MagicWand(c) => c.resource_id(),
            _ => return Err(NativeError::Unsupported("quantified resource properties")),
        };
        let factory = self.factory.clone();
        let chunks = heap.values().iter().collect::<Vec<_>>();
        for property in id
            .description()
            .instance_properties(state.may_assume_upper_bounds())
        {
            let term = crate::resources::non_quantified_property_interpreter::build(
                &factory,
                &chunks,
                id,
                Some(chunk),
                &property,
                |term| {
                    self.base
                        .decider
                        .check(term, self.base.decider.check_timeout)
                        .map_err(NativeError::Decider)
                },
            )
            .map_err(|e| NativeError::ResourceProperty(format!("{e:?}")))?;
            self.assume_term(&term)?;
        }
        Ok(())
    }
}

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::rules::state_consolidator::ConsolidationServices<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn find_merge_candidate(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        chunks: &[Chunk],
        incoming: &Chunk,
    ) -> Result<Option<usize>, Self::Error> {
        {
            use crate::interfaces::state::chunks::GeneralChunk;
            match incoming {
                crate::state::chunks::Chunk::Basic(chunk) => {
                    let heap = ListBackedHeap::from_chunks(chunks.iter().cloned());
                    crate::rules::chunk_supporter::find_chunk(
                        self,
                        &heap,
                        &chunk.identifier(),
                        chunk.args_ref(),
                    )
                    .map_err(|e| NativeError::Chunk(format!("{e:?}")))
                }
                crate::state::chunks::Chunk::MagicWand(_) => Ok(None),
                _ => Err(NativeError::Unsupported("quantified merge candidate")),
            }
        }
    }
    fn merge_quantified_chunks(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        recorder: FunctionRecorder<FD>,
        first: &Chunk,
        second: &Chunk,
        qvars: &[Term],
    ) -> Result<Option<(FunctionRecorder<FD>, Chunk, Vec<Term>)>, Self::Error> {
        Err(NativeError::Unsupported("merge_quantified_chunks"))
    }
    fn fresh_merged_snapshot(
        &mut self,
        sort: &Sort,
        qvars: &[Term],
    ) -> Result<(Term, ApplicationTarget), Self::Error> {
        {
            let sorts = qvars
                .iter()
                .map(|term| term.sort().clone())
                .collect::<Vec<_>>();
            let (target, _) = self
                .base
                .decider
                .fresh(&self.factory, "ms", &sorts, sort)
                .map_err(NativeError::Decider)?;
            let value = match &target {
                crate::state::terms::ApplicationTarget::Function(f) => {
                    self.factory.app(f.clone(), qvars.to_vec())
                }
                crate::state::terms::ApplicationTarget::Variable(v) if qvars.is_empty() => {
                    v.clone()
                }
                _ => return Err(NativeError::Unsupported("merged snapshot target")),
            };
            Ok((value, target))
        }
    }
    fn assume_merge_equations(
        &mut self,
        equations: &[Term],
        definitions: bool,
    ) -> Result<(), Self::Error> {
        {
            for term in equations {
                self.base
                    .decider
                    .assume([(term.clone(), None)], false, definitions)
                    .map_err(NativeError::Decider)?;
            }
            Ok(())
        }
    }
    fn assume_chunk_properties(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        chunk: &Chunk,
    ) -> Result<(), Self::Error> {
        crate::rules::chunk_supporter::ChunkSolver::assume_properties(self, state, heap, chunk)
    }
    fn assume_delayed_properties(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
    ) -> Result<(), Self::Error> {
        use crate::{resources::resources::ResourceId, state::heap::Heap};
        let factory = self.factory.clone();
        let chunks = heap.values().iter().collect::<Vec<_>>();
        for id in [
            ResourceId::Predicate,
            ResourceId::Field,
            ResourceId::MagicWand,
        ] {
            for property in id
                .description()
                .delayed_properties(state.may_assume_upper_bounds())
            {
                let term = crate::resources::non_quantified_property_interpreter::build(
                    &factory,
                    &chunks,
                    id,
                    None,
                    &property,
                    |term| {
                        self.base
                            .decider
                            .check(term, self.base.decider.check_timeout)
                            .map_err(NativeError::Decider)
                    },
                )
                .map_err(|e| NativeError::ResourceProperty(format!("{e:?}")))?;
                self.assume_term(&term)?;
            }
        }
        Ok(())
    }
    fn saturate_before_consolidation(&mut self) -> Result<(), Self::Error> {
        if let Some(ms) = self.options.before_repetition_timeout {
            self.base
                .decider
                .prover
                .saturate(ms, "before repetition")
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        Ok(())
    }
    fn assume_quantified_field_bounds(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heaps: &[Arc<ListBackedHeap>],
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        use crate::state::heap::Heap;
        if state.qp_fields.is_empty()
            && heaps.iter().all(|heap| {
                heap.values()
                    .iter()
                    .all(|chunk| !matches!(chunk, Chunk::QuantifiedField(_)))
            })
        {
            Ok(state)
        } else {
            Err(NativeError::Unsupported(
                "quantified field permission bounds",
            ))
        }
    }
    fn assume_more_complete_field_bounds(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<(), Self::Error> {
        Err(NativeError::Unsupported(
            "assume_more_complete_field_bounds",
        ))
    }
    fn merge_mask_heaps(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        first: &ListBackedHeap,
        second: &ListBackedHeap,
    ) -> Result<ListBackedHeap, Self::Error> {
        Err(NativeError::Unsupported("merge_mask_heaps"))
    }
    fn consolidation_debugging(&self) -> bool {
        false
    }
    fn begin_consolidation_record(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn finish_consolidation_record(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
}

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::rules::chunk_supporter::ChunkExecutionContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type VerificationError = Option<VerificationError>;
    fn retry_chunk(
        &mut self,
        state: State<PD, FD, JoinMode>,
        action: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                Arc<ListBackedHeap>,
                Option<Term>,
            ) -> Result<
                crate::interfaces::verification::VerificationResult<VerificationError>,
                ChunkExecutionError<Self::Error>,
            >,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<VerificationError>,
        ChunkExecutionError<Self::Error>,
    > {
        let mut bridge = ChunkRetryAction { action };
        crate::rules::execution_flow_controller::try_or_fail(
            self,
            state,
            &mut bridge,
            &mut |ctx, state, (heap, snapshot)| {
                continuation(ctx, state, heap, snapshot)
                    .map_err(|e| NativeError::Chunk(format!("{e:?}")))
            },
        )
        .map_err(ChunkExecutionError::Context)
    }
    fn consume_complete(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: Arc<ListBackedHeap>,
        resource: &crate::state::terms::ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
        permission: &Term,
        debug_permission: Option<&Exp>,
        return_snapshot: bool,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<VerificationError>,
        ChunkExecutionError<Self::Error>,
    > {
        Err(ChunkExecutionError::Context(NativeError::Unsupported(
            "consume_complete",
        )))
    }
    fn transfer_wand(
        &mut self,
        state: State<PD, FD, JoinMode>,
        permission: &Term,
        debug_permission: Option<&Exp>,
        identifier: &ChunkIdentifier,
        args: &[Term],
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Vec<Chunk>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<VerificationError>,
        ChunkExecutionError<Self::Error>,
    > {
        Err(ChunkExecutionError::Context(NativeError::Unsupported(
            "transfer_wand",
        )))
    }
    fn smoke(&mut self, is_assert: bool) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check_smoke(is_assert)
            .map_err(NativeError::Decider)
    }
    fn consumption_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        error: &Self::VerificationError,
        description: &str,
        generate_model: bool,
    ) -> Result<crate::interfaces::verification::VerificationResult<VerificationError>, Self::Error>
    {
        let error = error.clone().ok_or(NativeError::Unsupported(
            "failure from null partial verification error",
        ))?;
        self.failure_full(error, state.retry_level)
    }
    fn fresh_snapshot(
        &mut self,
        sort: &crate::state::terms::Sort,
    ) -> Result<(Term, crate::state::terms::ApplicationTarget), Self::Error> {
        {
            let (target, _) = self
                .base
                .decider
                .fresh(&self.factory, "snap", &[], sort)
                .map_err(NativeError::Decider)?;
            let term = match &target {
                ApplicationTarget::Function(f) => self.factory.app(f.clone(), vec![]),
                ApplicationTarget::Variable(v) => v.clone(),
            };
            Ok((term, target))
        }
    }
    fn lookup_complete(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: Arc<ListBackedHeap>,
        resource: &crate::state::terms::ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<VerificationError>,
        ChunkExecutionError<Self::Error>,
    > {
        Err(ChunkExecutionError::Context(NativeError::Unsupported(
            "lookup_complete",
        )))
    }
    fn resource_snapshot_sort(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &crate::state::terms::ResourceKey,
    ) -> Result<crate::state::terms::Sort, Self::Error> {
        Err(NativeError::Unsupported("resource_snapshot_sort"))
    }
    fn merge_chunk(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        chunk: &Chunk,
    ) -> Result<
        (
            crate::supporters::functions::function_recorder::FunctionRecorder<FD>,
            ListBackedHeap,
        ),
        Self::Error,
    > {
        {
            let factory = self.factory.clone();
            let addition = ListBackedHeap::from_chunks([chunk.clone()]);
            let choice = self.consolidation_choice(state)?;
            crate::rules::state_consolidator::merge_heaps(
                &factory,
                self,
                state,
                state.function_recorder.clone(),
                heap,
                &addition,
                choice,
            )
            .map_err(|e| NativeError::Consolidation(format!("{e:?}")))
        }
    }
}

struct ChunkRetryAction<'a, S: Prover, PD, FD> {
    action: &'a mut dyn FnMut(
        &mut NativeVerifierContext<S, PD, FD>,
        State<PD, FD, JoinMode>,
        &mut dyn FnMut(
            &mut NativeVerifierContext<S, PD, FD>,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ChunkExecutionError<NativeError<S::Error>>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        ChunkExecutionError<NativeError<S::Error>>,
    >,
}
impl<S: Prover, PD, FD: Clone>
    crate::rules::execution_flow_controller::RetryAction<
        NativeVerifierContext<S, PD, FD>,
        PD,
        FD,
        JoinMode,
        (Arc<ListBackedHeap>, Option<Term>),
        VerificationError,
    > for ChunkRetryAction<'_, S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn run(
        &mut self,
        context: &mut NativeVerifierContext<S, PD, FD>,
        state: State<PD, FD, JoinMode>,
        continuation: &mut dyn FnMut(
            &mut NativeVerifierContext<S, PD, FD>,
            State<PD, FD, JoinMode>,
            (Arc<ListBackedHeap>, Option<Term>),
        ) -> Result<
            VerificationResult<VerificationError>,
            NativeError<S::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        (self.action)(context, state, &mut |ctx, state, heap, snap| {
            continuation(ctx, state, (heap, snap)).map_err(ChunkExecutionError::Context)
        })
        .map_err(|e| NativeError::Chunk(format!("{e:?}")))
    }
}

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::rules::heap_supporter::HeapExecutionContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn produce_quantified_single(
        &mut self,
        state: State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
        snapshot: Term,
        permission: Term,
        debug_permission: Option<Exp>,
        merge_and_trigger: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ChunkExecutionError<Self::Error>> {
        Err(ChunkExecutionError::Context(NativeError::Unsupported(
            "produce_quantified_single",
        )))
    }
    fn consume_quantified_single(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: Arc<ListBackedHeap>,
        resource: &ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
        permission: &Term,
        debug_permission: Option<&Exp>,
        return_snapshot: bool,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ChunkExecutionError<Self::Error>> {
        Err(ChunkExecutionError::Context(NativeError::Unsupported(
            "consume_quantified_single",
        )))
    }
    fn create_wand_chunk(
        &mut self,
        state: State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        snapshot: Term,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Chunk,
        ) -> Result<
            VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ChunkExecutionError<Self::Error>> {
        Err(ChunkExecutionError::Context(NativeError::Unsupported(
            "create_wand_chunk",
        )))
    }
    fn quantified_current_permission(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        resource: &ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<(State<PD, FD, JoinMode>, Term), Self::Error> {
        Err(NativeError::Unsupported("quantified_current_permission"))
    }
    fn quantified_field_access(
        &mut self,
        state: State<PD, FD, JoinMode>,
        field_access: &Exp,
        resource: &ResourceKey,
        receiver: &Term,
        debug_receiver: Option<&Exp>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
        ) -> Result<
            VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ChunkExecutionError<Self::Error>> {
        Err(ChunkExecutionError::Context(NativeError::Unsupported(
            "quantified_field_access",
        )))
    }
    fn assign_quantified_field(
        &mut self,
        state: State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        receiver: &Term,
        debug_receiver: Option<&Exp>,
        value: &Term,
        debug_value: Option<&Exp>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ChunkExecutionError<Self::Error>> {
        Err(ChunkExecutionError::Context(NativeError::Unsupported(
            "assign_quantified_field",
        )))
    }
    fn record_assignment_heap(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn fresh_havoc_snapshot(&mut self, sort: &Sort, wand_map: bool) -> Result<Term, Self::Error> {
        Err(NativeError::Unsupported("fresh_havoc_snapshot"))
    }
    fn havoc_codomain(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
    ) -> Result<(Vec<Term>, Term), Self::Error> {
        Err(NativeError::Unsupported("havoc_codomain"))
    }
    fn fresh_havoc_map(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
    ) -> Result<Term, Self::Error> {
        Err(NativeError::Unsupported("fresh_havoc_map"))
    }
    fn assume_havoc_axiom(&mut self, axiom: &Term) -> Result<(), Self::Error> {
        Err(NativeError::Unsupported("assume_havoc_axiom"))
    }
    fn next_havoc_axiom_id(&mut self) -> u64 {
        self.havoc_counter = self.havoc_counter.wrapping_add(1);
        self.havoc_counter - 1
    }
    fn heap_branch_conditions(&self) -> Vec<Term> {
        self.base.decider.pcs.recorded().branch_conditions()
    }
    fn enable_predicate_triggers_on_inhale(&self) -> bool {
        self.options.enable_predicate_triggers_on_inhale
    }
    fn disable_function_unfold_trigger(&self) -> bool {
        self.options.disable_function_unfold_trigger
    }
    fn assume_predicate_trigger(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        predicate: &ferrum_silver::ast::program::Predicate,
        snapshot: &Term,
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<(), Self::Error> {
        Err(NativeError::Unsupported("assume_predicate_trigger"))
    }
}

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::rules::executor::ExecutionContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn open_statement(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        statement: &Stmt,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn close_statement(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn execution_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        if state.exhale_ext {
            Err(NativeError::Unsupported("wand execution heap"))
        } else {
            Ok(state.h.clone())
        }
    }
    fn move_to_reserve_heap(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        if state.exhale_ext {
            Err(NativeError::Unsupported("wand reserve heap"))
        } else {
            Ok(state)
        }
    }
    fn evaluation_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        if state.exhale_ext {
            Err(NativeError::Unsupported("wand evaluation heap"))
        } else {
            Ok(state.h.clone())
        }
    }
    fn record_label(
        &mut self,
        state: State<PD, FD, JoinMode>,
        label: &str,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn fresh_local(&mut self, variable: &LocalVar) -> Result<StoreValue, Self::Error> {
        {
            let sort = self
                .base
                .symbol_converter
                .to_sort(&variable.typ)
                .map_err(NativeError::Sort)?;
            let term = self
                .base
                .decider
                .fresh_variable(&self.factory, &variable.name, &sort, false, None)
                .map_err(NativeError::Decider)?;
            Ok((term, None))
        }
    }
    fn evaluate_assignment(
        &mut self,
        state: State<PD, FD, JoinMode>,
        statement: &Stmt,
        rhs: &Exp,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            StoreValue,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        {
            let partial = PartialVerificationError::for_kind(
                VerificationErrorKind::AssignmentFailed(statement.clone()),
            );
            let mut callback_error = None;
            let result = crate::rules::evaluator::evaluate(
                self,
                state,
                rhs,
                &partial,
                &mut |ctx, state, term, debug| match continuation(ctx, state, (term, debug)) {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(EvaluationError::Context(NativeError::ContinuationAbort))
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            result.map_err(|e| ExecutionError::Context(NativeError::Evaluation(format!("{e:?}"))))
        }
    }
    fn factory(&self) -> &crate::state::terms::TermFactory {
        &self.factory
    }
    fn debugging(&self) -> bool {
        false
    }
    fn fresh_ssa(
        &mut self,
        name: &str,
        typ: &ferrum_silver::ast::r#type::Type,
        source: &Exp,
    ) -> Result<StoreValue, Self::Error> {
        {
            let sort = self
                .base
                .symbol_converter
                .to_sort(typ)
                .map_err(NativeError::Sort)?;
            let term = self
                .base
                .decider
                .fresh_variable(&self.factory, name, &sort, false, None)
                .map_err(NativeError::Decider)?;
            Ok((term, None))
        }
    }
    fn assume_ssa_definition(
        &mut self,
        equation: &TermValue,
        name: &str,
        typ: &ferrum_silver::ast::r#type::Type,
        source: &Exp,
        rewritten: Option<&Exp>,
        new_variable: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.assume_term(equation)
    }
    fn assign_field(
        &mut self,
        state: State<PD, FD, JoinMode>,
        statement: &Stmt,
        receiver: TermValue,
        receiver_exp: Option<Exp>,
        snapshot: TermValue,
        rhs_exp: Option<Exp>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        let field = match statement.kind() {
            ferrum_silver::ast::statement::StmtKind::FieldAssign { lhs, .. } => lhs,
            _ => {
                return Err(ExecutionError::Context(NativeError::Unsupported(
                    "field assignment statement",
                )));
            }
        };
        let error = VerificationError::new(
            VerificationErrorKind::AssignmentFailed(statement.clone()),
            ErrorReason::InsufficientPermission(
                ferrum_silver::ast::utility::nodes::Node::FieldAccess(field.clone()),
            ),
        );
        let mut callback_error = None;
        let result = crate::rules::heap_supporter::assign_field(
            self,
            state,
            &field.field,
            &receiver,
            receiver_exp.as_ref(),
            &snapshot,
            rhs_exp.as_ref(),
            None,
            &Some(error),
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(value) => Ok(value),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ChunkExecutionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| ExecutionError::Context(NativeError::Chunk(format!("{e:?}"))))
    }
    fn produce(
        &mut self,
        state: State<PD, FD, JoinMode>,
        statement: &Stmt,
        assertion: &Exp,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        {
            let partial = PartialVerificationError::for_kind(VerificationErrorKind::InhaleFailed(
                statement.clone(),
            ));
            let mut callback_error = None;
            let result = crate::rules::producer::produce_all(
                self,
                state,
                NativeSnapshot::Fresh,
                std::slice::from_ref(assertion),
                &|_| partial.clone(),
                &mut |ctx, state| match continuation(ctx, state) {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(ProductionError::Context(NativeError::ContinuationAbort))
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            result.map_err(|e| ExecutionError::Context(NativeError::Production(format!("{e:?}"))))
        }
    }
    fn consume(
        &mut self,
        state: State<PD, FD, JoinMode>,
        statement: &Stmt,
        assertion: &Exp,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        {
            use ferrum_silver::ast::statement::StmtKind;
            let kind = match statement.kind() {
                StmtKind::Assert(_) => VerificationErrorKind::AssertFailed(statement.clone()),
                StmtKind::Exhale(_) => VerificationErrorKind::ExhaleFailed(statement.clone()),
                _ => {
                    return Err(ExecutionError::Context(NativeError::Unsupported(
                        "statement consumption reason",
                    )));
                }
            };
            let partial = PartialVerificationError::for_kind(kind);
            let mut callback_error = None;
            let result = crate::rules::consumer::consume_all(
                self,
                state,
                std::slice::from_ref(assertion),
                false,
                &|_| partial.clone(),
                &mut |ctx, state, _| match continuation(ctx, state) {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(ConsumptionError::Context(NativeError::ContinuationAbort))
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            result.map_err(|e| ExecutionError::Context(NativeError::Consumption(format!("{e:?}"))))
        }
    }
    fn saturate_after_inhale(&mut self) -> Result<(), Self::Error> {
        {
            if let Some(timeout) = self.options.after_inhale_timeout {
                self.base
                    .decider
                    .prover
                    .saturate(timeout, "after inhale")
                    .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            }
            Ok(())
        }
    }
    fn assume_new_nonnull(
        &mut self,
        term: &TermValue,
        original: &LocalVar,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        {
            let term = self
                .factory
                .not(self.factory.equals(term.clone(), self.factory.null()));
            self.assume_term(&term)
        }
    }
    fn fresh_field_snapshot(
        &mut self,
        field: &ferrum_silver::ast::program::Field,
        original: &LocalVar,
    ) -> Result<TermValue, Self::Error> {
        {
            let sort = self
                .base
                .symbol_converter
                .to_sort(&field.typ)
                .map_err(NativeError::Sort)?;
            self.base
                .decider
                .fresh_variable(&self.factory, "new", &sort, false, None)
                .map_err(NativeError::Decider)
        }
    }
    fn produce_new_field(
        &mut self,
        state: State<PD, FD, JoinMode>,
        field: &ferrum_silver::ast::program::Field,
        receiver: &TermValue,
        original: &LocalVar,
        rewritten: Option<&Exp>,
        snapshot: TermValue,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        let resource = ResourceKey::Field(Arc::new(field.clone()));
        let mut callback_error = None;
        let result = crate::rules::heap_supporter::produce_single(
            self,
            state,
            &resource,
            std::slice::from_ref(receiver),
            None,
            snapshot,
            None,
            self.factory.full_perm(),
            None,
            &None,
            false,
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(value) => Ok(value),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ChunkExecutionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| ExecutionError::Context(NativeError::Chunk(format!("{e:?}"))))
    }
    fn assume_reference_disjointness(
        &mut self,
        terms: &[TermValue],
        expressions: Option<&[Exp]>,
    ) -> Result<(), Self::Error> {
        {
            for term in terms {
                self.assume_term(term)?;
            }
            Ok(())
        }
    }
    fn record_new_heap(
        &mut self,
        state: State<PD, FD, JoinMode>,
        statement: &Stmt,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn disable_subsumption(&self) -> bool {
        self.options.disable_subsumption
    }
    fn start_key_heap(
        &mut self,
        state: State<PD, FD, JoinMode>,
        statement: &Stmt,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn finish_key_heap(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn check_empty_exhale_ext(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<(), Self::Error> {
        if state.exhale_ext {
            Err(NativeError::Unsupported("wand exhale reserve check"))
        } else {
            Ok(())
        }
    }
    fn retry_smoke_assertion(
        &mut self,
        state: State<PD, FD, JoinMode>,
        statement: &Stmt,
        original_heap: Arc<ListBackedHeap>,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        let partial = PartialVerificationError::for_kind(VerificationErrorKind::AssertFailed(
            statement.clone(),
        ));
        let expression = match statement.kind() {
            ferrum_silver::ast::statement::StmtKind::Assert(exp) => exp.clone(),
            _ => {
                return Err(ExecutionError::Context(NativeError::Unsupported(
                    "smoke assertion statement",
                )));
            }
        };
        self.retry_consumption(
            state,
            &mut |ctx, mut state, done| {
                let smoke = ctx
                    .base
                    .decider
                    .check_smoke(true)
                    .map_err(|e| ConsumptionError::Context(NativeError::Decider(e)))?;
                if smoke {
                    state.h = original_heap.clone();
                    done(ctx, state, ())
                } else {
                    ctx.failure(
                        &partial,
                        ErrorReason::AssertionFalse(expression.clone()),
                        state.retry_level,
                    )
                    .map_err(ConsumptionError::Context)
                }
            },
            &mut |_, _, ()| Ok(VerificationResult::success()),
        )
        .map_err(|e| ExecutionError::Context(NativeError::Consumption(format!("{e:?}"))))
    }
    fn disable_havoc_hack_407(&self) -> bool {
        self.options.disable_havoc_hack_407
    }
    fn evaluate_call_arguments(
        &mut self,
        state: State<PD, FD, JoinMode>,
        call: &Stmt,
        arguments: &[Exp],
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Vec<TermValue>,
            Option<Vec<Exp>>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        let partial =
            PartialVerificationError::for_kind(VerificationErrorKind::CallFailed(call.clone()));
        let mut callback_error = None;
        let result = crate::rules::evaluator::evaluate_all(
            self,
            state,
            arguments,
            &|_| partial.clone(),
            &mut |ctx, state, terms, debug| match continuation(ctx, state, terms, debug) {
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
        result.map_err(|e| ExecutionError::Context(NativeError::Evaluation(format!("{e:?}"))))
    }
    fn consume_call_preconditions(
        &mut self,
        state: State<PD, FD, JoinMode>,
        call: &Stmt,
        method: &ferrum_silver::ast::program::Method,
        return_snapshot: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Option<TermValue>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        let partial = self
            .call_partial(call, method, true)
            .map_err(ExecutionError::Context)?;
        let mut callback_error = None;
        let result = crate::rules::consumer::consume_all(
            self,
            state,
            &method.pres,
            return_snapshot,
            &|_| partial.clone(),
            &mut |ctx, state, snapshot| match continuation(ctx, state, snapshot) {
                Ok(value) => Ok(value),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ConsumptionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| ExecutionError::Context(NativeError::Consumption(format!("{e:?}"))))
    }
    fn reconstruct_pre_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        call: &Stmt,
        method: &ferrum_silver::ast::program::Method,
        snapshot: &TermValue,
    ) -> Result<Option<Arc<ListBackedHeap>>, Self::Error> {
        Err(NativeError::Unsupported("reconstruct_pre_heap"))
    }
    fn produce_call_postconditions(
        &mut self,
        state: State<PD, FD, JoinMode>,
        call: &Stmt,
        method: &ferrum_silver::ast::program::Method,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        let partial = self
            .call_partial(call, method, false)
            .map_err(ExecutionError::Context)?;
        let mut callback_error = None;
        let result = crate::rules::producer::produce_all(
            self,
            state,
            NativeSnapshot::Fresh,
            &method.posts,
            &|_| partial.clone(),
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(value) => Ok(value),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ProductionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| ExecutionError::Context(NativeError::Production(format!("{e:?}"))))
    }
    fn execute_special(
        &mut self,
        state: State<PD, FD, JoinMode>,
        statement: &Stmt,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        Err(ExecutionError::Context(NativeError::Unsupported(
            "execute_special",
        )))
    }
}

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::rules::executor::CfgContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn block_reached(
        &mut self,
        state: State<PD, FD, JoinMode>,
        block: &SilverBlock,
        path_id: i32,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn block_finished(
        &mut self,
        block: &SilverBlock,
        path_id: i32,
        result: &VerificationResult<VerificationError>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn outgoing_edges(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        block: &SilverBlock,
    ) -> Result<Vec<SilverEdge>, Self::Error> {
        {
            let cfg = state
                .method_cfg
                .as_ref()
                .ok_or(NativeError::Unsupported("missing CFG"))?;
            Ok(cfg.graph().out_edges(block).into_iter().cloned().collect())
        }
    }
    fn merge_invariant_context(
        &mut self,
        state: State<PD, FD, JoinMode>,
        saved: Arc<ListBackedHeap>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Err(NativeError::Unsupported("merge_invariant_context"))
    }
    fn evaluate_edge(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: &Exp,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            TermValue,
            Option<Exp>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        {
            let partial = PartialVerificationError::for_kind(VerificationErrorKind::IfFailed(
                condition.clone(),
            ));
            let mut callback_error = None;
            let result = crate::rules::evaluator::evaluate(
                self,
                state,
                condition,
                &partial,
                &mut |ctx, state, term, debug| match continuation(ctx, state, term, debug) {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(EvaluationError::Context(NativeError::ContinuationAbort))
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            result.map_err(|e| ExecutionError::Context(NativeError::Evaluation(format!("{e:?}"))))
        }
    }
    fn branch_edge(
        &mut self,
        state: State<PD, FD, JoinMode>,
        term: TermValue,
        condition: &Exp,
        rewritten: Option<&Exp>,
        yes: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
        no: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        use crate::rules::brancher;
        if state.exhale_ext {
            return Err(ExecutionError::Context(NativeError::Unsupported(
                "wand reserve heap",
            )));
        }
        let factory = self.factory.clone();
        let qvars = state
            .quantified_variables
            .iter()
            .map(|(v, _)| v.clone())
            .collect::<Vec<_>>();
        let decision = brancher::decide(&factory, &term, &qvars, false, false, |goal| {
            self.base
                .decider
                .check(goal, self.base.decider.check_timeout)
        })
        .map_err(|e| match e {
            brancher::BranchError::Solver(e) => ExecutionError::Context(NativeError::Decider(e)),
            brancher::BranchError::Traversal(e) => {
                ExecutionError::Context(NativeError::BranchTraversal(format!("{e:?}")))
            }
        })?;
        let run = |this: &mut Self,
                   active: bool,
                   positive: bool,
                   action: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >|
         -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        > {
            if !active {
                return Ok(VerificationResult::unreachable());
            }
            this.base
                .decider
                .push_scope()
                .map_err(|e| ExecutionError::Context(NativeError::Decider(e)))?;
            let guard = if positive {
                term.clone()
            } else {
                factory.not(term.clone())
            };
            let expr = if positive {
                condition.clone()
            } else {
                Exp::new(ExpKind::Not(condition.clone()), Default::default())
            };
            let debug = if positive {
                rewritten.cloned()
            } else {
                rewritten.map(|e| Exp::new(ExpKind::Not(e.clone()), Default::default()))
            };
            let result = (|| {
                this.base
                    .decider
                    .set_branch_condition(guard, (expr, debug), None)
                    .map_err(|e| ExecutionError::Context(NativeError::Decider(e)))?;
                let branch_state = this
                    .consolidate_optional(state.clone())
                    .map_err(ExecutionError::Context)?;
                action(this, branch_state)
            })();
            let cleanup = this.base.decider.pop_scope();
            match (result, cleanup) {
                (Ok(v), Ok(())) => Ok(v),
                (Err(e), Ok(())) => Err(e),
                (Ok(_), Err(e)) => Err(ExecutionError::Context(NativeError::Decider(e))),
                (Err(e), Err(cleanup)) => Err(ExecutionError::Context(NativeError::Cleanup(
                    format!("{e:?}; cleanup: {cleanup:?}"),
                ))),
            }
        };
        let else_result = run(self, decision.execute_else, false, no)?;
        let then_result = run(self, decision.execute_then, true, yes)?;
        Ok(then_result.combine(|| else_result, false))
    }
    fn all_cfg_joins(&self, state: &State<PD, FD, JoinMode>) -> bool {
        matches!(state.more_joins, JoinMode::All)
    }
    fn parallelize_cfg_branches(&self) -> bool {
        false
    }
    fn join_cfg_branches(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: TermValue,
        original: &Exp,
        rewritten: Option<&Exp>,
        yes: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ExecutionError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
        no: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ExecutionError<Self::Error>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        Err(ExecutionError::Context(NativeError::Unsupported(
            "join_cfg_branches",
        )))
    }
    fn begin_edges(&mut self, count: usize) -> Result<(), Self::Error> {
        Ok(())
    }
    fn next_edge(&mut self, index: usize) -> Result<(), Self::Error> {
        Ok(())
    }
    fn mark_edge_reachable(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_edges(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn empty_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        Ok(Arc::new(ListBackedHeap::new()))
    }
    fn locally_loop(
        &mut self,
        state: State<PD, FD, JoinMode>,
        block: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        Err(ExecutionError::Context(NativeError::Unsupported(
            "locally_loop",
        )))
    }
    fn loop_mark(&mut self) -> crate::decider::path_conditions::Mark {
        self.base.decider.mark()
    }
    fn loop_path_after(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<crate::decider::path_conditions::RecordedPathConditions, Self::Error> {
        self.base
            .decider
            .pcs
            .after(mark)
            .map_err(|e| NativeError::Decider(DeciderError::Path(e)))
    }
    fn loop_fresh_declarations(
        &self,
    ) -> (
        Vec<crate::state::terms::Declaration>,
        Vec<crate::state::terms::Declaration>,
    ) {
        (
            self.base.decider.fresh_functions.iter().cloned().collect(),
            self.base.decider.fresh_macros.clone(),
        )
    }
    fn replay_loop_path(
        &mut self,
        paths: &crate::decider::path_conditions::RecordedPathConditions,
        functions: &[crate::state::terms::Declaration],
        macros: &[crate::state::terms::Declaration],
    ) -> Result<(), Self::Error> {
        Err(NativeError::Unsupported("replay_loop_path"))
    }
    fn loop_produce_invariants(
        &mut self,
        state: State<PD, FD, JoinMode>,
        invariants: &[Exp],
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        Err(ExecutionError::Context(NativeError::Unsupported(
            "loop_produce_invariants",
        )))
    }
    fn loop_consume_invariants(
        &mut self,
        state: State<PD, FD, JoinMode>,
        invariants: &[Exp],
        preserved: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        Err(ExecutionError::Context(NativeError::Unsupported(
            "loop_consume_invariants",
        )))
    }
    fn loop_merge_debug_heaps(
        &mut self,
        state: State<PD, FD, JoinMode>,
        leftover: &State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn loop_saturate(&mut self) -> Result<(), Self::Error> {
        {
            if let Some(ms) = self.options.after_inhale_timeout {
                self.base
                    .decider
                    .prover
                    .saturate(ms, "after inhale")
                    .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            }
            Ok(())
        }
    }
    fn loop_smoke(&mut self) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check_smoke(false)
            .map_err(NativeError::Decider)
    }
    fn loop_comment(&mut self, text: &str) -> Result<(), Self::Error> {
        Ok(())
    }
}

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::supporters::method_supporter::MethodVerificationServices<
        PD,
        FD,
        JoinMode,
        VerificationError,
    > for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn warn_method_annotation(&mut self, warning: String) -> Result<(), Self::Error> {
        {
            self.warnings.push(warning);
            Ok(())
        }
    }
    fn set_method_prover_options(
        &mut self,
        options: crate::package::Map<String, String>,
    ) -> Result<(), Self::Error> {
        self.base
            .decider
            .set_options(options)
            .map_err(NativeError::Decider)
    }
    fn reset_method_prover_options(&mut self) -> Result<(), Self::Error> {
        self.base
            .decider
            .reset_options()
            .map_err(NativeError::Decider)
    }
    fn open_method_log(&mut self, method: &Method) -> Result<(), Self::Error> {
        Ok(())
    }
    fn close_method_log(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn warn_ignored_loop_labels(
        &mut self,
        labels: &[ferrum_silver::ast::program::LabelDeclaration],
    ) -> Result<(), Self::Error> {
        {
            for label in labels {
                self.warnings.push(format!(
                    "Loop invariants on label {} are ignored",
                    label.name
                ));
            }
            Ok(())
        }
    }
    fn fresh_method_local(
        &mut self,
        formal: &LocalVarDecl,
    ) -> Result<(Term, Option<Exp>), Self::Error> {
        {
            let sort = self
                .base
                .symbol_converter
                .to_sort(&formal.typ)
                .map_err(NativeError::Sort)?;
            let term = self
                .base
                .decider
                .fresh_variable(&self.factory, &formal.name, &sort, false, None)
                .map_err(NativeError::Decider)?;
            Ok((term, None))
        }
    }
    fn empty_method_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        Ok(Arc::new(ListBackedHeap::new()))
    }
    fn prepare_method_debug(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn record_method_pre_state(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn prepare_method_post_state(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn output_method_cfg(&mut self, method: &Method, cfg: &SilverCfg) -> Result<(), Self::Error> {
        Ok(())
    }
    fn reset_method_error_count(&mut self) {
        self.base.errors_reported.store(0, Ordering::SeqCst)
    }
    fn saturate_method_contract(&mut self) -> Result<(), Self::Error> {
        {
            if let Some(ms) = self.options.after_contract_timeout {
                self.base
                    .decider
                    .prover
                    .saturate(ms, "after contract")
                    .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            }
            Ok(())
        }
    }
    fn method_locally(
        &mut self,
        state: State<PD, FD, JoinMode>,
        action: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            MethodVerificationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, MethodVerificationError<Self::Error>> {
        {
            self.base
                .decider
                .push_scope()
                .map_err(|e| MethodVerificationError::Service(NativeError::Decider(e)))?;
            let result = action(self, state);
            let cleanup = self.base.decider.pop_scope();
            match (result, cleanup) {
                (Ok(value), Ok(())) => Ok(value),
                (Err(error), Ok(())) => Err(error),
                (Ok(_), Err(cleanup)) => Err(MethodVerificationError::Service(
                    NativeError::Decider(cleanup),
                )),
                (Err(error), Err(cleanup)) => Err(MethodVerificationError::Service(
                    NativeError::Cleanup(format!("{error:?}; cleanup: {cleanup:?}")),
                )),
            }
        }
    }
    fn produce_method_contract(
        &mut self,
        state: State<PD, FD, JoinMode>,
        assertions: &[Exp],
        method: &Method,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            MethodVerificationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, MethodVerificationError<Self::Error>> {
        {
            let mut callback_error = None;
            let result = crate::rules::producer::produce_all(
                self,
                state,
                NativeSnapshot::Fresh,
                assertions,
                &|exp| {
                    PartialVerificationError::for_kind(
                        VerificationErrorKind::ContractNotWellformed(exp.clone()),
                    )
                },
                &mut |ctx, state| match continuation(ctx, state) {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(ProductionError::Context(NativeError::ContinuationAbort))
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            result.map_err(|e| {
                MethodVerificationError::Service(NativeError::Production(format!("{e:?}")))
            })
        }
    }
    fn execute_method_cfg(
        &mut self,
        state: State<PD, FD, JoinMode>,
        cfg: &SilverCfg,
        method: &Method,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            MethodVerificationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, MethodVerificationError<Self::Error>> {
        {
            let mut callback_error = None;
            let result =
                crate::rules::executor::execute_cfg(self, state, cfg, &mut |ctx, state| {
                    match continuation(ctx, state) {
                        Ok(v) => Ok(v),
                        Err(e) => {
                            callback_error = Some(e);
                            Err(ExecutionError::Context(NativeError::ContinuationAbort))
                        }
                    }
                });
            if let Some(error) = callback_error {
                return Err(error);
            }
            result.map_err(|e| {
                MethodVerificationError::Service(NativeError::Execution(format!("{e:?}")))
            })
        }
    }
    fn consume_method_posts(
        &mut self,
        state: State<PD, FD, JoinMode>,
        posts: &[Exp],
        method: &Method,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            MethodVerificationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, MethodVerificationError<Self::Error>> {
        {
            let mut callback_error = None;
            let result = crate::rules::consumer::consume_all(
                self,
                state,
                posts,
                false,
                &|exp| {
                    PartialVerificationError::for_kind(
                        VerificationErrorKind::PostconditionViolated {
                            node: exp.clone(),
                            member: ferrum_silver::ast::program::Member::Method(method.clone()),
                        },
                    )
                },
                &mut |ctx, state, _| match continuation(ctx, state) {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(ConsumptionError::Context(NativeError::ContinuationAbort))
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            result.map_err(|e| {
                MethodVerificationError::Service(NativeError::Consumption(format!("{e:?}")))
            })
        }
    }
}

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::supporters::predicate_verification_unit::PredicateVerificationServices<
        PD,
        FD,
        JoinMode,
        VerificationError,
    > for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn open_predicate_verification(&mut self, predicate: &Predicate) -> Result<(), Self::Error> {
        Ok(())
    }
    fn close_predicate_verification(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn fresh_predicate_snapshot(&mut self) -> Result<Term, Self::Error> {
        self.base
            .decider
            .fresh_variable(&self.factory, "predicate", &Sort::Snap, false, None)
            .map_err(NativeError::Decider)
    }
    fn fresh_predicate_argument(
        &mut self,
        formal: &ferrum_silver::ast::program::LocalVarDecl,
    ) -> Result<(Term, Option<Exp>), Self::Error> {
        {
            let sort = self
                .base
                .symbol_converter
                .to_sort(&formal.typ)
                .map_err(NativeError::Sort)?;
            let term = self
                .base
                .decider
                .fresh_variable(&self.factory, &formal.name, &sort, false, None)
                .map_err(NativeError::Decider)?;
            Ok((term, None))
        }
    }
    fn empty_predicate_heap(
        &mut self,
        state: &crate::state::state::State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        Ok(Arc::new(ListBackedHeap::new()))
    }
    fn start_predicate_debug_heap(
        &mut self,
        state: crate::state::state::State<PD, FD, JoinMode>,
    ) -> Result<crate::state::state::State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn simplified_unfolds_enabled(&self) -> bool {
        self.options.enable_simplified_unfolds
    }
    fn predicate_debugging(&self) -> bool {
        false
    }
    fn produce_predicate_locally(
        &mut self,
        state: crate::state::state::State<PD, FD, JoinMode>,
        body: &Exp,
        snapshot: &Term,
        predicate: &Predicate,
        branch: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<PD, FD, JoinMode>,
            PredicateBranchResult,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<VerificationError>,
            PredicateVerificationError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<VerificationError>,
        PredicateVerificationError<Self::Error>,
    > {
        {
            self.base
                .decider
                .push_scope()
                .map_err(|e| PredicateVerificationError::Service(NativeError::Decider(e)))?;
            let mut callback_error = None;
            let result = crate::rules::producer::produce_all(
                self,
                state,
                NativeSnapshot::Projection(snapshot.clone()),
                std::slice::from_ref(body),
                &|_| {
                    PartialVerificationError::for_kind(
                        VerificationErrorKind::PredicateNotWellformed(predicate.clone()),
                    )
                },
                &mut |ctx, state| {
                    let pcs = ctx.base.decider.pcs.recorded();
                    let data = PredicateBranchResult {
                        conditions: pcs.branch_conditions(),
                        condition_exps: pcs.branch_condition_exps(),
                        heap: state.h.clone(),
                        assumptions: pcs.assumptions(),
                    };
                    match branch(ctx, state, data) {
                        Ok(v) => Ok(v),
                        Err(e) => {
                            callback_error = Some(e);
                            Err(ProductionError::Context(NativeError::ContinuationAbort))
                        }
                    }
                },
            );
            let cleanup = self.base.decider.pop_scope();
            if let Some(error) = callback_error {
                if let Err(cleanup) = cleanup {
                    return Err(PredicateVerificationError::Service(NativeError::Cleanup(
                        format!("{error:?}; cleanup: {cleanup:?}"),
                    )));
                }
                return Err(error);
            }
            match (result, cleanup) {
                (Ok(v), Ok(())) => Ok(v),
                (Err(e), Ok(())) => Err(PredicateVerificationError::Service(
                    NativeError::Production(format!("{e:?}")),
                )),
                (Ok(_), Err(e)) => {
                    Err(PredicateVerificationError::Service(NativeError::Decider(e)))
                }
                (Err(e), Err(cleanup)) => Err(PredicateVerificationError::Service(
                    NativeError::Cleanup(format!("{e:?}; cleanup: {cleanup:?}")),
                )),
            }
        }
    }
    fn store_predicate_recorder(
        &mut self,
        predicate: &Predicate,
        recorder: crate::supporters::functions::function_recorder::FunctionRecorder<FD>,
    ) -> Result<(), Self::Error> {
        if matches!(recorder, FunctionRecorder::Noop) {
            Ok(())
        } else {
            Err(NativeError::Unsupported("predicate recorder integration"))
        }
    }
}

/// Member data built once during source-ordered program analysis.
pub struct NativeAnalysis {
    predicates: crate::state::package::OrderedMap<
        String,
        Arc<crate::supporters::predicate_verification_unit::PredicateData>,
    >,
    snapshot_sorts: crate::state::package::OrderedMap<String, Sort>,
    snapshot_formals: crate::state::package::OrderedMap<String, Vec<Term>>,
}
impl NativeContext {
    /// Execute the actual main-verifier orchestration with one owned stdio solver.
    /// This first supported profile rejects constructs whose contributor, solver or
    /// worker services are not yet connected before starting any member proof.
    pub fn verify_program(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
        cfgs: &[SilverCfg],
    ) -> Result<
        Vec<VerificationResult<VerificationError>>,
        NativeError<crate::decider::prover_std_io::ProverError>,
    > {
        if !cfgs.is_empty() {
            return Err(NativeError::Unsupported("standalone CFG verification"));
        }
        crate::verifier::default_main_verifier::verify(self, program, cfgs, None)
    }
    fn initial_state(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
        member: ferrum_silver::ast::program::Member,
    ) -> Result<NativeState, NativeError<crate::decider::prover_std_io::ProverError>> {
        use ferrum_silver::ast::program::Member;
        let joins = match &member {
            Member::Method(method) => crate::supporters::annotation_supporter::join_mode(
                &method.name,
                &method.meta.info,
                |warning| {
                    self.warnings.push(warning);
                    Ok::<_, ()>(())
                },
            )
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?
            .unwrap_or(self.options.join_mode),
            _ => JoinMode::Off,
        };
        let mut state = State::new(
            program.clone(),
            analysis.predicates.clone(),
            Default::default(),
            joins,
            &self.factory,
            false,
            self.options.respect_function_pre_permission_amounts,
        );
        state.current_member = Some(member);
        state.predicate_snap_map = analysis.snapshot_sorts.clone();
        state.predicate_formal_var_map = analysis.snapshot_formals.clone();
        Ok(state)
    }
}
impl crate::verifier::default_main_verifier::MainVerificationServices for NativeContext {
    type Error = NativeError<crate::decider::prover_std_io::ProverError>;
    type Result = VerificationResult<VerificationError>;
    type Analysis = NativeAnalysis;
    type FunctionUnit = ferrum_silver::ast::program::Function;
    type PredicateUnit = ferrum_silver::ast::program::Predicate;
    type Task = Vec<VerificationResult<VerificationError>>;
    fn preprocess(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<ferrum_silver::ast::program::Program, Self::Error> {
        use ferrum_silver::ast::{
            expression::ExpKind,
            r#type::Type,
            utility::nodes::{Node, subnodes},
        };
        if !program.domains.is_empty()
            || !program.functions.is_empty()
            || !program.extensions.is_empty()
        {
            return Err(NativeError::Unsupported(
                "domain, function or program extension analysis",
            ));
        }
        if self.options.enable_simplified_unfolds {
            return Err(NativeError::Unsupported(
                "simplified predicate unfold recorder",
            ));
        }
        fn inspect(node: &Node) -> Result<(), &'static str> {
            if matches!(node, Node::Type(typ) if matches!(typ,Type::Seq(_) | Type::Set(_) | Type::Multiset(_) | Type::Map(_) | Type::Domain(_) | Type::Backend(_) | Type::Extension(_)))
            {
                return Err("collection or domain preamble analysis");
            }
            if matches!(node,Node::Exp(exp) if matches!(exp.kind(),ExpKind::Forall(..) | ExpKind::Exists(..) | ExpKind::ForPerm(..) | ExpKind::MagicWand(..) | ExpKind::Extension(_)))
            {
                return Err("quantifier, wand or extension preamble analysis");
            }
            for child in subnodes(node).map_err(|_| "program analysis traversal")? {
                inspect(&child)?;
            }
            Ok(())
        }
        inspect(&Node::Program(program.clone())).map_err(NativeError::Unsupported)?;
        self.active_program = Some(program.clone());
        Ok(program.clone())
    }
    fn setup_predicate_snapshots(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<(), Self::Error> {
        let mut generator =
            crate::supporters::qps::predicate_snap_generator::PredicateSnapGenerator::default();
        let symbols = self.base.symbol_converter.clone();
        let factory = self.factory.clone();
        generator
            .setup(&factory, &symbols, program, |body, program| {
                crate::supporters::snapshot_supporter::DefaultSnapshotSupporter {
                    symbols: &symbols,
                    factory: &factory,
                }
                .optimal_snapshot_sort::<()>(body, program)
            })
            .map_err(|e| NativeError::Snapshot(format!("{e:?}")))?;
        self.predicate_snapshots = generator;
        Ok(())
    }
    fn begin_preamble(&mut self, _: Option<&str>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_static_preamble(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn analyze_and_emit_contributions(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<NativeAnalysis, Self::Error> {
        let predicates = crate::supporters::predicate_verification_unit::analyze_predicates(
            program,
            &self.base.symbol_converter,
            &self.factory,
            Sort::Snap,
        )
        .map_err(NativeError::Sort)?;
        use crate::interfaces::{decider::prover::TextEmitter, preamble::PreambleReader};
        let reader = crate::decider::smt_lib2_preamble_reader::SmtLib2PreambleReader::default();
        for sort in [Sort::Int, Sort::Bool, Sort::Ref, Sort::Perm] {
            for (from, to) in [(sort.clone(), Sort::Snap), (Sort::Snap, sort.clone())] {
                let decl = self.factory.sort_wrapper_decl(from, to);
                self.base
                    .decider
                    .prover
                    .declare(&decl)
                    .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            }
            let sanitized = self
                .base
                .term_converter
                .convert_sanitized_sort(&sort)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            let rendered = self
                .base
                .term_converter
                .convert_sort(&sort)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            let substitutions = vec![("$S$".into(), sanitized), ("$T$".into(), rendered)];
            let commands = reader
                .read_parametric_preamble("/sortwrappers.smt2", &substitutions)
                .map_err(NativeError::Resource)?;
            self.base
                .decider
                .prover
                .emit_all(&commands)
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        crate::supporters::predicate_verification_unit::declare_predicate_triggers(
            &self.factory,
            &mut self.base.decider.prover,
            &predicates,
        )
        .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        Ok(NativeAnalysis {
            predicates,
            snapshot_sorts: self.predicate_snapshots.snap_map.clone(),
            snapshot_formals: self.predicate_snapshots.formal_var_map.clone(),
        })
    }
    fn end_preamble_and_saturate(&mut self) -> Result<(), Self::Error> {
        if let Some(ms) = self.options.after_prelude_timeout {
            self.base
                .decider
                .prover
                .saturate(ms, "after prelude")
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        Ok(())
    }
    fn function_units(&mut self) -> Result<Vec<Self::FunctionUnit>, Self::Error> {
        Ok(vec![])
    }
    fn predicate_units(&mut self) -> Result<Vec<Self::PredicateUnit>, Self::Error> {
        Ok(self
            .active_program
            .as_ref()
            .ok_or(NativeError::Unsupported("program analysis context"))?
            .predicates
            .clone())
    }
    fn verify_function(
        &mut self,
        _: Self::FunctionUnit,
        _: &ferrum_silver::ast::program::Program,
        _: &NativeAnalysis,
    ) -> Result<Vec<Self::Result>, Self::Error> {
        Err(NativeError::Unsupported("function verification"))
    }
    fn verify_predicate(
        &mut self,
        unit: Self::PredicateUnit,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
    ) -> Result<Vec<Self::Result>, Self::Error> {
        let data = analysis
            .predicates
            .get(&unit.name)
            .ok_or(NativeError::Unsupported("predicate analysis data"))?
            .clone();
        let state = self.initial_state(
            program,
            analysis,
            ferrum_silver::ast::program::Member::Predicate(unit),
        )?;
        let f = self.factory.clone();
        let result = crate::supporters::predicate_verification_unit::verify_predicate(
            &f, self, state, &data,
        )
        .map_err(|e| NativeError::Execution(format!("{e:?}")))?;
        Ok(flatten_results(result))
    }
    fn stop_main_prover(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn begin_worker_preamble(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn declare_predicate_sorts(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn declare_function_sorts(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn declare_predicate_symbols(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn declare_function_symbols(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_predicate_axioms(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn emit_function_axioms(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_worker_preamble(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn excluded_method(&mut self, _: &ferrum_silver::ast::program::Method) -> bool {
        false
    }
    fn queue_method(
        &mut self,
        method: &ferrum_silver::ast::program::Method,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
    ) -> Result<Self::Task, Self::Error> {
        let state = self.initial_state(
            program,
            analysis,
            ferrum_silver::ast::program::Member::Method(method.clone()),
        )?;
        crate::supporters::method_supporter::verify_method(self, state, method)
            .map_err(|e| NativeError::Execution(format!("{e:?}")))
    }
    fn queue_cfg(
        &mut self,
        _: &SilverCfg,
        _: &ferrum_silver::ast::program::Program,
        _: &NativeAnalysis,
    ) -> Result<Self::Task, Self::Error> {
        Err(NativeError::Unsupported("standalone CFG verification"))
    }
    fn await_task(&mut self, task: Self::Task) -> Result<Vec<Self::Result>, Self::Error> {
        Ok(flatten_results(task))
    }
    fn report_termination_and_optional_trace(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn run_optional_debugger(&mut self, _: &[Self::Result]) -> Result<(), Self::Error> {
        Ok(())
    }
}
fn flatten_results(
    values: Vec<VerificationResult<VerificationError>>,
) -> Vec<VerificationResult<VerificationError>> {
    let mut results = Vec::new();
    for result in values {
        results.push(result.clone());
        results.extend(result.previous());
    }
    results
}
