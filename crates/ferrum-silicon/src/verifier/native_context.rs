// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

//! Ferrum assembly described in PLAN.md.
//! Native verifier context connecting source rule algorithms to a real owned prover.
//! Upstream service composition:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/BaseVerifier.scala
//! Status: native execution connects the prover, basic heap and predicate operations,
//! function phases and calls, branching, loop invariants, method calls, collection and
//! domain preambles, quantified resources and magic-wand packaging/application.
//! Unsupported execution modes and resource operations return errors.

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
    pub after_unfold_timeout: Option<i32>,
    pub before_repetition_timeout: Option<i32>,
    pub enable_simplified_unfolds: bool,
    pub recursive_predicate_unfoldings: i32,
    pub disable_havoc_hack_407: bool,
    pub after_inhale_timeout: Option<i32>,
    pub enable_predicate_triggers_on_inhale: bool,
    pub disable_function_unfold_trigger: bool,
    pub exhale_mode: crate::config::ExhaleMode,
    pub exhale_mode_qp: crate::config::ExhaleMode,
    pub disable_short_circuiting: bool,
    pub error_limit: usize,
    pub respect_function_pre_permission_amounts: bool,
    pub qp_split_timeout: i32,
    pub assume_injectivity_on_inhale: bool,
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
            || config.disable_value_map_caching
            || config.disable_isc_triggers
            || config.disable_chunk_order_heuristics
            || config.disable_caches
            || config.simplify_on_consume
            || config.enable_branchcondition_reporting
            || config.alternative_function_verification_order
            || config.report_state_after.is_some()
        {
            return Err(NativeError::Unsupported(
                "requested timeout, logging, solver, worker, cache or encoding policy is not connected",
            ));
        }
        if config.include_methods != ".*" || !config.exclude_methods.is_empty() {
            return Err(NativeError::Unsupported(
                "method inclusion/exclusion filters",
            ));
        }
        let [prelude, contract, unfold, inhale, repetition] = config
            .saturation_weights
            .timeouts(config.prover_saturation_timeout);
        Ok(Self {
            unsafe_wildcard_optimization: config.unsafe_wildcard_optimization,
            disable_subsumption: config.disable_subsumption,
            join_mode: config.more_joins,
            after_prelude_timeout: prelude.map(|x| x.timeout_ms),
            after_contract_timeout: contract.map(|x| x.timeout_ms),
            after_unfold_timeout: unfold.map(|x| x.timeout_ms),
            before_repetition_timeout: repetition.map(|x| x.timeout_ms),
            enable_simplified_unfolds: config.enable_simplified_unfolds,
            recursive_predicate_unfoldings: config.recursive_predicate_unfoldings,
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
            qp_split_timeout: config.qp_split_timeout,
            assume_injectivity_on_inhale: config.frontend.assume_injectivity_on_inhale,
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
/// Non-owning handle: function units own the data, while recorders can refer back
/// to it without creating a cycle when the data retains phase recordings.
#[derive(Clone)]
pub struct NativeFunctionData(
    pub  std::sync::Weak<
        std::sync::Mutex<
            crate::supporters::functions::function_data::FunctionData<NativeFunctionData>,
        >,
    >,
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
    function_handles: crate::state::package::OrderedMap<String, Arc<FD>>,
    function_heights: std::collections::HashMap<String, i32>,
    function_fresh_variables: Vec<Term>,
    function_units: Vec<ferrum_silver::ast::program::Function>,
    failed_functions: std::collections::HashSet<String>,
    quantified_counter: u64,
    heap_supporter_counter: u64,
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
            function_handles: Default::default(),
            function_heights: Default::default(),
            function_fresh_variables: Vec::new(),
            function_units: Vec::new(),
            failed_functions: Default::default(),
            quantified_counter: 0,
            heap_supporter_counter: 0,
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
        crate::rules::magic_wand_supporter::evaluation_heap(self, state)
            .map_err(|e| NativeError::Execution(format!("wand evaluation heap: {e:?}")))
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
            // The synchronous else future is lazy and is forced by combine after the then branch.
            let then_result = run(self, decision.execute_then, true, yes)?;
            let branch_result = if then_result.continue_verification() {
                let else_result = run(self, decision.execute_else, false, no)?;
                then_result.combine(|| else_result, false)
            } else {
                then_result
            };
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
        let mut callback_error = None;
        let result = crate::rules::consumer::consume_all(
            self,
            state,
            std::slice::from_ref(assertion),
            false,
            &|_| error.clone(),
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
        result.map_err(|e| EvaluationError::Context(NativeError::Consumption(format!("{e:?}"))))
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
        let (state, amount) = crate::rules::heap_supporter::current_permission(
            self, state, &heap, resource, args, debug_args,
        )
        .map_err(EvaluationError::Context)?;
        continuation(self, state, amount)
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
        let (quantifier, vars, triggers, body) = match expression.kind() {
            ExpKind::Forall(vars, triggers, body) => (
                crate::state::terms::Quantifier::Forall,
                vars,
                triggers,
                body,
            ),
            ExpKind::Exists(vars, triggers, body) => (
                crate::state::terms::Quantifier::Exists,
                vars,
                triggers,
                body,
            ),
            _ => {
                return Err(EvaluationError::Context(NativeError::Unsupported(
                    "quantifier shape",
                )));
            }
        };
        crate::rules::evaluator::evaluate_quantified(
            self,
            state,
            quantifier,
            vars,
            &[],
            std::slice::from_ref(body),
            Some(triggers),
            name,
            error,
            &mut |ctx, state, data| {
                let result = if let Some(second) = data.second {
                    let mut terms = second.terms.into_iter();
                    let body = terms.next().ok_or(EvaluationError::InvalidJoinEntries)?;
                    if terms.next().is_some() {
                        return Err(EvaluationError::InvalidJoinEntries);
                    }
                    Some(QuantifiedExpressionData {
                        variables: data.variables,
                        variable_expressions: data.variable_expressions,
                        body,
                        body_expression: second.expressions.and_then(|mut exps| {
                            if exps.len() == 1 {
                                Some(exps.remove(0))
                            } else {
                                None
                            }
                        }),
                        triggers: second.triggers,
                        auxiliary_globals: second.auxiliary_globals,
                        auxiliary_non_globals: second.auxiliary_non_globals,
                        auxiliary_debug: second.auxiliary_debug,
                    })
                } else {
                    None
                };
                continuation(ctx, state, result)
            },
        )
    }
    fn heap_independent_auxiliaries(&mut self, terms: &[Term]) -> Result<Vec<Term>, Self::Error> {
        let factory = self.factory.clone();
        let mut result = Vec::new();
        for term in terms {
            result.extend(
                crate::supporters::quantifier_supporter::make_triggers_heap_independent(
                    &factory, self, term,
                )
                .map_err(|e| NativeError::Evaluation(format!("{e:?}")))?,
            );
        }
        Ok(result)
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
        for term in globals.iter().chain(non_globals) {
            self.assume_term(term)?;
        }
        Ok(())
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
            .check_smoke(true)
            .map_err(NativeError::Decider)
    }
    fn quantifier_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        expression: &Exp,
        error: &Self::PartialError,
    ) -> Result<VerificationResult<VerificationError>, Self::Error> {
        self.failure(
            error,
            ErrorReason::Internal {
                node: ferrum_silver::ast::utility::nodes::Node::Exp(expression.clone()),
                explanation: "Quantifier evaluation failed.".into(),
            },
            state.retry_level,
        )
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
        use crate::rules::joiner::{self, JoinDataEntry};
        let factory = self.factory.clone();
        self.base
            .decider
            .push_scope()
            .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
        let mark = self.base.decider.pcs.mark();
        let mut local = state.clone();
        local.under_join = true;
        let mut entries = Vec::new();
        let result = block(self, local, &mut |ctx, result_state, value, debug| {
            let path_conditions = ctx
                .base
                .decider
                .pcs
                .after(mark)
                .map_err(EvaluationError::Path)?;
            entries.push(JoinDataEntry {
                state: joiner::restore_state(result_state, &state),
                data: (value, debug),
                path_conditions,
            });
            Ok(VerificationResult::success())
        });
        let cleanup = self.base.decider.pop_scope().map_err(NativeError::Decider);
        let result = match (result, cleanup) {
            (Ok(value), Ok(())) => value,
            (Err(e), Ok(())) => return Err(e),
            (Err(e), Err(cleanup)) => {
                return Err(EvaluationError::TriggerCleanup {
                    evaluation: Box::new(e),
                    cleanup,
                });
            }
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
        let (merged, value, debug) = if entries.len() == 1 {
            let entry = &entries[0];
            (
                entry.state.clone(),
                entry.data.0.clone(),
                entry.data.1.clone(),
            )
        } else {
            let sort = self
                .base
                .symbol_converter
                .to_sort(&function.typ)
                .map_err(|e| EvaluationError::Context(NativeError::Sort(e)))?;
            let sorts: Vec<_> = args.iter().map(|arg| arg.sort().clone()).collect();
            let (target, _) = self
                .base
                .decider
                .fresh(
                    &factory,
                    &format!("joined_{}", function.name),
                    &sorts,
                    &sort,
                )
                .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
            let ApplicationTarget::Function(fun) = &target else {
                return Err(EvaluationError::Context(NativeError::Unsupported(
                    "function join symbol",
                )));
            };
            let value = factory.app(fun.clone(), args.to_vec());
            let mut merged = entries[0].state.clone();
            for entry in &entries[1..] {
                merged = merged
                    .merge_unconditional(&entry.state, &mut |warning| self.warnings.push(warning))
                    .map_err(|e| EvaluationError::Context(NativeError::State(e)))?;
            }
            merged.function_recorder = merged.function_recorder.record_path_symbol(target);
            for entry in &entries {
                let guard = factory.and(entry.path_conditions.branch_conditions());
                self.assume_term(&factory.implies(
                    guard,
                    factory.builtin_equals(value.clone(), entry.data.0.clone()),
                ))
                .map_err(EvaluationError::Context)?;
            }
            (merged, value, debug_exp.cloned())
        };
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
        use ferrum_silver::ast::{
            expression::ExpKind,
            utility::nodes::{Node, map_node_tree},
        };
        let preconditions = preconditions
            .iter()
            .map(|precondition| {
                let transformed = map_node_tree(&Node::Exp(precondition.clone()), &|node| {
                    if let Node::Exp(exp) = node {
                        if let ExpKind::Forall(vars, triggers, body) = exp.kind() {
                            if !triggers.is_empty() {
                                return Ok(Node::Exp(Exp::with_extra(
                                    ExpKind::Forall(vars.clone(), vec![], body.clone()),
                                    exp.metadata().clone(),
                                    exp.0.extra.clone(),
                                )));
                            }
                        }
                    }
                    Ok(node.clone())
                })
                .map_err(|e| {
                    EvaluationError::Context(NativeError::Diagnostic(format!(
                        "function precondition trigger rewriting: {e:?}"
                    )))
                })?;
                let Node::Exp(exp) = transformed else {
                    return Err(EvaluationError::Context(NativeError::Unsupported(
                        "function precondition rewrite result",
                    )));
                };
                Ok(exp)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let substitutions: Vec<_> = function
            .formal_args
            .iter()
            .zip(arguments)
            .map(|(formal, actual)| {
                (
                    Exp::new(ExpKind::LocalVar(formal.local_var()), formal.meta.clone()),
                    actual.clone(),
                )
            })
            .collect();
        let partial = PartialVerificationError::for_kind(
            VerificationErrorKind::PreconditionInAppFalse(application.clone()),
        )
        .with_reason_node_transformed(move |node| {
            ferrum_silver::ast::utility::nodes::replace_expressions(&node, &substitutions).map_err(
                |_| {
                    ferrum_silver::verifier::verification_result::DiagnosticError::Unsupported(
                        "function application error substitution",
                    )
                },
            )
        });
        let mut callback_error = None;
        let result = crate::rules::consumer::consume_all(
            self,
            state,
            &preconditions,
            true,
            &|_| partial.clone(),
            &mut |ctx, state, snapshot| match continuation(ctx, state, snapshot) {
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
        result.map_err(|e| EvaluationError::Context(NativeError::Consumption(format!("{e:?}"))))
    }
    fn function_snapshot_args(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        function: &ferrum_silver::ast::program::Function,
        arguments: &[Term],
        snapshot: &Term,
    ) -> Result<(Vec<Term>, Term), Self::Error> {
        let snapshot = self.factory.sort_wrapper(snapshot.clone(), Sort::Snap);
        Ok((vec![snapshot.clone()], snapshot))
    }
    fn heap_function(
        &mut self,
        function: &ferrum_silver::ast::program::Function,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<crate::state::terms::Applicable, Self::Error> {
        self.base
            .symbol_converter
            .heap_dependent_function(function, program, None)
            .map_err(NativeError::Sort)
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
        let sort = self
            .base
            .symbol_converter
            .to_sort(&declaration.typ)
            .map_err(NativeError::Sort)?;
        let term = self
            .base
            .decider
            .fresh_variable(&self.factory, &declaration.name, &sort, false, None)
            .map_err(NativeError::Decider)?;
        Ok((term, None))
    }
    fn for_perm_conditions(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &crate::state::terms::ResourceKey,
        variables: &[(Term, Option<Exp>)],
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<Vec<ForPermCondition>, Self::Error> {
        use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
        use crate::state::{
            heap::Heap,
            store::{MapBackedStore, Store},
        };
        use ferrum_silver::ast::{expression::LocalVar, r#type::Type};
        let factory = self.factory.clone();
        let name = |text: &str| {
            Exp::new(
                ExpKind::LocalVar(LocalVar::new(text.into(), Type::Bool, Default::default())),
                Default::default(),
            )
        };
        let source = native_quantified_source(resource);
        if state
            .is_quantified_resource(&source)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?
        {
            let mut out = Vec::new();
            for chunk in native_quantified_chunks(&state.h, resource) {
                let (vars, permission, map, value) = match &chunk {
                    Chunk::QuantifiedField(c) => (
                        c.quantified_vars(&factory),
                        c.permission(&factory),
                        c.snapshot_map().clone(),
                        c.value_at(&factory, args),
                    ),
                    Chunk::QuantifiedPredicate(c) => (
                        c.quantified_vars(&factory),
                        c.permission(&factory),
                        c.snapshot_map().clone(),
                        c.value_at(&factory, args),
                    ),
                    Chunk::QuantifiedMagicWand(c) => (
                        c.quantified_vars(&factory),
                        c.permission(&factory),
                        c.snapshot_map().clone(),
                        c.value_at(&factory, args),
                    ),
                    _ => return Err(NativeError::Unsupported("forperm quantified chunk")),
                };
                if vars.len() != args.len() {
                    return Err(NativeError::Unsupported("forperm resource arity"));
                }
                let substitutions = vars.into_iter().zip(args.iter().cloned()).collect();
                let permission = factory
                    .replace(&permission, &substitutions)
                    .map_err(|e| NativeError::Chunk(format!("forperm permission: {e:?}")))?;
                let condition = factory.and([
                    factory.resource_trigger(resource, map, args.to_vec()),
                    factory.is_positive_perm(permission),
                ]);
                out.push(ForPermCondition {
                    condition,
                    original: name("chunk has non-zero permission"),
                    rewritten: None,
                    variables: variables.iter().map(|(term, _)| term.clone()).collect(),
                    definitions: MapBackedStore::new(),
                    triggers: vec![crate::state::terms::Trigger { terms: vec![value] }],
                });
            }
            return Ok(out);
        }
        let mut out = Vec::new();
        for chunk in state.h.values() {
            let Chunk::Basic(chunk) = chunk else { continue };
            let same = match resource {
                ResourceKey::Field(field) => {
                    chunk.id_ref().0 == field.name
                        && chunk.resource_id() == crate::resources::resources::ResourceId::Field
                }
                ResourceKey::Predicate(predicate) => {
                    chunk.id_ref().0 == predicate.name
                        && chunk.resource_id() == crate::resources::resources::ResourceId::Predicate
                }
                ResourceKey::Wand(_) => false,
            };
            if !same {
                continue;
            }
            if args.len() != chunk.args_ref().len() {
                return Err(NativeError::Unsupported("forperm resource arity"));
            }
            let pairs: Vec<_> = args
                .iter()
                .cloned()
                .zip(chunk.args_ref().iter().cloned())
                .collect();
            let mut substitutions = std::collections::HashMap::new();
            let mut bindings = Vec::new();
            let mut chosen = Vec::new();
            for (variable, _) in variables {
                let pair = pairs.iter().find(|(arg, _)| arg == variable).ok_or(
                    NativeError::Unsupported("forperm variable is not a direct resource argument"),
                )?;
                let value = &pair.1;
                chosen.push(pair.clone());
                let local = state
                    .g
                    .values()
                    .iter()
                    .find(|(_, (term, _))| term == variable)
                    .map(|(local, _)| local.clone())
                    .ok_or(NativeError::Unsupported("forperm bound local"))?;
                substitutions.insert(variable.clone(), value.clone());
                bindings.push((local, (value.clone(), None)));
            }
            let mut equalities = Vec::new();
            for (arg, value) in pairs {
                if chosen.contains(&(arg.clone(), value.clone())) {
                    continue;
                }
                equalities.push(
                    factory.equals(
                        factory
                            .replace(&arg, &substitutions)
                            .map_err(|e| NativeError::Chunk(format!("forperm argument: {e:?}")))?,
                        value,
                    ),
                );
            }
            equalities.push(factory.is_positive_perm(chunk.permission(&factory)));
            out.push(ForPermCondition {
                condition: factory.and(equalities),
                original: name("chunk matches forperm pattern and has positive permission"),
                rewritten: None,
                variables: vec![],
                definitions: MapBackedStore::from_bindings(bindings),
                triggers: vec![],
            });
        }
        Ok(out)
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
        if let ExpKind::Asserting(assertion, in_expression) = expression.kind() {
            let original_store = state.g.clone();
            let original_heap = state.h.clone();
            let mut callback_error = None;
            let result = crate::rules::consumer::consume_all(
                self,
                state,
                std::slice::from_ref(assertion),
                false,
                &|_| error.clone(),
                &mut |ctx, mut state, _| {
                    state.g = original_store.clone();
                    state.h = original_heap.clone();
                    match crate::rules::evaluator::evaluate(
                        ctx,
                        state,
                        in_expression,
                        error,
                        continuation,
                    ) {
                        Ok(value) => Ok(value),
                        Err(e) => {
                            callback_error = Some(e);
                            Err(ConsumptionError::Context(NativeError::ContinuationAbort))
                        }
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            return result.map_err(|e| {
                EvaluationError::Context(NativeError::Consumption(format!(
                    "asserting expression: {e:?}"
                )))
            });
        }
        if let ExpKind::Applying(wand, in_expression) = expression.kind() {
            return self.join_applying_expression(state, wand, in_expression, error, continuation);
        }
        let ExpKind::Unfolding(access, in_expression) = expression.kind() else {
            return Err(EvaluationError::Context(NativeError::Unsupported(
                "evaluate_special",
            )));
        };
        let ExpKind::PredicateAccessPredicate(pap) = access.kind() else {
            return Err(EvaluationError::InvalidResourceAccess);
        };
        let predicate = state
            .program
            .find_predicate(&pap.location.predicate_name)
            .map_err(|_| EvaluationError::MissingPredicate(pap.location.predicate_name.clone()))?
            .clone();
        if (state.cycles(&ferrum_silver::ast::program::Member::Predicate(
            predicate.clone(),
        )) as i64)
            >= i64::from(self.options.recursive_predicate_unfoldings)
        {
            let sort = self
                .base
                .symbol_converter
                .to_sort(
                    &in_expression
                        .typ()
                        .map_err(EvaluationError::ExpressionType)?,
                )
                .map_err(|e| EvaluationError::Context(NativeError::Sort(e)))?;
            let args: Vec<_> = state
                .all_relevant_quantified_variables()
                .into_iter()
                .map(|(term, _)| term)
                .collect();
            let sorts: Vec<_> = args.iter().map(|term| term.sort().clone()).collect();
            let (target, _) = self
                .base
                .decider
                .fresh(&self.factory, "recunf", &sorts, &sort)
                .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
            let term = match &target {
                ApplicationTarget::Function(f) => self.factory.app(f.clone(), args),
                _ => {
                    return Err(EvaluationError::Context(NativeError::Unsupported(
                        "recursive unfold symbol",
                    )));
                }
            };
            let mut state = state;
            state.function_recorder = state.function_recorder.record_fresh_snapshot(target);
            return continuation(self, state, term, None);
        }
        let permission = pap.permission_or_full();
        crate::rules::evaluator::evaluate_all(
            self,
            state,
            &pap.location.args,
            &|_| error.clone(),
            &mut |ctx, state, args, _| {
                let arps = state.constrainable_arps.clone();
                crate::rules::evaluator::evaluate(
                    ctx,
                    state,
                    &permission,
                    error,
                    &mut |ctx, state, amount, _| {
                        let positive = ctx.factory.is_positive_perm(amount.clone());
                        let proven = ctx
                            .base
                            .decider
                            .check(&positive, ctx.base.decider.assert_timeout)
                            .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
                        if !proven {
                            return ctx
                                .failure(
                                    error,
                                    ErrorReason::NonPositivePermission(permission.clone()),
                                    state.retry_level,
                                )
                                .map_err(EvaluationError::Context);
                        }
                        ctx.join_unfold_expression(
                            state,
                            &predicate,
                            access,
                            in_expression,
                            &args,
                            &amount,
                            &arps,
                            error,
                            continuation,
                        )
                    },
                )
            },
        )
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
        // Only ordinary wand production reevaluates resource arguments and needs an
        // error context; fields and predicates are already evaluated by the producer.
        let full = match resource {
            ResourceKey::Wand(w) => Some(
                error
                    .due_to(ErrorReason::MagicWandChunkNotFound(
                        w.ghost_free_wand.clone(),
                    ))
                    .map_err(|e| {
                        ProductionError::Context(NativeError::Diagnostic(format!("{e:?}")))
                    })?,
            ),
            _ => None,
        };
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
            &full,
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
        if join {
            return self.joined_production(
                state,
                condition,
                original,
                rewritten,
                consolidate_on_merge,
                when_true,
                when_false,
                continuation,
            );
        }
        let saved_error = std::cell::RefCell::new(None);
        let continuation = std::cell::RefCell::new(continuation);
        let result = crate::rules::executor::CfgContext::branch_edge(
            self,
            state,
            condition,
            original,
            rewritten,
            &mut |ctx, state| {
                let outcome = when_true(ctx, state, &mut |ctx, state| {
                    let mut callback = continuation.try_borrow_mut().map_err(|_| {
                        ProductionError::Context(NativeError::Unsupported(
                            "reentrant production continuation",
                        ))
                    })?;
                    callback(ctx, state)
                });
                match outcome {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        *saved_error.borrow_mut() = Some(e);
                        Err(ExecutionError::Context(NativeError::ContinuationAbort))
                    }
                }
            },
            &mut |ctx, state| {
                let outcome = when_false(ctx, state, &mut |ctx, state| {
                    let mut callback = continuation.try_borrow_mut().map_err(|_| {
                        ProductionError::Context(NativeError::Unsupported(
                            "reentrant production continuation",
                        ))
                    })?;
                    callback(ctx, state)
                });
                match outcome {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        *saved_error.borrow_mut() = Some(e);
                        Err(ExecutionError::Context(NativeError::ContinuationAbort))
                    }
                }
            },
        );
        if let Some(error) = saved_error.into_inner() {
            return Err(error);
        }
        result.map_err(|e| ProductionError::Context(NativeError::Execution(format!("{e:?}"))))
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
        let mut callback_error = None;
        let result = self.handle_native_let(
            state,
            assertion,
            error,
            crate::state::store::MapBackedStore::default(),
            &mut |ctx, state, bindings, body| match continuation(ctx, state, bindings, body) {
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
        let mut callback_error = None;
        let result = self.evaluate_native_quantified_permission(
            state,
            forall,
            condition,
            permission,
            arguments,
            qid,
            error,
            &mut |ctx, state, data| match continuation(ctx, state, data) {
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
        use crate::rules::quantified_chunk_support::{
            GeneralProductionInput, GeneralProductionOutcome, SnapshotResource,
        };
        let source = match resource {
            ResourceKey::Field(field) => SnapshotResource::Field(field.clone()),
            ResourceKey::Predicate(predicate) => SnapshotResource::Predicate(predicate.clone()),
            ResourceKey::Wand(wand) => SnapshotResource::Wand(wand.ghost_free_wand.clone()),
        };
        let formals = state
            .formal_arg_vars(&source, &self.base.symbol_converter, &self.factory)
            .map_err(|e| ProductionError::Context(NativeError::Diagnostic(format!("{e:?}"))))?;
        let sort = match resource {
            ResourceKey::Field(field) => Sort::FieldValueFunction {
                codomain: Box::new(
                    self.base
                        .symbol_converter
                        .to_sort(&field.typ)
                        .map_err(|e| ProductionError::Context(NativeError::Sort(e)))?,
                ),
                field_name: field.name.clone(),
            },
            ResourceKey::Predicate(predicate) => Sort::PredicateSnapFunction {
                codomain: Box::new(
                    state
                        .predicate_snap_map
                        .get(&predicate.name)
                        .cloned()
                        .ok_or(ProductionError::Context(NativeError::Unsupported(
                            "predicate snapshot sort",
                        )))?,
                ),
                predicate_name: predicate.name.clone(),
            },
            ResourceKey::Wand(wand) => Sort::PredicateSnapFunction {
                codomain: Box::new(Sort::MagicWandSnapFunction),
                predicate_name: wand.to_string(),
            },
        };
        let snapshot_map = self
            .snapshot_term(snapshot, sort)
            .map_err(ProductionError::Context)?;
        let (_, _, access) =
            ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(
                forall,
            )
            .ok_or(ProductionError::Context(NativeError::Unsupported(
                "quantified permission shape",
            )))?;
        let permission = access.permission_or_full().ok_or(ProductionError::Context(
            NativeError::Unsupported("quantified permission expression"),
        ))?;
        let has_explicit_triggers =
            matches!(forall.kind(), ExpKind::Forall(_, triggers, _) if !triggers.is_empty());
        let failure = NativeQuantifiedProductionError {
            partial: error.clone(),
            permission,
            access,
        };
        let input = GeneralProductionInput {
            qvars: data.qvars.clone(),
            qvar_exps: data.qvar_expressions.clone(),
            formal_vars: formals,
            formal_var_exps: None,
            qid: qid.into(),
            has_explicit_triggers,
            triggers: data.triggers.clone(),
            aux_globals: data.auxiliary_globals.clone(),
            aux_non_globals: data.auxiliary_non_globals.clone(),
            condition: data.condition.clone(),
            condition_exp: data.condition_exp.clone(),
            args: data.arguments.clone(),
            arg_exps: data.argument_expressions.clone(),
            snapshot_map,
            permission: data.permission.clone(),
            permission_exp: data.permission_exp.clone(),
            debugging: false,
        };
        let factory = self.factory.clone();
        match crate::rules::quantified_chunk_support::produce_general_quantified(
            &factory, self, state, resource, input, &failure,
        )
        .map_err(|e| {
            ProductionError::Context(NativeError::Chunk(format!("quantified production: {e:?}")))
        })? {
            GeneralProductionOutcome::Produced(state) => continuation(self, state),
            GeneralProductionOutcome::Failed(result) => Ok(result),
        }
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

impl<S: Prover, PD, FD> crate::supporters::functions::heap_access_replacing_expression_translator::HeapExpressionServices
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;

    fn fresh_unresolved(&mut self, sort: &Sort, _: &Exp) -> Result<Term, Self::Error> {
        let variable = self.base.decider.fresh_variable(&self.factory, "$unresolved", sort, false, None)
            .map_err(NativeError::Decider)?;
        self.function_fresh_variables.push(variable.clone());
        Ok(variable)
    }

    fn warn_unresolved(&mut self, expression: &Exp, function: &ferrum_silver::ast::program::Function) -> Result<(), Self::Error> {
        self.warnings.push(format!("Could not resolve expression {expression:?} during axiomatisation of function {}; it is replaced by a fresh symbol", function.name));
        Ok(())
    }

    fn stop_on_unresolved(&self, _: &Exp, _: &ferrum_silver::ast::program::Function) -> bool { false }

    fn callee_height(&self, name: &str) -> Option<i32> { self.function_heights.get(name).copied() }

    fn heap_function(&mut self, function: &ferrum_silver::ast::program::Function, program: &ferrum_silver::ast::program::Program) -> Result<crate::state::terms::Applicable, Self::Error> {
        self.base.symbol_converter.heap_dependent_function(function, program, None).map_err(NativeError::Sort)
    }

    fn translate_heap_function_application(&mut self, function: crate::state::terms::Applicable, snapshot: Term, args: Vec<Term>, _: &ferrum_silver::ast::program::Function, _: &ferrum_silver::ast::program::Program) -> Result<Term, Self::Error> {
        Ok(crate::supporters::functions::function_encoding::DefaultFunctionEncoding::translate_function_application(&self.factory, function, snapshot, &args))
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
            return Ok(state);
        }
        let resource = match assertion.kind() {
            ExpKind::FieldAccessPredicate(access, _) => {
                ResourceKey::Field(Arc::new(access.field.clone()))
            }
            ExpKind::FieldAccess(access) => ResourceKey::Field(Arc::new(access.field.clone())),
            ExpKind::PredicateAccessPredicate(access) => ResourceKey::Predicate(Arc::new(
                state
                    .program
                    .find_predicate(&access.location.predicate_name)
                    .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?
                    .clone(),
            )),
            ExpKind::PredicateAccess(access) => ResourceKey::Predicate(Arc::new(
                state
                    .program
                    .find_predicate(&access.predicate_name)
                    .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?
                    .clone(),
            )),
            ExpKind::MagicWand(..) => ResourceKey::Wand(
                crate::state::chunks::MagicWandIdentifier::new(assertion.clone(), &state.program)
                    .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?,
            ),
            _ => return Err(NativeError::Unsupported("resource trigger access shape")),
        };
        if !state.heap_dependent_triggers.contains(&resource) {
            return Ok(state);
        }
        let source = native_quantified_source(&resource);
        let formals = state
            .formal_arg_vars(&source, &self.base.symbol_converter, &self.factory)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        let chunks = native_quantified_chunks(&state.h, &resource);
        let (definition, cache) = crate::rules::quantified_chunk_support::GeneralConsumptionExecution::summarise_general_consumed(self, &state, &resource, &formals, &chunks, None)?;
        self.assume_term(&self.factory.resource_trigger(
            &resource,
            definition.snapshot_map.clone(),
            args.to_vec(),
        ))?;
        let mut state = state;
        state.sm_cache = cache;
        state.function_recorder = state.function_recorder.record_fvf_and_domain(definition);
        Ok(state)
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
        let reason = if matches!(assertion.kind(), ExpKind::MagicWand(..)) {
            ErrorReason::MagicWandChunkNotFound(assertion.clone())
        } else {
            ErrorReason::InsufficientPermission(location)
        };
        let full = error
            .due_to(reason)
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
        crate::rules::magic_wand_supporter::evaluation_heap(self, state)
            .map_err(|e| NativeError::Execution(format!("wand evaluation heap: {e:?}")))
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
        if join {
            return self.joined_consumption(
                state,
                condition,
                original,
                rewritten,
                return_snapshot,
                when_true,
                when_false,
                continuation,
            );
        }
        let saved_error = std::cell::RefCell::new(None);
        let continuation = std::cell::RefCell::new(continuation);
        let result = crate::rules::executor::CfgContext::branch_edge(
            self,
            state,
            condition,
            original,
            rewritten,
            &mut |ctx, state| {
                let outcome = when_true(ctx, state, &mut |ctx, state, heap, snapshot| {
                    let mut callback = continuation.try_borrow_mut().map_err(|_| {
                        ConsumptionError::Context(NativeError::Unsupported(
                            "reentrant consumption continuation",
                        ))
                    })?;
                    callback(ctx, state, heap, snapshot)
                });
                match outcome {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        *saved_error.borrow_mut() = Some(e);
                        Err(ExecutionError::Context(NativeError::ContinuationAbort))
                    }
                }
            },
            &mut |ctx, state| {
                let outcome = when_false(ctx, state, &mut |ctx, state, heap, snapshot| {
                    let mut callback = continuation.try_borrow_mut().map_err(|_| {
                        ConsumptionError::Context(NativeError::Unsupported(
                            "reentrant consumption continuation",
                        ))
                    })?;
                    callback(ctx, state, heap, snapshot)
                });
                match outcome {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        *saved_error.borrow_mut() = Some(e);
                        Err(ExecutionError::Context(NativeError::ContinuationAbort))
                    }
                }
            },
        );
        if let Some(error) = saved_error.into_inner() {
            return Err(error);
        }
        result.map_err(|e| ConsumptionError::Context(NativeError::Execution(format!("{e:?}"))))
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
        let mut callback_error = None;
        let result = self.handle_native_let(
            state,
            assertion,
            error,
            crate::state::store::MapBackedStore::default(),
            &mut |ctx, state, bindings, body| match continuation(ctx, state, bindings, body) {
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
        let mut callback_error = None;
        let result = self.evaluate_native_quantified_permission(
            state,
            forall,
            condition,
            permission,
            arguments,
            qid,
            error,
            &mut |ctx, state, data| match continuation(ctx, state, data) {
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
        use crate::rules::quantified_chunk_support::{
            GeneralConsumptionExecutionError, GeneralConsumptionPreparation,
            GeneralProductionInput, SnapshotResource,
        };
        let source = match resource {
            ResourceKey::Field(field) => SnapshotResource::Field(field.clone()),
            ResourceKey::Predicate(predicate) => SnapshotResource::Predicate(predicate.clone()),
            ResourceKey::Wand(wand) => SnapshotResource::Wand(wand.ghost_free_wand.clone()),
        };
        let formals = state
            .formal_arg_vars(&source, &self.base.symbol_converter, &self.factory)
            .map_err(|e| ConsumptionError::Context(NativeError::Diagnostic(format!("{e:?}"))))?;
        let identifier = match resource {
            ResourceKey::Field(f) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(f.name.clone()))
            }
            ResourceKey::Predicate(p) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(p.name.clone()))
            }
            ResourceKey::Wand(w) => ChunkIdentifier::Wand(w.clone()),
        };
        let (_, _, access) =
            ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(
                forall,
            )
            .ok_or(ConsumptionError::Context(NativeError::Unsupported(
                "quantified permission shape",
            )))?;
        let permission = access
            .permission_or_full()
            .ok_or(ConsumptionError::Context(NativeError::Unsupported(
                "quantified permission expression",
            )))?;
        let failure = NativeQuantifiedProductionError {
            partial: error.clone(),
            permission,
            access,
        };
        let has_explicit_triggers =
            matches!(forall.kind(), ExpKind::Forall(_, triggers, _) if !triggers.is_empty());
        let input = GeneralProductionInput {
            qvars: data.qvars.clone(),
            qvar_exps: data.qvar_expressions.clone(),
            formal_vars: formals,
            formal_var_exps: None,
            qid: qid.into(),
            has_explicit_triggers,
            triggers: data.triggers.clone(),
            aux_globals: data.auxiliary_globals.clone(),
            aux_non_globals: data.auxiliary_non_globals.clone(),
            condition: data.condition.clone(),
            condition_exp: data.condition_exp.clone(),
            args: data.arguments.clone(),
            arg_exps: data.argument_expressions.clone(),
            // The shared input's snapshot map is consumed only by production; preparation never reads it.
            snapshot_map: self.factory.unit(),
            permission: data.permission.clone(),
            permission_exp: data.permission_exp.clone(),
            debugging: false,
        };
        let factory = self.factory.clone();
        let plan =
            match crate::rules::quantified_chunk_support::prepare_general_quantified_consumption(
                &factory,
                self,
                state,
                &heap,
                resource,
                &identifier,
                input,
                &failure,
            )
            .map_err(|e| {
                ConsumptionError::Context(NativeError::Chunk(format!(
                    "quantified consumption preparation: {e:?}"
                )))
            })? {
                GeneralConsumptionPreparation::Ready(plan) => plan,
                GeneralConsumptionPreparation::Failed(result) => return Ok(result),
            };
        let mut callback_error = None;
        let result = crate::rules::quantified_chunk_support::execute_general_quantified_consumption(
            &factory,
            self,
            plan,
            heap,
            resource,
            &identifier,
            return_snapshot,
            &failure,
            &mut |ctx, state, heap, snapshot| match continuation(ctx, state, heap, snapshot) {
                Ok(result) => Ok(result),
                Err(e) => {
                    callback_error = Some(e);
                    Err(GeneralConsumptionExecutionError::Service(
                        NativeError::ContinuationAbort,
                    ))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| {
            ConsumptionError::Context(NativeError::Chunk(format!("quantified consumption: {e:?}")))
        })
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
            Chunk::QuantifiedField(c) if c.singleton_rcvr_ref().is_some() => c.resource_id(),
            Chunk::QuantifiedPredicate(c) if c.singleton_args_ref().is_some() => c.resource_id(),
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
                _ => {
                    let factory = self.factory.clone();
                    let result =
                        if self.options.exhale_mode_qp == crate::config::ExhaleMode::MoreComplete {
                            crate::rules::quantified_chunk_support::find_quantified_chunk_complete(
                                &factory, self, chunks, incoming,
                            )
                        } else {
                            crate::rules::quantified_chunk_support::find_quantified_chunk_greedy(
                                &factory, self, chunks, incoming,
                            )
                        };
                    result.map_err(|e| {
                        NativeError::Chunk(format!("quantified merge candidate: {e:?}"))
                    })
                }
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
        let factory = self.factory.clone();
        crate::rules::state_consolidator::merge_quantified_pair(
            &factory, self, state, recorder, first, second, qvars,
        )
        .map_err(|e| NativeError::Chunk(format!("quantified chunk merge: {e:?}")))
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
            let factory = self.factory.clone();
            crate::rules::state_consolidator::assume_quantified_field_bounds(
                &factory,
                self,
                state,
                heaps,
                &factory.predef_receiver_var(),
            )
            .map_err(|e| NativeError::Consolidation(format!("quantified field bounds: {e:?}")))
        }
    }
    fn assume_more_complete_field_bounds(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<(), Self::Error> {
        use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk};
        use crate::state::heap::Heap;
        let mut groups: Vec<(String, Vec<crate::state::chunks::BasicChunk>)> = Vec::new();
        for chunk in state.h.values() {
            if let Chunk::Basic(chunk) = chunk {
                if chunk.resource_id() == crate::resources::resources::ResourceId::Field {
                    let name = chunk.id_ref().0.clone();
                    if let Some((_, values)) = groups.iter_mut().find(|(id, _)| id == &name) {
                        values.push(chunk.clone());
                    } else {
                        groups.push((name, vec![chunk.clone()]));
                    }
                }
            }
        }
        let factory = self.factory.clone();
        let receiver = factory.var(
            crate::state::identifiers::Identifier::new("?rcvr"),
            Sort::Ref,
            false,
        );
        for (_, chunks) in groups {
            let mut sum = factory.no_perm();
            for chunk in &chunks {
                let arg = chunk
                    .args()
                    .first()
                    .ok_or(NativeError::Unsupported("field chunk receiver"))?;
                let equal = factory.builtin_equals(receiver.clone(), arg.clone());
                sum = factory.perm_plus(
                    sum,
                    factory.ite(equal, chunk.permission(&factory), factory.no_perm()),
                );
            }
            for chunk in chunks {
                let arg = chunk
                    .args()
                    .first()
                    .ok_or(NativeError::Unsupported("field chunk receiver"))?;
                let instantiated = factory
                    .replace(
                        &sum,
                        &std::collections::HashMap::from([(receiver.clone(), arg.clone())]),
                    )
                    .map_err(|e| {
                        NativeError::Consolidation(format!("field bound substitution: {e:?}"))
                    })?;
                self.assume_term(&factory.perm_at_most(instantiated, factory.full_perm()))?;
            }
        }
        Ok(())
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
        use crate::interfaces::state::chunks::GeneralChunk;
        use crate::state::heap::Heap;
        use crate::state::package::{
            NonQuantifiedChunkKey as C, SnapshotSummary, SnapshotSummaryKey,
        };
        let identifier = match resource {
            ResourceKey::Field(f) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(f.name.clone()))
            }
            ResourceKey::Predicate(p) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(p.name.clone()))
            }
            ResourceKey::Wand(w) => ChunkIdentifier::Wand(w.clone()),
        };
        let chunks: Vec<_> = heap
            .values()
            .iter()
            .filter_map(|chunk| match chunk {
                Chunk::Basic(c) if c.identifier() == identifier => Some(C::Basic(c.clone())),
                Chunk::MagicWand(c) if c.identifier() == identifier => Some(C::Wand(c.clone())),
                _ => None,
            })
            .collect();
        if !state.assert_read_access_only {
            return self.complete_consume_exact(
                state,
                heap,
                resource,
                args,
                permission,
                return_snapshot,
                error,
                continuation,
            );
        }
        let factory = self.factory.clone();
        let (state, snapshot, available) = if return_snapshot {
            let (state, snapshot, sum) = self
                .complete_lookup_summary(state, resource, &chunks, args, None)
                .map_err(ChunkExecutionError::Context)?;
            (state, Some(snapshot), sum)
        } else {
            let mut state = state;
            let key = SnapshotSummaryKey {
                resource: native_quantified_source(resource),
                chunks: chunks.clone(),
                arguments: args.to_vec(),
            };
            let sum = if let Some(summary) = state.ss_cache.get(&key) {
                summary.permission.clone()
            } else {
                let sum = crate::rules::more_complete_exhale_supporter::permission_sum(
                    &factory, &chunks, args,
                );
                state.ss_cache.insert(
                    key,
                    SnapshotSummary {
                        tagged_snapshot: None,
                        definitions: None,
                        permission: sum.clone(),
                        permission_exp: None,
                    },
                );
                sum
            };
            (state, None, sum)
        };
        let goal = factory.implies(
            factory.is_positive_perm(permission.clone()),
            factory.is_positive_perm(available),
        );
        if self
            .base
            .decider
            .check(&goal, self.base.decider.assert_timeout)
            .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?
        {
            continuation(self, state, heap, snapshot)
        } else {
            self.consumption_failure(&state, error, "complete read permission", true)
                .map_err(ChunkExecutionError::Context)
        }
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
        use crate::rules::magic_wand_supporter::WandTransferError as WE;
        let full = error
            .clone()
            .ok_or(ChunkExecutionError::Context(NativeError::Unsupported(
                "wand transfer failure context",
            )))?;
        let failure = self
            .failure_full(full, state.retry_level)
            .map_err(ChunkExecutionError::Context)?;
        let factory = self.factory.clone();
        let mut callback_error = None;
        let result = crate::rules::magic_wand_supporter::transfer(
            &factory,
            self,
            state,
            permission.clone(),
            debug_permission.cloned(),
            failure,
            &[],
            &mut |ctx, state, heap, needed, needed_exp| {
                let result = crate::rules::chunk_supporter::consume_greedy(
                    ctx, state, heap, identifier, args, needed, needed_exp,
                )
                .map_err(|e| NativeError::Chunk(format!("wand transfer consume: {e:?}")))?;
                Ok((result.result, result.state, result.heap, result.taken))
            },
            &mut |ctx, state, chunks| match continuation(ctx, state, chunks) {
                Ok(result) => Ok(result),
                Err(e) => {
                    callback_error = Some(e);
                    Err(WE::Service(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| {
            ChunkExecutionError::Context(NativeError::Execution(format!("wand transfer: {e:?}")))
        })
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
        use crate::state::heap::Heap;
        use crate::state::package::NonQuantifiedChunkKey as C;
        let identifier = match resource {
            ResourceKey::Field(f) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(f.name.clone()))
            }
            ResourceKey::Predicate(p) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(p.name.clone()))
            }
            ResourceKey::Wand(w) => ChunkIdentifier::Wand(w.clone()),
        };
        use crate::interfaces::state::chunks::GeneralChunk;
        let chunks: Vec<_> = heap
            .values()
            .iter()
            .filter_map(|chunk| match chunk {
                Chunk::Basic(c) if c.identifier() == identifier => Some(C::Basic(c.clone())),
                Chunk::MagicWand(c) if c.identifier() == identifier => Some(C::Wand(c.clone())),
                _ => None,
            })
            .collect();
        if chunks.is_empty() {
            if self
                .base
                .decider
                .check_smoke(true)
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?
            {
                if state.is_in_package {
                    let sort = self
                        .resource_snapshot_sort(&state, resource)
                        .map_err(ChunkExecutionError::Context)?;
                    let (snapshot, _) = self
                        .fresh_snapshot(&sort)
                        .map_err(ChunkExecutionError::Context)?;
                    return continuation(self, state, snapshot);
                }
                return Ok(VerificationResult::success());
            }
            return self
                .consumption_failure(&state, error, "branch is dead", true)
                .map_err(ChunkExecutionError::Context);
        }
        let (state, snapshot, permission) = self
            .complete_lookup_summary(state, resource, &chunks, args, None)
            .map_err(ChunkExecutionError::Context)?;
        let positive = self.factory.is_positive_perm(permission);
        if self
            .base
            .decider
            .check(&positive, self.base.decider.assert_timeout)
            .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?
        {
            continuation(self, state, snapshot)
        } else {
            self.consumption_failure(&state, error, "complete lookup permission", true)
                .map_err(ChunkExecutionError::Context)
        }
    }
    fn resource_snapshot_sort(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &crate::state::terms::ResourceKey,
    ) -> Result<crate::state::terms::Sort, Self::Error> {
        match resource {
            ResourceKey::Field(field) => self
                .base
                .symbol_converter
                .to_sort(&field.typ)
                .map_err(NativeError::Sort),
            ResourceKey::Predicate(predicate) => {
                if let Some(sort) = state.predicate_snap_map.get(&predicate.name) {
                    return Ok(sort.clone());
                }
                match &predicate.body {
                    None => Ok(Sort::Snap),
                    Some(body) => crate::supporters::snapshot_supporter::DefaultSnapshotSupporter {
                        symbols: &self.base.symbol_converter,
                        factory: &self.factory,
                    }
                    .optimal_snapshot_sort::<()>(body, &state.program)
                    .map(|(sort, _)| sort)
                    .map_err(|e| NativeError::Snapshot(format!("{e:?}"))),
                }
            }
            ResourceKey::Wand(_) => Ok(Sort::MagicWandSnapFunction),
        }
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
        use crate::rules::quantified_chunk_support::SnapshotResource;
        let source_resource = match resource {
            ResourceKey::Field(field) => SnapshotResource::Field(field.clone()),
            ResourceKey::Predicate(predicate) => SnapshotResource::Predicate(predicate.clone()),
            ResourceKey::Wand(wand) => SnapshotResource::Wand(wand.ghost_free_wand.clone()),
        };
        let formals = state
            .formal_arg_vars(&source_resource, &self.base.symbol_converter, &self.factory)
            .map_err(|e| ChunkExecutionError::Context(NativeError::Diagnostic(format!("{e:?}"))))?;
        let factory = self.factory.clone();
        let next = crate::rules::quantified_chunk_support::produce_single_quantified_location(
            &factory,
            self,
            state,
            resource,
            source_resource,
            formals,
            None,
            args.to_vec(),
            debug_args.map(|items| items.to_vec()),
            snapshot,
            permission,
            debug_permission,
            merge_and_trigger,
            false,
        )
        .map_err(|e| {
            ChunkExecutionError::Context(NativeError::Chunk(format!(
                "quantified production: {e:?}"
            )))
        })?;
        continuation(self, next)
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
        use crate::rules::quantified_chunk_support::{SingleConsumptionError, SnapshotResource};
        let source = match resource {
            ResourceKey::Field(field) => SnapshotResource::Field(field.clone()),
            ResourceKey::Predicate(predicate) => SnapshotResource::Predicate(predicate.clone()),
            ResourceKey::Wand(wand) => SnapshotResource::Wand(wand.ghost_free_wand.clone()),
        };
        let variables = state
            .formal_arg_vars(&source, &self.base.symbol_converter, &self.factory)
            .map_err(|e| ChunkExecutionError::Context(NativeError::Diagnostic(format!("{e:?}"))))?;
        let identifier = match resource {
            ResourceKey::Field(f) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(f.name.clone()))
            }
            ResourceKey::Predicate(p) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(p.name.clone()))
            }
            ResourceKey::Wand(w) => ChunkIdentifier::Wand(w.clone()),
        };
        let factory = self.factory.clone();
        let mut callback_error = None;
        let result = crate::rules::quantified_chunk_support::consume_single_quantified_location(
            &factory,
            self,
            state,
            heap,
            resource,
            &identifier,
            &variables,
            None,
            args,
            debug_args,
            permission,
            debug_permission,
            return_snapshot,
            error,
            &mut |ctx, state, heap, snapshot| match continuation(ctx, state, heap, snapshot) {
                Ok(value) => Ok(value),
                Err(e) => {
                    callback_error = Some(e);
                    Err(SingleConsumptionError::Service(
                        NativeError::ContinuationAbort,
                    ))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| {
            ChunkExecutionError::Context(NativeError::Chunk(format!(
                "quantified single consumption: {e:?}"
            )))
        })
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
        let ResourceKey::Wand(wand) = resource else {
            return Err(ChunkExecutionError::Context(NativeError::Unsupported(
                "non-wand chunk creation",
            )));
        };
        let full = error
            .clone()
            .ok_or(ChunkExecutionError::Context(NativeError::Unsupported(
                "wand error context",
            )))?;
        let partial = PartialVerificationError::new(move |reason| Ok(full.with_reason(reason)));
        let snapshot = if matches!(
            snapshot.kind(),
            crate::state::terms::TermKind::MagicWandSnapshot(_)
        ) {
            snapshot
        } else {
            self.factory.magic_wand_snapshot(
                self.factory
                    .sort_wrapper(snapshot, Sort::MagicWandSnapFunction),
            )
        };
        let mut callback_error = None;
        let result = crate::rules::magic_wand_supporter::create_wand_chunk(
            self,
            state,
            &wand.ghost_free_wand,
            snapshot,
            &partial,
            &mut |ctx, state, chunk| match continuation(ctx, state, Chunk::MagicWand(chunk)) {
                Ok(result) => Ok(result),
                Err(e) => {
                    callback_error = Some(e);
                    Err(EvaluationError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| {
            ChunkExecutionError::Context(NativeError::Evaluation(format!(
                "wand chunk creation: {e:?}"
            )))
        })
    }
    fn quantified_current_permission(
        &mut self,
        state: State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        resource: &ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<(State<PD, FD, JoinMode>, Term), Self::Error> {
        let source = native_quantified_source(resource);
        let formals = state
            .formal_arg_vars(&source, &self.base.symbol_converter, &self.factory)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        let chunks = native_quantified_chunks(heap, resource);
        let factory = self.factory.clone();
        let trigger = state.heap_dependent_triggers.contains(resource);
        let (state, snapshot, permission) =
            crate::rules::quantified_chunk_support::heap_summarising_maps(
                &factory, self, state, resource, source, &formals, &chunks, None, None, trigger,
                false, false, false,
            )
            .map_err(|e| NativeError::Chunk(format!("quantified current permission: {e:?}")))?;
        if trigger {
            self.assume_term(&factory.resource_trigger(
                resource,
                snapshot.snapshot_map,
                args.to_vec(),
            ))?;
        }
        let amount =
            factory.resource_permission_lookup(resource, permission.permission_map, args.to_vec());
        if matches!(resource, ResourceKey::Field(_)) {
            self.assume_term(&factory.perm_at_most(amount.clone(), factory.full_perm()))?;
        }
        Ok((state, amount))
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
        use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
        use crate::state::snapshot_map_cache::{CacheKey, QuantifiedBasicChunk};
        let ResourceKey::Field(field) = resource else {
            return Err(ChunkExecutionError::Context(NativeError::Unsupported(
                "quantified non-field access",
            )));
        };
        let factory = self.factory.clone();
        let chunks = native_quantified_chunks(&state.h, resource);
        let key = CacheKey {
            resource: native_quantified_source(resource),
            relevant_chunks: chunks
                .iter()
                .map(|chunk| match chunk {
                    Chunk::QuantifiedField(c) => QuantifiedBasicChunk::Field(c.clone()),
                    _ => unreachable!(),
                })
                .collect(),
        };
        let cached = state
            .sm_cache
            .get(&key, None)
            .map(|(definition, total)| (definition.clone(), total.clone()));
        let trigger = state.heap_dependent_triggers.contains(resource);
        let (mut state, map, total, cached_definition) = if let Some((definition, total)) = cached {
            for term in &definition.value_definitions {
                self.assume_term(term)
                    .map_err(ChunkExecutionError::Context)?;
            }
            let total = factory
                .replace(
                    &total,
                    &std::collections::HashMap::from([(
                        factory.predef_receiver_var(),
                        receiver.clone(),
                    )]),
                )
                .map_err(|e| {
                    ChunkExecutionError::Context(NativeError::Chunk(format!(
                        "field permission replacement: {e:?}"
                    )))
                })?;
            (
                state,
                definition.snapshot_map.clone(),
                total,
                Some(definition),
            )
        } else if let [Chunk::QuantifiedField(chunk)] = chunks.as_slice() {
            let substitutions = chunk
                .quantified_vars(&factory)
                .into_iter()
                .zip([receiver.clone()])
                .collect();
            let total = factory
                .replace(&chunk.permission(&factory), &substitutions)
                .map_err(|e| {
                    ChunkExecutionError::Context(NativeError::Chunk(format!(
                        "field permission replacement: {e:?}"
                    )))
                })?;
            (state, chunk.fvf_ref().clone(), total, None)
        } else {
            let (state, definition, permission) =
                crate::rules::quantified_chunk_support::heap_summarising_maps(
                    &factory,
                    self,
                    state,
                    resource,
                    native_quantified_source(resource),
                    &[factory.predef_receiver_var()],
                    &chunks,
                    None,
                    None,
                    trigger,
                    false,
                    false,
                    false,
                )
                .map_err(|e| {
                    ChunkExecutionError::Context(NativeError::Chunk(format!(
                        "field snapshot summary: {e:?}"
                    )))
                })?;
            let total = factory.resource_permission_lookup(
                resource,
                permission.permission_map,
                vec![receiver.clone()],
            );
            (state, definition.snapshot_map, total, None)
        };
        if trigger {
            self.assume_term(&factory.resource_trigger(
                resource,
                map.clone(),
                vec![receiver.clone()],
            ))
            .map_err(ChunkExecutionError::Context)?;
        }
        let goal = if state.trigger_exp {
            factory.boolean(true)
        } else if cached_definition.is_some()
            || matches!(
                receiver.kind(),
                crate::state::terms::TermKind::Var(_) | crate::state::terms::TermKind::Null
            )
        {
            factory.is_positive_perm(total)
        } else {
            let args: Vec<_> = state
                .all_relevant_quantified_variables()
                .into_iter()
                .map(|(term, _)| term)
                .collect();
            let sorts: Vec<_> = args.iter().map(|term| term.sort().clone()).collect();
            let (target, _) = self
                .base
                .decider
                .fresh(&factory, "rcvr", &sorts, receiver.sort())
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?;
            let fresh = match &target {
                ApplicationTarget::Function(fun) => factory.app(fun.clone(), args),
                ApplicationTarget::Variable(var) if args.is_empty() => var.clone(),
                _ => {
                    return Err(ChunkExecutionError::Context(NativeError::Unsupported(
                        "quantified receiver symbol",
                    )));
                }
            };
            state.function_recorder = state.function_recorder.record_fresh_snapshot(target);
            factory.implies(
                factory.builtin_equals(fresh, receiver.clone()),
                factory.is_positive_perm(total),
            )
        };
        if !state.trigger_exp
            && !self
                .base
                .decider
                .check(&goal, self.base.decider.assert_timeout)
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?
        {
            let failure =
                error
                    .clone()
                    .ok_or(ChunkExecutionError::Context(NativeError::Unsupported(
                        "field access failure context",
                    )))?;
            return self
                .failure_full(failure, state.retry_level)
                .map_err(ChunkExecutionError::Context);
        }
        let value = factory.lookup(field.name.clone(), map.clone(), receiver.clone());
        state.function_recorder = state.function_recorder.record_location_snapshot(
            field_access.clone(),
            self.base.decider.pcs.recorded().branch_conditions(),
            value.clone(),
        );
        if let Some(definition) = cached_definition {
            if !state.trigger_exp {
                state.function_recorder = state.function_recorder.record_fvf_and_domain(definition);
            }
        }
        if trigger && state.record_possible_triggers && !state.trigger_exp {
            state.possible_triggers.insert(
                field_access.clone(),
                factory.resource_trigger(resource, map, vec![receiver.clone()]),
            );
        }
        continuation(self, state, value)
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
        use crate::interfaces::state::chunks::GeneralChunk;
        use crate::rules::consumption_result::ConsumptionResult;
        use crate::rules::quantified_chunk_support as qp;
        let ResourceKey::Field(field) = resource else {
            return Err(ChunkExecutionError::Context(NativeError::Unsupported(
                "quantified non-field assignment",
            )));
        };
        let factory = self.factory.clone();
        let identifier = ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(
            field.name.clone(),
        ));
        let mut action = |ctx: &mut Self,
                          mut state: State<PD, FD, JoinMode>,
                          done: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ChunkExecutionError<Self::Error>,
        >| {
            let (relevant, others) =
                qp::split_quantified_heap(&state.h, &identifier).map_err(|e| {
                    ChunkExecutionError::Context(NativeError::Chunk(format!(
                        "field assignment split: {e:?}"
                    )))
                })?;
            let hints =
                qp::extract_hints(&factory, None, std::slice::from_ref(receiver)).map_err(|e| {
                    ChunkExecutionError::Context(NativeError::Chunk(format!(
                        "field assignment hints: {e:?}"
                    )))
                })?;
            let candidates = qp::single_receiver_chunk_order(
                &factory,
                ctx,
                &relevant,
                std::slice::from_ref(receiver),
                &hints,
            )
            .map_err(|e| {
                ChunkExecutionError::Context(NativeError::Chunk(format!(
                    "field assignment ordering: {e:?}"
                )))
            })?;
            if state.heap_dependent_triggers.contains(resource) {
                let (definition, cache) =
                    qp::GeneralConsumptionExecution::summarise_general_consumed(
                        ctx,
                        &state,
                        resource,
                        &[factory.predef_receiver_var()],
                        &relevant,
                        None,
                    )
                    .map_err(ChunkExecutionError::Context)?;
                ctx.assume_term(&factory.resource_trigger(
                    resource,
                    definition.snapshot_map.clone(),
                    vec![receiver.clone()],
                ))
                .map_err(ChunkExecutionError::Context)?;
                state.sm_cache = cache;
                state.function_recorder = state.function_recorder.record_fvf_and_domain(definition);
            }
            ctx.base.decider.clear_model();
            let codomain = factory.predef_receiver_var();
            let condition = factory.equals(codomain.clone(), receiver.clone());
            let (outcome, mut state, mut remaining, untouched) = qp::remove_quantified_permissions(
                &factory,
                ctx,
                state,
                &candidates,
                &relevant,
                &identifier,
                std::slice::from_ref(&codomain),
                None,
                condition,
                None,
                Some(std::slice::from_ref(receiver)),
                factory.full_perm(),
                None,
                false,
                false,
            )
            .map_err(|e| {
                ChunkExecutionError::Context(NativeError::Chunk(format!(
                    "field assignment removal: {e:?}"
                )))
            })?;
            if !matches!(outcome, ConsumptionResult::Complete) {
                let failure =
                    error
                        .clone()
                        .ok_or(ChunkExecutionError::Context(NativeError::Unsupported(
                            "field assignment failure context",
                        )))?;
                return ctx
                    .failure_full(failure, state.retry_level)
                    .map_err(ChunkExecutionError::Context);
            }
            let mut consumed = relevant;
            for chunk in &untouched {
                if let Some(index) = consumed.iter().position(|c| c == chunk) {
                    consumed.remove(index);
                }
            }
            let mut counts = Vec::<(i32, usize)>::new();
            for chunk in &consumed {
                if let Chunk::QuantifiedField(c) = chunk {
                    if let Some(tag) = c.tag() {
                        if let Some((_, count)) =
                            counts.iter_mut().find(|(candidate, _)| *candidate == tag)
                        {
                            *count += 1;
                        } else {
                            counts.push((tag, 1));
                        }
                    }
                }
            }
            let tag = counts
                .into_iter()
                .max_by_key(|(_, count)| *count)
                .map(|(tag, _)| tag)
                .unwrap_or_else(|| {
                    let id = ctx.heap_supporter_counter as i32;
                    ctx.heap_supporter_counter = ctx.heap_supporter_counter.wrapping_add(1);
                    id
                });
            remaining.extend(untouched);
            remaining.extend(others);
            let (map, definition) = qp::singleton_snapshot_map(
                &factory,
                ctx,
                &state,
                resource,
                std::slice::from_ref(receiver),
                value.clone(),
            )
            .map_err(|e| {
                ChunkExecutionError::Context(NativeError::Chunk(format!(
                    "field assignment snapshot: {e:?}"
                )))
            })?;
            ctx.base
                .decider
                .assume([(definition, None)], false, true)
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?;
            let chunk = qp::singleton_quantified_chunk(
                &factory,
                resource,
                vec![codomain],
                None,
                vec![receiver.clone()],
                None,
                factory.full_perm(),
                None,
                map.clone(),
                Some(tag),
                false,
            )
            .map_err(|e| {
                ChunkExecutionError::Context(NativeError::Chunk(format!(
                    "field assignment chunk: {e:?}"
                )))
            })?;
            if state.heap_dependent_triggers.contains(resource) {
                ctx.assume_term(&factory.resource_trigger(resource, map, vec![receiver.clone()]))
                    .map_err(ChunkExecutionError::Context)?;
            }
            state.h = Arc::new(ListBackedHeap::from_chunks(remaining).with_chunk(chunk));
            let heap = state.h.clone();
            done(ctx, state, heap, None)
        };
        if self.options.exhale_mode_qp == crate::config::ExhaleMode::MoreComplete {
            action(self, state, &mut |ctx, state, _, _| {
                continuation(ctx, state)
            })
        } else {
            crate::rules::chunk_supporter::ChunkExecutionContext::retry_chunk(
                self,
                state,
                &mut action,
                &mut |ctx, state, _, _| continuation(ctx, state),
            )
        }
    }
    fn record_assignment_heap(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Ok(state)
    }
    fn fresh_havoc_snapshot(&mut self, sort: &Sort, wand_map: bool) -> Result<Term, Self::Error> {
        let name = if wand_map { "mwsf" } else { "snap" };
        let (target, _) = self
            .base
            .decider
            .fresh(&self.factory, name, &[], sort)
            .map_err(NativeError::Decider)?;
        Ok(match target {
            ApplicationTarget::Function(f) => self.factory.app(f, vec![]),
            ApplicationTarget::Variable(v) => v,
        })
    }
    fn havoc_codomain(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
    ) -> Result<(Vec<Term>, Term), Self::Error> {
        let source = native_quantified_source(resource);
        let vars = state
            .formal_arg_vars(&source, &self.base.symbol_converter, &self.factory)
            .map_err(|e| NativeError::Chunk(format!("havoc codomain: {e:?}")))?;
        let aggregate = if matches!(resource, ResourceKey::Field(_)) {
            self.factory.predef_receiver_var()
        } else {
            self.factory.predef_snapshot_var()
        };
        Ok((vars, aggregate))
    }
    fn fresh_havoc_map(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
    ) -> Result<Term, Self::Error> {
        crate::rules::quantified_chunk_support::SnapshotMapFreshener::fresh_snapshot_map(
            self,
            state,
            resource,
            &[],
        )
    }
    fn assume_havoc_axiom(&mut self, axiom: &Term) -> Result<(), Self::Error> {
        self.assume_term(axiom)
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
        crate::rules::predicate_supporter::PredicateExecutionServices::assume_unfold_trigger(
            self, state, predicate, snapshot, &state.h, args, debug_args,
        )
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
        crate::rules::magic_wand_supporter::execution_heap(state)
            .ok_or(NativeError::Unsupported("missing wand execution reserve"))
    }
    fn move_to_reserve_heap(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        crate::rules::magic_wand_supporter::move_to_reserve_heap(self, state)
            .map_err(|e| NativeError::Execution(format!("wand reserve heap: {e:?}")))
    }
    fn evaluation_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        crate::rules::magic_wand_supporter::evaluation_heap(self, state)
            .map_err(|e| NativeError::Execution(format!("wand evaluation heap: {e:?}")))
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
                .fresh_variable(&self.factory, &field.name, &sort, false, None)
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
        let partial = self.call_partial(call, method, false)?;
        let mut reconstructed = None;
        crate::rules::producer::produce_all(
            self,
            state.clone(),
            NativeSnapshot::Projection(snapshot.clone()),
            &method.pres,
            &|_| partial.clone(),
            &mut |ctx, produced| {
                reconstructed = Some(
                    crate::rules::magic_wand_supporter::evaluation_heap(ctx, &produced).map_err(
                        |e| {
                            ProductionError::Context(NativeError::Execution(format!(
                                "reconstructed call heap: {e:?}"
                            )))
                        },
                    )?,
                );
                Ok(VerificationResult::success())
            },
        )
        .map_err(|e| {
            NativeError::Production(format!("reconstruct call precondition heap: {e:?}"))
        })?;
        Ok(reconstructed)
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
        use crate::rules::predicate_supporter::{
            PredicateExecutionError, fold_predicate, unfold_predicate,
        };
        use ferrum_silver::ast::statement::StmtKind;
        if let StmtKind::Quasihavocall {
            variables,
            guard,
            resource,
        } = statement.kind()
        {
            use crate::rules::quantified_chunk_support as qp;
            use ferrum_silver::ast::statement::ResourceAccess;
            let error = PartialVerificationError::for_kind(VerificationErrorKind::HavocallFailed(
                statement.clone(),
            ));
            let guard = guard
                .clone()
                .unwrap_or_else(|| Exp::new(ExpKind::TrueLit, statement.metadata().clone()));
            let (expressions, key, qid) = match resource {
                ResourceAccess::Field(field) => (
                    vec![field.receiver.clone()],
                    ResourceKey::Field(Arc::new(field.field.clone())),
                    field.field.name.clone(),
                ),
                ResourceAccess::Predicate(predicate) => (
                    predicate.args.clone(),
                    ResourceKey::Predicate(Arc::new(
                        state
                            .program
                            .find_predicate(&predicate.predicate_name)
                            .map_err(|e| {
                                ExecutionError::Context(NativeError::Diagnostic(format!("{e:?}")))
                            })?
                            .clone(),
                    )),
                    predicate.predicate_name.clone(),
                ),
                ResourceAccess::MagicWand(wand) => {
                    let id = crate::state::chunks::MagicWandIdentifier::new(
                        wand.clone(),
                        &state.program,
                    )
                    .map_err(|e| ExecutionError::Context(NativeError::Chunk(format!("{e:?}"))))?;
                    (
                        wand.magic_wand_subexpressions(&state.program)
                            .map_err(|e| {
                                ExecutionError::Context(NativeError::Execution(format!("{e:?}")))
                            })?,
                        ResourceKey::Wand(id.clone()),
                        id.to_string(),
                    )
                }
            };
            let factory = self.factory.clone();
            let mut callback_error = None;
            let result = crate::rules::evaluator::evaluate_quantified(
                self,
                state,
                crate::state::terms::Quantifier::Forall,
                variables,
                std::slice::from_ref(&guard),
                &expressions,
                None,
                &qid,
                &error,
                &mut |ctx, mut state, data| {
                    let Some(body) = data.second else {
                        return match continuation(ctx, state) {
                            Ok(value) => Ok(value),
                            Err(e) => {
                                callback_error = Some(e);
                                Err(EvaluationError::Context(NativeError::ContinuationAbort))
                            }
                        };
                    };
                    if data.first_terms.len() != 1 {
                        return Err(EvaluationError::InvalidJoinEntries);
                    }
                    let condition = data.first_terms[0].clone();
                    let source = native_quantified_source(&key);
                    let formals = state
                        .formal_arg_vars(&source, &ctx.base.symbol_converter, &factory)
                        .map_err(|e| {
                            EvaluationError::Context(NativeError::Chunk(format!(
                                "havocall formals: {e:?}"
                            )))
                        })?;
                    let check = qp::injectivity_axiom(
                        &factory,
                        &data.variables,
                        &condition,
                        &factory.full_perm(),
                        &body.terms,
                        vec![],
                        &qid,
                    )
                    .map_err(|e| {
                        EvaluationError::Context(NativeError::Chunk(format!(
                            "havocall injectivity: {e:?}"
                        )))
                    })?;
                    let precondition = crate::state::function_precondition_transformer::transform(
                        &factory,
                        &check,
                        &mut |fun| {
                            Ok::<_, NativeError<S::Error>>(
                                crate::rules::function_supporter::precondition_version(
                                    &factory, fun,
                                ),
                            )
                        },
                    )
                    .map_err(|e| {
                        EvaluationError::Context(NativeError::Chunk(format!(
                            "havocall precondition: {e:?}"
                        )))
                    })?;
                    ctx.assume_term(&precondition)
                        .map_err(EvaluationError::Context)?;
                    let proven = ctx
                        .base
                        .decider
                        .check(&check, ctx.base.decider.assert_timeout)
                        .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
                    if !proven {
                        return ctx
                            .failure(
                                &error,
                                ErrorReason::QuasihavocallNotInjective(statement.clone()),
                                state.retry_level,
                            )
                            .map_err(EvaluationError::Context);
                    }
                    let (inverse, images) = qp::fresh_inverse_functions(
                        &factory,
                        ctx,
                        &data.variables,
                        data.variable_expressions,
                        condition.clone(),
                        body.terms,
                        body.expressions,
                        &formals,
                        vec![],
                        &[],
                        None,
                        &qid,
                        false,
                    )
                    .map_err(|e| {
                        EvaluationError::Context(NativeError::Chunk(format!(
                            "havocall inverses: {e:?}"
                        )))
                    })?;
                    ctx.base
                        .decider
                        .assume(
                            inverse
                                .definitional_axioms()
                                .into_iter()
                                .cloned()
                                .map(|t| (t, None)),
                            false,
                            false,
                        )
                        .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
                    let helper = crate::rules::havoc_supporter::HavocHelperData::All {
                        inverse_functions: inverse,
                        codomain_vars: formals,
                        images_of_codomain: images,
                    };
                    let heap = crate::rules::heap_supporter::havoc_resource(
                        ctx, &state, &condition, &key, &helper,
                    )
                    .map_err(|e| {
                        EvaluationError::Context(NativeError::Execution(format!(
                            "havocall resource: {e:?}"
                        )))
                    })?;
                    state.h = Arc::new(heap);
                    match continuation(ctx, state) {
                        Ok(value) => Ok(value),
                        Err(e) => {
                            callback_error = Some(e);
                            Err(EvaluationError::Context(NativeError::ContinuationAbort))
                        }
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            return result.map_err(|e| {
                ExecutionError::Context(NativeError::Evaluation(format!("havocall: {e:?}")))
            });
        }
        if let StmtKind::Quasihavoc { guard, resource } = statement.kind() {
            use ferrum_silver::ast::statement::ResourceAccess;
            let error = PartialVerificationError::for_kind(
                VerificationErrorKind::QuasihavocFailed(statement.clone()),
            );
            let guard = guard
                .clone()
                .unwrap_or_else(|| Exp::new(ExpKind::TrueLit, statement.metadata().clone()));
            let expressions = match resource {
                ResourceAccess::Field(field) => vec![field.receiver.clone()],
                ResourceAccess::Predicate(predicate) => predicate.args.clone(),
                ResourceAccess::MagicWand(wand) => wand
                    .magic_wand_subexpressions(&state.program)
                    .map_err(|e| {
                    ExecutionError::Context(NativeError::Execution(format!(
                        "havoc wand arguments: {e:?}"
                    )))
                })?,
            };
            let mut callback_error = None;
            let result = crate::rules::evaluator::evaluate(
                self,
                state,
                &guard,
                &error,
                &mut |ctx, state, condition, _| {
                    crate::rules::evaluator::evaluate_all(
                        ctx,
                        state,
                        &expressions,
                        &|_| error.clone(),
                        &mut |ctx, mut state, arguments, _| {
                            let resource = match resource {
                                ResourceAccess::Field(field) => {
                                    ResourceKey::Field(Arc::new(field.field.clone()))
                                }
                                ResourceAccess::Predicate(predicate) => {
                                    ResourceKey::Predicate(Arc::new(
                                        state
                                            .program
                                            .find_predicate(&predicate.predicate_name)
                                            .map_err(|e| {
                                                EvaluationError::Context(NativeError::Diagnostic(
                                                    format!("{e:?}"),
                                                ))
                                            })?
                                            .clone(),
                                    ))
                                }
                                ResourceAccess::MagicWand(wand) => ResourceKey::Wand(
                                    crate::state::chunks::MagicWandIdentifier::new(
                                        wand.clone(),
                                        &state.program,
                                    )
                                    .map_err(|e| {
                                        EvaluationError::Context(NativeError::Chunk(format!(
                                            "{e:?}"
                                        )))
                                    })?,
                                ),
                            };
                            let heap = crate::rules::heap_supporter::havoc_resource(
                                ctx,
                                &state,
                                &condition,
                                &resource,
                                &crate::rules::havoc_supporter::HavocHelperData::One(arguments),
                            )
                            .map_err(|e| {
                                EvaluationError::Context(NativeError::Execution(format!(
                                    "havoc resource: {e:?}"
                                )))
                            })?;
                            state.h = Arc::new(heap);
                            match continuation(ctx, state) {
                                Ok(value) => Ok(value),
                                Err(e) => {
                                    callback_error = Some(e);
                                    Err(EvaluationError::Context(NativeError::ContinuationAbort))
                                }
                            }
                        },
                    )
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            return result.map_err(|e| {
                ExecutionError::Context(NativeError::Evaluation(format!("havoc: {e:?}")))
            });
        }
        if let StmtKind::Package { wand, proof_script } = statement.kind() {
            use crate::rules::magic_wand_supporter::PackageExecutionError as PE;
            let error = PartialVerificationError::for_kind(VerificationErrorKind::PackageFailed(
                statement.clone(),
            ));
            let original = state.clone();
            let mut state = state;
            state.is_in_package = true;
            let factory = self.factory.clone();
            let mut callback_error = None;
            let result = crate::rules::magic_wand_supporter::package_wand(
                &factory,
                self,
                state,
                wand,
                proof_script,
                &error,
                &mut |ctx, mut state, chunk| {
                    if state.reserve_heaps.is_empty() {
                        return Err(PE::MissingReserveHeap);
                    }
                    let trigger_args = if let Chunk::QuantifiedMagicWand(ref wand_chunk) = chunk {
                        let args = wand_chunk.singleton_args_ref().clone().ok_or_else(|| {
                            PE::Service(NativeError::Chunk(
                                "missing quantified wand singleton arguments".into(),
                            ))
                        })?;
                        Some((args, wand_chunk.singleton_arg_exps_ref().clone()))
                    } else {
                        None
                    };
                    let operations = Arc::new(state.reserve_heaps[0].with_chunk(chunk));
                    if original.exhale_ext {
                        if original.reserve_heaps.is_empty() {
                            return Err(PE::MissingReserveHeap);
                        }
                        let mut reserve = vec![original.reserve_heaps[0].clone(), operations];
                        reserve.extend_from_slice(&state.reserve_heaps[1..]);
                        state.h = Arc::new(ListBackedHeap::new());
                        state.exhale_ext = true;
                        state.reserve_heaps = reserve;
                    } else {
                        if state.reserve_heaps.len() != 1 {
                            return Err(PE::MissingReserveHeap);
                        }
                        state.h = operations;
                        state.exhale_ext = false;
                        state.reserve_heaps.clear();
                    }
                    if let Some((args, debug_args)) = trigger_args {
                        state = crate::rules::consumer::ConsumptionContext::trigger_resource(
                            ctx,
                            state,
                            wand,
                            &args,
                            debug_args.as_deref(),
                        )
                        .map_err(PE::Service)?;
                    }
                    state.is_in_package = original.is_in_package;
                    match continuation(ctx, state) {
                        Ok(value) => Ok(value),
                        Err(e) => {
                            callback_error = Some(e);
                            Err(PE::Service(NativeError::ContinuationAbort))
                        }
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            return result.map_err(|e| {
                ExecutionError::Context(NativeError::Execution(format!("package wand: {e:?}")))
            });
        }
        if let StmtKind::Apply(wand) = statement.kind() {
            use crate::rules::magic_wand_supporter::WandApplicationError as WE;
            let error = PartialVerificationError::for_kind(VerificationErrorKind::ApplyFailed(
                statement.clone(),
            ));
            let factory = self.factory.clone();
            let mut callback_error = None;
            let result = crate::rules::magic_wand_supporter::apply_wand(
                &factory,
                self,
                state,
                wand,
                &error,
                &mut |ctx, state| match continuation(ctx, state) {
                    Ok(result) => Ok(result),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(WE::Service(NativeError::ContinuationAbort))
                    }
                },
            );
            if let Some(error) = callback_error {
                return Err(error);
            }
            return result.map_err(|e| {
                ExecutionError::Context(NativeError::Execution(format!("apply wand: {e:?}")))
            });
        }
        let (access, folding) = match statement.kind() {
            StmtKind::Fold(access) => (access, true),
            StmtKind::Unfold(access) => (access, false),
            _ => {
                return Err(ExecutionError::Context(NativeError::Unsupported(
                    "execute_special",
                )));
            }
        };
        if !state.constrainable_arps.is_empty() {
            return Err(ExecutionError::Context(NativeError::Unsupported(
                "preexisting constrainable permissions at predicate statement",
            )));
        }
        let predicate = state
            .program
            .find_predicate(&access.location.predicate_name)
            .map_err(|e| ExecutionError::Context(NativeError::Diagnostic(format!("{e:?}"))))?
            .clone();
        let location = Exp::new(
            ExpKind::PredicateAccess(access.location.clone()),
            access.location.meta.clone(),
        );
        let permission = access.permission_or_full();
        let partial = PartialVerificationError::for_kind(if folding {
            VerificationErrorKind::FoldFailed(statement.clone())
        } else {
            VerificationErrorKind::UnfoldFailed(statement.clone())
        });
        let mut outer_error = None;
        let result = crate::rules::evaluator::evaluate_all(
            self,
            state,
            &access.location.args,
            &|_| partial.clone(),
            &mut |ctx, state, args, arg_exps| {
                let original_arps = state.constrainable_arps.clone();
                let mut inner_error = None;
                let evaluated = crate::rules::evaluator::evaluate(
                    ctx,
                    state,
                    &permission,
                    &partial,
                    &mut |ctx, state, amount, amount_exp| {
                        let result: Result<_, ExecutionError<NativeError<S::Error>>> = (|| {
                            let state = if folding {
                                state
                            } else {
                                crate::rules::consumer::ConsumptionContext::trigger_resource(
                                    ctx,
                                    state,
                                    &location,
                                    &args,
                                    arg_exps.as_deref(),
                                )
                                .map_err(ExecutionError::Context)?
                            };
                            let valid = crate::rules::permission_supporter::assert_permission(
                                &ctx.factory,
                                &amount,
                                &permission,
                                amount_exp.as_ref(),
                                state.constrainable_arps.iter().cloned(),
                                true,
                                |term| {
                                    ctx.base
                                        .decider
                                        .check(term, ctx.base.decider.assert_timeout)
                                        .map_err(NativeError::Decider)
                                },
                                || true,
                                |_, _, _, _| false,
                            )
                            .map_err(ExecutionError::Context)?;
                            if !valid {
                                return ctx
                                    .failure(
                                        &partial,
                                        ErrorReason::NonPositivePermission(permission.clone()),
                                        state.retry_level,
                                    )
                                    .map_err(ExecutionError::Context);
                            }
                            let wildcards: Vec<_> = state
                                .constrainable_arps
                                .iter()
                                .filter(|v| !original_arps.contains(*v))
                                .cloned()
                                .collect();
                            let factory = ctx.factory.clone();
                            let mut continuation_error = None;
                            let mut next = |ctx: &mut Self, state| match continuation(ctx, state) {
                                Ok(v) => Ok(v),
                                Err(e) => {
                                    continuation_error = Some(e);
                                    Err(PredicateExecutionError::Service(
                                        NativeError::ContinuationAbort,
                                    ))
                                }
                            };
                            let result = if folding {
                                fold_predicate(
                                    &factory,
                                    ctx,
                                    state,
                                    &predicate,
                                    &location,
                                    &args,
                                    arg_exps.as_deref(),
                                    &amount,
                                    amount_exp.as_ref(),
                                    &wildcards,
                                    &partial,
                                    &mut next,
                                )
                            } else {
                                unfold_predicate(
                                    &factory,
                                    ctx,
                                    state,
                                    &predicate,
                                    &location,
                                    &args,
                                    arg_exps.as_deref(),
                                    &amount,
                                    amount_exp.as_ref(),
                                    &wildcards,
                                    &partial,
                                    &mut next,
                                )
                            };
                            if let Some(error) = continuation_error {
                                return Err(error);
                            }
                            result.map_err(|e| {
                                ExecutionError::Context(NativeError::Execution(format!("{e:?}")))
                            })
                        })(
                        );
                        match result {
                            Ok(value) => Ok(value),
                            Err(error) => {
                                inner_error = Some(error);
                                Err(EvaluationError::Context(NativeError::ContinuationAbort))
                            }
                        }
                    },
                );
                if let Some(error) = inner_error {
                    outer_error = Some(error);
                    return Err(EvaluationError::Context(NativeError::ContinuationAbort));
                }
                evaluated
            },
        );
        if let Some(error) = outer_error {
            return Err(error);
        }
        result.map_err(|e| ExecutionError::Context(NativeError::Evaluation(format!("{e:?}"))))
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
        let factory = self.factory.clone();
        let choice = self.consolidation_choice(&state)?;
        let (recorder, heap) = crate::rules::state_consolidator::merge_heaps(
            &factory,
            self,
            &state,
            state.function_recorder.clone(),
            &state.h,
            &saved,
            choice,
        )
        .map_err(|e| NativeError::Consolidation(format!("{e:?}")))?;
        let mut state = state;
        state.function_recorder = recorder;
        state.h = Arc::new(heap);
        Ok(state)
    }
    fn evaluate_edge(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: &Exp,
        is_loop_guard: bool,
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
            let partial = PartialVerificationError::for_kind(if is_loop_guard {
                VerificationErrorKind::WhileFailed(condition.clone())
            } else {
                VerificationErrorKind::IfFailed(condition.clone())
            });
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
        let then_result = run(self, decision.execute_then, true, yes)?;
        if !then_result.continue_verification() {
            return Ok(then_result);
        }
        let else_result = run(self, decision.execute_else, false, no)?;
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
        let error = std::cell::RefCell::new(None);
        let result = self.join_impure_branches(
            state,
            condition,
            original,
            rewritten,
            &mut |ctx, state, done| match yes(ctx, state, &mut |ctx, state| {
                done(ctx, state, ()).map_err(ExecutionError::Context)
            }) {
                Ok(value) => Ok(value),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
            &mut |ctx, state, done| match no(ctx, state, &mut |ctx, state| {
                done(ctx, state, ()).map_err(ExecutionError::Context)
            }) {
                Ok(value) => Ok(value),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
            &mut |ctx, entries| {
                let state = match entries {
                    [one] => one.state.clone(),
                    [first, second] => {
                        let factory = ctx.factory.clone();
                        let merged = first
                            .state
                            .merge_recorded(
                                &first.path_conditions,
                                &second.state,
                                &second.path_conditions,
                                &factory,
                                false,
                                &mut |warning| ctx.warnings.push(warning),
                            )
                            .map_err(NativeError::State)?;
                        let choice = ctx.consolidation_choice(&merged)?;
                        crate::rules::state_consolidator::consolidate(
                            &factory, ctx, merged, choice, false,
                        )
                        .map_err(|e| NativeError::Consolidation(format!("CFG join: {e:?}")))?
                    }
                    _ => return Err(NativeError::Unsupported("unexpected CFG join entries")),
                };
                Ok((state, ()))
            },
            &mut |ctx, state, ()| match continuation(ctx, state) {
                Ok(value) => Ok(value),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
        );
        if let Some(error) = error.into_inner() {
            return Err(error);
        }
        result.map_err(ExecutionError::Context)
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
        self.base
            .decider
            .push_scope()
            .map_err(|e| ExecutionError::Context(NativeError::Decider(e)))?;
        let result = block(self, state);
        let cleanup = self.base.decider.pop_scope();
        match (result, cleanup) {
            (Ok(v), Ok(())) => Ok(v),
            (Err(e), Ok(())) => Err(e),
            (Ok(_), Err(e)) => Err(ExecutionError::Context(NativeError::Decider(e))),
            (Err(e), Err(cleanup)) => Err(ExecutionError::Context(NativeError::Cleanup(format!(
                "{e:?}; cleanup: {cleanup:?}"
            )))),
        }
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
        self.base
            .decider
            .declare_fresh_functions(functions.iter().cloned())
            .map_err(NativeError::Decider)?;
        self.base
            .decider
            .declare_fresh_macros(macros.iter().cloned())
            .map_err(NativeError::Decider)?;
        self.base
            .decider
            .assume(
                paths.assumptions().into_iter().map(|term| (term, None)),
                false,
                false,
            )
            .map_err(NativeError::Decider)
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
        let mut callback_error = None;
        let result = crate::rules::producer::produce_all(
            self,
            state,
            NativeSnapshot::Fresh,
            invariants,
            &|exp| {
                PartialVerificationError::for_kind(VerificationErrorKind::ContractNotWellformed(
                    exp.clone(),
                ))
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
        result.map_err(|e| ExecutionError::Context(NativeError::Production(format!("{e:?}"))))
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
        let mut callback_error = None;
        let result = crate::rules::consumer::consume_all(
            self,
            state,
            invariants,
            false,
            &|exp| {
                PartialVerificationError::for_kind(if preserved {
                    VerificationErrorKind::LoopInvariantNotPreserved(exp.clone())
                } else {
                    VerificationErrorKind::LoopInvariantNotEstablished(exp.clone())
                })
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
        result.map_err(|e| ExecutionError::Context(NativeError::Consumption(format!("{e:?}"))))
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
    functions: std::cell::RefCell<
        crate::supporters::functions::function_verification_unit::FunctionVerificationUnit<
            NativeFunctionData,
        >,
    >,
    function_handles: crate::state::package::OrderedMap<String, Arc<NativeFunctionData>>,
    predicates: crate::state::package::OrderedMap<
        String,
        Arc<crate::supporters::predicate_verification_unit::PredicateData>,
    >,
    snapshot_sorts: crate::state::package::OrderedMap<String, Sort>,
    snapshot_formals: crate::state::package::OrderedMap<String, Vec<Term>>,
}
/// Owned analysis retained after function and predicate verification for worker methods.
/// Strong owners keep the weak function handles valid throughout worker execution.
/// A worker must replay the source-ordered main and member preamble before using this.
#[derive(Clone)]
pub struct NativeWorkerAnalysis {
    program: ferrum_silver::ast::program::Program,
    function_owners: Vec<(
        String,
        Arc<
            std::sync::Mutex<
                crate::supporters::functions::function_data::FunctionData<NativeFunctionData>,
            >,
        >,
    )>,
    function_handles: crate::state::package::OrderedMap<String, Arc<NativeFunctionData>>,
    predicates: crate::state::package::OrderedMap<
        String,
        Arc<crate::supporters::predicate_verification_unit::PredicateData>,
    >,
    snapshot_sorts: crate::state::package::OrderedMap<String, Sort>,
    snapshot_formals: crate::state::package::OrderedMap<String, Vec<Term>>,
    function_heights: std::collections::HashMap<String, i32>,
    function_fresh_variables: Vec<Term>,
    failed_functions: std::collections::HashSet<String>,
}

impl<S: Prover>
    NativeVerifierContext<
        S,
        crate::supporters::predicate_verification_unit::PredicateData,
        NativeFunctionData,
    >
where
    S::Error: std::fmt::Debug,
{
    /// Replay verification-generated symbols and axioms after the worker's main preamble.
    /// Predicate symbols precede function symbols; function axioms are emitted last.
    pub fn emit_worker_post_preamble<T: crate::interfaces::decider::prover::ProverLike>(
        &self,
        analysis: &NativeAnalysis,
        sink: &mut T,
    ) -> Result<(), T::Error> {
        crate::supporters::predicate_verification_unit::declare_predicate_verification_symbols(
            sink,
            &analysis.predicates,
        )?;
        let functions = analysis.functions.borrow();
        functions.declare_verification_symbols(&self.factory, sink)?;
        functions.emit_recorded_axioms(sink)
    }

    /// Capture immutable method-phase analysis after source function/predicate verification.
    pub fn worker_analysis(
        &self,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
    ) -> NativeWorkerAnalysis {
        NativeWorkerAnalysis {
            program: program.clone(),
            function_owners: analysis.functions.borrow().data.clone(),
            function_handles: analysis.function_handles.clone(),
            predicates: analysis.predicates.clone(),
            snapshot_sorts: analysis.snapshot_sorts.clone(),
            snapshot_formals: analysis.snapshot_formals.clone(),
            function_heights: self.function_heights.clone(),
            function_fresh_variables: self.function_fresh_variables.clone(),
            failed_functions: self.failed_functions.clone(),
        }
    }
    /// Verify one method with an already-started worker prover and replayed preamble.
    pub fn verify_worker_method(
        &mut self,
        analysis: &NativeWorkerAnalysis,
        method: &Method,
    ) -> Result<Vec<VerificationResult<VerificationError>>, NativeError<S::Error>> {
        self.active_program = Some(analysis.program.clone());
        self.function_handles = analysis.function_handles.clone();
        self.function_heights = analysis.function_heights.clone();
        self.function_fresh_variables = analysis.function_fresh_variables.clone();
        self.failed_functions = analysis.failed_functions.clone();
        self.predicate_snapshots.snap_map = analysis.snapshot_sorts.clone();
        self.predicate_snapshots.formal_var_map = analysis.snapshot_formals.clone();
        let mut unit = crate::supporters::functions::function_verification_unit::FunctionVerificationUnit::default();
        unit.program = Some(analysis.program.clone());
        unit.data = analysis.function_owners.clone();
        let local = NativeAnalysis {
            functions: std::cell::RefCell::new(unit),
            function_handles: analysis.function_handles.clone(),
            predicates: analysis.predicates.clone(),
            snapshot_sorts: analysis.snapshot_sorts.clone(),
            snapshot_formals: analysis.snapshot_formals.clone(),
        };
        let state = self.initial_state(
            &analysis.program,
            &local,
            ferrum_silver::ast::program::Member::Method(method.clone()),
        )?;
        let results = crate::supporters::method_supporter::verify_method(self, state, method)
            .map(flatten_results)
            .map_err(|e| NativeError::Execution(format!("worker method verification: {e:?}")))?;
        Ok(results)
    }

    /// Verify an externally supplied CFG on an initialized worker solver.
    pub fn verify_worker_cfg(
        &mut self,
        analysis: &NativeWorkerAnalysis,
        cfg: &SilverCfg,
    ) -> Result<Vec<VerificationResult<VerificationError>>, NativeError<S::Error>> {
        self.active_program = Some(analysis.program.clone());
        self.function_handles = analysis.function_handles.clone();
        self.function_heights = analysis.function_heights.clone();
        self.function_fresh_variables = analysis.function_fresh_variables.clone();
        self.failed_functions = analysis.failed_functions.clone();
        self.predicate_snapshots.snap_map = analysis.snapshot_sorts.clone();
        self.predicate_snapshots.formal_var_map = analysis.snapshot_formals.clone();
        let mut unit = crate::supporters::functions::function_verification_unit::FunctionVerificationUnit::default();
        unit.program = Some(analysis.program.clone());
        unit.data = analysis.function_owners.clone();
        let local = NativeAnalysis {
            functions: std::cell::RefCell::new(unit),
            function_handles: analysis.function_handles.clone(),
            predicates: analysis.predicates.clone(),
            snapshot_sorts: analysis.snapshot_sorts.clone(),
            snapshot_formals: analysis.snapshot_formals.clone(),
        };
        let state = self.initial_cfg_state(&analysis.program, &local);
        crate::supporters::cfg_supporter::verify_cfg(self, state, Arc::new(cfg.clone()))
            .map(flatten_results)
            .map_err(|e| NativeError::Execution(format!("worker CFG verification: {e:?}")))
    }

    /// Verify a function before reporting and scope assignment in a pool orchestrator.
    pub fn verify_function_unscoped(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
        function: &ferrum_silver::ast::program::Function,
    ) -> Result<Vec<VerificationResult<VerificationError>>, NativeError<S::Error>> {
        let state = self.initial_state(
            program,
            analysis,
            ferrum_silver::ast::program::Member::Function(function.clone()),
        )?;
        let factory = self.factory.clone();
        analysis
            .functions
            .borrow_mut()
            .verify(&factory, self, state, function)
            .map(flatten_results)
            .map_err(|e| NativeError::Execution(format!("function verification: {e:?}")))
    }
    /// Verify a predicate before reporting and scope assignment in a pool orchestrator.
    pub fn verify_predicate_unscoped(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
        predicate: &Predicate,
    ) -> Result<Vec<VerificationResult<VerificationError>>, NativeError<S::Error>> {
        let data = analysis
            .predicates
            .get(&predicate.name)
            .ok_or(NativeError::Unsupported("predicate analysis data"))?
            .clone();
        let state = self.initial_state(
            program,
            analysis,
            ferrum_silver::ast::program::Member::Predicate(predicate.clone()),
        )?;
        let factory = self.factory.clone();
        crate::supporters::predicate_verification_unit::verify_predicate(
            &factory, self, state, &data,
        )
        .map(flatten_results)
        .map_err(|e| NativeError::Execution(format!("{e:?}")))
    }

    /// Execute the actual main-verifier orchestration with one owned solver.
    /// This first supported profile rejects constructs whose contributor, solver or
    /// worker services are not yet connected before starting any member proof.
    pub fn verify_program(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
        cfgs: &[SilverCfg],
    ) -> Result<Vec<VerificationResult<VerificationError>>, NativeError<S::Error>> {
        crate::verifier::default_main_verifier::verify(self, program, cfgs, None)
    }
    fn initial_cfg_state(
        &self,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
    ) -> NativeState {
        let mut state = State::new(
            program.clone(),
            analysis.predicates.clone(),
            analysis.function_handles.clone(),
            self.options.join_mode,
            &self.factory,
            false,
            self.options.respect_function_pre_permission_amounts,
        );
        state.qp_fields = program.fields.clone();
        state.qp_predicates = program.predicates.clone();
        state.predicate_snap_map = analysis.snapshot_sorts.clone();
        state.predicate_formal_var_map = analysis.snapshot_formals.clone();
        state.more_complete_exhale =
            self.options.exhale_mode == crate::config::ExhaleMode::MoreComplete;
        state.more_complete_exhale_qp =
            self.options.exhale_mode_qp == crate::config::ExhaleMode::MoreComplete;
        state.parallelize_branches = true;
        state
    }
    fn initial_state(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
        member: ferrum_silver::ast::program::Member,
    ) -> Result<NativeState, NativeError<S::Error>> {
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
            analysis.function_handles.clone(),
            joins,
            &self.factory,
            false,
            self.options.respect_function_pre_permission_amounts,
        );
        if self.options.unsafe_wildcard_optimization {
            if let Member::Method(method) = &member {
                state.perm_locations = wildcard_permission_locations(program, method)?;
            }
        }
        use ferrum_silver::ast::utility::{
            nodes::Node,
            quantified_permissions::{self, Resource},
        };
        state.qp_fields = quantified_permissions::quantified_fields(&member, program)
            .map_err(|e| NativeError::Diagnostic(format!("quantified field analysis: {e:?}")))?;
        state.qp_predicates = quantified_permissions::quantified_predicates(&member, program)
            .map_err(|e| {
                NativeError::Diagnostic(format!("quantified predicate analysis: {e:?}"))
            })?;
        state.qp_magic_wands =
            quantified_permissions::quantified_magic_wands(&Node::Member(member.clone()), program)
                .map_err(|e| NativeError::Diagnostic(format!("quantified wand analysis: {e:?}")))?
                .into_iter()
                .map(|wand| {
                    crate::state::chunks::MagicWandIdentifier::new(wand, program)
                        .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))
                })
                .collect::<Result<_, _>>()?;
        state.heap_dependent_triggers = quantified_permissions::resource_triggers(&member, program)
            .map_err(|e| NativeError::Diagnostic(format!("resource trigger analysis: {e:?}")))?
            .into_iter()
            .map(|resource| match resource {
                Resource::Field(field) => Ok(ResourceKey::Field(Arc::new(field))),
                Resource::Predicate(predicate) => Ok(ResourceKey::Predicate(Arc::new(predicate))),
                Resource::MagicWand(wand) => {
                    crate::state::chunks::MagicWandIdentifier::new(wand, program)
                        .map(ResourceKey::Wand)
                        .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))
                }
            })
            .collect::<Result<_, _>>()?;
        let info = match &member {
            Member::Domain(m) => &m.meta.info,
            Member::Field(m) => &m.meta.info,
            Member::Function(m) => &m.meta.info,
            Member::Predicate(m) => &m.meta.info,
            Member::Method(m) => &m.meta.info,
            Member::Extension(_) => {
                return Err(NativeError::Unsupported("extension member annotations"));
            }
        };
        let mut mode = |quantified| {
            crate::supporters::annotation_supporter::exhale_mode(
                member.name(),
                info,
                quantified,
                |message| {
                    self.warnings.push(message);
                    Ok::<_, ()>(())
                },
            )
            .map_err(|_| NativeError::Unsupported("exhale annotation"))
        };
        state.more_complete_exhale = mode(false)?.unwrap_or(self.options.exhale_mode)
            == crate::config::ExhaleMode::MoreComplete;
        state.more_complete_exhale_qp = mode(true)?.unwrap_or(self.options.exhale_mode_qp)
            == crate::config::ExhaleMode::MoreComplete;
        state.current_member = Some(member);
        state.predicate_snap_map = analysis.snapshot_sorts.clone();
        state.predicate_formal_var_map = analysis.snapshot_formals.clone();
        Ok(state)
    }
}
impl<S: Prover> crate::verifier::default_main_verifier::MainVerificationServices
    for NativeVerifierContext<
        S,
        crate::supporters::predicate_verification_unit::PredicateData,
        NativeFunctionData,
    >
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
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
        if !program.extensions.is_empty() {
            return Err(NativeError::Unsupported("program extension analysis"));
        }
        let general = use_general_preamble(program, &self.base.symbol_converter, &self.factory)
            .map_err(NativeError::Preamble)?;
        let has_quantified = crate::verifier::native_preamble::uses_quantified_resource(program)
            .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
        let (has_sequence, has_set, has_map, has_multiset) = if general {
            (false, false, false, false)
        } else {
            collection_program(program).map_err(NativeError::Preamble)?
        };
        if !general
            && (has_sequence || has_set || has_map || has_multiset)
            && !program.domains.is_empty()
        {
            return Err(NativeError::Unsupported(
                "collections combined with user domains",
            ));
        }
        if !general && (has_sequence || has_set || has_map || has_multiset || has_quantified) {
            crate::verifier::native_preamble::analyze_collections(
                program,
                &self.base.symbol_converter,
                &self.factory,
                self.factory.options().use_old_axiomatization,
            )
            .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
        }
        if general {
            crate::verifier::native_preamble::analyze_general(
                program,
                &self.base.symbol_converter,
                &self.factory,
                self.factory.options().use_old_axiomatization,
                1,
            )
            .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
        }
        if self.options.enable_simplified_unfolds {
            return Err(NativeError::Unsupported(
                "simplified predicate unfold recorder",
            ));
        }
        fn inspect(
            node: &Node,
            program: &ferrum_silver::ast::program::Program,
        ) -> Result<(), &'static str> {
            // Domain axioms are checked and translated by the native domain contributor.
            if matches!(node, Node::DomainAxiom(_)) {
                return Ok(());
            }
            if matches!(node, Node::Type(typ) if matches!(typ,Type::Extension(_))) {
                return Err("collection or domain preamble analysis");
            }
            if matches!(node,Node::Exp(exp) if matches!(exp.kind(),ExpKind::Extension(_))) {
                return Err("extension preamble analysis");
            }
            for child in subnodes(node).map_err(|_| "program analysis traversal")? {
                inspect(&child, program)?;
            }
            Ok(())
        }
        inspect(&Node::Program(program.clone()), program).map_err(NativeError::Unsupported)?;
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
        let general = use_general_preamble(program, &self.base.symbol_converter, &self.factory)
            .map_err(NativeError::Preamble)?;
        let mut contributed_sorts = Vec::new();
        if general {
            let preamble = crate::verifier::native_preamble::analyze_general(
                program,
                &self.base.symbol_converter,
                &self.factory,
                self.factory.options().use_old_axiomatization,
                1,
            )
            .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            preamble
                .declare_sorts(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            preamble
                .declare_symbols(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            preamble
                .emit_axioms(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            contributed_sorts.extend(preamble.sorts().cloned());
        } else {
            let (has_sequence, has_set, has_map, has_multiset) =
                collection_program(program).map_err(NativeError::Preamble)?;
            let has_quantified =
                crate::verifier::native_preamble::uses_quantified_resource(program)
                    .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            let collections =
                if has_sequence || has_set || has_map || has_multiset || has_quantified {
                    Some(
                        crate::verifier::native_preamble::analyze_collections(
                            program,
                            &self.base.symbol_converter,
                            &self.factory,
                            self.factory.options().use_old_axiomatization,
                        )
                        .map_err(|e| NativeError::Preamble(format!("{e:?}")))?,
                    )
                } else {
                    None
                };
            let domain_preamble =
                native_domain_preamble(program, &self.base.symbol_converter, &self.factory)
                    .map_err(NativeError::Preamble)?;
            domain_preamble
                .declare_sorts(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            if let Some(preamble) = &collections {
                preamble
                    .declare_sorts(&self.factory, &mut self.base.decider.prover)
                    .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            }
            domain_preamble
                .declare_symbols(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            if let Some(preamble) = &collections {
                preamble
                    .declare_symbols(&self.factory, &mut self.base.decider.prover)
                    .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            }
            domain_preamble
                .emit_axioms(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            if let Some(preamble) = &collections {
                preamble
                    .emit_axioms(&mut self.base.decider.prover)
                    .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            }
            contributed_sorts.extend(domain_preamble.sorts().cloned());
            if let Some(preamble) = &collections {
                contributed_sorts.extend(preamble.sorts().cloned());
            }
        }
        let predicates = crate::supporters::predicate_verification_unit::analyze_predicates(
            program,
            &self.base.symbol_converter,
            &self.factory,
            Sort::Snap,
        )
        .map_err(NativeError::Sort)?;
        use crate::interfaces::preamble::PreambleReader;
        let reader = crate::decider::smt_lib2_preamble_reader::SmtLib2PreambleReader::default();
        let mut wand_functions = crate::supporters::magic_wand_snap_functions_contributor::MagicWandSnapFunctionsContributor::default();
        wand_functions
            .analyze(program, &reader)
            .map_err(|e| NativeError::Preamble(format!("wand snapshot functions: {e:?}")))?;
        wand_functions
            .declare_sorts(&self.factory, &mut self.base.decider.prover)
            .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        wand_functions
            .declare_symbols(&mut self.base.decider.prover)
            .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        let has_quantified = crate::verifier::native_preamble::uses_quantified_resource(program)
            .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
        let mut field_maps = crate::supporters::qps::field_value_functions_contributor::FieldValueFunctionsContributor::default();
        let mut predicate_maps = crate::supporters::qps::predicate_and_wand_snap_functions_contributor::PredicateAndWandSnapFunctionsContributor::default();
        if has_quantified {
            field_maps
                .analyze(
                    program,
                    &self.base.symbol_converter,
                    &mut self.base.term_converter,
                    &reader,
                    false,
                    |sort| Ok::<_, String>(sort.to_string()),
                )
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            predicate_maps
                .analyze(
                    program,
                    &self.predicate_snapshots,
                    &mut self.base.term_converter,
                    &reader,
                    false,
                    |sort| Ok::<_, String>(sort.to_string()),
                    |wand| {
                        ferrum_silver::ast::pretty::pretty_printer::pretty_expression(wand)
                            .map_err(|e| format!("{e:?}"))
                    },
                )
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            field_maps
                .declare_sorts(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            predicate_maps
                .declare_sorts(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        let mut wrapper_sorts = vec![Sort::Int, Sort::Bool, Sort::Ref, Sort::Perm];
        wrapper_sorts.extend(contributed_sorts);
        wrapper_sorts.extend(wand_functions.sorts.iter().cloned());
        wrapper_sorts.extend(field_maps.sorts.iter().cloned());
        wrapper_sorts.extend(predicate_maps.sorts.iter().cloned());
        for sort in wrapper_sorts {
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
        for blocks in [
            &field_maps.function_blocks,
            &predicate_maps.function_blocks,
            &field_maps.axiom_blocks,
            &predicate_maps.axiom_blocks,
        ] {
            crate::supporters::qps::field_value_functions_contributor::FieldValueFunctionsContributor::emit_blocks(blocks, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        crate::supporters::predicate_verification_unit::declare_predicate_triggers(
            &self.factory,
            &mut self.base.decider.prover,
            &predicates,
        )
        .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        let mut functions = crate::supporters::functions::function_verification_unit::FunctionVerificationUnit::default();
        let factory = self.factory.clone();
        functions.analyze(&factory, &self.base.symbol_converter, &mut self.base.identifiers, program, false, false,
            |_, _| Ok::<_, std::convert::Infallible>((crate::supporters::functions::function_encoding::DefaultFunctionEncoding::state_args(&factory), None)))
            .map_err(|e| NativeError::Execution(format!("function analysis: {e:?}")))?;
        if !program.functions.is_empty() {
            functions
                .declare_analysis_symbols(&factory, &mut self.base.decider.prover, |_| vec![])
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        let mut function_handles = crate::state::package::OrderedMap::default();
        self.function_heights.clear();
        for (name, data) in &functions.data {
            let height = data
                .lock()
                .map_err(|_| NativeError::Execution("function data lock poisoned".into()))?
                .height;
            self.function_heights.insert(name.clone(), height);
            function_handles.insert(
                name.clone(),
                Arc::new(NativeFunctionData(Arc::downgrade(data))),
            );
        }
        self.function_handles = function_handles.clone();
        self.function_units = functions.units();
        self.function_fresh_variables.clear();
        self.failed_functions.clear();
        self.quantified_counter = 0;
        self.heap_supporter_counter = 0;
        Ok(NativeAnalysis {
            functions: std::cell::RefCell::new(functions),
            function_handles,
            predicates,
            snapshot_sorts: self.predicate_snapshots.snap_map.clone(),
            snapshot_formals: self.predicate_snapshots.formal_var_map.clone(),
        })
    }
    fn end_preamble_and_saturate(&mut self) -> Result<(), Self::Error> {
        let timeout = self.options.after_prelude_timeout.map(|timeout_ms| {
            crate::interfaces::decider::prover::ProverStateSaturationTimeout {
                timeout_ms,
                comment: "after prelude".into(),
            }
        });
        self.base
            .decider
            .prover
            .saturate_configured(timeout.as_ref())
            .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))
    }
    fn function_units(&mut self) -> Result<Vec<Self::FunctionUnit>, Self::Error> {
        Ok(self.function_units.clone())
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
        unit: Self::FunctionUnit,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
    ) -> Result<Vec<Self::Result>, Self::Error> {
        let results = self.verify_function_unscoped(program, analysis, &unit)?;
        set_member_scope(
            &results,
            ferrum_silver::ast::program::Member::Function(unit),
        );
        Ok(results)
    }
    fn verify_predicate(
        &mut self,
        unit: Self::PredicateUnit,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
    ) -> Result<Vec<Self::Result>, Self::Error> {
        let results = self.verify_predicate_unscoped(program, analysis, &unit)?;
        set_member_scope(
            &results,
            ferrum_silver::ast::program::Member::Predicate(unit),
        );
        Ok(results)
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
        let results = crate::supporters::method_supporter::verify_method(self, state, method)
            .map_err(|e| NativeError::Execution(format!("{e:?}")))?;
        set_member_scope(
            &results,
            ferrum_silver::ast::program::Member::Method(method.clone()),
        );
        Ok(results)
    }
    fn queue_cfg(
        &mut self,
        cfg: &SilverCfg,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
    ) -> Result<Self::Task, Self::Error> {
        let state = self.initial_cfg_state(program, analysis);
        crate::supporters::cfg_supporter::verify_cfg(self, state, Arc::new(cfg.clone()))
            .map_err(|e| NativeError::Execution(format!("CFG verification: {e:?}")))
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
fn set_member_scope(
    results: &[VerificationResult<VerificationError>],
    member: ferrum_silver::ast::program::Member,
) {
    let scope = Arc::new(member);
    for result in results {
        for item in std::iter::once(result.clone()).chain(result.previous()) {
            item.with_kind(|kind| {
                if let crate::interfaces::verification::ResultKind::Failure(error) = kind {
                    error.set_scope(Some(scope.clone()));
                }
            });
        }
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

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::rules::predicate_supporter::PredicateExecutionServices<
        PD,
        FD,
        JoinMode,
        VerificationError,
    > for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    type VerificationError = PartialVerificationError;

    fn predicate_debugging(&self) -> bool {
        false
    }

    fn consume_predicate_body(
        &mut self,
        state: State<PD, FD, JoinMode>,
        body: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
    > {
        use crate::rules::predicate_supporter::PredicateExecutionError as PE;
        let mut callback_error = None;
        let result = crate::rules::consumer::consume_all(
            self,
            state,
            std::slice::from_ref(body),
            true,
            &|_| error.clone(),
            &mut |ctx, state, snapshot| match continuation(ctx, state, snapshot) {
                Ok(v) => Ok(v),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ConsumptionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(e) = callback_error {
            return Err(e);
        }
        result.map_err(|e| PE::Service(NativeError::Consumption(format!("{e:?}"))))
    }
    fn produce_predicate_chunk(
        &mut self,
        state: State<PD, FD, JoinMode>,
        predicate: &Predicate,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
        snapshot: Term,
        permission: Term,
        permission_exp: Option<Exp>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
    > {
        use crate::rules::predicate_supporter::PredicateExecutionError as PE;
        use ferrum_silver::ast::{program::Member, utility::nodes::Node};
        let full = error
            .due_to(ErrorReason::InsufficientPermission(Node::Member(
                Member::Predicate(predicate.clone()),
            )))
            .map_err(|e| PE::Service(NativeError::Diagnostic(format!("{e:?}"))))?;
        let resource = ResourceKey::Predicate(Arc::new(predicate.clone()));
        let mut callback_error = None;
        let result = crate::rules::heap_supporter::produce_single(
            self,
            state,
            &resource,
            args,
            arg_exps,
            snapshot,
            None,
            permission,
            permission_exp,
            &Some(full),
            true,
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(v) => Ok(v),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ChunkExecutionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(e) = callback_error {
            return Err(e);
        }
        result.map_err(|e| PE::Service(NativeError::Chunk(format!("{e:?}"))))
    }
    fn consume_predicate_chunk(
        &mut self,
        state: State<PD, FD, JoinMode>,
        access: &Exp,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
        permission: &Term,
        permission_exp: Option<&Exp>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
    > {
        use crate::rules::predicate_supporter::PredicateExecutionError as PE;
        let ExpKind::PredicateAccess(location) = access.kind() else {
            return Err(PE::Service(NativeError::Unsupported(
                "predicate access shape",
            )));
        };
        let predicate = state
            .program
            .find_predicate(&location.predicate_name)
            .map_err(|e| PE::Service(NativeError::Diagnostic(format!("{e:?}"))))?
            .clone();
        let full = error
            .due_to(ErrorReason::InsufficientPermission(
                ferrum_silver::ast::utility::nodes::Node::PredicateAccess(location.clone()),
            ))
            .map_err(|e| PE::Service(NativeError::Diagnostic(format!("{e:?}"))))?;
        let heap = state.h.clone();
        let resource = ResourceKey::Predicate(Arc::new(predicate));
        let mut callback_error = None;
        let result = crate::rules::heap_supporter::consume_single(
            self,
            state,
            heap,
            &resource,
            args,
            arg_exps,
            permission,
            permission_exp,
            true,
            &Some(full),
            &mut |ctx, state, heap, snapshot| match continuation(ctx, state, heap, snapshot) {
                Ok(v) => Ok(v),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ChunkExecutionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(e) = callback_error {
            return Err(e);
        }
        result.map_err(|e| PE::Service(NativeError::Chunk(format!("{e:?}"))))
    }
    fn folded_predicate_snapshot(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        predicate: &Predicate,
        args: &[Term],
        snapshot: &Term,
    ) -> Result<Term, Self::Error> {
        let sort = state
            .predicate_snap_map
            .get(&predicate.name)
            .ok_or(NativeError::Unsupported("predicate snapshot sort"))?;
        Ok(self.factory.sort_wrapper(snapshot.clone(), sort.clone()))
    }
    fn cached_predicate_contents(
        &self,
        state: &State<PD, FD, JoinMode>,
        predicate: &Predicate,
    ) -> Result<
        Option<(
            crate::supporters::predicate_verification_unit::PredicateContentsTree,
            Vec<Term>,
        )>,
        Self::Error,
    > {
        Ok(None)
    }
    fn produce_cached_predicate(
        &mut self,
        state: State<PD, FD, JoinMode>,
        tree: &crate::supporters::predicate_verification_unit::PredicateContentsTree,
        replacements: &std::collections::HashMap<Term, Term>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
    > {
        Err(
            crate::rules::predicate_supporter::PredicateExecutionError::Service(
                NativeError::Unsupported("cached predicate contents"),
            ),
        )
    }
    fn produce_unfolded_body(
        &mut self,
        state: State<PD, FD, JoinMode>,
        predicate: &Predicate,
        args: &[Term],
        snapshot: &Term,
        pre_heap: &ListBackedHeap,
        body: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::rules::predicate_supporter::PredicateExecutionError<Self::Error>,
    > {
        use crate::rules::predicate_supporter::PredicateExecutionError as PE;
        let mut callback_error = None;
        let result = crate::rules::producer::produce_all(
            self,
            state,
            NativeSnapshot::Projection(snapshot.clone()),
            std::slice::from_ref(body),
            &|_| error.clone(),
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(v) => Ok(v),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ProductionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(e) = callback_error {
            return Err(e);
        }
        result.map_err(|e| PE::Service(NativeError::Production(format!("{e:?}"))))
    }
    fn saturate_after_unfold(&mut self) -> Result<(), Self::Error> {
        if let Some(ms) = self.options.after_unfold_timeout {
            self.base
                .decider
                .prover
                .saturate(ms, "after unfold")
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        Ok(())
    }
    fn predicate_unfold_triggers_enabled(&self) -> bool {
        !self.options.disable_function_unfold_trigger
    }
    fn assume_unfold_trigger(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        predicate: &Predicate,
        snapshot: &Term,
        heap: &ListBackedHeap,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
    ) -> Result<(), Self::Error> {
        let data = crate::supporters::predicate_verification_unit::PredicateData::new(
            predicate.clone(),
            &self.base.symbol_converter,
            &self.factory,
            Sort::Snap,
        )
        .map_err(NativeError::Sort)?;
        let mut terms = vec![self.factory.sort_wrapper(snapshot.clone(), Sort::Snap)];
        terms.extend_from_slice(args);
        self.assume_term(&self.factory.app(data.trigger_function, terms))
    }
    fn trigger_predicate_resource(
        &mut self,
        state: State<PD, FD, JoinMode>,
        access: &Exp,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        crate::rules::consumer::ConsumptionContext::trigger_resource(
            self, state, access, args, arg_exps,
        )
    }
}

impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn unfold_expression_body(
        &mut self,
        state: State<PD, FD, JoinMode>,
        predicate: &Predicate,
        access: &Exp,
        body: &Exp,
        args: &[Term],
        permission: &Term,
        old_arps: &crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<Term>,
        error: &PartialVerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
            Option<Exp>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<NativeError<S::Error>>> {
        use crate::state::store::AbstractLocalVar;
        use ferrum_silver::ast::program::Member;
        let outer = state.clone();
        let mut state = state.inc_cycle_counter(predicate.clone());
        state.record_visited = true;
        let mut callback_error = None;
        let result = crate::rules::consumer::consume_all(
            self,
            state,
            std::slice::from_ref(access),
            true,
            &|_| error.clone(),
            &mut |ctx, mut state, snapshot| {
                let next: Result<_, EvaluationError<NativeError<S::Error>>> = (|| {
                    let snapshot = snapshot.ok_or(EvaluationError::MissingFunctionSnapshot)?;
                    let location = match access.kind() {
                        ExpKind::PredicateAccessPredicate(p) => Exp::new(
                            ExpKind::PredicateAccess(p.location.clone()),
                            p.location.meta.clone(),
                        ),
                        _ => return Err(EvaluationError::InvalidResourceAccess),
                    };
                    state.function_recorder = state
                        .function_recorder
                        .record_location_snapshot(
                            location,
                            ctx.base.decider.pcs.recorded().branch_conditions(),
                            snapshot.clone(),
                        )
                        .change_depth_by(1);
                    state.constrainable_arps = old_arps.clone();
                    if !ctx.options.disable_function_unfold_trigger {
                        crate::rules::predicate_supporter::PredicateExecutionServices::assume_unfold_trigger(ctx, &state, predicate, &snapshot, &state.h, args, None).map_err(EvaluationError::Context)?;
                    }
                    let scaled =
                        state.scale_permission_factor(permission.clone(), None, &ctx.factory);
                    let mut store = scaled.g.as_ref().clone();
                    for (formal, arg) in predicate.formal_args.iter().zip(args) {
                        let local =
                            Exp::new(ExpKind::LocalVar(formal.local_var()), formal.meta.clone());
                        store =
                            store.with_binding(AbstractLocalVar::new(local), (arg.clone(), None));
                    }
                    let mut bound = scaled.clone();
                    bound.g = Arc::new(store);
                    bound = bound.set_constrainable(
                        bound.constrainable_arps.iter().cloned().collect::<Vec<_>>(),
                        false,
                    );
                    let mut production_callback_error = None;
                    let predicate_body = predicate
                        .body
                        .as_ref()
                        .ok_or(EvaluationError::MissingPredicate(predicate.name.clone()))?;
                    let result = crate::rules::producer::produce_all(
                        ctx,
                        bound,
                        NativeSnapshot::Projection(snapshot),
                        std::slice::from_ref(predicate_body),
                        &|_| error.clone(),
                        &mut |ctx, mut state| {
                            state.g = scaled.g.clone();
                            state.function_recorder = state.function_recorder.change_depth_by(-1);
                            state.record_visited = outer.record_visited;
                            state.permission_scaling_factor =
                                outer.permission_scaling_factor.clone();
                            state.permission_scaling_factor_exp =
                                outer.permission_scaling_factor_exp.clone();
                            state.constrainable_arps = old_arps.clone();
                            state = state.dec_cycle_counter(&Member::Predicate(predicate.clone()));
                            match ctx.consolidate_optional(state) {
                                Ok(state) => match crate::rules::evaluator::evaluate(
                                    ctx,
                                    state,
                                    body,
                                    error,
                                    continuation,
                                ) {
                                    Ok(v) => Ok(v),
                                    Err(e) => {
                                        production_callback_error = Some(e);
                                        Err(ProductionError::Context(
                                            NativeError::ContinuationAbort,
                                        ))
                                    }
                                },
                                Err(e) => Err(ProductionError::Context(e)),
                            }
                        },
                    );
                    if let Some(e) = production_callback_error {
                        return Err(e);
                    }
                    result.map_err(|e| {
                        EvaluationError::Context(NativeError::Production(format!("{e:?}")))
                    })
                })();
                match next {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(ConsumptionError::Context(NativeError::ContinuationAbort))
                    }
                }
            },
        );
        if let Some(e) = callback_error {
            return Err(e);
        }
        result.map_err(|e| EvaluationError::Context(NativeError::Consumption(format!("{e:?}"))))
    }
}
impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn join_unfold_expression(
        &mut self,
        state: State<PD, FD, JoinMode>,
        predicate: &Predicate,
        access: &Exp,
        in_expression: &Exp,
        args: &[Term],
        permission: &Term,
        old_arps: &crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<Term>,
        error: &PartialVerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
            Option<Exp>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<NativeError<S::Error>>> {
        use crate::rules::joiner::{self, JoinDataEntry};
        let factory = self.factory.clone();
        self.base
            .decider
            .push_scope()
            .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
        let mark = self.base.decider.pcs.mark();
        let mut joined = state.clone();
        joined.under_join = true;
        let mut entries = Vec::new();
        let block = self.unfold_expression_body(
            joined,
            predicate,
            access,
            in_expression,
            args,
            permission,
            old_arps,
            error,
            &mut |ctx, result_state, value, debug| {
                let path_conditions = ctx
                    .base
                    .decider
                    .pcs
                    .after(mark)
                    .map_err(EvaluationError::Path)?;
                entries.push(JoinDataEntry {
                    state: joiner::restore_state(result_state, &state),
                    data: (value, debug),
                    path_conditions,
                });
                Ok(VerificationResult::success())
            },
        );
        let cleanup = self.base.decider.pop_scope().map_err(NativeError::Decider);
        let block = match (block, cleanup) {
            (Ok(v), Ok(())) => v,
            (Err(e), Err(cleanup)) => {
                return Err(EvaluationError::TriggerCleanup {
                    evaluation: Box::new(e),
                    cleanup,
                });
            }
            (Err(e), Ok(())) => return Err(e),
            (Ok(_), Err(cleanup)) => return Err(EvaluationError::Context(cleanup)),
        };
        let block = VerificationResult::success().and_then(|| block);
        if !block.continue_verification() {
            return Ok(block);
        }
        if entries.is_empty() {
            return Ok(block.combine(VerificationResult::success, false));
        }
        let (assumptions, feasible) = joiner::joined_conditions(&entries, &factory);
        let (merged, value, debug) = if entries.len() == 1 {
            let entry = &entries[0];
            (
                entry.state.clone(),
                entry.data.0.clone(),
                entry.data.1.clone(),
            )
        } else {
            let sort = self
                .base
                .symbol_converter
                .to_sort(
                    &in_expression
                        .typ()
                        .map_err(EvaluationError::ExpressionType)?,
                )
                .map_err(|e| EvaluationError::Context(NativeError::Sort(e)))?;
            let arguments: Vec<_> = state
                .all_relevant_quantified_variables()
                .into_iter()
                .map(|(term, _)| term)
                .collect();
            let sorts: Vec<_> = arguments.iter().map(|term| term.sort().clone()).collect();
            let (target, _) = self
                .base
                .decider
                .fresh(&factory, "joined_unfolding", &sorts, &sort)
                .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
            let value = match &target {
                ApplicationTarget::Function(f) => factory.app(f.clone(), arguments),
                _ => {
                    return Err(EvaluationError::Context(NativeError::Unsupported(
                        "unfolding join symbol",
                    )));
                }
            };
            let mut merged = entries[0].state.clone();
            for entry in &entries[1..] {
                merged = merged
                    .merge_unconditional(&entry.state, &mut |warning| self.warnings.push(warning))
                    .map_err(|e| EvaluationError::Context(NativeError::State(e)))?;
            }
            merged.function_recorder = merged.function_recorder.record_path_symbol(target);
            for entry in &entries {
                let guard = factory.and(entry.path_conditions.branch_conditions());
                let equation = factory.builtin_equals(value.clone(), entry.data.0.clone());
                self.assume_term(&factory.implies(guard, equation))
                    .map_err(EvaluationError::Context)?;
            }
            (merged, value, None)
        };
        for group in assumptions {
            for term in group {
                self.assume_term(&term).map_err(EvaluationError::Context)?;
            }
        }
        self.assume_term(&feasible)
            .map_err(EvaluationError::Context)?;
        let next = continuation(self, merged, value, debug)?;
        Ok(block.combine(|| next, false))
    }
    fn join_applying_expression(
        &mut self,
        state: State<PD, FD, JoinMode>,
        wand: &Exp,
        in_expression: &Exp,
        error: &PartialVerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
            Option<Exp>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<NativeError<S::Error>>> {
        use crate::rules::joiner::{self, JoinDataEntry};
        let factory = self.factory.clone();
        self.base
            .decider
            .push_scope()
            .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
        let mark = self.base.decider.pcs.mark();
        let mut joined = state.clone();
        joined.under_join = true;
        let mut entries = Vec::new();
        use crate::rules::magic_wand_supporter::WandApplicationError as WE;
        let mut evaluation_error = None;
        let block = crate::rules::magic_wand_supporter::apply_wand(
            &factory,
            self,
            joined,
            wand,
            error,
            &mut |ctx, result_state| {
                let result = crate::rules::evaluator::evaluate(
                    ctx,
                    result_state,
                    in_expression,
                    error,
                    &mut |ctx, result_state, value, debug| {
                        let path_conditions = ctx
                            .base
                            .decider
                            .pcs
                            .after(mark)
                            .map_err(EvaluationError::Path)?;
                        entries.push(JoinDataEntry {
                            state: joiner::restore_state(result_state, &state),
                            data: (value, debug),
                            path_conditions,
                        });
                        Ok(VerificationResult::success())
                    },
                );
                match result {
                    Ok(value) => Ok(value),
                    Err(e) => {
                        evaluation_error = Some(e);
                        Err(WE::Service(NativeError::ContinuationAbort))
                    }
                }
            },
        );
        let block = match (evaluation_error, block) {
            (Some(error), _) => Err(error),
            (None, result) => result.map_err(|e| {
                EvaluationError::Context(NativeError::Execution(format!(
                    "applying expression: {e:?}"
                )))
            }),
        };
        let cleanup = self.base.decider.pop_scope().map_err(NativeError::Decider);
        let block = match (block, cleanup) {
            (Ok(v), Ok(())) => v,
            (Err(e), Err(cleanup)) => {
                return Err(EvaluationError::TriggerCleanup {
                    evaluation: Box::new(e),
                    cleanup,
                });
            }
            (Err(e), Ok(())) => return Err(e),
            (Ok(_), Err(cleanup)) => return Err(EvaluationError::Context(cleanup)),
        };
        let block = VerificationResult::success().and_then(|| block);
        if !block.continue_verification() {
            return Ok(block);
        }
        if entries.is_empty() {
            return Ok(block.combine(VerificationResult::success, false));
        }
        let (assumptions, feasible) = joiner::joined_conditions(&entries, &factory);
        let (merged, value, debug) = if entries.len() == 1 {
            let entry = &entries[0];
            (
                entry.state.clone(),
                entry.data.0.clone(),
                entry.data.1.clone(),
            )
        } else {
            let sort = self
                .base
                .symbol_converter
                .to_sort(
                    &in_expression
                        .typ()
                        .map_err(EvaluationError::ExpressionType)?,
                )
                .map_err(|e| EvaluationError::Context(NativeError::Sort(e)))?;
            let arguments: Vec<_> = state
                .all_relevant_quantified_variables()
                .into_iter()
                .map(|(term, _)| term)
                .collect();
            let sorts: Vec<_> = arguments.iter().map(|term| term.sort().clone()).collect();
            let (target, _) = self
                .base
                .decider
                .fresh(&factory, "joined_applying", &sorts, &sort)
                .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
            let value = match &target {
                ApplicationTarget::Function(f) => factory.app(f.clone(), arguments),
                _ => {
                    return Err(EvaluationError::Context(NativeError::Unsupported(
                        "applying join symbol",
                    )));
                }
            };
            let mut merged = entries[0].state.clone();
            for entry in &entries[1..] {
                merged = merged
                    .merge_unconditional(&entry.state, &mut |warning| self.warnings.push(warning))
                    .map_err(|e| EvaluationError::Context(NativeError::State(e)))?;
            }
            merged.function_recorder = merged.function_recorder.record_path_symbol(target);
            for entry in &entries {
                let guard = factory.and(entry.path_conditions.branch_conditions());
                let equation = factory.builtin_equals(value.clone(), entry.data.0.clone());
                self.assume_term(&factory.implies(guard, equation))
                    .map_err(EvaluationError::Context)?;
            }
            (merged, value, None)
        };
        for group in assumptions {
            for term in group {
                self.assume_term(&term).map_err(EvaluationError::Context)?;
            }
        }
        self.assume_term(&feasible)
            .map_err(EvaluationError::Context)?;
        let next = continuation(self, merged, value, debug)?;
        Ok(block.combine(|| next, false))
    }
}

impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    /// Source LetSupporter recursion, with evaluator continuations bound to this context.
    fn handle_native_let(
        &mut self,
        state: State<PD, FD, JoinMode>,
        expression: &Exp,
        error: &PartialVerificationError,
        bindings: crate::state::store::MapBackedStore,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            crate::state::store::MapBackedStore,
            Exp,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<NativeError<S::Error>>> {
        if let ExpKind::Let(variable, value, body) = expression.kind() {
            let key = crate::state::store::AbstractLocalVar::new(Exp::new(
                ExpKind::LocalVar(variable.local_var()),
                variable.meta.clone(),
            ));
            crate::rules::evaluator::evaluate(
                self,
                state,
                value,
                error,
                &mut |ctx, mut state, term, debug| {
                    let value = (term, debug);
                    let next = bindings.with_binding(key.clone(), value.clone());
                    state.g = Arc::new(state.g.with_binding(key.clone(), value));
                    ctx.handle_native_let(state, body, error, next, continuation)
                },
            )
        } else {
            continuation(self, state, bindings, expression.clone())
        }
    }
}

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::rules::evaluator::QuantifiedScopeContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn fresh_quantified_variable(
        &mut self,
        decl: &LocalVarDecl,
    ) -> Result<(Term, Option<Exp>), Self::Error> {
        let sort = self
            .base
            .symbol_converter
            .to_sort(&decl.typ)
            .map_err(NativeError::Sort)?;
        let term = self
            .base
            .decider
            .fresh_variable(&self.factory, &decl.name, &sort, false, None)
            .map_err(NativeError::Decider)?;
        Ok((term, None))
    }
    fn locally_quantified(
        &mut self,
        state: State<PD, FD, JoinMode>,
        block: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                crate::rules::evaluator::ScopedQuantifiedState<PD, FD, JoinMode>,
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
            crate::rules::evaluator::ScopedQuantifiedState<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        self.base
            .decider
            .push_scope()
            .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
        let mut data = None;
        let block = block(self, state, &mut |_, value| {
            if data.is_some() {
                return Err(EvaluationError::Context(NativeError::Unsupported(
                    "multiple local quantifier results",
                )));
            }
            data = Some(value);
            Ok(VerificationResult::success())
        });
        let cleanup = self.base.decider.pop_scope().map_err(NativeError::Decider);
        let block = match (block, cleanup) {
            (Ok(v), Ok(())) => v,
            (Err(e), Err(cleanup)) => {
                return Err(EvaluationError::TriggerCleanup {
                    evaluation: Box::new(e),
                    cleanup,
                });
            }
            (Err(e), Ok(())) => return Err(e),
            (Ok(_), Err(cleanup)) => return Err(EvaluationError::Context(cleanup)),
        };
        if block.is_fatal() {
            return Ok(block);
        }
        if let Some(data) = data {
            let next = continuation(self, data)?;
            Ok(block.and_then(|| next))
        } else {
            Ok(block)
        }
    }
    fn path_mark(&mut self) -> crate::decider::path_conditions::Mark {
        self.base.decider.pcs.mark()
    }
    fn set_quantified_branch(
        &mut self,
        condition: Term,
        original: Exp,
        rewritten: Option<Exp>,
    ) -> Result<(), Self::Error> {
        self.base
            .decider
            .set_branch_condition(condition, (original, rewritten), None)
            .map_err(NativeError::Decider)
    }
    fn path_after(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<crate::decider::path_conditions::RecordedPathConditions, Self::Error> {
        self.base
            .decider
            .pcs
            .after(mark)
            .map_err(|e| NativeError::Decider(DeciderError::Path(e)))
    }
    fn evaluate_triggers(
        &mut self,
        state: State<PD, FD, JoinMode>,
        triggers: &[ferrum_silver::ast::expression::Trigger],
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Vec<crate::state::terms::Trigger>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<Self::Error>> {
        crate::rules::evaluator::evaluate_triggers(self, state, triggers, error, continuation)
    }
    fn quantified_debug(
        &mut self,
        paths: &crate::decider::path_conditions::RecordedPathConditions,
        quantifier: crate::state::terms::Quantifier,
        variables: &[Term],
        variable_expressions: &[Exp],
        ast_triggers: &[ferrum_silver::ast::expression::Trigger],
        term_triggers: &[crate::state::terms::Trigger],
        condition: &Term,
    ) -> Result<
        (
            crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
                crate::debugger::debug_exp::DebugExp,
            >,
            crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
                crate::debugger::debug_exp::DebugExp,
            >,
        ),
        Self::Error,
    > {
        Err(NativeError::Unsupported("quantifier debugging"))
    }
}
#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::rules::evaluator::TriggerEvaluationContext<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn cacheable_trigger(&self, expression: &Exp) -> bool {
        expression.is_possible_trigger()
            || matches!(
                expression.kind(),
                ExpKind::FieldAccess(_) | ExpKind::Old(_) | ExpKind::LabelledOld(..)
            )
    }
    fn path_pop_until(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<(), Self::Error> {
        self.base
            .decider
            .pcs
            .pop_until_mark(mark)
            .map_err(|e| NativeError::Decider(DeciderError::Path(e)))
    }
    fn reported_errors(&self) -> usize {
        self.base.errors_reported.load(Ordering::SeqCst)
    }
    fn set_reported_errors(&mut self, count: usize) {
        self.base.errors_reported.store(count, Ordering::SeqCst);
    }
    fn assume_trigger_delta(
        &mut self,
        paths: &crate::decider::path_conditions::RecordedPathConditions,
    ) -> Result<(), Self::Error> {
        self.base
            .decider
            .assume(
                paths.assumptions().into_iter().map(|term| (term, None)),
                false,
                false,
            )
            .map_err(NativeError::Decider)
    }
    fn adapt_trigger_terms(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        terms: Vec<Term>,
    ) -> Result<Vec<Term>, Self::Error> {
        Ok(terms)
    }
    fn warn_trigger(&mut self, expression: &Exp) -> Result<(), Self::Error> {
        self.warnings
            .push(format!("Might not be able to use trigger: {expression:?}"));
        Ok(())
    }
    fn handles_resource_trigger(&self, state: &State<PD, FD, JoinMode>, expression: &Exp) -> bool {
        match expression.kind() {
            ExpKind::FieldAccess(access) => state
                .heap_dependent_triggers
                .contains(&ResourceKey::Field(Arc::new(access.field.clone()))),
            ExpKind::PredicateAccess(access) => state
                .program
                .find_predicate_optionally(&access.predicate_name)
                .is_some_and(|predicate| {
                    state
                        .heap_dependent_triggers
                        .contains(&ResourceKey::Predicate(Arc::new(predicate.clone())))
                }),
            ExpKind::MagicWand(..) => {
                crate::state::chunks::MagicWandIdentifier::new(expression.clone(), &state.program)
                    .is_ok_and(|wand| {
                        state
                            .heap_dependent_triggers
                            .contains(&ResourceKey::Wand(wand))
                    })
            }
            _ => false,
        }
    }
    fn resource_trigger_variants(
        &mut self,
        state: State<PD, FD, JoinMode>,
        expression: &Exp,
        error: &Self::PartialError,
    ) -> Result<
        (
            State<PD, FD, JoinMode>,
            Vec<Term>,
            Vec<Vec<Term>>,
            Vec<crate::rules::quantified_chunk_support::SnapshotMapDefinition>,
        ),
        Self::Error,
    > {
        use crate::rules::quantified_chunk_support::GeneralConsumptionExecution;
        let (resource, args) = match expression.kind() {
            ExpKind::FieldAccess(access) => (
                ResourceKey::Field(Arc::new(access.field.clone())),
                vec![access.receiver.clone()],
            ),
            ExpKind::PredicateAccess(access) => (
                ResourceKey::Predicate(Arc::new(
                    state
                        .program
                        .find_predicate(&access.predicate_name)
                        .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?
                        .clone(),
                )),
                access.args.clone(),
            ),
            ExpKind::MagicWand(..) => (
                ResourceKey::Wand(
                    crate::state::chunks::MagicWandIdentifier::new(
                        expression.clone(),
                        &state.program,
                    )
                    .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?,
                ),
                expression
                    .magic_wand_subexpressions(&state.program)
                    .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?,
            ),
            _ => return Err(NativeError::Unsupported("heap trigger resource shape")),
        };
        let factory = self.factory.clone();
        let source = native_quantified_source(&resource);
        let formals = state
            .formal_arg_vars(&source, &self.base.symbol_converter, &factory)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        let chunks = native_quantified_chunks(&state.h, &resource);
        let (definition, cache) = GeneralConsumptionExecution::summarise_general_consumed(
            self, &state, &resource, &formals, &chunks, None,
        )?;
        let mut result_state = state.clone();
        result_state.sm_cache = cache;
        let mut trigger_state = result_state.clone();
        trigger_state.trigger_exp = true;
        let mut evaluated = None;
        let result = crate::rules::evaluator::evaluate_all(
            self,
            trigger_state,
            &args,
            &|_| error.clone(),
            &mut |_, _, terms, _| {
                evaluated = Some(terms);
                Ok(VerificationResult::success())
            },
        )
        .map_err(|e| NativeError::Evaluation(format!("heap trigger arguments: {e:?}")))?;
        if result.is_fatal() {
            return Err(NativeError::Unsupported(
                "heap trigger argument verification failure",
            ));
        }
        let terms = evaluated.ok_or(NativeError::Unsupported(
            "unreachable heap trigger arguments",
        ))?;
        let trigger = factory.resource_trigger(&resource, definition.snapshot_map.clone(), terms);
        Ok((
            state,
            definition.value_definitions.clone(),
            vec![vec![trigger]],
            vec![definition],
        ))
    }
    fn assume_heap_trigger_axioms(
        &mut self,
        expressions: &[Exp],
        axioms: &[Term],
    ) -> Result<(), Self::Error> {
        for term in axioms {
            self.assume_term(term)?;
        }
        Ok(())
    }
}
#[allow(unused_variables)]
impl<S: Prover, PD, FD> crate::supporters::quantifier_supporter::QuantifierTriggerServices
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn generate_trigger_sets(
        &mut self,
        variables: &[Term],
        body: &Term,
    ) -> Result<Option<(Vec<crate::state::terms::Trigger>, Vec<Term>)>, Self::Error> {
        let (triggers, extra) = self
            .base
            .trigger_generator
            .generate_group(&self.factory, variables, std::slice::from_ref(body), false)
            .map_err(|e| NativeError::Chunk(format!("quantifier trigger search: {e:?}")))?;
        Ok((!triggers.is_empty()).then_some((triggers, extra)))
    }
    fn fresh_projection(&mut self, sort: &Sort) -> Result<Term, Self::Error> {
        self.base
            .decider
            .fresh_variable(&self.factory, "proj", sort, false, None)
            .map_err(NativeError::Decider)
    }
    fn render_term(&mut self, term: &Term) -> Result<String, Self::Error> {
        self.base
            .term_converter
            .convert_term(term)
            .map_err(|e| NativeError::Preamble(format!("{e:?}")))
    }
    fn render_trigger(
        &mut self,
        trigger: &crate::state::terms::Trigger,
    ) -> Result<String, Self::Error> {
        trigger
            .terms
            .iter()
            .map(|term| {
                self.base
                    .term_converter
                    .convert_term(term)
                    .map_err(|e| NativeError::Preamble(format!("{e:?}")))
            })
            .collect::<Result<Vec<_>, _>>()
            .map(|terms| terms.join(" "))
    }
}

/// Source method-local resource scan for unsafe wildcard optimization. Contract projections
/// differ at caller and callee boundaries, and called method bodies are not traversed.
fn wildcard_permission_locations<E>(
    program: &ferrum_silver::ast::program::Program,
    method: &Method,
) -> Result<Vec<ResourceKey>, NativeError<E>> {
    use ferrum_silver::ast::{
        statement::StmtKind,
        utility::{
            expressions::{when_exhaling, when_inhaling},
            nodes::{Node, subnodes},
        },
    };
    let Some(body) = &method.body else {
        return Ok(Vec::new());
    };
    fn scan<E>(
        program: &ferrum_silver::ast::program::Program,
        node: &Node,
        out: &mut Vec<ResourceKey>,
        inspect_calls: bool,
    ) -> Result<(), NativeError<E>> {
        if let Node::Exp(exp) = node {
            if let ExpKind::CurrentPerm(access) = exp.kind() {
                let key = match access.kind() {
                    ExpKind::FieldAccess(field) => {
                        Some(ResourceKey::Field(Arc::new(field.field.clone())))
                    }
                    ExpKind::PredicateAccess(location) => Some(ResourceKey::Predicate(Arc::new(
                        program
                            .find_predicate(&location.predicate_name)
                            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?
                            .clone(),
                    ))),
                    _ => None,
                };
                if let Some(key) = key {
                    if !out.contains(&key) {
                        out.push(key);
                    }
                }
            }
        }
        if inspect_calls {
            if let Node::Stmt(stmt) = node {
                if let StmtKind::MethodCall { method_name, .. } = stmt.kind() {
                    let called = program
                        .find_method(method_name)
                        .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
                    for exp in &called.pres {
                        let exp = when_exhaling(exp)
                            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
                        scan(program, &Node::Exp(exp), out, false)?;
                    }
                    for exp in &called.posts {
                        let exp = when_inhaling(exp)
                            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
                        scan(program, &Node::Exp(exp), out, false)?;
                    }
                }
            }
        }
        for child in subnodes(node).map_err(|e| NativeError::Diagnostic(format!("{e:?}")))? {
            scan(program, &child, out, inspect_calls)?;
        }
        Ok(())
    }
    let mut locations = Vec::new();
    scan(program, &Node::Stmt(body.clone()), &mut locations, true)?;
    for exp in &method.pres {
        let exp = when_inhaling(exp).map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        scan(program, &Node::Exp(exp), &mut locations, false)?;
    }
    for exp in &method.posts {
        let exp = when_exhaling(exp).map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        scan(program, &Node::Exp(exp), &mut locations, false)?;
    }
    Ok(locations)
}

/// Restrict collection element sorts until nested declaration order is wired.
fn collection_program(
    program: &ferrum_silver::ast::program::Program,
) -> Result<(bool, bool, bool, bool), String> {
    use ferrum_silver::ast::{
        r#type::Type,
        utility::{domain_instances::collect_ground_types, nodes::Node},
    };
    let ground = collect_ground_types(&Node::Program(program.clone()), program)
        .map_err(|e| format!("{e:?}"))?;
    let (mut sequences, mut sets, mut maps, mut multisets) = (false, false, false, false);
    fn nested_element(t: &Type) -> bool {
        match t {
            Type::Seq(inner) | Type::Set(inner) | Type::Multiset(inner) => nested_element(inner),
            Type::Map(pair) => nested_element(&pair.0) && nested_element(&pair.1),
            Type::Int | Type::Bool | Type::Ref | Type::Perm => true,
            _ => false,
        }
    }
    for typ in ground {
        match typ {
            Type::Seq(element) => {
                if !nested_element(&element) {
                    return Err(
                        "nested or nonprimitive sequence element sort is not connected".into(),
                    );
                }
                sequences = true;
            }
            Type::Set(element) => {
                if !nested_element(&element) {
                    return Err("nested or nonprimitive set element sort is not connected".into());
                }
                sets = true;
            }
            Type::Multiset(element) => {
                if !nested_element(&element) {
                    return Err(
                        "nested or nonprimitive multiset element sort is not connected".into(),
                    );
                }
                multisets = true;
            }
            Type::Map(pair) => {
                if !nested_element(&pair.0) || !nested_element(&pair.1) {
                    return Err("nonprimitive map key or value sort is not connected".into());
                }
                maps = true;
            }
            _ => {}
        }
    }
    Ok((sequences, sets, maps, multisets))
}

fn native_domain_preamble(
    program: &ferrum_silver::ast::program::Program,
    converter: &crate::state::symbol_converter::DefaultSymbolConverter,
    factory: &TermFactory,
) -> Result<crate::verifier::native_preamble::NativePreambleData, String> {
    let has_generic_axioms = program
        .domains
        .iter()
        .any(|domain| !domain.type_vars.is_empty() && !domain.axioms.is_empty());
    if has_generic_axioms {
        crate::verifier::native_preamble::analyze_generic_axioms(program, converter, factory)
    } else {
        crate::verifier::native_preamble::analyze_with_multisets(program, converter, factory)
    }
    .map_err(|e| format!("{e:?}"))
}

/// Admit source ground closure for uninterpreted domains and collection instances.
fn use_general_preamble(
    program: &ferrum_silver::ast::program::Program,
    converter: &crate::state::symbol_converter::DefaultSymbolConverter,
    factory: &TermFactory,
) -> Result<bool, String> {
    use ferrum_silver::ast::{
        expression::ExpKind,
        r#type::Type,
        utility::nodes::{Node, subnodes},
    };
    fn contains_backend(node: &Node) -> Result<bool, String> {
        if matches!(node, Node::Type(Type::Backend(_))) {
            return Ok(true);
        }
        for child in subnodes(node).map_err(|e| format!("{e:?}"))? {
            if contains_backend(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    let backend = contains_backend(&Node::Program(program.clone()))?
        || program.domains.iter().any(|domain| {
            domain
                .functions
                .iter()
                .any(|function| function.interpretation.is_some())
        });
    let collection = collection_program(program);
    let legacy = native_domain_preamble(program, converter, factory);
    let quantified = crate::verifier::native_preamble::uses_quantified_resource(program)
        .map_err(|e| format!("{e:?}"))?;
    if let Ok((seq, set, map, multiset)) = collection
        && legacy.is_ok()
        && !backend
        && (!(seq || set || map || multiset || quantified) || program.domains.is_empty())
    {
        return Ok(false);
    }
    if program.domains.is_empty() && !backend {
        return Err("general domain preamble requires a user domain".into());
    }
    fn inspect(
        node: &Node,
        program: &ferrum_silver::ast::program::Program,
        name: &str,
        dependencies: &mut Vec<String>,
    ) -> Result<(), String> {
        if matches!(node, Node::Type(Type::Extension(_))) {
            return Err("backend or extension types in the general domain preamble".into());
        }
        if let Node::Type(Type::Domain(domain)) = node {
            if domain.domain_name != name {
                dependencies.push(domain.domain_name.clone());
            }
        }
        if let Node::Exp(exp) = node {
            match exp.kind() {
                ExpKind::FuncApp(..) => {
                    return Err("heap function in general domain axioms".into());
                }
                ExpKind::DomainFuncApp(function, ..) => {
                    let target = program
                        .find_domain_function_optionally(function)
                        .ok_or_else(|| format!("unknown domain function {function}"))?;
                    if target.domain_name != name {
                        dependencies.push(target.domain_name.clone());
                    }
                }
                _ => {}
            }
        }
        for child in subnodes(node).map_err(|e| format!("{e:?}"))? {
            inspect(&child, program, name, dependencies)?;
        }
        Ok(())
    }
    let mut dependencies = std::collections::HashMap::<String, Vec<String>>::new();
    for domain in &program.domains {
        let mut targets = Vec::new();
        inspect(
            &Node::Member(ferrum_silver::ast::program::Member::Domain(domain.clone())),
            program,
            &domain.name,
            &mut targets,
        )?;
        dependencies.insert(domain.name.clone(), targets);
    }
    for target in dependencies.values().flatten() {
        if !dependencies.contains_key(target) {
            return Err(format!("unknown domain dependency {target}"));
        }
    }
    Ok(true)
}

impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    /// Source join(resetState=false): collect branch-local outcomes, merge and replay paths.
    fn join_impure_branches<T: Clone>(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        yes: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                T,
            )
                -> Result<VerificationResult<VerificationError>, NativeError<S::Error>>,
        )
            -> Result<VerificationResult<VerificationError>, NativeError<S::Error>>,
        no: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                T,
            )
                -> Result<VerificationResult<VerificationError>, NativeError<S::Error>>,
        )
            -> Result<VerificationResult<VerificationError>, NativeError<S::Error>>,
        merge: &mut dyn FnMut(
            &mut Self,
            &[crate::rules::joiner::JoinDataEntry<PD, FD, JoinMode, T>],
        )
            -> Result<(State<PD, FD, JoinMode>, T), NativeError<S::Error>>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            T,
        ) -> Result<
            VerificationResult<VerificationError>,
            NativeError<S::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        use crate::rules::joiner::{self, JoinDataEntry};
        self.base
            .decider
            .push_scope()
            .map_err(NativeError::Decider)?;
        let mark = self.base.decider.pcs.mark();
        let mut state = state;
        state.under_join = true;
        let entries = std::cell::RefCell::new(Vec::<JoinDataEntry<PD, FD, JoinMode, T>>::new());
        let saved_error = std::cell::RefCell::new(None);
        let block = crate::rules::executor::CfgContext::branch_edge(
            self,
            state,
            condition,
            original,
            rewritten,
            &mut |ctx, state| {
                let result = yes(ctx, state, &mut |ctx, state, data| {
                    let paths = ctx
                        .base
                        .decider
                        .pcs
                        .after(mark)
                        .map_err(|e| NativeError::Decider(DeciderError::Path(e)))?;
                    entries.borrow_mut().push(JoinDataEntry {
                        state,
                        data,
                        path_conditions: paths,
                    });
                    Ok(VerificationResult::success())
                });
                match result {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        *saved_error.borrow_mut() = Some(e);
                        Err(ExecutionError::Context(NativeError::ContinuationAbort))
                    }
                }
            },
            &mut |ctx, state| {
                let result = no(ctx, state, &mut |ctx, state, data| {
                    let paths = ctx
                        .base
                        .decider
                        .pcs
                        .after(mark)
                        .map_err(|e| NativeError::Decider(DeciderError::Path(e)))?;
                    entries.borrow_mut().push(JoinDataEntry {
                        state,
                        data,
                        path_conditions: paths,
                    });
                    Ok(VerificationResult::success())
                });
                match result {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        *saved_error.borrow_mut() = Some(e);
                        Err(ExecutionError::Context(NativeError::ContinuationAbort))
                    }
                }
            },
        );
        let cleanup = self.base.decider.pop_scope().map_err(NativeError::Decider);
        let block = if let Some(e) = saved_error.into_inner() {
            Err(e)
        } else {
            block.map_err(|e| NativeError::Execution(format!("{e:?}")))
        };
        let block = match (block, cleanup) {
            (Ok(v), Ok(())) => v,
            (Err(e), Ok(())) => return Err(e),
            (Ok(_), Err(e)) => return Err(e),
            (Err(e), Err(cleanup)) => {
                return Err(NativeError::Cleanup(format!("{e:?}; cleanup: {cleanup:?}")));
            }
        };
        let block = VerificationResult::success().and_then(|| block);
        if !block.continue_verification() {
            return Ok(block);
        }
        let entries = entries.into_inner();
        if entries.is_empty() {
            return Ok(block.combine(VerificationResult::success, false));
        }
        let (state, data) = merge(self, &entries)?;
        let (assumptions, feasible) = joiner::joined_conditions(&entries, &self.factory);
        for group in assumptions {
            for term in group {
                self.assume_term(&term)?;
            }
        }
        self.assume_term(&feasible)?;
        let next = continuation(self, state, data)?;
        Ok(block.combine(|| next, false))
    }
}
impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn joined_production(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        consolidate: bool,
        yes: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ProductionError<NativeError<S::Error>>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<NativeError<S::Error>>,
        >,
        no: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ProductionError<NativeError<S::Error>>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<NativeError<S::Error>>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ProductionError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ProductionError<NativeError<S::Error>>> {
        let error = std::cell::RefCell::new(None);
        let result = self.join_impure_branches(
            state,
            condition,
            original,
            rewritten,
            &mut |ctx, state, done| match yes(ctx, state, &mut |ctx, state| {
                done(ctx, state, ()).map_err(ProductionError::Context)
            }) {
                Ok(v) => Ok(v),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
            &mut |ctx, state, done| match no(ctx, state, &mut |ctx, state| {
                done(ctx, state, ()).map_err(ProductionError::Context)
            }) {
                Ok(v) => Ok(v),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
            &mut |ctx, entries| {
                let state = match entries {
                    [entry] => entry.state.clone(),
                    [first, second] => {
                        let factory = ctx.factory.clone();
                        let merged = first
                            .state
                            .merge_recorded(
                                &first.path_conditions,
                                &second.state,
                                &second.path_conditions,
                                &factory,
                                false,
                                &mut |w| ctx.warnings.push(w),
                            )
                            .map_err(NativeError::State)?;
                        if consolidate {
                            crate::rules::execution_flow_controller::RetryContext::consolidate(
                                ctx, merged,
                            )?
                        } else {
                            merged
                        }
                    }
                    _ => {
                        return Err(NativeError::Unsupported(
                            "unexpected joined production branches",
                        ));
                    }
                };
                Ok((state, ()))
            },
            &mut |ctx, state, ()| match continuation(ctx, state) {
                Ok(v) => Ok(v),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
        );
        if let Some(e) = error.into_inner() {
            return Err(e);
        }
        result.map_err(ProductionError::Context)
    }
    fn joined_consumption(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        return_snapshot: bool,
        yes: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                Arc<ListBackedHeap>,
                Option<Term>,
            ) -> Result<
                VerificationResult<VerificationError>,
                ConsumptionError<NativeError<S::Error>>,
            >,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<NativeError<S::Error>>,
        >,
        no: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                Arc<ListBackedHeap>,
                Option<Term>,
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
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ConsumptionError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ConsumptionError<NativeError<S::Error>>>
    {
        let error = std::cell::RefCell::new(None);
        let result = self.join_impure_branches(
            state,
            condition,
            original,
            rewritten,
            &mut |ctx, state, done| match yes(ctx, state, &mut |ctx, state, heap, snapshot| {
                done(ctx, state, (heap, snapshot)).map_err(ConsumptionError::Context)
            }) {
                Ok(v) => Ok(v),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
            &mut |ctx, state, done| match no(ctx, state, &mut |ctx, state, heap, snapshot| {
                done(ctx, state, (heap, snapshot)).map_err(ConsumptionError::Context)
            }) {
                Ok(v) => Ok(v),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
            &mut |ctx, entries| match entries {
                [entry] => Ok((entry.state.clone(), entry.data.clone())),
                [first, second] => {
                    let factory = ctx.factory.clone();
                    let c1 = factory.and(first.path_conditions.branch_conditions());
                    let c2 = factory.and(second.path_conditions.branch_conditions());
                    let heap = crate::state::state::merge_heap(
                        first.data.0.as_ref(),
                        &c1,
                        &None,
                        second.data.0.as_ref(),
                        &c2,
                        &None,
                        &factory,
                    )
                    .map_err(NativeError::State)?;
                    let snapshot = match (&first.data.1, &second.data.1, return_snapshot) {
                        (Some(a), Some(b), true) => Some(factory.ite(c1, a.clone(), b.clone())),
                        (None, None, false) => None,
                        _ => {
                            return Err(NativeError::Unsupported(
                                "inconsistent joined consumption snapshots",
                            ));
                        }
                    };
                    let state = first
                        .state
                        .merge_recorded(
                            &first.path_conditions,
                            &second.state,
                            &second.path_conditions,
                            &factory,
                            false,
                            &mut |w| ctx.warnings.push(w),
                        )
                        .map_err(NativeError::State)?;
                    Ok((state, (Arc::new(heap), snapshot)))
                }
                _ => Err(NativeError::Unsupported(
                    "unexpected joined consumption branches",
                )),
            },
            &mut |ctx, state, (heap, snapshot)| match continuation(ctx, state, heap, snapshot) {
                Ok(v) => Ok(v),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
        );
        if let Some(e) = error.into_inner() {
            return Err(e);
        }
        result.map_err(ConsumptionError::Context)
    }
}

#[allow(unused_variables)]
impl<S: Prover, PD, FD: Clone>
    crate::supporters::functions::function_verification_unit::FunctionPhaseServices<
        PD,
        FD,
        JoinMode,
        VerificationError,
    > for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn function_debugging(&self) -> bool {
        false
    }
    fn empty_function_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        Ok(Arc::new(ListBackedHeap::new()))
    }
    fn function_debug_begin(
        &mut self,
        state: State<PD, FD, JoinMode>,
        body: Option<&Exp>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Err(NativeError::Unsupported("function debugging"))
    }
    fn function_debug_finish(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        Err(NativeError::Unsupported("function debugging"))
    }
    fn function_local(
        &mut self,
        state: State<PD, FD, JoinMode>,
        action: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::supporters::functions::function_verification_unit::FunctionPhaseError<
                Self::Error,
            >,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::supporters::functions::function_verification_unit::FunctionPhaseError<Self::Error>,
    > {
        use crate::supporters::functions::function_verification_unit::FunctionPhaseError as FE;
        self.base
            .decider
            .push_scope()
            .map_err(|e| FE::Service(NativeError::Decider(e)))?;
        let result = action(self, state);
        let cleanup = self.base.decider.pop_scope();
        match (result, cleanup) {
            (Ok(v), Ok(())) => Ok(v),
            (Err(e), Ok(())) => Err(e),
            (Ok(_), Err(e)) => Err(FE::Service(NativeError::Decider(e))),
            (Err(e), Err(cleanup)) => Err(FE::Service(NativeError::Cleanup(format!(
                "{e:?}; cleanup: {cleanup:?}"
            )))),
        }
    }
    fn function_mark(&mut self) -> Result<crate::decider::path_conditions::Mark, Self::Error> {
        Ok(self.base.decider.mark())
    }
    fn function_paths_after(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<crate::decider::path_conditions::RecordedPathConditions, Self::Error> {
        self.base
            .decider
            .pcs
            .after(mark)
            .map_err(|e| NativeError::Decider(DeciderError::Path(e)))
    }
    fn produce_function_contract(
        &mut self,
        state: State<PD, FD, JoinMode>,
        snapshot: crate::supporters::functions::function_verification_unit::ContractSnapshot<'_>,
        assertions: &[Exp],
        function: &ferrum_silver::ast::program::Function,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::supporters::functions::function_verification_unit::FunctionPhaseError<
                Self::Error,
            >,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::supporters::functions::function_verification_unit::FunctionPhaseError<Self::Error>,
    > {
        use crate::supporters::functions::function_verification_unit::{
            ContractSnapshot, FunctionPhaseError as FE,
        };
        let snapshot = match snapshot {
            ContractSnapshot::Fixed(t) => NativeSnapshot::Projection(t.clone()),
            ContractSnapshot::Fresh => NativeSnapshot::Fresh,
        };
        let mut callback_error = None;
        let result = crate::rules::producer::produce_all(
            self,
            state,
            snapshot,
            assertions,
            &|exp| {
                PartialVerificationError::for_kind(VerificationErrorKind::ContractNotWellformed(
                    exp.clone(),
                ))
            },
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(v) => Ok(v),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ProductionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(e) = callback_error {
            return Err(e);
        }
        result.map_err(|e| FE::Service(NativeError::Production(format!("{e:?}"))))
    }
    fn restore_function_preconditions(
        &mut self,
        path: &crate::supporters::functions::function_verification_unit::FunctionPhasePath<
            PD,
            FD,
            JoinMode,
        >,
        function: &ferrum_silver::ast::program::Function,
    ) -> Result<(), Self::Error> {
        let condition = self.factory.and(path.branch_conditions.clone());
        let mut exps = path.branch_condition_exps.iter().map(|(e, _)| e.clone());
        let first = exps
            .next()
            .unwrap_or_else(|| Exp::new(ExpKind::TrueLit, Default::default()));
        let exp = exps.fold(first, |a, b| {
            Exp::new(ExpKind::And(a, b), Default::default())
        });
        self.base
            .decider
            .set_branch_condition(condition, (exp, None), None)
            .map_err(NativeError::Decider)?;
        self.base
            .decider
            .assume(
                path.assumptions.iter().cloned().map(|t| (t, None)),
                false,
                false,
            )
            .map_err(NativeError::Decider)
    }
    fn saturate_function_contract(&mut self) -> Result<(), Self::Error> {
        if let Some(ms) = self.options.after_contract_timeout {
            self.base
                .decider
                .prover
                .saturate(ms, "after contract")
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        Ok(())
    }
    fn evaluate_function_body(
        &mut self,
        state: State<PD, FD, JoinMode>,
        body: &Exp,
        function: &ferrum_silver::ast::program::Function,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Term,
            Option<Exp>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::supporters::functions::function_verification_unit::FunctionPhaseError<
                Self::Error,
            >,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::supporters::functions::function_verification_unit::FunctionPhaseError<Self::Error>,
    > {
        use crate::supporters::functions::function_verification_unit::FunctionPhaseError as FE;
        let error = PartialVerificationError::for_kind(
            VerificationErrorKind::FunctionNotWellformed(function.clone()),
        );
        let mut callback_error = None;
        let result = crate::rules::evaluator::evaluate(
            self,
            state,
            body,
            &error,
            &mut |ctx, state, term, debug| match continuation(ctx, state, term, debug) {
                Ok(v) => Ok(v),
                Err(e) => {
                    callback_error = Some(e);
                    Err(EvaluationError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(e) = callback_error {
            return Err(e);
        }
        result.map_err(|e| FE::Service(NativeError::Evaluation(format!("{e:?}"))))
    }
    fn assume_function_result(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
        body: &Exp,
        term: &Term,
        debug: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.assume_term(
            &self
                .factory
                .builtin_equals(data.formal_result.clone(), term.clone()),
        )
    }
    fn consume_function_posts(
        &mut self,
        state: State<PD, FD, JoinMode>,
        posts: &[Exp],
        function: &ferrum_silver::ast::program::Function,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::supporters::functions::function_verification_unit::FunctionPhaseError<
                Self::Error,
            >,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::supporters::functions::function_verification_unit::FunctionPhaseError<Self::Error>,
    > {
        use crate::supporters::functions::function_verification_unit::FunctionPhaseError as FE;
        let mut callback_error = None;
        let result = crate::rules::consumer::consume_all(
            self,
            state,
            posts,
            false,
            &|exp| {
                PartialVerificationError::for_kind(VerificationErrorKind::PostconditionViolated {
                    node: exp.clone(),
                    member: ferrum_silver::ast::program::Member::Function(function.clone()),
                })
            },
            &mut |ctx, state, _| match continuation(ctx, state) {
                Ok(v) => Ok(v),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ConsumptionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(e) = callback_error {
            return Err(e);
        }
        result.map_err(|e| FE::Service(NativeError::Consumption(format!("{e:?}"))))
    }
}

impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn translate_function_terms(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
        body: bool,
    ) -> Result<(Vec<Term>, Option<Term>), NativeError<S::Error>> {
        use crate::supporters::{
            expression_translator::ExpressionTranslator,
            functions::heap_access_replacing_expression_translator::HeapAccessReplacingTranslator,
        };
        let factory = self.factory.clone();
        let converter = self.base.symbol_converter.clone();
        let translator = ExpressionTranslator::new(&factory, &converter, |sort: &Sort| {
            Ok::<_, NativeError<S::Error>>(sort.to_string())
        });
        let prior = self.failed_functions.contains(&data.program_function.name);
        let mut replacing = HeapAccessReplacingTranslator {
            program: &data.program,
            data,
            services: self,
            failed: false,
            prior_verification_failures: prior,
            ignore_access_predicates: false,
            context: vec![],
            check_inner_contexts: false,
        };
        if body {
            let translated = replacing
                .translate_body(&translator)
                .map_err(|e| NativeError::Execution(format!("function body translation: {e:?}")))?;
            Ok((vec![], translated))
        } else {
            let posts = replacing
                .translate_postconditions(&translator, &data.program_function.posts)
                .map_err(|e| {
                    NativeError::Execution(format!("function postcondition translation: {e:?}"))
                })?;
            Ok((posts, None))
        }
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::supporters::functions::function_verification_unit::FunctionVerificationServices<
        PD,
        FD,
        JoinMode,
        VerificationError,
    > for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn begin_function(
        &mut self,
        function: &ferrum_silver::ast::program::Function,
        _: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<(), Self::Error> {
        let options = crate::supporters::annotation_supporter::prover_config_args(
            &function.name,
            &function.meta.info,
            |warning| {
                self.warnings.push(warning);
                Ok::<_, ()>(())
            },
        )
        .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        self.base
            .decider
            .set_options(options)
            .map_err(NativeError::Decider)
    }
    fn end_function(&mut self) -> Result<(), Self::Error> {
        self.base
            .decider
            .reset_options()
            .map_err(NativeError::Decider)
    }
    fn check_function_specifications(
        &mut self,
        state: State<PD, FD, JoinMode>,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<
        crate::supporters::functions::function_verification_unit::FunctionPhaseOne<
            PD,
            FD,
            JoinMode,
            VerificationError,
        >,
        Self::Error,
    > {
        let factory = self.factory.clone();
        crate::supporters::functions::function_verification_unit::check_specification_well_definedness(&factory, self, state, data)
            .map_err(|e| NativeError::Execution(format!("function specification phase: {e:?}")))
    }
    fn well_definedness_declarations(
        &mut self,
        _: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<Vec<crate::state::terms::Declaration>, Self::Error> {
        Ok(vec![])
    }
    fn build_phase_one_axioms(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<
        crate::supporters::functions::function_verification_unit::FunctionPhaseOneAxioms,
        Self::Error,
    > {
        let factory = self.factory.clone();
        let (posts, _) = self.translate_function_terms(data, false)?;
        let nested: Vec<_> = data
            .nested_definitional_axioms()
            .map_err(|e| NativeError::Execution(format!("function nested axioms: {e:?}")))?
            .into_iter()
            .collect();
        let post_axiom = data
            .post_axiom(&factory, &posts, &nested, |term| Ok::<_, Self::Error>(term))
            .map_err(|e| NativeError::Execution(format!("function post axiom: {e:?}")))?;
        let post_precondition_axioms = data
            .post_precondition_axioms(
                &factory,
                &posts,
                |term| {
                    crate::state::function_precondition_transformer::transform(
                        &factory,
                        term,
                        &mut |fun| {
                            Ok::<_, Self::Error>(
                                crate::rules::function_supporter::precondition_version(
                                    &factory, fun,
                                ),
                            )
                        },
                    )
                    .map_err(|e| {
                        NativeError::<S::Error>::Execution(format!(
                            "function post preconditions: {e:?}"
                        ))
                    })
                },
                |term| Ok(term),
            )
            .map_err(|e| NativeError::Execution(format!("function post propagation: {e:?}")))?;
        Ok(
            crate::supporters::functions::function_verification_unit::FunctionPhaseOneAxioms {
                auxiliary_declarations: vec![],
                auxiliary_axioms: vec![],
                post_axiom,
                post_precondition_axioms,
            },
        )
    }
    fn declare_function_axiom_symbol(
        &mut self,
        decl: &crate::state::terms::Declaration,
    ) -> Result<(), Self::Error> {
        self.base
            .decider
            .prover
            .declare(decl)
            .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))
    }
    fn assume_function_axioms(&mut self, axioms: &[Term]) -> Result<(), Self::Error> {
        self.base
            .decider
            .prover
            .assume_axioms(&axioms.iter().cloned().collect(), "Function axioms")
            .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))
    }
    fn check_function_body(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
        paths: Vec<
            crate::supporters::functions::function_verification_unit::FunctionPhasePath<
                PD,
                FD,
                JoinMode,
            >,
        >,
    ) -> Result<
        crate::supporters::functions::function_verification_unit::FunctionPhaseTwo<
            FD,
            VerificationError,
        >,
        Self::Error,
    > {
        crate::supporters::functions::function_verification_unit::check_function_body(
            self, data, paths,
        )
        .map_err(|e| NativeError::Execution(format!("function body phase: {e:?}")))
    }
    fn build_phase_two_axioms(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<(Option<Term>, Vec<Term>), Self::Error> {
        let calls =
            ferrum_silver::ast::utility::functions::recursive_calls_and_surrounding_unfoldings(
                &data.program_function,
            )
            .map_err(|e| NativeError::Execution(format!("recursive function analysis: {e:?}")))?;
        let factory = self.factory.clone();
        let (_, body) = self.translate_function_terms(data, true)?;
        let mut predicate_triggers = crate::state::package::OrderedMap::<String, Term>::default();
        if body.is_some() {
            use crate::supporters::{
                expression_translator::ExpressionTranslator,
                functions::heap_access_replacing_expression_translator::HeapAccessReplacingTranslator,
            };
            let converter = self.base.symbol_converter.clone();
            let translator = ExpressionTranslator::new(&factory, &converter, |sort: &Sort| {
                Ok::<_, Self::Error>(sort.to_string())
            });
            let ignored: Vec<_> = data
                .formal_args
                .iter()
                .map(|(local, _)| local.expression().clone())
                .collect();
            let prior = self.failed_functions.contains(&data.program_function.name);
            let mut replacing = HeapAccessReplacingTranslator {
                program: &data.program,
                data,
                services: self,
                failed: false,
                prior_verification_failures: prior,
                ignore_access_predicates: false,
                context: vec![],
                check_inner_contexts: false,
            };
            for (_, unfoldings) in calls {
                let Some(unfolding) = unfoldings.first() else {
                    continue;
                };
                let ExpKind::Unfolding(access, _) = unfolding.kind() else {
                    return Err(NativeError::Unsupported("recursive unfolding shape"));
                };
                let ExpKind::PredicateAccessPredicate(access) = access.kind() else {
                    return Err(NativeError::Unsupported("recursive predicate access"));
                };
                let location = &access.location;
                let mut allowed = true;
                for arg in &location.args {
                    if !ferrum_silver::ast::utility::expressions::free_variables(arg, &ignored)
                        .map_err(|e| {
                            NativeError::Diagnostic(format!(
                                "recursive trigger free variables: {e:?}"
                            ))
                        })?
                        .is_empty()
                    {
                        allowed = false;
                        break;
                    }
                }
                if !allowed {
                    continue;
                }
                let predicate = data
                    .program
                    .find_predicate(&location.predicate_name)
                    .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
                let predicate_data =
                    crate::supporters::predicate_verification_unit::PredicateData::new(
                        predicate.clone(),
                        &converter,
                        &factory,
                        Sort::Snap,
                    )
                    .map_err(NativeError::Sort)?;
                let location_exp = Exp::new(
                    ExpKind::PredicateAccess(location.clone()),
                    location.meta.clone(),
                );
                let snapshot = replacing
                    .resolve_location(&translator, &location_exp, Sort::Snap)
                    .map_err(|e| {
                        NativeError::Execution(format!("recursive predicate snapshot: {e:?}"))
                    })?;
                let args = replacing
                    .translate_preconditions(&translator, &location.args)
                    .map_err(|e| {
                        NativeError::Execution(format!("recursive predicate arguments: {e:?}"))
                    })?;
                let terms = std::iter::once(snapshot).chain(args).collect();
                predicate_triggers.insert(
                    predicate.name.clone(),
                    factory.app(predicate_data.trigger_function, terms),
                );
            }
        }
        let nested: Vec<_> = data
            .nested_definitional_axioms()
            .map_err(|e| NativeError::Execution(format!("function nested axioms: {e:?}")))?
            .into_iter()
            .collect();
        let definition = data
            .definitional_axiom(
                &factory,
                body.clone(),
                &nested,
                &predicate_triggers
                    .iter()
                    .map(|(_, value)| value.clone())
                    .collect::<Vec<_>>(),
                |term| Ok::<_, Self::Error>(term),
            )
            .map_err(|e| NativeError::Execution(format!("function definition: {e:?}")))?;
        let propagation = data
            .body_precondition_axioms(
                &factory,
                body.as_ref(),
                |term| {
                    crate::state::function_precondition_transformer::transform(
                        &factory,
                        term,
                        &mut |fun| {
                            Ok::<_, Self::Error>(
                                crate::rules::function_supporter::precondition_version(
                                    &factory, fun,
                                ),
                            )
                        },
                    )
                    .map_err(|e| {
                        NativeError::<S::Error>::Execution(format!(
                            "function body preconditions: {e:?}"
                        ))
                    })
                },
                |term| Ok(term),
            )
            .map_err(|e| NativeError::Execution(format!("function body propagation: {e:?}")))?;
        Ok((definition, propagation))
    }
    fn record_function_failure(
        &mut self,
        function: &ferrum_silver::ast::program::Function,
        _: &VerificationResult<VerificationError>,
    ) {
        self.failed_functions.insert(function.name.clone());
    }
    fn actual_function_recorder(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<FunctionRecorder<FD>, Self::Error> {
        let handle = self
            .function_handles
            .get(&data.program_function.name)
            .cloned()
            .ok_or(NativeError::Unsupported("function recorder owner"))?;
        let arguments = std::iter::once((self.factory.predef_snapshot_var(), None))
            .chain(
                data.formal_args
                    .iter()
                    .map(|(local, term)| (term.clone(), Some(local.clone()))),
            )
            .collect();
        Ok(FunctionRecorder::actual(
            crate::supporters::functions::function_recorder::RecorderOwner::Function {
                data: handle,
                arguments,
            },
        ))
    }
    fn respect_function_pre_permissions(&self) -> bool {
        self.options.respect_function_pre_permission_amounts
    }
}

impl<S: Prover, PD, FD> crate::rules::quantified_chunk_support::QuantifiedChunkSolver
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn check_quantified_alias(
        &mut self,
        assertion: &Term,
        timeout_ms: i32,
    ) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check(assertion, Some(timeout_ms))
            .map_err(NativeError::Decider)
    }
    fn quantified_check_timeout(&self) -> i32 {
        self.base.decider.check_timeout.unwrap_or(0)
    }
}
impl<S: Prover, PD, FD> crate::rules::quantified_chunk_support::CompleteQuantifiedChunkSolver
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn assume_quantified_alias(&mut self, assertion: &Term) -> Result<(), Self::Error> {
        self.assume_term(assertion)
    }
}

impl<S: Prover, PD, FD: Clone> crate::rules::quantified_chunk_support::SnapshotCombinationFreshener
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn fresh_combined_snapshot_map(
        &mut self,
        sort: &Sort,
        additional_variables: &[Term],
    ) -> Result<(Term, ApplicationTarget), Self::Error> {
        crate::rules::state_consolidator::ConsolidationServices::fresh_merged_snapshot(
            self,
            sort,
            additional_variables,
        )
    }
}

impl<S: Prover, PD, FD>
    crate::rules::quantified_chunk_support::SnapshotMapFreshener<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn fresh_snapshot_map(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        additional_arguments: &[Term],
    ) -> Result<Term, Self::Error> {
        let sort = match resource {
            ResourceKey::Field(field) => Sort::FieldValueFunction {
                codomain: Box::new(
                    self.base
                        .symbol_converter
                        .to_sort(&field.typ)
                        .map_err(NativeError::Sort)?,
                ),
                field_name: field.name.clone(),
            },
            ResourceKey::Predicate(predicate) => Sort::PredicateSnapFunction {
                codomain: Box::new(
                    state
                        .predicate_snap_map
                        .get(&predicate.name)
                        .cloned()
                        .ok_or(NativeError::Unsupported("predicate snapshot sort"))?,
                ),
                predicate_name: predicate.name.clone(),
            },
            ResourceKey::Wand(wand) => Sort::PredicateSnapFunction {
                codomain: Box::new(Sort::MagicWandSnapFunction),
                predicate_name: wand.to_string(),
            },
        };
        let sorts = additional_arguments
            .iter()
            .map(|term| term.sort().clone())
            .collect::<Vec<_>>();
        let (target, _) = self
            .base
            .decider
            .fresh(&self.factory, "sm", &sorts, &sort)
            .map_err(NativeError::Decider)?;
        match target {
            ApplicationTarget::Function(fun) => {
                Ok(self.factory.app(fun, additional_arguments.to_vec()))
            }
            ApplicationTarget::Variable(var) if additional_arguments.is_empty() => Ok(var),
            _ => Err(NativeError::Unsupported("snapshot map target")),
        }
    }
}

impl<S: Prover, PD, FD>
    crate::rules::quantified_chunk_support::SnapshotSummaryFreshener<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn fresh_summary_binder(&mut self) -> Result<Term, Self::Error> {
        self.base
            .decider
            .fresh_variable(&self.factory, "s", &Sort::Snap, false, None)
            .map_err(NativeError::Decider)
    }
    fn next_snapshot_summary_id(&mut self) -> u64 {
        let id = self.quantified_counter;
        self.quantified_counter = self.quantified_counter.wrapping_add(1);
        id
    }
}
impl<S: Prover, PD, FD> crate::rules::quantified_chunk_support::PermissionMapFreshener
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn fresh_permission_map(&mut self, resource: &ResourceKey) -> Result<Term, Self::Error> {
        let sort = match resource {
            ResourceKey::Field(_) => Sort::FieldPermFunction,
            ResourceKey::Predicate(_) | ResourceKey::Wand(_) => Sort::PredicatePermFunction,
        };
        let (target, _) = self
            .base
            .decider
            .fresh(&self.factory, "pm", &[], &sort)
            .map_err(NativeError::Decider)?;
        match target {
            ApplicationTarget::Function(fun) => Ok(self.factory.app(fun, vec![])),
            ApplicationTarget::Variable(var) => Ok(var),
        }
    }
    fn next_summary_id(&mut self) -> u64 {
        let id = self.quantified_counter;
        self.quantified_counter = self.quantified_counter.wrapping_add(1);
        id
    }
}
impl<S: Prover, PD, FD> crate::rules::quantified_chunk_support::SummaryEmission
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn assume_summary_definitions(
        &mut self,
        definitions: &[Term],
        _: bool,
        _: bool,
    ) -> Result<(), Self::Error> {
        for definition in definitions {
            self.assume_term(definition)?;
        }
        Ok(())
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::rules::state_consolidator::QuantifiedMergeServices<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn complete_quantified_exhale(&self) -> bool {
        self.options.exhale_mode_qp == crate::config::ExhaleMode::MoreComplete
    }
    fn replace_quantified_debug(
        &mut self,
        _: &Exp,
        _: &[ferrum_silver::ast::program::LocalVarDecl],
        _: &[ferrum_silver::ast::program::LocalVarDecl],
    ) -> Result<Exp, NativeError<S::Error>> {
        Err(NativeError::Unsupported("quantified chunk merge debugging"))
    }
    fn summarise_quantified_pair(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        first: &Chunk,
        second: &Chunk,
    ) -> Result<
        (
            crate::rules::quantified_chunk_support::SnapshotMapDefinition,
            Vec<Term>,
        ),
        NativeError<S::Error>,
    > {
        use crate::rules::quantified_chunk_support::{SnapshotMapDefinition, SnapshotResource};
        let resource = match first {
            Chunk::QuantifiedField(field) => SnapshotResource::Field(Arc::new(
                state
                    .program
                    .find_field_optionally(&field.id_ref().0)
                    .ok_or(NativeError::Unsupported("quantified field resource"))?
                    .clone(),
            )),
            Chunk::QuantifiedPredicate(predicate) => SnapshotResource::Predicate(Arc::new(
                state
                    .program
                    .find_predicate_optionally(&predicate.id_ref().0)
                    .ok_or(NativeError::Unsupported("quantified predicate resource"))?
                    .clone(),
            )),
            Chunk::QuantifiedMagicWand(wand) => {
                let structures = state
                    .program
                    .magic_wand_structures()
                    .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
                let index = usize::try_from(wand.id_ref().structure_index)
                    .map_err(|_| NativeError::Unsupported("wand structure index"))?;
                SnapshotResource::Wand(
                    structures
                        .get(index)
                        .cloned()
                        .ok_or(NativeError::Unsupported("wand structure index"))?,
                )
            }
            _ => return Err(NativeError::Unsupported("quantified merge resource")),
        };
        let key = match &resource {
            SnapshotResource::Field(field) => ResourceKey::Field(field.clone()),
            SnapshotResource::Predicate(predicate) => ResourceKey::Predicate(predicate.clone()),
            SnapshotResource::Wand(wand) => ResourceKey::Wand(
                crate::state::chunks::MagicWandIdentifier::new(wand.clone(), &state.program)
                    .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?,
            ),
        };
        let variables = state
            .formal_arg_vars(&resource, &self.base.symbol_converter, &self.factory)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        let trigger = state
            .is_used_as_trigger(&resource)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        let factory = self.factory.clone();
        let (snapshot_map, value_definitions, domain_definitions) =
            crate::rules::quantified_chunk_support::summarise_snapshot_map(
                &factory,
                self,
                state,
                &key,
                &variables,
                &[first.clone(), second.clone()],
                None,
                trigger,
                false,
            )
            .map_err(|e| NativeError::Chunk(format!("quantified snapshot summary: {e:?}")))?;
        let equations = value_definitions.clone();
        Ok((
            SnapshotMapDefinition {
                resource,
                snapshot_map,
                value_definitions,
                domain_definitions,
            },
            equations,
        ))
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::rules::quantified_chunk_support::SingleLocationProduction<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn assume_singleton_value(&mut self, definition: &Term) -> Result<(), Self::Error> {
        self.base
            .decider
            .assume([(definition.clone(), None)], false, true)
            .map_err(NativeError::Decider)
    }
    fn next_quantified_tag(&mut self) -> i32 {
        let id = self.quantified_counter as i32;
        self.quantified_counter = self.quantified_counter.wrapping_add(1);
        id
    }
    fn merge_quantified_chunk(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        chunk: &Chunk,
    ) -> Result<(FunctionRecorder<FD>, ListBackedHeap), Self::Error> {
        let factory = self.factory.clone();
        let choice = self.consolidation_choice(state)?;
        crate::rules::state_consolidator::merge_heaps(
            &factory,
            self,
            state,
            state.function_recorder.clone(),
            &state.h,
            &ListBackedHeap::from_chunks([chunk.clone()]),
            choice,
        )
        .map_err(|e| NativeError::Chunk(format!("quantified heap merge: {e:?}")))
    }
    fn assume_quantified_chunk_properties(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        chunk: &Chunk,
    ) -> Result<(), Self::Error> {
        crate::rules::chunk_supporter::ChunkSolver::assume_properties(self, state, heap, chunk)
    }
    fn trigger_single_location(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        resource: &ResourceKey,
        formals: &[Term],
        args: &[Term],
    ) -> Result<crate::state::snapshot_map_cache::SnapshotMapCache, Self::Error> {
        use crate::interfaces::state::chunks::GeneralChunk;
        use crate::rules::quantified_chunk_support::{SnapshotMapDefinition, SnapshotResource};
        use crate::state::{
            heap::Heap,
            snapshot_map_cache::{CacheKey, QuantifiedBasicChunk},
        };
        let source = match resource {
            ResourceKey::Field(f) => SnapshotResource::Field(f.clone()),
            ResourceKey::Predicate(p) => SnapshotResource::Predicate(p.clone()),
            ResourceKey::Wand(w) => SnapshotResource::Wand(w.ghost_free_wand.clone()),
        };
        let mut chunks = Vec::new();
        let mut cached_chunks = Vec::new();
        for chunk in heap.values() {
            match (resource, chunk) {
                (ResourceKey::Field(f), Chunk::QuantifiedField(c)) if c.id_ref().0 == f.name => {
                    chunks.push(chunk.clone());
                    cached_chunks.push(QuantifiedBasicChunk::Field(c.clone()));
                }
                (ResourceKey::Predicate(p), Chunk::QuantifiedPredicate(c))
                    if c.id_ref().0 == p.name =>
                {
                    chunks.push(chunk.clone());
                    cached_chunks.push(QuantifiedBasicChunk::Predicate(c.clone()));
                }
                (ResourceKey::Wand(w), Chunk::QuantifiedMagicWand(c)) if c.id_ref() == w => {
                    chunks.push(chunk.clone());
                    cached_chunks.push(QuantifiedBasicChunk::Wand(c.clone()));
                }
                _ => {}
            }
        }
        let key = CacheKey {
            resource: source.clone(),
            relevant_chunks: cached_chunks,
        };
        let cached = (!state.exhale_ext)
            .then(|| state.sm_cache.get(&key, None))
            .flatten()
            .map(|(definition, _)| definition.clone());
        let factory = self.factory.clone();
        let mut cache = state.sm_cache.clone();
        let definition = if let Some(cached) = cached {
            cached
        } else {
            let (snapshot_map, value_definitions, domain_definitions) =
                crate::rules::quantified_chunk_support::summarise_snapshot_map(
                    &factory, self, state, resource, formals, &chunks, None, true, false,
                )
                .map_err(|e| NativeError::Chunk(format!("singleton trigger summary: {e:?}")))?;
            let definition = SnapshotMapDefinition {
                resource: source,
                snapshot_map,
                value_definitions,
                domain_definitions,
            };
            let mut total = factory.no_perm();
            for chunk in &chunks {
                let permission = match chunk {
                    Chunk::QuantifiedField(c) => c.permission(&factory),
                    Chunk::QuantifiedPredicate(c) => c.permission(&factory),
                    Chunk::QuantifiedMagicWand(c) => c.permission(&factory),
                    _ => unreachable!(),
                };
                total = factory.perm_plus(total, permission);
            }
            cache = cache.with_entry(key, definition.clone(), total, None);
            definition
        };
        if state.sm_domain_needed {
            for term in &definition.domain_definitions {
                self.assume_term(term)?;
            }
        }
        for term in &definition.value_definitions {
            self.assume_term(term)?;
        }
        self.assume_term(&factory.resource_trigger(
            resource,
            definition.snapshot_map,
            args.to_vec(),
        ))?;
        Ok(cache)
    }
    fn is_resource_trigger(&self, state: &State<PD, FD, JoinMode>, resource: &ResourceKey) -> bool {
        state.heap_dependent_triggers.contains(resource)
    }
}

impl<S: Prover, PD, FD> crate::rules::quantified_chunk_support::QuantifiedReadPermissionSolver
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn check_read_permission(&mut self, goal: &Term, timeout_ms: i32) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check(goal, Some(timeout_ms))
            .map_err(NativeError::Decider)
    }
    fn quantified_assert_timeout(&self) -> i32 {
        self.base.decider.assert_timeout.unwrap_or(0)
    }
}
impl<S: Prover, PD, FD> crate::rules::quantified_chunk_support::QuantifiedRemovalServices
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn check_removal_goal(&mut self, goal: &Term, timeout_ms: i32) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check(goal, Some(timeout_ms))
            .map_err(NativeError::Decider)
    }
    fn removal_check_timeout(&self) -> i32 {
        self.base.decider.check_timeout.unwrap_or(0)
    }
    fn removal_split_timeout(&self) -> i32 {
        self.options.qp_split_timeout
    }
    fn saturate_before_removal(&mut self) -> Result<(), Self::Error> {
        if let Some(timeout) = self.options.before_repetition_timeout {
            self.base
                .decider
                .prover
                .saturate(timeout, "before iteration")
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        Ok(())
    }
    fn removal_macros_enabled(&self) -> bool {
        true
    }
    fn fresh_permission_macro(
        &mut self,
        arguments: &[Term],
        body: &Term,
    ) -> Result<(Term, crate::state::terms::Declaration), Self::Error> {
        use crate::state::terms::{ApplicableData, ApplicableKind};
        let declaration = self
            .base
            .decider
            .fresh_macro(
                &self.factory,
                &mut self.base.identifiers,
                "pTaken",
                arguments.to_vec(),
                body.clone(),
            )
            .map_err(NativeError::Decider)?;
        let applicable = self.factory.applicable(ApplicableData {
            kind: ApplicableKind::Macro,
            id: declaration.id(),
            arg_sorts: arguments.iter().map(|a| a.sort().clone()).collect(),
            result_sort: body.sort().clone(),
        });
        Ok((
            self.factory.app(applicable, arguments.to_vec()),
            declaration,
        ))
    }
    fn auto_trigger_permission_constraint(
        &mut self,
        quantifier: Term,
    ) -> Result<Term, Self::Error> {
        let crate::state::terms::TermKind::Quantification {
            quantifier: kind,
            vars,
            body,
            triggers,
            name,
            is_global: _,
            weight: _,
        } = quantifier.kind()
        else {
            return Err(NativeError::Unsupported(
                "permission trigger quantifier shape",
            ));
        };
        if !triggers.is_empty() {
            return Ok(quantifier);
        }
        let (generated, extra) = self
            .base
            .trigger_generator
            .generate_group(&self.factory, vars, std::slice::from_ref(body), false)
            .map_err(|e| NativeError::Chunk(format!("permission trigger generation: {e:?}")))?;
        if generated.is_empty() {
            return Ok(quantifier);
        }
        let mut variables = vars.clone();
        variables.extend(extra);
        self.factory
            .quantification(
                *kind,
                variables,
                body.clone(),
                generated,
                name.clone(),
                false,
                None,
            )
            .map_err(|e| NativeError::Chunk(format!("permission trigger quantifier: {e:?}")))
    }
    fn assume_permission_constraint(
        &mut self,
        term: &Term,
        _: Option<&Exp>,
    ) -> Result<(), Self::Error> {
        self.assume_term(term)
    }
    fn next_permission_constraint_id(&mut self) -> i32 {
        let id = self.quantified_counter as i32;
        self.quantified_counter = self.quantified_counter.wrapping_add(1);
        id
    }
    fn removal_constraint_debug(
        &mut self,
        _: Option<&[ferrum_silver::ast::program::LocalVarDecl]>,
        _: Option<&Exp>,
        _: Option<&Exp>,
        _: Option<&Exp>,
    ) -> Result<Option<Exp>, Self::Error> {
        Err(NativeError::Unsupported("quantified removal debugging"))
    }
}

type NativeSingleResult<E> = Result<
    VerificationResult<VerificationError>,
    crate::rules::quantified_chunk_support::SingleConsumptionError<NativeError<E>>,
>;
impl<S: Prover, PD, FD: Clone>
    crate::rules::quantified_chunk_support::SingleLocationConsumption<
        PD,
        FD,
        JoinMode,
        VerificationError,
    > for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type VerificationError = Option<VerificationError>;
    fn retry_single_quantified(
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
            ) -> NativeSingleResult<S::Error>,
        ) -> NativeSingleResult<S::Error>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> NativeSingleResult<S::Error>,
    ) -> NativeSingleResult<S::Error> {
        use crate::rules::quantified_chunk_support::SingleConsumptionError as SE;
        crate::rules::chunk_supporter::ChunkExecutionContext::retry_chunk(
            self,
            state,
            &mut |ctx, state, done| {
                action(ctx, state, &mut |ctx, state, heap, snapshot| {
                    done(ctx, state, heap, snapshot)
                        .map_err(|e| SE::Service(NativeError::Chunk(format!("{e:?}"))))
                })
                .map_err(|e| ChunkExecutionError::Context(NativeError::Chunk(format!("{e:?}"))))
            },
            &mut |ctx, state, heap, snapshot| {
                continuation(ctx, state, heap, snapshot)
                    .map_err(|e| ChunkExecutionError::Context(NativeError::Chunk(format!("{e:?}"))))
            },
        )
        .map_err(|e| SE::Service(NativeError::Chunk(format!("{e:?}"))))
    }
    fn single_consumption_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        error: &Self::VerificationError,
        _: bool,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        let error = error.clone().ok_or(NativeError::Unsupported(
            "failure from null partial verification error",
        ))?;
        self.failure_full(error, state.retry_level)
    }
    fn consume_single_in_package(
        &mut self,
        state: State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        identifier: &ChunkIdentifier,
        codomain_vars: &[Term],
        codomain_var_exps: Option<&[ferrum_silver::ast::program::LocalVarDecl]>,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
        permission: &Term,
        permission_exp: Option<&Exp>,
        return_snapshot: bool,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> NativeSingleResult<S::Error>,
    ) -> NativeSingleResult<S::Error> {
        use crate::interfaces::state::chunks::QuantifiedChunk;
        use crate::rules::consumption_result::ConsumptionResult;
        use crate::rules::magic_wand_supporter::WandTransferError as WE;
        use crate::rules::quantified_chunk_support::{self as qp, SingleConsumptionError as SE};
        let failure = self
            .single_consumption_failure(&state, error, matches!(resource, ResourceKey::Wand(_)))
            .map_err(SE::Service)?;
        let factory = self.factory.clone();
        let mut callback_error = None;
        let result = crate::rules::magic_wand_supporter::transfer(
            &factory,
            self,
            state,
            permission.clone(),
            permission_exp.cloned(),
            failure,
            &[],
            &mut |ctx, state, heap, needed, needed_exp| {
                let (relevant, others) = qp::split_quantified_heap(&heap, identifier)
                    .map_err(|e| NativeError::Chunk(format!("wand quantified split: {e:?}")))?;
                let candidates = if ctx.disable_quantified_chunk_ordering() {
                    relevant.clone()
                } else {
                    let hints = qp::extract_hints(&factory, None, args)
                        .map_err(|e| NativeError::Chunk(format!("wand quantified hints: {e:?}")))?;
                    qp::single_receiver_chunk_order(&factory, ctx, &relevant, args, &hints)
                        .map_err(|e| NativeError::Chunk(format!("wand quantified order: {e:?}")))?
                };
                let condition = factory.and(
                    codomain_vars
                        .iter()
                        .zip(args)
                        .map(|(v, a)| factory.equals(v.clone(), a.clone())),
                );
                if codomain_var_exps.is_some() || arg_exps.is_some() || needed_exp.is_some() {
                    return Err(NativeError::Unsupported(
                        "quantified wand transfer debugging",
                    ));
                }
                let disable_triggers = ctx.disable_quantified_triggers();
                let (removal, mut state, mut remaining, untouched) =
                    qp::remove_quantified_permissions(
                        &factory,
                        ctx,
                        state,
                        &candidates,
                        &relevant,
                        identifier,
                        codomain_vars,
                        None,
                        condition,
                        None,
                        Some(args),
                        needed.clone(),
                        None,
                        disable_triggers,
                        false,
                    )
                    .map_err(|e| NativeError::Chunk(format!("wand quantified removal: {e:?}")))?;
                remaining.extend(untouched.clone());
                remaining.extend(others);
                let mut consumed = relevant;
                for chunk in untouched {
                    if let Some(i) = consumed.iter().position(|c| c == &chunk) {
                        consumed.remove(i);
                    }
                }
                let (definition, cache) = ctx.summarise_consumed_snapshot(
                    &state,
                    resource,
                    codomain_vars,
                    &consumed,
                    args,
                )?;
                let taken = match &removal {
                    ConsumptionResult::Complete => needed,
                    ConsumptionResult::Incomplete { perms_needed, .. } => {
                        factory.perm_minus(needed, perms_needed.clone())
                    }
                };
                let chunk = qp::singleton_quantified_chunk(
                    &factory,
                    resource,
                    codomain_vars.to_vec(),
                    None,
                    args.to_vec(),
                    None,
                    taken,
                    None,
                    definition.snapshot_map.clone(),
                    None,
                    false,
                )
                .map_err(|e| NativeError::Chunk(format!("wand quantified singleton: {e:?}")))?;
                state.function_recorder = state.function_recorder.record_fvf_and_domain(definition);
                state.sm_cache = cache;
                Ok((
                    removal,
                    state,
                    Arc::new(ListBackedHeap::from_chunks(remaining)),
                    Some(chunk),
                ))
            },
            &mut |ctx, state, chunks| {
                let snapshot = if return_snapshot {
                    if let Some(chunk) = chunks.last() {
                        let map = match chunk {
                            Chunk::QuantifiedField(c) => c.snapshot_map(),
                            Chunk::QuantifiedPredicate(c) => c.snapshot_map(),
                            Chunk::QuantifiedMagicWand(c) => c.snapshot_map(),
                            _ => {
                                return Err(WE::Service(NativeError::Unsupported(
                                    "wand transferred non-quantified chunk",
                                )));
                            }
                        };
                        let lookup = factory.resource_lookup(resource, map.clone(), args.to_vec());
                        Some(if matches!(resource, ResourceKey::Wand(_)) {
                            lookup
                        } else {
                            factory.sort_wrapper(lookup, Sort::Snap)
                        })
                    } else {
                        let (target, _) = ctx
                            .base
                            .decider
                            .fresh(&factory, "snap", &[], &Sort::Snap)
                            .map_err(|e| WE::Service(NativeError::Decider(e)))?;
                        Some(match target {
                            ApplicationTarget::Function(f) => factory.app(f, vec![]),
                            ApplicationTarget::Variable(v) => v,
                        })
                    }
                } else {
                    None
                };
                let heap = state.h.clone();
                match continuation(ctx, state, heap, snapshot) {
                    Ok(result) => Ok(result),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(WE::Service(NativeError::ContinuationAbort))
                    }
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| {
            SE::Service(NativeError::Chunk(format!(
                "wand quantified transfer: {e:?}"
            )))
        })
    }
    fn summarise_consumed_snapshot(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        formals: &[Term],
        consumed: &[Chunk],
        args: &[Term],
    ) -> Result<
        (
            crate::rules::quantified_chunk_support::SnapshotMapDefinition,
            crate::state::snapshot_map_cache::SnapshotMapCache,
        ),
        NativeError<S::Error>,
    > {
        use crate::interfaces::state::chunks::GeneralChunk;
        use crate::rules::quantified_chunk_support::{SnapshotMapDefinition, SnapshotResource};
        use crate::state::snapshot_map_cache::{CacheKey, QuantifiedBasicChunk};
        let source = match resource {
            ResourceKey::Field(f) => SnapshotResource::Field(f.clone()),
            ResourceKey::Predicate(p) => SnapshotResource::Predicate(p.clone()),
            ResourceKey::Wand(w) => SnapshotResource::Wand(w.ghost_free_wand.clone()),
        };
        let chunks = consumed
            .iter()
            .map(|chunk| match chunk {
                Chunk::QuantifiedField(c) => Ok(QuantifiedBasicChunk::Field(c.clone())),
                Chunk::QuantifiedPredicate(c) => Ok(QuantifiedBasicChunk::Predicate(c.clone())),
                Chunk::QuantifiedMagicWand(c) => Ok(QuantifiedBasicChunk::Wand(c.clone())),
                _ => Err(NativeError::Unsupported(
                    "non-quantified snapshot summary chunk",
                )),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let key = CacheKey {
            resource: source.clone(),
            relevant_chunks: chunks,
        };
        let cached = (!state.exhale_ext)
            .then(|| state.sm_cache.get(&key, None))
            .flatten()
            .map(|(definition, _)| definition.clone());
        let factory = self.factory.clone();
        let mut cache = state.sm_cache.clone();
        let definition = if let Some(definition) = cached {
            definition
        } else {
            let (snapshot_map, value_definitions, domain_definitions) =
                crate::rules::quantified_chunk_support::summarise_snapshot_map(
                    &factory,
                    self,
                    state,
                    resource,
                    formals,
                    consumed,
                    None,
                    state.heap_dependent_triggers.contains(resource),
                    false,
                )
                .map_err(|e| NativeError::Chunk(format!("consumed snapshot summary: {e:?}")))?;
            let definition = SnapshotMapDefinition {
                resource: source,
                snapshot_map,
                value_definitions,
                domain_definitions,
            };
            let mut total = factory.no_perm();
            for chunk in consumed {
                let permission = match chunk {
                    Chunk::QuantifiedField(c) => c.permission(&factory),
                    Chunk::QuantifiedPredicate(c) => c.permission(&factory),
                    Chunk::QuantifiedMagicWand(c) => c.permission(&factory),
                    _ => {
                        return Err(NativeError::Unsupported(
                            "non-quantified snapshot summary chunk",
                        ));
                    }
                };
                total = factory.perm_plus(total, permission);
            }
            cache = cache.with_entry(key, definition.clone(), total, None);
            definition
        };
        let instantiations = match resource {
            ResourceKey::Field(_) => args.to_vec(),
            _ => vec![factory.to_snap_tree(args.to_vec())],
        };
        for term in definition
            .value_definitions
            .iter()
            .chain(if state.sm_domain_needed {
                definition.domain_definitions.iter()
            } else {
                [].iter()
            })
        {
            let instantiated = factory.instantiate(term, &instantiations).map_err(|e| {
                NativeError::Chunk(format!("snapshot summary instantiation: {e:?}"))
            })?;
            self.assume_term(&instantiated)?;
        }
        Ok((definition, cache))
    }
    fn next_consumption_tag(&mut self) -> i32 {
        let id = self.quantified_counter as i32;
        self.quantified_counter = self.quantified_counter.wrapping_add(1);
        id
    }
    fn use_complete_quantified_exhale(&self) -> bool {
        self.options.exhale_mode_qp == crate::config::ExhaleMode::MoreComplete
    }
    fn disable_quantified_chunk_ordering(&self) -> bool {
        false
    }
    fn disable_quantified_triggers(&self) -> bool {
        false
    }
    fn debug_quantified_consumption(&self) -> bool {
        false
    }
}

impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn evaluate_native_quantified_permission(
        &mut self,
        state: State<PD, FD, JoinMode>,
        forall: &Exp,
        condition: &Exp,
        permission: &Exp,
        arguments: &[Exp],
        qid: &str,
        error: &PartialVerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Option<QuantifiedProductionData>,
        ) -> Result<
            VerificationResult<VerificationError>,
            EvaluationError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, EvaluationError<NativeError<S::Error>>> {
        let ExpKind::Forall(vars, triggers, _) = forall.kind() else {
            return Err(EvaluationError::Context(NativeError::Unsupported(
                "quantified permission shape",
            )));
        };
        let second: Vec<_> = std::iter::once(permission.clone())
            .chain(arguments.iter().cloned())
            .collect();
        crate::rules::evaluator::evaluate_quantified(
            self,
            state,
            crate::state::terms::Quantifier::Forall,
            vars,
            std::slice::from_ref(condition),
            &second,
            (!triggers.is_empty()).then_some(triggers.as_slice()),
            qid,
            error,
            &mut |ctx, state, data| {
                let Some(body) = data.second else {
                    return continuation(ctx, state, None);
                };
                if data.first_terms.len() != 1 || body.terms.len() != arguments.len() + 1 {
                    return Err(EvaluationError::InvalidJoinEntries);
                }
                let mut terms = body.terms.into_iter();
                let permission = terms.next().ok_or(EvaluationError::InvalidJoinEntries)?;
                let mut expressions = body.expressions;
                if expressions
                    .as_ref()
                    .is_some_and(|items| items.len() != arguments.len() + 1)
                {
                    return Err(EvaluationError::InvalidJoinEntries);
                }
                let permission_exp = expressions.as_mut().map(|items| items.remove(0));
                let condition_exp = data.first_expressions.and_then(|mut items| {
                    if items.len() == 1 {
                        Some(items.remove(0))
                    } else {
                        None
                    }
                });
                continuation(
                    ctx,
                    state,
                    Some(QuantifiedProductionData {
                        qvars: data.variables,
                        qvar_expressions: data.variable_expressions,
                        condition: data.first_terms[0].clone(),
                        condition_exp,
                        permission,
                        permission_exp,
                        arguments: terms.collect(),
                        argument_expressions: expressions,
                        triggers: body.triggers,
                        auxiliary_globals: body.auxiliary_globals,
                        auxiliary_non_globals: body.auxiliary_non_globals,
                        auxiliary_debug: body.auxiliary_debug,
                    }),
                )
            },
        )
    }
}

impl<S: Prover, PD, FD> crate::rules::quantified_chunk_support::InverseFunctionServices
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn fresh_inverse_function(
        &mut self,
        name: &str,
        arguments: &[Sort],
        result: &Sort,
    ) -> Result<ApplicationTarget, Self::Error> {
        self.base
            .decider
            .fresh(&self.factory, name, arguments, result)
            .map(|(target, _)| target)
            .map_err(NativeError::Decider)
    }
    fn assemble_inverse_quantifier(
        &mut self,
        variables: &[Term],
        body: Term,
        candidate_terms: &[Term],
        explicit_triggers: Option<&[crate::state::terms::Trigger]>,
        name: &str,
        global: bool,
    ) -> Result<Term, Self::Error> {
        let (triggers, extra) = if let Some(triggers) = explicit_triggers {
            (triggers.to_vec(), vec![])
        } else {
            self.base
                .trigger_generator
                .generate_group(&self.factory, variables, candidate_terms, true)
                .map_err(|e| NativeError::Chunk(format!("inverse trigger generation: {e:?}")))?
        };
        let mut vars = variables.to_vec();
        vars.extend(extra);
        let quantifier = self
            .factory
            .quantification(
                crate::state::terms::Quantifier::Forall,
                vars,
                body,
                triggers,
                name.to_string(),
                global,
                None,
            )
            .map_err(|e| NativeError::Chunk(format!("inverse quantifier: {e:?}")))?;
        self.base
            .trigger_generator
            .rewrite_axiom(&self.factory, &quantifier)
            .map_err(|e| NativeError::Chunk(format!("inverse trigger rewrite: {e:?}")))
    }
}

pub struct NativeQuantifiedProductionError {
    partial: PartialVerificationError,
    permission: Exp,
    access: Exp,
}
impl<S: Prover, PD, FD: Clone>
    crate::rules::quantified_chunk_support::GeneralQuantifiedProduction<
        PD,
        FD,
        JoinMode,
        VerificationError,
    > for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type VerificationError = NativeQuantifiedProductionError;
    fn transform_precondition(
        &mut self,
        _: &State<PD, FD, JoinMode>,
        term: &Term,
    ) -> Result<Term, Self::Error> {
        let factory = self.factory.clone();
        crate::state::function_precondition_transformer::transform(&factory, term, &mut |fun| {
            Ok::<_, Self::Error>(crate::rules::function_supporter::precondition_version(
                &factory, fun,
            ))
        })
        .map_err(|e| NativeError::Chunk(format!("quantified precondition: {e:?}")))
    }
    fn assume_quantified_terms(
        &mut self,
        terms: &[Term],
        definitions: bool,
    ) -> Result<(), Self::Error> {
        self.base
            .decider
            .assume(terms.iter().cloned().map(|t| (t, None)), false, definitions)
            .map_err(NativeError::Decider)
    }
    fn assert_quantified_goal(&mut self, goal: &Term) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check(goal, self.base.decider.assert_timeout)
            .map_err(NativeError::Decider)
    }
    fn quantified_production_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        error: &Self::VerificationError,
        reason: crate::rules::quantified_chunk_support::QuantifiedProductionFailure,
        _: &Term,
    ) -> Result<VerificationResult<VerificationError>, Self::Error> {
        let reason = match reason {
            crate::rules::quantified_chunk_support::QuantifiedProductionFailure::NegativePermission => ErrorReason::NegativePermission(error.permission.clone()),
            crate::rules::quantified_chunk_support::QuantifiedProductionFailure::NotInjective => {
                use ferrum_silver::ast::utility::nodes::Node;
                let node = match error.access.kind() {
                    ExpKind::FieldAccessPredicate(access, _) => Node::FieldAccess(access.clone()),
                    ExpKind::PredicateAccessPredicate(access) => Node::PredicateAccess(access.location.clone()),
                    ExpKind::MagicWand(..) => Node::Exp(error.access.clone()),
                    _ => return Err(NativeError::Unsupported("quantified injectivity error location")),
                };
                ErrorReason::QPAssertionNotInjective(node)
            }
        };
        self.failure(&error.partial, reason, state.retry_level)
    }
    fn warn_missing_quantified_triggers(&mut self) -> Result<(), Self::Error> {
        self.warnings
            .push("Quantified permission has no usable trigger".into());
        Ok(())
    }
    fn assume_quantified_properties(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        chunk: &Chunk,
        args: &[Term],
        permission: &Term,
        condition: &Term,
        qvars: &[Term],
        triggers: &[crate::state::terms::Trigger],
        qid: &str,
    ) -> Result<(), Self::Error> {
        use crate::interfaces::state::chunks::GeneralChunk;
        let factory = self.factory.clone();
        let properties = match chunk {
            Chunk::QuantifiedField(c) => c
                .resource_id()
                .description()
                .instance_properties(state.may_assume_upper_bounds()),
            Chunk::QuantifiedPredicate(c) => c
                .resource_id()
                .description()
                .instance_properties(state.may_assume_upper_bounds()),
            Chunk::QuantifiedMagicWand(c) => c
                .resource_id()
                .description()
                .instance_properties(state.may_assume_upper_bounds()),
            _ => return Err(NativeError::Unsupported("quantified property chunk")),
        };
        for property in properties {
            let term = match chunk {
                Chunk::QuantifiedField(c) => {
                    crate::resources::quantified_property_interpreter::build_for_chunk(
                        &factory,
                        c,
                        &property,
                        qvars.to_vec(),
                        args,
                        permission,
                        condition,
                        triggers.to_vec(),
                        qid,
                    )
                }
                Chunk::QuantifiedPredicate(c) => {
                    crate::resources::quantified_property_interpreter::build_for_chunk(
                        &factory,
                        c,
                        &property,
                        qvars.to_vec(),
                        args,
                        permission,
                        condition,
                        triggers.to_vec(),
                        qid,
                    )
                }
                Chunk::QuantifiedMagicWand(c) => {
                    crate::resources::quantified_property_interpreter::build_for_chunk(
                        &factory,
                        c,
                        &property,
                        qvars.to_vec(),
                        args,
                        permission,
                        condition,
                        triggers.to_vec(),
                        qid,
                    )
                }
                _ => unreachable!(),
            }
            .map_err(|e| NativeError::ResourceProperty(format!("{e:?}")))?;
            self.assume_term(&term)?;
        }
        Ok(())
    }
    fn merge_produced_quantified_chunk(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        chunk: &Chunk,
    ) -> Result<(FunctionRecorder<FD>, ListBackedHeap), Self::Error> {
        crate::rules::quantified_chunk_support::SingleLocationProduction::merge_quantified_chunk(
            self, state, chunk,
        )
    }
    fn production_resource_trigger(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        heap: &ListBackedHeap,
        inverse: &crate::rules::quantified_chunk_support::InverseFunctions,
        condition: &Term,
    ) -> Result<
        Option<(
            crate::rules::quantified_chunk_support::SnapshotMapDefinition,
            crate::state::snapshot_map_cache::SnapshotMapCache,
        )>,
        Self::Error,
    > {
        if !state.heap_dependent_triggers.contains(resource) {
            return Ok(None);
        }
        let source = native_quantified_source(resource);
        let formals = state
            .formal_arg_vars(&source, &self.base.symbol_converter, &self.factory)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        let chunks = native_quantified_chunks(heap, resource);
        let (definition, cache) = crate::rules::quantified_chunk_support::GeneralConsumptionExecution::summarise_general_consumed(self, state, resource, &formals, &chunks, None)?;
        self.assume_native_inverse_trigger(resource, &formals, condition, inverse, &definition)?;
        Ok(Some((definition, cache)))
    }
    fn next_production_tag(&mut self) -> i32 {
        let id = self.quantified_counter as i32;
        self.quantified_counter = self.quantified_counter.wrapping_add(1);
        id
    }
    fn assume_injectivity_on_inhale(&self) -> bool {
        self.options.assume_injectivity_on_inhale
    }
    fn unsafe_wildcard_optimization(&self) -> bool {
        self.options.unsafe_wildcard_optimization
    }
    fn disable_isc_triggers(&self) -> bool {
        false
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::rules::quantified_chunk_support::GeneralQuantifiedConsumptionPreparation<
        PD,
        FD,
        JoinMode,
        VerificationError,
    > for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type VerificationError = NativeQuantifiedProductionError;
    fn consume_transform_precondition(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        term: &Term,
    ) -> Result<Term, Self::Error> {
        crate::rules::quantified_chunk_support::GeneralQuantifiedProduction::transform_precondition(
            self, state, term,
        )
    }
    fn consume_assume_terms(&mut self, terms: &[Term]) -> Result<(), Self::Error> {
        crate::rules::quantified_chunk_support::GeneralQuantifiedProduction::assume_quantified_terms(
            self, terms, false,
        )
    }
    fn consume_assert_goal(&mut self, term: &Term) -> Result<bool, Self::Error> {
        crate::rules::quantified_chunk_support::GeneralQuantifiedProduction::assert_quantified_goal(
            self, term,
        )
    }
    fn general_consumption_failure(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        error: &Self::VerificationError,
        reason: crate::rules::quantified_chunk_support::QuantifiedProductionFailure,
        goal: &Term,
    ) -> Result<VerificationResult<VerificationError>, Self::Error> {
        crate::rules::quantified_chunk_support::GeneralQuantifiedProduction::quantified_production_failure(self, state, error, reason, goal)
    }
    fn consume_trigger_summary(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        resource: &ResourceKey,
        formals: &[Term],
        _: &ChunkIdentifier,
    ) -> Result<
        Option<(
            crate::rules::quantified_chunk_support::SnapshotMapDefinition,
            crate::state::snapshot_map_cache::SnapshotMapCache,
        )>,
        Self::Error,
    > {
        if !state.heap_dependent_triggers.contains(resource) {
            return Ok(None);
        }
        let chunks = native_quantified_chunks(heap, resource);
        let summary = crate::rules::quantified_chunk_support::GeneralConsumptionExecution::summarise_general_consumed(self, state, resource, formals, &chunks, None)?;
        Ok(Some(summary))
    }
    fn consume_assume_inverse_trigger(
        &mut self,
        _: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        formals: &[Term],
        condition: &Term,
        inverse: &crate::rules::quantified_chunk_support::InverseFunctions,
        definition: &crate::rules::quantified_chunk_support::SnapshotMapDefinition,
    ) -> Result<(), Self::Error> {
        self.assume_native_inverse_trigger(resource, formals, condition, inverse, definition)
    }
    fn consumption_unsafe_wildcard(&self) -> bool {
        self.options.unsafe_wildcard_optimization
    }
    fn consumption_disable_isc_triggers(&self) -> bool {
        false
    }
}

type NativeGeneralResult<E> = Result<
    VerificationResult<VerificationError>,
    crate::rules::quantified_chunk_support::GeneralConsumptionExecutionError<NativeError<E>>,
>;
impl<S: Prover, PD, FD: Clone>
    crate::rules::quantified_chunk_support::GeneralConsumptionExecution<
        PD,
        FD,
        JoinMode,
        VerificationError,
    > for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type VerificationError = NativeQuantifiedProductionError;
    fn retry_general_quantified(
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
            ) -> NativeGeneralResult<S::Error>,
        ) -> NativeGeneralResult<S::Error>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> NativeGeneralResult<S::Error>,
    ) -> NativeGeneralResult<S::Error> {
        use crate::rules::quantified_chunk_support::GeneralConsumptionExecutionError as GE;
        crate::rules::chunk_supporter::ChunkExecutionContext::retry_chunk(
            self,
            state,
            &mut |ctx, state, done| {
                action(ctx, state, &mut |ctx, state, heap, snapshot| {
                    done(ctx, state, heap, snapshot)
                        .map_err(|e| GE::Service(NativeError::Chunk(format!("{e:?}"))))
                })
                .map_err(|e| ChunkExecutionError::Context(NativeError::Chunk(format!("{e:?}"))))
            },
            &mut |ctx, state, heap, snapshot| {
                continuation(ctx, state, heap, snapshot)
                    .map_err(|e| ChunkExecutionError::Context(NativeError::Chunk(format!("{e:?}"))))
            },
        )
        .map_err(|e| GE::Service(NativeError::Chunk(format!("{e:?}"))))
    }
    fn general_insufficient_permission(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        error: &Self::VerificationError,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        use ferrum_silver::ast::utility::nodes::Node;
        let reason = match error.access.kind() {
            ExpKind::FieldAccessPredicate(access, _) => {
                ErrorReason::InsufficientPermission(Node::FieldAccess(access.clone()))
            }
            ExpKind::PredicateAccessPredicate(access) => {
                ErrorReason::InsufficientPermission(Node::PredicateAccess(access.location.clone()))
            }
            ExpKind::MagicWand(..) => ErrorReason::MagicWandChunkNotFound(error.access.clone()),
            _ => {
                return Err(NativeError::Unsupported(
                    "quantified permission failure reason",
                ));
            }
        };
        self.failure(&error.partial, reason, state.retry_level)
    }
    fn consume_general_in_package(
        &mut self,
        mut state: State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        identifier: &ChunkIdentifier,
        plan: &crate::rules::quantified_chunk_support::GeneralConsumptionTerms,
        error: &Self::VerificationError,
        return_snapshot: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> NativeGeneralResult<S::Error>,
    ) -> NativeGeneralResult<S::Error> {
        use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
        use crate::rules::consumption_result::ConsumptionResult;
        use crate::rules::magic_wand_supporter::WandTransferError as WE;
        use crate::rules::quantified_chunk_support::{
            self as qp, GeneralConsumptionExecutionError as GE,
            GeneralQuantifiedConsumptionPreparation,
        };
        if plan.formal_var_exps.is_some() || plan.condition_exp.is_some() || plan.loss_exp.is_some()
        {
            return Err(GE::Service(NativeError::Unsupported(
                "general quantified wand debugging",
            )));
        }
        let failure = self
            .general_insufficient_permission(&state, error)
            .map_err(GE::Service)?;
        let factory = self.factory.clone();
        let original_arps = state.constrainable_arps.clone();
        state.sm_cache = plan.trigger_cache.clone();
        let mut callback_error = None;
        let result = crate::rules::magic_wand_supporter::transfer(
            &factory,
            self,
            state,
            plan.loss.clone(),
            None,
            failure,
            &plan.formal_vars,
            &mut |ctx, state, heap, needed, needed_exp| {
                if needed_exp.is_some() {
                    return Err(NativeError::Unsupported(
                        "general quantified wand debugging",
                    ));
                }
                let (relevant, others) = qp::split_quantified_heap(&heap, identifier)
                    .map_err(|e| NativeError::Chunk(format!("wand general split: {e:?}")))?;
                let candidates = if ctx.disable_general_chunk_ordering() {
                    relevant.clone()
                } else {
                    qp::quantified_application_chunk_order(
                        &factory,
                        ctx,
                        &relevant,
                        &plan.inverse.invertibles,
                        &plan.qvars,
                        &plan.hints,
                    )
                    .map_err(|e| NativeError::Chunk(format!("wand general order: {e:?}")))?
                };
                let disabled = ctx.disable_general_isc_triggers();
                let (removal, mut state, mut remaining, untouched) =
                    qp::remove_quantified_permissions(
                        &factory,
                        ctx,
                        state,
                        &candidates,
                        &relevant,
                        identifier,
                        &plan.formal_vars,
                        None,
                        plan.condition.clone(),
                        None,
                        None,
                        needed.clone(),
                        None,
                        disabled,
                        false,
                    )
                    .map_err(|e| NativeError::Chunk(format!("wand general removal: {e:?}")))?;
                remaining.extend(untouched.clone());
                remaining.extend(others);
                let mut consumed = relevant;
                for chunk in untouched {
                    if let Some(i) = consumed.iter().position(|c| c == &chunk) {
                        consumed.remove(i);
                    }
                }
                let domain = state.sm_domain_needed.then_some(&plan.domain_condition);
                let (definition, cache) = ctx.summarise_general_consumed(
                    &state,
                    resource,
                    &plan.formal_vars,
                    &consumed,
                    domain,
                )?;
                let taken = match &removal {
                    ConsumptionResult::Complete => needed,
                    ConsumptionResult::Incomplete { perms_needed, .. } => {
                        factory.perm_minus(needed, perms_needed.clone())
                    }
                };
                let additional = state
                    .relevant_quantified_variables_in(&plan.original_args)
                    .map_err(|e| NativeError::Chunk(format!("wand general variables: {e:?}")))?
                    .into_iter()
                    .map(|(v, _)| v)
                    .collect();
                let mut state_vars = Vec::new();
                for (var, _) in &state.quantified_variables {
                    let mut occurs = plan.original_condition.contains(var).map_err(|e| {
                        NativeError::Chunk(format!("wand general condition: {e:?}"))
                    })?;
                    for arg in &plan.original_args {
                        occurs |= arg.contains(var).map_err(|e| {
                            NativeError::Chunk(format!("wand general arguments: {e:?}"))
                        })?;
                    }
                    if occurs {
                        state_vars.push(var.clone());
                    }
                }
                let inv_cond = factory.and([
                    plan.inverse_condition.clone(),
                    factory.is_positive_perm(taken.clone()),
                ]);
                let (inverse, images) = qp::fresh_inverse_functions(
                    &factory,
                    ctx,
                    &plan.qvars,
                    None,
                    inv_cond,
                    plan.original_args.clone(),
                    None,
                    &plan.formal_vars,
                    additional,
                    &state_vars,
                    plan.explicit_triggers.as_deref(),
                    &plan.qid,
                    disabled,
                )
                .map_err(|e| NativeError::Chunk(format!("wand general inverse: {e:?}")))?;
                let mut counts: Vec<(i32, usize)> = Vec::new();
                for chunk in &consumed {
                    let tag = match chunk {
                        Chunk::QuantifiedField(c) => c.tag(),
                        Chunk::QuantifiedPredicate(c) => c.tag(),
                        Chunk::QuantifiedMagicWand(c) => c.tag(),
                        _ => None,
                    };
                    if let Some(tag) = tag {
                        if let Some((_, n)) = counts.iter_mut().find(|(v, _)| *v == tag) {
                            *n += 1;
                        } else {
                            counts.push((tag, 1));
                        }
                    }
                }
                let tag = counts
                    .into_iter()
                    .max_by_key(|(_, n)| *n)
                    .map(|(tag, _)| tag)
                    .unwrap_or_else(|| {
                        let n = ctx.quantified_counter as i32;
                        ctx.quantified_counter = ctx.quantified_counter.wrapping_add(1);
                        n
                    });
                let chunk = qp::quantified_chunk_from_inverses(
                    &factory,
                    resource,
                    qp::QuantifiedChunkData {
                        codomain_vars: plan.formal_vars.clone(),
                        codomain_var_exps: None,
                        arguments: plan.original_args.clone(),
                        snapshot_map: definition.snapshot_map.clone(),
                        condition: plan.inverse_condition.clone(),
                        condition_exp: None,
                        permission: taken,
                        permission_exp: None,
                        inverses: vec![],
                        singleton_args: None,
                        singleton_arg_exps: None,
                        tag: Some(tag),
                        hints: vec![],
                        debugging: false,
                    },
                    inverse.clone(),
                    images,
                )
                .map_err(|e| NativeError::Chunk(format!("wand general chunk: {e:?}")))?;
                let axiom1 = inverse.axiom_invertibles_of_inverses.clone();
                let substitutions = plan
                    .formal_vars
                    .iter()
                    .cloned()
                    .zip(plan.original_args.iter().cloned())
                    .collect();
                let axiom2 = factory
                    .replace(&inverse.axiom_inverses_of_invertibles, &substitutions)
                    .map_err(|e| {
                        NativeError::Chunk(format!("wand general inverse substitution: {e:?}"))
                    })?;
                for axiom in [axiom1, axiom2] {
                    let precondition = ctx.consume_transform_precondition(&state, &axiom)?;
                    ctx.consume_assume_terms(&[precondition, axiom])?;
                }
                state.sm_cache = cache;
                state.constrainable_arps = original_arps.clone();
                Ok((
                    removal,
                    state,
                    Arc::new(ListBackedHeap::from_chunks(remaining)),
                    Some(chunk),
                ))
            },
            &mut |ctx, state, chunks| {
                let snapshot = if return_snapshot {
                    if let Some(chunk) = chunks.last() {
                        let map = match chunk {
                            Chunk::QuantifiedField(c) => c.snapshot_map(),
                            Chunk::QuantifiedPredicate(c) => c.snapshot_map(),
                            Chunk::QuantifiedMagicWand(c) => c.snapshot_map(),
                            _ => {
                                return Err(WE::Service(NativeError::Unsupported(
                                    "wand transferred non-quantified chunk",
                                )));
                            }
                        };
                        Some(factory.sort_wrapper(map.clone(), Sort::Snap))
                    } else {
                        let (target, _) = ctx
                            .base
                            .decider
                            .fresh(&factory, "snap", &[], &Sort::Snap)
                            .map_err(|e| WE::Service(NativeError::Decider(e)))?;
                        Some(match target {
                            ApplicationTarget::Function(f) => factory.app(f, vec![]),
                            ApplicationTarget::Variable(v) => v,
                        })
                    }
                } else {
                    None
                };
                let heap = state.h.clone();
                match continuation(ctx, state, heap, snapshot) {
                    Ok(result) => Ok(result),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(WE::Service(NativeError::ContinuationAbort))
                    }
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| GE::Service(NativeError::Chunk(format!("wand general transfer: {e:?}"))))
    }
    fn summarise_general_consumed(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        formals: &[Term],
        consumed: &[Chunk],
        domain_condition: Option<&Term>,
    ) -> Result<
        (
            crate::rules::quantified_chunk_support::SnapshotMapDefinition,
            crate::state::snapshot_map_cache::SnapshotMapCache,
        ),
        NativeError<S::Error>,
    > {
        use crate::interfaces::state::chunks::GeneralChunk;
        use crate::rules::quantified_chunk_support::{SnapshotMapDefinition, SnapshotResource};
        use crate::state::snapshot_map_cache::{CacheKey, QuantifiedBasicChunk};
        let source = match resource {
            ResourceKey::Field(f) => SnapshotResource::Field(f.clone()),
            ResourceKey::Predicate(p) => SnapshotResource::Predicate(p.clone()),
            ResourceKey::Wand(w) => SnapshotResource::Wand(w.ghost_free_wand.clone()),
        };
        let chunks = consumed
            .iter()
            .map(|chunk| match chunk {
                Chunk::QuantifiedField(c) => Ok(QuantifiedBasicChunk::Field(c.clone())),
                Chunk::QuantifiedPredicate(c) => Ok(QuantifiedBasicChunk::Predicate(c.clone())),
                Chunk::QuantifiedMagicWand(c) => Ok(QuantifiedBasicChunk::Wand(c.clone())),
                _ => Err(NativeError::Unsupported(
                    "non-quantified snapshot summary chunk",
                )),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let key = CacheKey {
            resource: source.clone(),
            relevant_chunks: chunks,
        };
        let cached = (!state.exhale_ext)
            .then(|| state.sm_cache.get(&key, domain_condition))
            .flatten()
            .map(|(definition, _)| definition.clone());
        let factory = self.factory.clone();
        let mut cache = state.sm_cache.clone();
        let definition = if let Some(definition) = cached {
            definition
        } else {
            let (snapshot_map, value_definitions, domain_definitions) =
                crate::rules::quantified_chunk_support::summarise_snapshot_map(
                    &factory,
                    self,
                    state,
                    resource,
                    formals,
                    consumed,
                    domain_condition,
                    state.heap_dependent_triggers.contains(resource),
                    false,
                )
                .map_err(|e| {
                    NativeError::Chunk(format!("general consumed snapshot summary: {e:?}"))
                })?;
            let definition = SnapshotMapDefinition {
                resource: source,
                snapshot_map,
                value_definitions,
                domain_definitions,
            };
            let mut total = factory.no_perm();
            for chunk in consumed {
                let permission = match chunk {
                    Chunk::QuantifiedField(c) => c.permission(&factory),
                    Chunk::QuantifiedPredicate(c) => c.permission(&factory),
                    Chunk::QuantifiedMagicWand(c) => c.permission(&factory),
                    _ => {
                        return Err(NativeError::Unsupported(
                            "non-quantified snapshot summary chunk",
                        ));
                    }
                };
                total = factory.perm_plus(total, permission);
            }
            cache = cache.with_entry(key, definition.clone(), total, domain_condition.cloned());
            definition
        };
        if state.sm_domain_needed {
            for term in &definition.domain_definitions {
                self.assume_term(term)?;
            }
        }
        for term in &definition.value_definitions {
            self.assume_term(term)?;
        }
        Ok((definition, cache))
    }
    fn clear_general_consumption_model(&mut self) -> Result<(), NativeError<S::Error>> {
        self.base.decider.clear_model();
        Ok(())
    }
    fn next_general_consumption_tag(&mut self) -> i32 {
        let id = self.quantified_counter as i32;
        self.quantified_counter = self.quantified_counter.wrapping_add(1);
        id
    }
    fn complete_general_quantified_exhale(&self) -> bool {
        self.options.exhale_mode_qp == crate::config::ExhaleMode::MoreComplete
    }
    fn disable_general_chunk_ordering(&self) -> bool {
        false
    }
    fn disable_general_isc_triggers(&self) -> bool {
        false
    }
    fn debug_general_consumption(&self) -> bool {
        false
    }
}

fn native_quantified_source(
    resource: &ResourceKey,
) -> crate::rules::quantified_chunk_support::SnapshotResource {
    use crate::rules::quantified_chunk_support::SnapshotResource;
    match resource {
        ResourceKey::Field(f) => SnapshotResource::Field(f.clone()),
        ResourceKey::Predicate(p) => SnapshotResource::Predicate(p.clone()),
        ResourceKey::Wand(w) => SnapshotResource::Wand(w.ghost_free_wand.clone()),
    }
}
fn native_quantified_chunks(heap: &ListBackedHeap, resource: &ResourceKey) -> Vec<Chunk> {
    use crate::state::heap::Heap;
    heap.values()
        .iter()
        .filter(|chunk| match (resource, chunk) {
            (ResourceKey::Field(f), Chunk::QuantifiedField(c)) => c.id_ref().0 == f.name,
            (ResourceKey::Predicate(p), Chunk::QuantifiedPredicate(c)) => c.id_ref().0 == p.name,
            (ResourceKey::Wand(w), Chunk::QuantifiedMagicWand(c)) => c.id_ref() == w,
            _ => false,
        })
        .cloned()
        .collect()
}

impl<S: Prover, PD, FD: Clone>
    crate::rules::state_consolidator::QuantifiedFieldBoundServices<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn summarise_bound_maps(
        &mut self,
        state: State<PD, FD, JoinMode>,
        field: &ferrum_silver::ast::program::Field,
        receiver: &Term,
        chunks: &[crate::state::chunks::QuantifiedFieldChunk],
    ) -> Result<
        (
            State<PD, FD, JoinMode>,
            crate::rules::quantified_chunk_support::SnapshotMapDefinition,
            crate::rules::quantified_chunk_support::PermMapDefinition,
        ),
        Self::Error,
    > {
        let resource = ResourceKey::Field(Arc::new(field.clone()));
        let source = native_quantified_source(&resource);
        let chunks: Vec<_> = chunks.iter().cloned().map(Chunk::QuantifiedField).collect();
        let trigger = state.heap_dependent_triggers.contains(&resource);
        let factory = self.factory.clone();
        crate::rules::quantified_chunk_support::heap_summarising_maps(
            &factory,
            self,
            state,
            &resource,
            source,
            std::slice::from_ref(receiver),
            &chunks,
            None,
            None,
            trigger,
            false,
            false,
            false,
        )
        .map_err(|e| NativeError::Consolidation(format!("quantified bound summaries: {e:?}")))
    }
    fn assume_quantified_field_bound(
        &mut self,
        state: State<PD, FD, JoinMode>,
        _: &ferrum_silver::ast::program::Field,
        _: Option<&crate::state::chunks::QuantifiedFieldChunk>,
        _: &Term,
        goal: &Term,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        self.assume_term(goal)?;
        Ok(state)
    }
}

impl<S: Prover, PD, FD> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn assume_native_inverse_trigger(
        &mut self,
        resource: &ResourceKey,
        formals: &[Term],
        condition: &Term,
        inverse: &crate::rules::quantified_chunk_support::InverseFunctions,
        definition: &crate::rules::quantified_chunk_support::SnapshotMapDefinition,
    ) -> Result<(), NativeError<S::Error>> {
        let substitutions = inverse.qvars_to_inverses_of(&self.factory, formals);
        let condition = self
            .factory
            .replace(condition, &substitutions.iter().cloned().collect())
            .map_err(|e| NativeError::Chunk(format!("inverse trigger substitution: {e:?}")))?;
        let trigger = self.factory.resource_trigger(
            resource,
            definition.snapshot_map.clone(),
            formals.to_vec(),
        );
        let patterns = substitutions.into_iter().map(|(_, term)| term).collect();
        let axiom = self
            .factory
            .quantification(
                crate::state::terms::Quantifier::Forall,
                formals.to_vec(),
                self.factory.implies(condition, trigger),
                vec![crate::state::terms::Trigger { terms: patterns }],
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(|e| NativeError::Chunk(format!("inverse trigger quantifier: {e:?}")))?;
        self.assume_term(&axiom)
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::rules::magic_wand_supporter::WandReserveHeapServices<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn merge_evaluation_reserves(
        &mut self,
        _: &State<PD, FD, JoinMode>,
        used: &ListBackedHeap,
        operations: &ListBackedHeap,
        lhs: &ListBackedHeap,
    ) -> Result<ListBackedHeap, Self::Error> {
        Ok(used.with_heap(operations).with_heap(lhs))
    }
    fn empty_wand_heap(
        &mut self,
        _: &State<PD, FD, JoinMode>,
    ) -> Result<ListBackedHeap, Self::Error> {
        Ok(ListBackedHeap::new())
    }
    fn merge_wand_operations(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        operations: &ListBackedHeap,
        new_heap: &ListBackedHeap,
    ) -> Result<(FunctionRecorder<FD>, ListBackedHeap), Self::Error> {
        let factory = self.factory.clone();
        let choice = self.consolidation_choice(state)?;
        crate::rules::state_consolidator::merge_heaps(
            &factory,
            self,
            state,
            state.function_recorder.clone(),
            operations,
            new_heap,
            choice,
        )
        .map_err(|e| NativeError::Consolidation(format!("wand operations heap: {e:?}")))
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::rules::magic_wand_supporter::WandApplicationServices<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    type VerificationError = PartialVerificationError;
    fn consume_wand_assertion(
        &mut self,
        state: State<PD, FD, JoinMode>,
        assertion: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::rules::magic_wand_supporter::WandApplicationError<Self::Error>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::rules::magic_wand_supporter::WandApplicationError<Self::Error>,
    > {
        use crate::rules::magic_wand_supporter::WandApplicationError as WE;
        let mut callback_error = None;
        let result = crate::rules::consumer::consume_all(
            self,
            state,
            std::slice::from_ref(assertion),
            true,
            &|_| error.clone(),
            &mut |ctx, state, snapshot| match continuation(ctx, state, snapshot) {
                Ok(result) => Ok(result),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ConsumptionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result
            .map_err(|e| WE::Service(NativeError::Consumption(format!("wand application: {e:?}"))))
    }
    fn wand_evaluation_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        crate::rules::magic_wand_supporter::evaluation_heap(self, state)
            .map_err(|e| NativeError::Execution(format!("wand evaluation heap: {e:?}")))
    }
    fn assume_wand_token(&mut self, token: &Term) -> Result<(), Self::Error> {
        self.assume_term(token)
    }
    fn produce_wand_rhs(
        &mut self,
        state: State<PD, FD, JoinMode>,
        rhs: &Exp,
        snapshot: &Term,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::rules::magic_wand_supporter::WandApplicationError<Self::Error>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::rules::magic_wand_supporter::WandApplicationError<Self::Error>,
    > {
        use crate::rules::magic_wand_supporter::WandApplicationError as WE;
        let mut callback_error = None;
        let result = crate::rules::producer::produce_all(
            self,
            state,
            NativeSnapshot::Projection(snapshot.clone()),
            std::slice::from_ref(rhs),
            &|_| error.clone(),
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(result) => Ok(result),
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
            WE::Service(NativeError::Production(format!(
                "wand application RHS: {e:?}"
            )))
        })
    }
    fn consolidate_wand_state(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        let choice = self.consolidation_choice(&state)?;
        let factory = self.factory.clone();
        crate::rules::state_consolidator::consolidate(&factory, self, state, choice, false)
            .map_err(|e| NativeError::Consolidation(format!("wand application: {e:?}")))
    }
}

impl<S: Prover, PD, FD> crate::rules::magic_wand_supporter::WandHeapServices
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn check_wand_permissions(
        &mut self,
        assertion: &Term,
        timeout_ms: i32,
    ) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check(assertion, Some(timeout_ms))
            .map_err(NativeError::Decider)
    }
    fn wand_check_timeout(&self) -> i32 {
        self.base.decider.check_timeout.unwrap_or(0)
    }
    fn assume_wand_snapshot_definition(&mut self, definition: &Term) -> Result<(), Self::Error> {
        self.base
            .decider
            .assume([(definition.clone(), None)], false, true)
            .map_err(NativeError::Decider)
    }
    fn wand_smoke_check(&mut self) -> Result<bool, Self::Error> {
        self.base
            .decider
            .check_smoke(false)
            .map_err(NativeError::Decider)
    }
}

type NativeWandTransferResult<E> = Result<
    VerificationResult<VerificationError>,
    crate::rules::magic_wand_supporter::WandTransferError<NativeError<E>>,
>;
impl<S: Prover, PD, FD: Clone>
    crate::rules::magic_wand_supporter::WandTransferServices<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn retry_wand_transfer(
        &mut self,
        state: State<PD, FD, JoinMode>,
        action: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            &mut dyn FnMut(
                &mut Self,
                State<PD, FD, JoinMode>,
                Vec<Arc<ListBackedHeap>>,
                Vec<Option<Chunk>>,
            ) -> NativeWandTransferResult<S::Error>,
        ) -> NativeWandTransferResult<S::Error>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Vec<Arc<ListBackedHeap>>,
            Vec<Option<Chunk>>,
        ) -> NativeWandTransferResult<S::Error>,
    ) -> NativeWandTransferResult<S::Error> {
        use crate::rules::magic_wand_supporter::WandTransferError as WE;
        self.retry_consumption(
            state,
            &mut |ctx, state, done| {
                action(ctx, state, &mut |ctx, state, heaps, chunks| {
                    done(ctx, state, (heaps, chunks))
                        .map_err(|e| WE::Service(NativeError::Consumption(format!("{e:?}"))))
                })
                .map_err(|e| ConsumptionError::Context(NativeError::Execution(format!("{e:?}"))))
            },
            &mut |ctx, state, (heaps, chunks)| {
                continuation(ctx, state, heaps, chunks).map_err(|e| {
                    ConsumptionError::Context(NativeError::Execution(format!("{e:?}")))
                })
            },
        )
        .map_err(|e| WE::Service(NativeError::Consumption(format!("{e:?}"))))
    }
    fn merge_transferred_chunks(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        chunks: &[Chunk],
    ) -> Result<(FunctionRecorder<FD>, ListBackedHeap), Self::Error> {
        let factory = self.factory.clone();
        let choice = self.consolidation_choice(state)?;
        crate::rules::state_consolidator::merge_heaps(
            &factory,
            self,
            state,
            state.function_recorder.clone(),
            heap,
            &ListBackedHeap::from_chunks(chunks.iter().cloned()),
            choice,
        )
        .map_err(|e| NativeError::Consolidation(format!("wand transferred chunks: {e:?}")))
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::rules::magic_wand_supporter::WandPackagingFinalization<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;

    fn fresh_unknown_lhs(&mut self) -> Result<Term, Self::Error> {
        self.base
            .decider
            .fresh_variable(&self.factory, "snap", &Sort::Snap, false, None)
            .map_err(NativeError::Decider)
    }
    fn empty_package_heap(
        &mut self,
        _: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        Ok(Arc::new(ListBackedHeap::new()))
    }
    fn assume_package_token_axiom(&mut self, axiom: &Term) -> Result<(), Self::Error> {
        self.assume_term(axiom)
    }
    fn assume_package_definitions(&mut self, definitions: &[Term]) -> Result<(), Self::Error> {
        self.base
            .decider
            .assume(
                definitions.iter().cloned().map(|term| (term, None)),
                false,
                true,
            )
            .map_err(NativeError::Decider)
    }
    fn consolidate_package_branches(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        let choice = self.consolidation_choice(&state)?;
        let factory = self.factory.clone();
        crate::rules::state_consolidator::consolidate(&factory, self, state, choice, false)
            .map_err(|e| NativeError::Consolidation(format!("wand package branches: {e:?}")))
    }
    fn create_packaged_wand(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        wand: &Exp,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
        snapshot: &Term,
    ) -> Result<Chunk, Self::Error> {
        let resource = crate::rules::quantified_chunk_support::SnapshotResource::Wand(wand.clone());
        let id = crate::state::chunks::MagicWandIdentifier::new(wand.clone(), &state.program)
            .map_err(|e| NativeError::Chunk(format!("wand identifier: {e:?}")))?;
        if state
            .is_quantified_resource(&resource)
            .map_err(|e| NativeError::Chunk(format!("wand resource: {e:?}")))?
        {
            use crate::state::terms::TermKind;
            let TermKind::MagicWandSnapshot(function) = snapshot.kind() else {
                return Err(NativeError::Chunk("expected magic wand snapshot".into()));
            };
            let key = ResourceKey::Wand(id);
            let formals = state
                .formal_arg_vars(&resource, &self.base.symbol_converter, &self.factory)
                .map_err(|e| NativeError::Chunk(format!("wand formals: {e:?}")))?;
            let factory = self.factory.clone();
            let (map, definition) = crate::rules::quantified_chunk_support::singleton_snapshot_map(
                &factory,
                self,
                state,
                &key,
                args,
                function.clone(),
            )
            .map_err(|e| NativeError::Chunk(format!("wand singleton map: {e:?}")))?;
            self.base
                .decider
                .assume([(definition, None)], false, true)
                .map_err(NativeError::Decider)?;
            return crate::rules::quantified_chunk_support::singleton_quantified_chunk(
                &factory,
                &key,
                formals,
                None,
                args.to_vec(),
                arg_exps.map(<[Exp]>::to_vec),
                factory.full_perm(),
                None,
                map,
                None,
                false,
            )
            .map_err(|e| NativeError::Chunk(format!("quantified wand chunk: {e:?}")));
        }
        use crate::state::store::Store;
        let bindings = crate::state::chunks::ChunkBindings::new(state.g.values().iter().cloned());
        Ok(Chunk::MagicWand(crate::state::chunks::MagicWandChunk::new(
            id,
            bindings,
            args.to_vec(),
            arg_exps.map(<[Exp]>::to_vec),
            snapshot.clone(),
            self.factory.full_perm(),
            None,
            None,
        )))
    }
    fn package_merge_warning(&mut self, warning: String) {
        self.warnings.push(warning);
    }
    fn debug_package_branches(&self) -> bool {
        false
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::rules::magic_wand_supporter::WandPackageServices<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type VerificationError = PartialVerificationError;
    fn consolidate_before_package(
        &mut self,
        state: State<PD, FD, JoinMode>,
    ) -> Result<State<PD, FD, JoinMode>, Self::Error> {
        <Self as crate::rules::magic_wand_supporter::WandPackagingFinalization<PD, FD, JoinMode>>::consolidate_package_branches(self, state)
    }
    fn fresh_package_root(&mut self) -> Result<Term, Self::Error> {
        <Self as crate::rules::magic_wand_supporter::WandPackagingFinalization<PD, FD, JoinMode>>::fresh_unknown_lhs(self)
    }
    fn fresh_wand_snapshot_function(&mut self) -> Result<Term, Self::Error> {
        let (target, _) = self
            .base
            .decider
            .fresh(&self.factory, "mwsf", &[], &Sort::MagicWandSnapFunction)
            .map_err(NativeError::Decider)?;
        Ok(match target {
            ApplicationTarget::Function(f) => self.factory.app(f, vec![]),
            ApplicationTarget::Variable(v) => v,
        })
    }
    fn package_root_debug_variable(
        &mut self,
    ) -> Result<Option<crate::state::store::AbstractLocalVar>, Self::Error> {
        Ok(None)
    }
    fn evaluate_package_arguments(
        &mut self,
        state: State<PD, FD, JoinMode>,
        wand: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Vec<Term>,
            Option<Vec<Exp>>,
        ) -> NativePackageResult<S::Error>,
    ) -> NativePackageResult<S::Error> {
        use crate::rules::magic_wand_supporter::PackageExecutionError as PE;
        let mut callback_error = None;
        let result = crate::rules::magic_wand_supporter::evaluate_wand_arguments(
            self,
            state,
            wand,
            error,
            &mut |ctx, state, args, exps| match continuation(ctx, state, args, exps) {
                Ok(result) => Ok(result),
                Err(e) => {
                    callback_error = Some(e);
                    Err(EvaluationError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| {
            PE::Service(NativeError::Evaluation(format!(
                "wand package arguments: {e:?}"
            )))
        })
    }
    fn locally_package(
        &mut self,
        state: State<PD, FD, JoinMode>,
        action: &mut dyn FnMut(&mut Self, State<PD, FD, JoinMode>) -> NativePackageResult<S::Error>,
    ) -> NativePackageResult<S::Error> {
        use crate::rules::magic_wand_supporter::PackageExecutionError as PE;
        self.base
            .decider
            .push_scope()
            .map_err(|e| PE::Service(NativeError::Decider(e)))?;
        let result = action(self, state);
        let cleanup = self.base.decider.pop_scope();
        match (result, cleanup) {
            (Ok(v), Ok(())) => Ok(v),
            (Err(e), Ok(())) => Err(e),
            (Ok(_), Err(e)) => Err(PE::Service(NativeError::Decider(e))),
            (Err(e), Err(cleanup)) => Err(PE::Service(NativeError::Cleanup(format!(
                "{e:?}; cleanup: {cleanup:?}"
            )))),
        }
    }
    fn package_path_mark(&mut self) -> Result<crate::decider::path_conditions::Mark, Self::Error> {
        Ok(self.base.decider.mark())
    }
    fn package_paths_after(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<crate::decider::path_conditions::RecordedPathConditions, Self::Error> {
        self.base
            .decider
            .pcs
            .after(mark)
            .map_err(|e| NativeError::Decider(DeciderError::Path(e)))
    }
    fn produce_package_lhs(
        &mut self,
        state: State<PD, FD, JoinMode>,
        lhs: &Exp,
        root: &Term,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> NativePackageResult<S::Error>,
    ) -> NativePackageResult<S::Error> {
        use crate::rules::magic_wand_supporter::PackageExecutionError as PE;
        let mut callback_error = None;
        let result = crate::rules::producer::produce_all(
            self,
            state,
            NativeSnapshot::Projection(root.clone()),
            std::slice::from_ref(lhs),
            &|_| error.clone(),
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(result) => Ok(result),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ProductionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| PE::Service(NativeError::Production(format!("wand package LHS: {e:?}"))))
    }
    fn package_proof_cfg(&mut self, proof: &Stmt) -> Result<Arc<SilverCfg>, Self::Error> {
        ferrum_silver::cfg::silver::cfg_generator::statement_to_cfg(proof, false, true)
            .map(Arc::new)
            .map_err(|e| NativeError::Execution(format!("wand proof CFG: {e:?}")))
    }
    fn execute_package_proof(
        &mut self,
        state: State<PD, FD, JoinMode>,
        cfg: Arc<SilverCfg>,
        _: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> NativePackageResult<S::Error>,
    ) -> NativePackageResult<S::Error> {
        use crate::rules::magic_wand_supporter::PackageExecutionError as PE;
        let mut callback_error = None;
        let result = crate::rules::executor::execute_cfg(self, state, &cfg, &mut |ctx, state| {
            match continuation(ctx, state) {
                Ok(result) => Ok(result),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ExecutionError::Context(NativeError::ContinuationAbort))
                }
            }
        });
        if let Some(error) = callback_error {
            return Err(error);
        }
        result
            .map_err(|e| PE::Service(NativeError::Execution(format!("wand package proof: {e:?}"))))
    }
    fn consume_package_rhs(
        &mut self,
        state: State<PD, FD, JoinMode>,
        rhs: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Option<Term>,
        ) -> NativePackageResult<S::Error>,
    ) -> NativePackageResult<S::Error> {
        use crate::rules::magic_wand_supporter::PackageExecutionError as PE;
        let mut callback_error = None;
        let result = crate::rules::consumer::consume_all(
            self,
            state,
            std::slice::from_ref(rhs),
            true,
            &|_| error.clone(),
            &mut |ctx, state, snapshot| match continuation(ctx, state, snapshot) {
                Ok(result) => Ok(result),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ConsumptionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result
            .map_err(|e| PE::Service(NativeError::Consumption(format!("wand package RHS: {e:?}"))))
    }
    fn assume_package_snapshot_definition(&mut self, definition: &Term) -> Result<(), Self::Error> {
        self.assume_term(definition)
    }
}
type NativePackageResult<E> = Result<
    VerificationResult<VerificationError>,
    crate::rules::magic_wand_supporter::PackageExecutionError<NativeError<E>>,
>;

impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    /// Summarise a source-ordered nonquantified resource heap for complete exhale.
    fn complete_lookup_summary(
        &mut self,
        mut state: State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        chunks: &[crate::state::package::NonQuantifiedChunkKey],
        args: &[Term],
        known_value: Option<Option<Term>>,
    ) -> Result<(State<PD, FD, JoinMode>, Term, Term), NativeError<S::Error>> {
        use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk};
        use crate::rules::more_complete_exhale_supporter::{
            TaggedSummarisingSnapshot, permission_sum,
        };
        use crate::state::package::{
            NonQuantifiedChunkKey as C, SnapshotSummary, SnapshotSummaryKey,
        };
        let factory = self.factory.clone();
        let view = |c: &C| match c {
            C::Basic(v) => (
                v.args().to_vec(),
                v.permission(&factory),
                v.snapshot().clone(),
            ),
            C::Wand(v) => (
                v.args().to_vec(),
                v.permission(&factory),
                v.snapshot().clone(),
            ),
        };
        if let [only] = chunks {
            let (arguments, permission, snapshot) = view(only);
            let equal = factory.and(
                arguments
                    .into_iter()
                    .zip(args.iter().cloned())
                    .map(|(a, b)| factory.equals(a, b)),
            );
            if self
                .base
                .decider
                .check(&equal, self.base.decider.check_timeout)
                .map_err(NativeError::Decider)?
            {
                return Ok((state, snapshot, permission));
            }
        }
        let source = native_quantified_source(resource);
        let key = SnapshotSummaryKey {
            resource: source.clone(),
            chunks: chunks.to_vec(),
            arguments: args.to_vec(),
        };
        if let Some(summary) = state.ss_cache.get(&key).cloned() {
            if let (Some(tagged), Some(definitions)) =
                (summary.tagged_snapshot, summary.definitions)
            {
                self.base
                    .decider
                    .assume([(factory.and(definitions.clone()), None)], false, true)
                    .map_err(NativeError::Decider)?;
                if matches!(tagged, TaggedSummarisingSnapshot::Fresh(_)) {
                    state.function_recorder = state.function_recorder.record_fvf_and_domain(
                        crate::rules::quantified_chunk_support::SnapshotMapDefinition {
                            resource: source.clone(),
                            snapshot_map: tagged.snapshot().clone(),
                            value_definitions: definitions,
                            domain_definitions: vec![],
                        },
                    );
                }
                return Ok((state, tagged.snapshot().clone(), summary.permission));
            }
        }
        let sort = match resource {
            ResourceKey::Field(field) => self
                .base
                .symbol_converter
                .to_sort(&field.typ)
                .map_err(NativeError::Sort)?,
            ResourceKey::Predicate(_) => Sort::Snap,
            ResourceKey::Wand(_) => Sort::MagicWandSnapFunction,
        };
        let hole = factory.var(
            crate::state::identifiers::Identifier::new("?s"),
            sort.clone(),
            false,
        );
        let mut definitions = Vec::new();
        for chunk in chunks {
            let (arguments, permission, snapshot) = view(chunk);
            let equal = factory.and(
                arguments
                    .into_iter()
                    .zip(args.iter().cloned())
                    .map(|(a, b)| factory.equals(a, b)),
            );
            definitions.push(factory.implies(
                factory.and([equal, factory.is_positive_perm(permission)]),
                factory.equals(hole.clone(), snapshot),
            ));
        }
        let mut reused = None;
        for definition in &definitions {
            if let crate::state::terms::TermKind::BuiltinEquals(a, b)
            | crate::state::terms::TermKind::CustomEquals(a, b) = definition.kind()
            {
                if *a == hole {
                    reused = Some(b.clone());
                    break;
                }
            }
        }
        if reused.is_none() {
            if let Some(value) = &known_value {
                reused = value.clone();
            }
        }
        if reused.is_none() && known_value.is_none() {
            let heap = ListBackedHeap::from_chunks(chunks.iter().map(|chunk| match chunk {
                C::Basic(v) => Chunk::Basic(v.clone()),
                C::Wand(v) => Chunk::MagicWand(v.clone()),
            }));
            let identifier = match resource {
                ResourceKey::Field(f) => ChunkIdentifier::Basic(
                    crate::state::chunks::BasicChunkIdentifier(f.name.clone()),
                ),
                ResourceKey::Predicate(p) => ChunkIdentifier::Basic(
                    crate::state::chunks::BasicChunkIdentifier(p.name.clone()),
                ),
                ResourceKey::Wand(w) => ChunkIdentifier::Wand(w.clone()),
            };
            if let Some(index) =
                crate::rules::chunk_supporter::find_chunk(self, &heap, &identifier, args)
                    .map_err(|e| NativeError::Chunk(format!("summary alias: {e:?}")))?
            {
                let (_, permission, snapshot) = view(&chunks[index]);
                if self
                    .base
                    .decider
                    .check(
                        &factory.is_positive_perm(permission),
                        self.base.decider.check_timeout,
                    )
                    .map_err(NativeError::Decider)?
                {
                    reused = Some(snapshot);
                }
            }
        }
        let tagged = if let Some(snapshot) = reused {
            TaggedSummarisingSnapshot::Reused(snapshot)
        } else {
            let variables: Vec<_> = state
                .function_recorder
                .arguments()
                .unwrap_or_default()
                .into_iter()
                .map(|(t, _)| t)
                .chain(
                    state
                        .packaging_wand_snapshots
                        .iter()
                        .map(|(t, _)| t.clone()),
                )
                .chain(state.quantified_variables.iter().map(|(t, _)| t.clone()))
                .collect();
            let sorts: Vec<_> = variables.iter().map(|v| v.sort().clone()).collect();
            let (target, _) = self
                .base
                .decider
                .fresh(&factory, "ss", &sorts, &sort)
                .map_err(NativeError::Decider)?;
            let snapshot = match target {
                ApplicationTarget::Function(f) => factory.app(f, variables),
                ApplicationTarget::Variable(v) if variables.is_empty() => v,
                _ => return Err(NativeError::Unsupported("summary snapshot target")),
            };
            TaggedSummarisingSnapshot::Fresh(snapshot)
        };
        let snapshot = tagged.snapshot().clone();
        let replacements = std::collections::HashMap::from([(hole, snapshot.clone())]);
        let definitions = definitions
            .into_iter()
            .map(|term| factory.replace(&term, &replacements))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| NativeError::Chunk(format!("snapshot summary substitution: {e:?}")))?;
        let permission = permission_sum(&factory, chunks, args);
        state.ss_cache.insert(
            key,
            SnapshotSummary {
                tagged_snapshot: Some(tagged.clone()),
                definitions: Some(definitions.clone()),
                permission: permission.clone(),
                permission_exp: None,
            },
        );
        self.base
            .decider
            .assume([(factory.and(definitions.clone()), None)], false, true)
            .map_err(NativeError::Decider)?;
        if matches!(tagged, TaggedSummarisingSnapshot::Fresh(_)) {
            state.function_recorder = state.function_recorder.record_fvf_and_domain(
                crate::rules::quantified_chunk_support::SnapshotMapDefinition {
                    resource: source,
                    snapshot_map: snapshot.clone(),
                    value_definitions: definitions,
                    domain_definitions: vec![],
                },
            );
        }
        Ok((state, snapshot, permission))
    }
}

impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn complete_consume_exact(
        &mut self,
        mut state: State<PD, FD, JoinMode>,
        heap: Arc<ListBackedHeap>,
        resource: &ResourceKey,
        args: &[Term],
        permission: &Term,
        return_snapshot: bool,
        error: &Option<VerificationError>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ChunkExecutionError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ChunkExecutionError<NativeError<S::Error>>>
    {
        use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk};
        use crate::rules::chunk_supporter::ChunkExecutionContext;
        use crate::state::{
            heap::Heap,
            package::NonQuantifiedChunkKey as C,
            terms::{ApplicableData, ApplicableKind, TermKind},
        };
        let factory = self.factory.clone();
        let identifier = match resource {
            ResourceKey::Field(f) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(f.name.clone()))
            }
            ResourceKey::Predicate(p) => {
                ChunkIdentifier::Basic(crate::state::chunks::BasicChunkIdentifier(p.name.clone()))
            }
            ResourceKey::Wand(w) => ChunkIdentifier::Wand(w.clone()),
        };
        let mut relevant = Vec::new();
        let mut others = Vec::new();
        for chunk in heap.values() {
            match chunk {
                Chunk::Basic(c) if c.identifier() == identifier => {
                    relevant.push(C::Basic(c.clone()))
                }
                Chunk::MagicWand(c) if c.identifier() == identifier => {
                    relevant.push(C::Wand(c.clone()))
                }
                _ => others.push(chunk.clone()),
            }
        }
        if relevant.is_empty() {
            let goal = factory.equals(permission.clone(), factory.no_perm());
            if self
                .base
                .decider
                .check(&goal, self.base.decider.assert_timeout)
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?
            {
                return continuation(self, state, heap, None);
            }
            return self
                .consumption_failure(&state, error, "complete empty heap", true)
                .map_err(ChunkExecutionError::Context);
        }
        if !crate::state::terms::consume_exact_read(permission, &state.constrainable_arps) {
            return self.complete_consume_constrainable(
                state,
                relevant,
                others,
                resource,
                args,
                permission,
                return_snapshot,
                error,
                continuation,
            );
        }
        let originals = relevant.clone();
        let candidate_heap = ListBackedHeap::from_chunks(relevant.iter().map(|c| match c {
            C::Basic(v) => Chunk::Basic(v.clone()),
            C::Wand(v) => Chunk::MagicWand(v.clone()),
        }));
        let alias =
            crate::rules::chunk_supporter::find_chunk(self, &candidate_heap, &identifier, args)
                .map_err(|e| {
                    ChunkExecutionError::Context(NativeError::Chunk(format!(
                        "complete alias: {e:?}"
                    )))
                })?;
        let view = |c: &C| match c {
            C::Basic(v) => (v.args().to_vec(), v.permission(&factory)),
            C::Wand(v) => (v.args().to_vec(), v.permission(&factory)),
        };
        let definite = if let Some(index) = alias {
            let (_, p) = view(&relevant[index]);
            if self
                .base
                .decider
                .check(
                    &factory.is_positive_perm(p),
                    self.base.decider.check_timeout,
                )
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?
            {
                Some(relevant[index].clone())
            } else {
                None
            }
        } else {
            None
        };
        relevant.sort_by_key(|chunk| {
            if definite.as_ref() == Some(chunk) {
                0
            } else if view(chunk).0 == args {
                1
            } else {
                2
            }
        });
        let additional: Vec<_> = state
            .function_recorder
            .arguments()
            .unwrap_or_default()
            .into_iter()
            .map(|(t, _)| t)
            .chain(state.quantified_variables.iter().map(|(t, _)| t.clone()))
            .collect();
        let mut needed = permission.clone();
        let mut more = true;
        let mut updated = Vec::new();
        for chunk in relevant {
            if !more {
                updated.push(chunk);
                continue;
            }
            let (arguments, available) = view(&chunk);
            let equal = factory.and(
                arguments
                    .into_iter()
                    .zip(args.iter().cloned())
                    .map(|(a, b)| factory.equals(a, b)),
            );
            let taken = factory.ite(
                equal,
                factory.perm_min(available.clone(), needed.clone()),
                factory.no_perm(),
            );
            let literal = matches!(
                taken.kind(),
                TermKind::NoPerm | TermKind::FullPerm | TermKind::FractionPermLiteral(_)
            );
            let taken = if literal
                || !matches!(state.function_recorder, FunctionRecorder::Noop)
                || factory.options().use_flyweight
            {
                taken
            } else {
                let declaration = self
                    .base
                    .decider
                    .fresh_macro(
                        &factory,
                        &mut self.base.identifiers,
                        "mce_pTaken",
                        additional.clone(),
                        taken.clone(),
                    )
                    .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?;
                let target = factory.applicable(ApplicableData {
                    kind: ApplicableKind::Macro,
                    id: declaration.id(),
                    arg_sorts: additional.iter().map(|t| t.sort().clone()).collect(),
                    result_sort: taken.sort().clone(),
                });
                state.function_recorder = state.function_recorder.record_fresh_macro(declaration);
                factory.app(target, additional.clone())
            };
            let remaining = factory.perm_minus(available, taken.clone());
            needed = factory.perm_minus(needed, taken);
            let keep = !self
                .base
                .decider
                .check(
                    &factory.is_nonpositive_perm(remaining.clone()),
                    Some(self.options.qp_split_timeout),
                )
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?;
            if keep {
                updated.push(match chunk {
                    C::Basic(c) => C::Basic(c.with_permission(remaining, None)),
                    C::Wand(c) => C::Wand(c.with_permission(remaining, None)),
                });
            }
            more = !self
                .base
                .decider
                .check(
                    &factory.equals(needed.clone(), factory.no_perm()),
                    Some(self.options.qp_split_timeout),
                )
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?;
        }
        let new_chunks: Vec<_> = updated
            .into_iter()
            .map(|c| match c {
                C::Basic(v) => Chunk::Basic(v),
                C::Wand(v) => Chunk::MagicWand(v),
            })
            .collect();
        let result_heap =
            ListBackedHeap::from_chunks(others.into_iter().chain(new_chunks.iter().cloned()));
        for chunk in &new_chunks {
            crate::rules::chunk_supporter::ChunkSolver::assume_properties(
                self,
                &state,
                &result_heap,
                chunk,
            )
            .map_err(ChunkExecutionError::Context)?;
        }
        let snapshot = if return_snapshot {
            let (next, snapshot, _) = self
                .complete_lookup_summary(
                    state,
                    resource,
                    &originals,
                    args,
                    Some(definite.as_ref().map(|chunk| match chunk {
                        C::Basic(c) => c.snapshot().clone(),
                        C::Wand(c) => c.snapshot().clone(),
                    })),
                )
                .map_err(ChunkExecutionError::Context)?;
            state = next;
            if self
                .base
                .decider
                .check(
                    &factory.is_positive_perm(permission.clone()),
                    self.base.decider.check_timeout,
                )
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?
            {
                Some(snapshot)
            } else {
                Some(factory.ite(
                    factory.is_positive_perm(permission.clone()),
                    factory.sort_wrapper(snapshot, Sort::Snap),
                    factory.unit(),
                ))
            }
        } else {
            None
        };
        if more
            && !self
                .base
                .decider
                .check(
                    &factory.equals(needed, factory.no_perm()),
                    self.base.decider.assert_timeout,
                )
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?
        {
            return self
                .consumption_failure(&state, error, "complete permission consumption", true)
                .map_err(ChunkExecutionError::Context);
        }
        continuation(self, state, Arc::new(result_heap), snapshot)
    }
}

impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn complete_consume_constrainable(
        &mut self,
        state: State<PD, FD, JoinMode>,
        chunks: Vec<crate::state::package::NonQuantifiedChunkKey>,
        others: Vec<Chunk>,
        resource: &ResourceKey,
        args: &[Term],
        permission: &Term,
        return_snapshot: bool,
        error: &Option<VerificationError>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ChunkExecutionError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ChunkExecutionError<NativeError<S::Error>>>
    {
        use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk};
        use crate::rules::chunk_supporter::ChunkExecutionContext;
        use crate::state::package::NonQuantifiedChunkKey as C;
        let factory = self.factory.clone();
        let variables: Vec<_> = state
            .function_recorder
            .arguments()
            .unwrap_or_default()
            .into_iter()
            .map(|(t, _)| t)
            .chain(state.quantified_variables.iter().map(|(t, _)| t.clone()))
            .collect();
        let sorts: Vec<_> = variables.iter().map(|term| term.sort().clone()).collect();
        let mut recorder = state.function_recorder.clone();
        let mut total_sum = factory.no_perm();
        let mut total_taken = factory.no_perm();
        let mut updated = Vec::new();
        for chunk in &chunks {
            let (arguments, available) = match chunk {
                C::Basic(c) => (c.args(), c.permission(&factory)),
                C::Wand(c) => (c.args(), c.permission(&factory)),
            };
            let equal = factory.and(
                arguments
                    .iter()
                    .cloned()
                    .zip(args.iter().cloned())
                    .map(|(a, b)| factory.equals(a, b)),
            );
            let (target, _) = self
                .base
                .decider
                .fresh(&factory, "p", &sorts, &Sort::Perm)
                .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?;
            let taken = match &target {
                ApplicationTarget::Function(fun) => factory.app(fun.clone(), variables.clone()),
                ApplicationTarget::Variable(v) if variables.is_empty() => v.clone(),
                _ => {
                    return Err(ChunkExecutionError::Context(NativeError::Unsupported(
                        "complete fresh permission target",
                    )));
                }
            };
            total_sum = factory.perm_plus(
                total_sum,
                factory.ite(equal.clone(), available.clone(), factory.no_perm()),
            );
            total_taken = factory.perm_plus(total_taken, taken.clone());
            let constraint = factory.and([
                factory.is_valid_perm_val(taken.clone()),
                factory.perm_at_most(taken.clone(), available.clone()),
                factory.implies(
                    factory.not(equal.clone()),
                    factory.equals(taken.clone(), factory.no_perm()),
                ),
                factory.implies(
                    factory.and([equal, factory.is_positive_perm(available.clone())]),
                    factory.perm_less(taken.clone(), available.clone()),
                ),
            ]);
            self.assume_term(&constraint)
                .map_err(ChunkExecutionError::Context)?;
            recorder = recorder
                .record_path_symbol(target)
                .record_constraint(constraint);
            let remaining = factory.perm_minus(available, taken);
            updated.push(match chunk {
                C::Basic(c) => Chunk::Basic(c.with_permission(remaining, None)),
                C::Wand(c) => Chunk::MagicWand(c.with_permission(remaining, None)),
            });
        }
        let bounds = factory.implies(
            factory.not(factory.equals(total_sum.clone(), factory.no_perm())),
            factory.and([
                factory.perm_less(factory.no_perm(), total_taken.clone()),
                factory.perm_less(total_taken.clone(), total_sum),
            ]),
        );
        self.assume_term(&bounds)
            .map_err(ChunkExecutionError::Context)?;
        recorder = recorder.record_constraint(bounds);
        let goal = factory.implies(
            factory.perm_less(factory.no_perm(), permission.clone()),
            factory.not(factory.equals(total_taken.clone(), factory.no_perm())),
        );
        if !self
            .base
            .decider
            .check(&goal, self.base.decider.assert_timeout)
            .map_err(|e| ChunkExecutionError::Context(NativeError::Decider(e)))?
        {
            return self
                .consumption_failure(&state, error, "complete constrainable permission", true)
                .map_err(ChunkExecutionError::Context);
        }
        self.assume_term(&factory.equals(permission.clone(), total_taken))
            .map_err(ChunkExecutionError::Context)?;
        let mut state = state;
        state.function_recorder = recorder;
        let snapshot = if return_snapshot {
            let (next, snapshot, _) = self
                .complete_lookup_summary(state, resource, &chunks, args, None)
                .map_err(ChunkExecutionError::Context)?;
            state = next;
            Some(snapshot)
        } else {
            None
        };
        let heap = Arc::new(ListBackedHeap::from_chunks(
            updated.into_iter().chain(others),
        ));
        continuation(self, state, heap, snapshot)
    }
}

#[cfg(test)]
mod worker_analysis_contract_tests {
    #[test]
    fn member_scope_is_set_on_failure_and_history() {
        use crate::interfaces::verification::VerificationResult;
        use ferrum_silver::ast::{
            ast::Metadata,
            expression::{Exp, ExpKind},
            program::{Field, FieldData, Member},
            statement::{Stmt, StmtKind},
            r#type::Type,
        };
        use ferrum_silver::verifier::verification_error::{
            ErrorReason, VerificationError, VerificationErrorKind,
        };
        let meta = Metadata::default();
        let expression = Exp::new(ExpKind::FalseLit, meta.clone());
        let stmt = Stmt::new(StmtKind::Assert(expression.clone()), meta.clone());
        let first = VerificationResult::failure(
            VerificationError::new(
                VerificationErrorKind::AssertFailed(stmt.clone()),
                ErrorReason::AssertionFalse(expression.clone()),
            ),
            true,
        );
        let second = VerificationResult::failure(
            VerificationError::new(
                VerificationErrorKind::AssertFailed(stmt),
                ErrorReason::AssertionFalse(expression),
            ),
            true,
        );
        let joined = first.clone().combine(|| second.clone(), false);
        let member = Member::Field(Field::new(FieldData {
            name: "scope".into(),
            typ: Type::Int,
            meta,
        }));
        super::set_member_scope(&[joined], member.clone());
        for result in [first, second] {
            result.with_kind(|kind| match kind {
                crate::interfaces::verification::ResultKind::Failure(error) => {
                    assert_eq!(error.scope().as_deref(), Some(&member))
                }
                _ => panic!("expected failure"),
            });
        }
    }
    #[test]
    fn worker_analysis_is_send_and_sync() {
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<super::NativeWorkerAnalysis>();
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::supporters::cfg_supporter::CfgVerificationServices<PD, FD, JoinMode, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn empty_cfg_heap(
        &mut self,
        _: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        Ok(Arc::new(ListBackedHeap::new()))
    }
    fn output_cfg(&mut self, _: &SilverCfg) -> Result<(), Self::Error> {
        Ok(())
    }
    fn cfg_locally(
        &mut self,
        state: State<PD, FD, JoinMode>,
        action: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::supporters::cfg_supporter::CfgVerificationError<Self::Error>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::supporters::cfg_supporter::CfgVerificationError<Self::Error>,
    > {
        use crate::supporters::cfg_supporter::CfgVerificationError as CE;
        self.base
            .decider
            .push_scope()
            .map_err(|e| CE::Service(NativeError::Decider(e)))?;
        let result = action(self, state);
        let cleanup = self.base.decider.pop_scope();
        match (result, cleanup) {
            (Ok(value), Ok(())) => Ok(value),
            (Err(e), Ok(())) => Err(e),
            (Ok(_), Err(e)) => Err(CE::Service(NativeError::Decider(e))),
            (Err(e), Err(cleanup)) => Err(CE::Service(NativeError::Cleanup(format!(
                "{e:?}; cleanup: {cleanup:?}"
            )))),
        }
    }
    fn execute_cfg(
        &mut self,
        state: State<PD, FD, JoinMode>,
        cfg: &SilverCfg,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            crate::supporters::cfg_supporter::CfgVerificationError<Self::Error>,
        >,
    ) -> Result<
        VerificationResult<VerificationError>,
        crate::supporters::cfg_supporter::CfgVerificationError<Self::Error>,
    > {
        use crate::supporters::cfg_supporter::CfgVerificationError as CE;
        let mut callback_error = None;
        let result = crate::rules::executor::execute_cfg(self, state, cfg, &mut |ctx, state| {
            match continuation(ctx, state) {
                Ok(value) => Ok(value),
                Err(e) => {
                    callback_error = Some(e);
                    Err(ExecutionError::Context(NativeError::ContinuationAbort))
                }
            }
        });
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| CE::Service(NativeError::Execution(format!("CFG execution: {e:?}"))))
    }
}
