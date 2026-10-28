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
    pub conditionalize_permissions: bool,
    pub print_translated_program: bool,
    pub cfg_output_directory: Option<std::path::PathBuf>,
    pub mask_heap_mode: bool,
    pub simplify_on_consume: bool,
    pub set_axiomatization_file: Option<std::path::PathBuf>,
    pub multiset_axiomatization_file: Option<std::path::PathBuf>,
    pub sequence_axiomatization_file: Option<std::path::PathBuf>,
    pub map_axiomatization_file: Option<std::path::PathBuf>,
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
    pub disable_chunk_order_heuristics: bool,
    pub disable_value_map_caching: bool,
    pub disable_caches: bool,
    pub disable_isc_triggers: bool,
    pub include_methods: regex::Regex,
    pub exclude_methods: regex::Regex,
    pub counterexample: Option<crate::rules::symbolic_execution_rules::CounterexampleKind>,
    pub report_reason_unknown: bool,
    pub report_branch_conditions: bool,
    pub alternative_function_verification_order: bool,
    pub prover_randomize_seeds: bool,
    seed_commands: Arc<std::sync::Mutex<Option<(Vec<String>, Vec<String>)>>>,
}
impl NativeOptions {
    fn collection_axiomatization_sources(
        &self,
    ) -> crate::verifier::native_preamble::CollectionAxiomatizationSources {
        crate::verifier::native_preamble::CollectionAxiomatizationSources {
            sequences: self.sequence_axiomatization_file.clone(),
            sets: self.set_axiomatization_file.clone(),
            multisets: self.multiset_axiomatization_file.clone(),
            maps: self.map_axiomatization_file.clone(),
        }
    }
    /// Begin a fresh solver run after all contexts from the previous run have stopped.
    /// The coordinating owner calls this once before resetting shared worker contexts.
    pub fn reset_seed_epoch(&self) {
        *self.seed_commands.lock().unwrap_or_else(|e| e.into_inner()) = None;
    }
    /// Select only features for which the native execution and reporting context is connected.
    pub fn from_config(
        config: &crate::config::Config,
    ) -> Result<Self, NativeError<crate::decider::prover_std_io::ProverError>> {
        if config.enable_debugging
            || config.parallelize_branches
            || config.frontend.ide_mode_advanced
            || config.generate_block_messages
        {
            return Err(NativeError::Unsupported(
                "requested verifier configuration is not connected",
            ));
        }
        if config.report_state_after.is_some()
            || config.log_config.is_some()
            || config.log_level.is_some()
            || !config.logger.is_empty()
            || config.report_state_after.is_some()
        {
            return Err(NativeError::Unsupported(
                "requested timeout, logging, solver, worker, cache or encoding policy is not connected",
            ));
        }
        fn method_pattern(
            pattern: &str,
        ) -> Result<regex::Regex, NativeError<crate::decider::prover_std_io::ProverError>> {
            // Java's regex supports constructs with semantics absent in Rust's regex crate.
            // Admit a shared subset and fail explicitly for the remainder.
            let mut chars = pattern.chars();
            while let Some(ch) = chars.next() {
                if ch == '\\' {
                    if !matches!(chars.next(), Some('.' | '$')) {
                        return Err(NativeError::Unsupported("method filter regular expression"));
                    }
                } else if !(ch.is_ascii_alphanumeric() || matches!(ch, '_' | '.' | '*' | '?' | '|'))
                {
                    return Err(NativeError::Unsupported("method filter regular expression"));
                }
            }
            regex::Regex::new(&format!(r"\A(?:{pattern})\z"))
                .map_err(|error| NativeError::Diagnostic(format!("invalid method filter: {error}")))
        }
        let include_methods = method_pattern(&config.include_methods)?;
        let exclude_methods = method_pattern(&config.exclude_methods)?;
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
            conditionalize_permissions: config.conditionalize_permissions,
            print_translated_program: config.print_translated_program,
            cfg_output_directory: config
                .print_method_cf_gs
                .then(|| config.temp_directory.clone().into()),
            mask_heap_mode: config.mask_heap_mode,
            simplify_on_consume: config.simplify_on_consume,
            set_axiomatization_file: config.set_axiomatization_file.as_ref().map(Into::into),
            multiset_axiomatization_file: config
                .multiset_axiomatization_file
                .as_ref()
                .map(Into::into),
            sequence_axiomatization_file: config
                .sequence_axiomatization_file
                .as_ref()
                .map(Into::into),
            map_axiomatization_file: config.map_axiomatization_file.as_ref().map(Into::into),
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
            disable_chunk_order_heuristics: config.disable_chunk_order_heuristics,
            disable_value_map_caching: config.disable_value_map_caching,
            disable_caches: config.disable_caches,
            disable_isc_triggers: config.disable_isc_triggers,
            include_methods,
            exclude_methods,
            counterexample: config.frontend.counterexample.map(|value| {
                use crate::rules::symbolic_execution_rules::CounterexampleKind as K;
                use ferrum_silver::frontend::sil_front_end_config::CounterexampleModel as M;
                match value {
                    M::Native => K::Native,
                    M::Variables => K::Variables,
                    M::Mapped => K::Mapped,
                    M::Raw => K::Raw,
                    M::Resolved => K::Resolved,
                }
            }),
            report_reason_unknown: config.report_reason_unknown,
            report_branch_conditions: config.enable_branchcondition_reporting,
            alternative_function_verification_order: config.alternative_function_verification_order,
            prover_randomize_seeds: config.prover_randomize_seeds,
            seed_commands: Arc::new(std::sync::Mutex::new(None)),
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
    BranchWarnings {
        primary: Box<NativeError<E>>,
        warnings: Vec<String>,
    },
    Cancelled,
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
#[derive(Clone, Copy)]
enum LoggedScopeKind {
    Evaluate,
    Produce,
    Consume,
}
pub struct NativeVerifierContext<S: Prover, PD, FD> {
    pub base: BaseVerifier<S>,
    pub factory: TermFactory,
    pub options: NativeOptions,
    pub warnings: Vec<String>,
    /// Owner-local symbolic logger and record constructor. Both are inactive until
    /// the verification lifecycle explicitly installs a member log.
    pub(crate) logging_root: Option<Arc<crate::logger::symb_ex_logger::NativeSymbExLogger>>,
    pub(crate) member_log: Option<Arc<crate::logger::symb_ex_logger::MemberSymbExLog>>,
    pub(crate) record_factory: Option<
        std::rc::Rc<
            dyn crate::logger::records::data::data_record::NativeRecordFactory<PD, FD, JoinMode>,
        >,
    >,
    pub(crate) joined_branch_scheduler:
        Option<std::rc::Rc<dyn super::verification_pool_manager::NativeJoinScheduler<S, PD, FD>>>,
    pub(crate) joined_branch_scheduler_enabled: bool,
    /// Source-order quantifier trigger choices from preprocessing, for reporter delivery.
    pub quantifier_trigger_events: Vec<crate::utils::ast::QuantifierTriggerEvent>,
    preprocessing_reporter: Option<Arc<dyn ferrum_silver::reporter::reporter::Reporter>>,
    cancellation: Option<crate::verifier::verification_pool_manager::CancellationController>,
    havoc_counter: u64,
    config_options: Vec<String>,
    predicate_snapshots: crate::supporters::qps::predicate_snap_generator::PredicateSnapGenerator,
    mask_resources: crate::rules::mask_heap_supporter::ResourceSequenceCache,
    mask_frames: crate::supporters::functions::mask_heap_function_encoding::SharedFrameCache<FD>,
    mask_frames_in_progress: Vec<Arc<()>>,
    active_function_snapshot: Option<crate::supporters::functions::function_data::FunctionData<FD>>,
    mask_predicate_triggers: Vec<(Arc<()>, crate::state::package::OrderedMap<String, Term>)>,
    active_program: Option<ferrum_silver::ast::program::Program>,
    predicate_contents: crate::state::package::OrderedMap<
        String,
        Arc<crate::supporters::predicate_verification_unit::PredicateData>,
    >,
    function_handles: crate::state::package::OrderedMap<String, Arc<FD>>,
    function_owners: Vec<(
        String,
        Arc<std::sync::Mutex<crate::supporters::functions::function_data::FunctionData<FD>>>,
    )>,
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
            logging_root: None,
            member_log: None,
            record_factory: None,
            joined_branch_scheduler: None,
            joined_branch_scheduler_enabled: false,
            quantifier_trigger_events: Vec::new(),
            preprocessing_reporter: None,
            cancellation: None,
            havoc_counter: 0,
            config_options: Vec::new(),
            predicate_snapshots: Default::default(),
            mask_resources: Default::default(),
            mask_frames: Default::default(),
            mask_frames_in_progress: Vec::new(),
            active_function_snapshot: None,
            mask_predicate_triggers: Vec::new(),
            active_program: None,
            predicate_contents: Default::default(),
            function_handles: Default::default(),
            function_owners: Vec::new(),
            function_heights: Default::default(),
            function_fresh_variables: Vec::new(),
            function_units: Vec::new(),
            failed_functions: Default::default(),
            quantified_counter: 0,
            heap_supporter_counter: 0,
            _state_types: PhantomData,
        }
    }
    /// Install a member log and its full-state record constructor for this owner.
    /// Run/member lifecycle management is intentionally a separate integration step.
    pub fn set_member_logging(
        &mut self,
        member: Option<Arc<crate::logger::symb_ex_logger::MemberSymbExLog>>,
        factory: Option<
            std::rc::Rc<
                dyn crate::logger::records::data::data_record::NativeRecordFactory<PD, FD, JoinMode>,
            >,
        >,
    ) {
        self.member_log = member;
        self.record_factory = factory;
    }
    /// Install a run-owned root; callers must also supply its full-state factory.
    /// The public logging profiles stay gated until all event producers are wired.
    pub fn set_logging_root(
        &mut self,
        root: Option<Arc<crate::logger::symb_ex_logger::NativeSymbExLogger>>,
        factory: Option<
            std::rc::Rc<
                dyn crate::logger::records::data::data_record::NativeRecordFactory<PD, FD, JoinMode>,
            >,
        >,
    ) {
        self.logging_root = root;
        self.member_log = None;
        self.record_factory = factory;
    }
    fn open_member_log(
        &mut self,
        member: ferrum_silver::ast::program::Member,
    ) -> Result<(), NativeError<S::Error>> {
        let Some(root) = &self.logging_root else {
            return Ok(());
        };
        if matches!(
            root.as_ref(),
            crate::logger::symb_ex_logger::NativeSymbExLogger::Enabled(_)
        ) && self.record_factory.is_none()
        {
            return Err(NativeError::Unsupported(
                "active symbolic logger requires record factory",
            ));
        }
        let renderer = crate::logger::state_reporting::NativeStateRecordRenderer {
            factory: &self.factory,
        };
        self.member_log = Some(
            root.open_member_scope(member, &self.base.decider.pcs, &renderer)
                .map_err(|error| NativeError::Diagnostic(format!("symbolic logging: {error:?}")))?,
        );
        Ok(())
    }
    fn close_member_log(&self) -> Result<(), NativeError<S::Error>> {
        if let Some(log) = &self.member_log {
            log.close_member_scope()
                .map_err(|error| NativeError::Diagnostic(format!("symbolic logging: {error:?}")))?;
        }
        Ok(())
    }
    fn open_logged_scope(
        &self,
        state: &State<PD, FD, JoinMode>,
        expression: &Exp,
        kind: LoggedScopeKind,
    ) -> Result<Option<i32>, NativeError<S::Error>> {
        let Some(log) = &self.member_log else {
            return Ok(None);
        };
        if log.when_enabled(|| ()).is_none() {
            return Ok(None);
        }
        let factory = self
            .record_factory
            .as_ref()
            .ok_or(NativeError::Unsupported(
                "active symbolic logger requires record factory",
            ))?;
        let record = match kind {
            LoggedScopeKind::Evaluate => {
                factory.evaluate(expression, state, &self.base.decider.pcs)
            }
            LoggedScopeKind::Produce => factory.produce(expression, state, &self.base.decider.pcs),
            LoggedScopeKind::Consume => factory.consume(expression, state, &self.base.decider.pcs),
        };
        let renderer = crate::logger::state_reporting::NativeStateRecordRenderer {
            factory: &self.factory,
        };
        log.open_scope(record, &renderer)
            .map(Some)
            .map_err(|error| NativeError::Diagnostic(format!("symbolic logging: {error:?}")))
    }
    fn open_joining_scope(
        &self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Option<i32>, NativeError<S::Error>> {
        let Some(log) = &self.member_log else {
            return Ok(None);
        };
        if log.when_enabled(|| ()).is_none() {
            return Ok(None);
        }
        let factory = self
            .record_factory
            .as_ref()
            .ok_or(NativeError::Unsupported(
                "active symbolic logger requires record factory",
            ))?;
        let record = factory.joining(state, &self.base.decider.pcs);
        let renderer = crate::logger::state_reporting::NativeStateRecordRenderer {
            factory: &self.factory,
        };
        log.open_scope(record, &renderer)
            .map(Some)
            .map_err(|error| NativeError::Diagnostic(format!("symbolic logging: {error:?}")))
    }
    fn open_assertion_conditional_scope(
        &self,
        state: &State<PD, FD, JoinMode>,
        assertion: &Exp,
        environment: &str,
    ) -> Result<Option<i32>, NativeError<S::Error>> {
        let Some(log) = &self.member_log else {
            return Ok(None);
        };
        if log.when_enabled(|| ()).is_none() {
            return Ok(None);
        }
        let factory = self
            .record_factory
            .as_ref()
            .ok_or(NativeError::Unsupported(
                "active symbolic logger requires record factory",
            ))?;
        let record = match assertion.kind() {
            ExpKind::Implies(..) => {
                factory.implies(Some(assertion), state, &self.base.decider.pcs, environment)
            }
            ExpKind::CondExp(..) => factory.conditional_expression(
                assertion,
                state,
                &self.base.decider.pcs,
                environment,
            ),
            _ => return Err(NativeError::Unsupported("conditional symbolic record")),
        };
        let renderer = crate::logger::state_reporting::NativeStateRecordRenderer {
            factory: &self.factory,
        };
        log.open_scope(record, &renderer)
            .map(Some)
            .map_err(|error| NativeError::Diagnostic(format!("symbolic logging: {error:?}")))
    }
    fn close_logged_scope(&self, id: Option<i32>) -> Result<(), NativeError<S::Error>> {
        match (&self.member_log, id) {
            (None, None) => Ok(()),
            (Some(log), None) if log.when_enabled(|| ()).is_none() => Ok(()),
            (Some(log), Some(id)) => log
                .close_scope(id)
                .map_err(|error| NativeError::Diagnostic(format!("symbolic logging: {error:?}"))),
            _ => Err(NativeError::Unsupported(
                "symbolic logger changed during scope",
            )),
        }
    }
    /// Source heap-support strategy creates per-resource zero-mask heaps in mask mode.
    fn native_empty_heap(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
        may_define_new_vars: bool,
    ) -> Result<ListBackedHeap, NativeError<S::Error>>
    where
        S::Error: std::fmt::Debug,
    {
        if !self.options.mask_heap_mode {
            return Ok(ListBackedHeap::new());
        }
        let factory = self.factory.clone();
        let converter = self.base.symbol_converter.clone();
        crate::rules::mask_heap_supporter::empty_heap(
            program,
            &factory,
            &converter,
            may_define_new_vars,
            |name, sort| {
                self.base
                    .decider
                    .fresh_variable(&factory, name, &sort, false, None)
                    .map_err(NativeError::Decider)
            },
        )
        .map_err(|e| NativeError::Chunk(format!("empty mask heap: {e:?}")))
    }
    fn mask_resource_sequence(
        &mut self,
        assertions: &[Exp],
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<Vec<ResourceKey>, NativeError<S::Error>> {
        self.mask_resources
            .resources(assertions, program)
            .map_err(|e| NativeError::Snapshot(format!("mask resources: {e:?}")))
    }
    fn mask_term_alias(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        term: Term,
    ) -> Result<Term, NativeError<S::Error>> {
        self.base
            .decider
            .create_alias(&self.factory, &mut self.base.identifiers, &term, state)
            .map_err(NativeError::Decider)
    }
    fn merge_native_mask_heaps(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        first: &ListBackedHeap,
        second: &ListBackedHeap,
    ) -> Result<ListBackedHeap, NativeError<S::Error>>
    where
        S::Error: std::fmt::Debug,
    {
        let factory = self.factory.clone();
        let mut service = NativeMaskMerge {
            context: self,
            state,
        };
        crate::rules::mask_heap_supporter::merge_wand_heaps(
            &factory,
            first,
            second,
            state.may_assume_upper_bounds(),
            &mut service,
        )
        .map_err(|e| NativeError::Chunk(format!("mask heap merge: {e:?}")))
    }
    fn produce_native_mask_single(
        &mut self,
        mut state: State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        arguments: &[Term],
        snapshot: Term,
        permission: Term,
    ) -> Result<State<PD, FD, JoinMode>, NativeError<S::Error>>
    where
        S::Error: std::fmt::Debug,
    {
        let factory = self.factory.clone();
        let heap = state.h.clone();
        let mut service = NativeMaskProduction {
            context: self,
            state: &state,
            simplify_state: None,
        };
        let result = crate::rules::mask_heap_supporter::produce_single_location(
            &factory,
            &heap,
            resource,
            arguments,
            permission,
            snapshot,
            state.may_assume_upper_bounds(),
            &mut service,
        )
        .map_err(|e| NativeError::Chunk(format!("mask single production: {e:?}")))?;
        state.h = Arc::new(result);
        Ok(state)
    }
    fn consume_native_mask_single(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        heap: &ListBackedHeap,
        resource: &ResourceKey,
        arguments: &[Term],
        permission: Term,
        return_snapshot: bool,
    ) -> Result<crate::rules::mask_heap_supporter::MaskConsumption, NativeError<S::Error>>
    where
        S::Error: std::fmt::Debug,
    {
        if state.exhale_ext {
            return Err(NativeError::Unsupported(
                "mask single resource transfer inside wand package",
            ));
        }
        let factory = self.factory.clone();
        let exact = crate::state::terms::consume_exact_read(&permission, &state.constrainable_arps);
        let recording = !matches!(state.function_recorder, FunctionRecorder::Noop);
        let timeout = self.base.decider.check_timeout.unwrap_or(0);
        let simplify = self.options.simplify_on_consume;
        let mut service = NativeMaskProduction {
            context: self,
            state,
            simplify_state: None,
        };
        crate::rules::mask_heap_supporter::consume_single_location(
            &factory,
            heap,
            resource,
            arguments,
            permission,
            exact,
            state.assert_read_access_only,
            recording,
            state.may_assume_upper_bounds(),
            return_snapshot,
            simplify,
            timeout,
            &mut service,
        )
        .map_err(|e| NativeError::Chunk(format!("mask single consumption: {e:?}")))
    }
    fn consume_mask_transfer(
        &mut self,
        state: State<PD, FD, JoinMode>,
        resource: &ResourceKey,
        args: &[Term],
        permission: Term,
        return_snapshot: bool,
        error: VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<VerificationError>,
            NativeError<S::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>>
    where
        S::Error: std::fmt::Debug,
        FD: Clone,
    {
        use crate::rules::{
            consumption_result::ConsumptionResult, magic_wand_supporter::WandTransferError,
        };
        let failure = self.failure_full(error, &state, true)?;
        let original_state = state.clone();
        let factory = self.factory.clone();
        let mut callback_error = None;
        let result = crate::rules::magic_wand_supporter::transfer(
            &factory,
            self,
            state,
            permission,
            None,
            failure,
            &[],
            &mut |ctx, state, heap, needed, needed_exp| {
                if needed_exp.is_some() {
                    return Err(NativeError::Unsupported("mask wand transfer debugging"));
                }
                let exact =
                    crate::state::terms::consume_exact_read(&needed, &state.constrainable_arps);
                let simplify = ctx.options.simplify_on_consume;
                let timeout = ctx.options.qp_split_timeout;
                let mut service = NativeMaskProduction {
                    context: ctx,
                    state: &state,
                    simplify_state: Some(&original_state),
                };
                let step = crate::rules::mask_heap_supporter::transfer_single_location(
                    &factory,
                    &heap,
                    resource,
                    args,
                    needed,
                    exact,
                    state.assert_read_access_only,
                    simplify,
                    timeout,
                    &mut service,
                )
                .map_err(|e| NativeError::Chunk(format!("mask wand transfer: {e:?}")))?;
                let outcome = match step.remaining {
                    None => ConsumptionResult::Complete,
                    Some(perms_needed) => ConsumptionResult::Incomplete {
                        perms_needed,
                        perms_needed_exp: None,
                    },
                };
                Ok((outcome, state, Arc::new(step.heap), step.consumed))
            },
            &mut |ctx, state, chunks| {
                let snapshot = if return_snapshot {
                    let mut mask = None;
                    for chunk in chunks {
                        let Chunk::MaskHeap(chunk) = chunk else {
                            return Err(WandTransferError::Service(NativeError::Unsupported(
                                "non-mask transferred chunk",
                            )));
                        };
                        mask = Some(match mask {
                            None => chunk.mask,
                            Some(old) => factory.mask_sum(old, chunk.mask),
                        });
                    }
                    let mask = mask.unwrap_or_else(|| {
                        if matches!(resource, ResourceKey::Field(_)) {
                            factory.zero_mask()
                        } else {
                            factory.pred_zero_mask()
                        }
                    });
                    Some(factory.mask_map_term([(resource.clone(), mask)]))
                } else {
                    None
                };
                let heap = state.h.clone();
                match continuation(ctx, state, heap, snapshot) {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        callback_error = Some(e);
                        Err(WandTransferError::Service(NativeError::ContinuationAbort))
                    }
                }
            },
        );
        if let Some(error) = callback_error {
            return Err(error);
        }
        result.map_err(|e| NativeError::Chunk(format!("mask wand transfer: {e:?}")))
    }
    fn native_havoc_resource(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        condition: &Term,
        resource: &ResourceKey,
        info: &crate::rules::havoc_supporter::HavocHelperData,
    ) -> Result<ListBackedHeap, NativeError<S::Error>>
    where
        S::Error: std::fmt::Debug,
        FD: Clone,
    {
        if !self.options.mask_heap_mode {
            return crate::rules::heap_supporter::havoc_resource(
                self, state, condition, resource, info,
            )
            .map_err(|e| NativeError::Execution(format!("havoc resource: {e:?}")));
        }
        let factory = self.factory.clone();
        let mut service = NativeMaskProduction {
            context: self,
            state,
            simplify_state: None,
        };
        crate::rules::mask_heap_supporter::havoc_resource(
            &factory,
            &state.h,
            resource,
            condition.clone(),
            info,
            &mut service,
        )
        .map_err(|e| NativeError::Chunk(format!("mask havoc: {e:?}")))
    }
    /// Write the source CFG dump at the method/standalone verification hook.
    fn write_cfg_output(
        &self,
        filename: &str,
        cfg: &SilverCfg,
    ) -> Result<(), NativeError<S::Error>> {
        let Some(directory) = &self.options.cfg_output_directory else {
            return Ok(());
        };
        let dot = cfg
            .to_dot()
            .map_err(|error| NativeError::Diagnostic(format!("CFG rendering: {error:?}")))?;
        crate::common::io::package::to_file(&dot, directory.join(filename))
            .map_err(|error| NativeError::Diagnostic(format!("CFG output: {error}")))
    }
    /// Set the reporter used for source-ordered quantifier preprocessing events.
    pub fn set_preprocessing_reporter(
        &mut self,
        reporter: Option<Arc<dyn ferrum_silver::reporter::reporter::Reporter>>,
    ) {
        self.preprocessing_reporter = reporter;
    }
    /// Install the same latched cancellation controller used by the session and workers.
    pub fn set_cancellation(
        &mut self,
        cancellation: crate::verifier::verification_pool_manager::CancellationController,
    ) {
        self.cancellation = Some(cancellation);
    }
    /// Check without clearing the shared cancellation latch.
    pub fn checkpoint(&self) -> Result<(), NativeError<S::Error>> {
        if let Some(controller) = &self.cancellation {
            controller
                .checkpoint()
                .map_err(|_| NativeError::Cancelled)?;
        }
        Ok(())
    }
    /// Start the owned solver and install the source static settings and base preamble.
    /// Contributor-specific declarations and axioms must be installed separately after analysis.
    pub fn start(
        &mut self,
        user_args: Option<&str>,
        config_options: &[String],
    ) -> Result<(), NativeError<S::Error>> {
        self.checkpoint()?;
        self.base.start(user_args).map_err(NativeError::Decider)?;
        if let Err(cancelled) = self.checkpoint() {
            return match self.base.stop() {
                Ok(()) => Err(cancelled),
                Err(cleanup) => Err(NativeError::StartCleanup {
                    primary: Box::new(cancelled),
                    cleanup,
                }),
            };
        }
        self.config_options = config_options.to_vec();
        self.install_preamble()
    }
    /// Reinitialize the solver and reinstall all static options before another verification run.
    pub fn reset(&mut self) -> Result<(), NativeError<S::Error>> {
        self.checkpoint()?;
        self.base.reset().map_err(NativeError::Decider)?;
        self.checkpoint()?;
        self.quantifier_trigger_events.clear();
        self.predicate_snapshots = Default::default();
        self.mask_resources.reset();
        self.mask_frames = Default::default();
        self.mask_frames_in_progress.clear();
        self.active_function_snapshot = None;
        self.mask_predicate_triggers.clear();
        self.function_owners.clear();
        self.active_program = None;
        self.predicate_contents = Default::default();
        self.havoc_counter = 0;
        self.install_preamble()
    }
    fn install_preamble(&mut self) -> Result<(), NativeError<S::Error>> {
        use crate::interfaces::preamble::PreambleReader;
        let reader = crate::decider::smt_lib2_preamble_reader::SmtLib2PreambleReader::default();
        let resource = self.base.decider.prover.static_preamble().to_string();
        let result = (|| {
            self.checkpoint()?;
            let settings = reader
                .read_preamble(&resource)
                .map_err(NativeError::Resource)?;
            self.base
                .decider
                .prover
                .emit_settings(&settings)
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            self.checkpoint()?;
            if self.options.prover_randomize_seeds {
                use std::hash::{BuildHasher, Hasher};
                let keys = self.base.decider.prover.randomize_seeds_options().to_vec();
                let seeds = {
                    let mut shared = self
                        .options
                        .seed_commands
                        .lock()
                        .unwrap_or_else(|e| e.into_inner());
                    if let Some((existing_keys, commands)) = shared.as_ref() {
                        if existing_keys != &keys {
                            return Err(NativeError::Unsupported(
                                "different solver profiles in one seed epoch",
                            ));
                        }
                        commands.clone()
                    } else {
                        let commands = keys
                            .iter()
                            .map(|key| {
                                let mut random =
                                    std::collections::hash_map::RandomState::new().build_hasher();
                                random.write(key.as_bytes());
                                format!("(set-option :{key} {})", random.finish() % 10_000)
                            })
                            .collect::<Vec<_>>();
                        *shared = Some((keys, commands.clone()));
                        commands
                    }
                };
                self.base
                    .decider
                    .prover
                    .emit_settings(&seeds)
                    .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            }
            self.checkpoint()?;
            if !self.config_options.is_empty() {
                self.base
                    .decider
                    .prover
                    .emit_settings(&self.config_options)
                    .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
            }
            self.checkpoint()?;
            let commands = reader
                .read_preamble("/preamble.smt2")
                .map_err(NativeError::Resource)?;
            self.checkpoint()?;
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
        self.checkpoint()?;
        self.base
            .decider
            .assume([(term.clone(), None)], false, false)
            .map_err(NativeError::Decider)
    }
    fn store_counterexample_transformer(
        &self,
        store: &Arc<crate::state::store::MapBackedStore>,
    ) -> ferrum_silver::verifier::verification_error::CounterexampleTransformer {
        let store = store.clone();
        let converter = self.base.symbol_converter.clone();
        Arc::new(move |example| {
            use crate::reporting::silicon_resolved_counterexample::NativeCounterexample;
            let any = example.as_ref() as &dyn std::any::Any;
            if let Some(native) = any.downcast_ref::<NativeCounterexample>() {
                Ok(Arc::new(native.with_store(store.clone(), &converter)?))
            } else {
                Ok(example)
            }
        })
    }
    fn failure_full(
        &mut self,
        mut error: VerificationError,
        state: &State<PD, FD, JoinMode>,
        generate_new_model: bool,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        self.checkpoint()?;
        if state.retry_level == 0
            && !error
                .is_expected()
                .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?
        {
            self.base.errors_reported.fetch_add(1, Ordering::SeqCst);
        }
        let (unwrapped, example_transformer) = error.unwrap_example_transformer();
        error = unwrapped;
        let (counterexample, reason) =
            if self.options.counterexample.is_some() || self.options.report_reason_unknown {
                if generate_new_model || !self.base.decider.has_model() {
                    self.base
                        .decider
                        .generate_model(&self.factory)
                        .map_err(NativeError::Decider)?;
                }
                let counterexample = if let Some(kind) = self.options.counterexample
                    && self.base.decider.is_model_valid()
                {
                    let model = self
                        .base
                        .decider
                        .get_model()
                        .map_err(NativeError::Decider)?;
                    let value =
                        crate::reporting::silicon_resolved_counterexample::build_counterexample(
                            &model,
                            state,
                            kind,
                            &self.base.symbol_converter,
                        )
                        .map_err(NativeError::Diagnostic)?;
                    Some(Arc::new(value)
                        as Arc<
                            dyn ferrum_silver::verifier::verification_error::Counterexample,
                        >)
                } else {
                    None
                };
                let reason = if self.options.report_reason_unknown {
                    Some(
                        self.base
                            .decider
                            .prover
                            .get_reason_unknown()
                            .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?,
                    )
                } else {
                    None
                };
                (counterexample, reason)
            } else {
                (None, None)
            };
        let branches = if self.options.report_branch_conditions {
            self.base
                .decider
                .pcs
                .recorded()
                .branch_condition_exps()
                .into_iter()
                .map(|(expression, _)| expression)
                .filter(|expression| !matches!(expression.kind(), ExpKind::TrueLit))
                .collect()
        } else {
            Vec::new()
        };
        let context = crate::reporting::silicon_resolved_counterexample::SiliconFailureContext::from_transformed_with_reason(
            branches, counterexample, example_transformer.as_ref(), reason,
        ).map_err(NativeError::Diagnostic)?;
        error.failure_contexts = vec![Arc::new(context)];
        Ok(VerificationResult::failure(
            error,
            self.base.report_further_errors(self.options.error_limit),
        ))
    }
    fn failure(
        &mut self,
        partial: &PartialVerificationError,
        reason: ErrorReason,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<VerificationResult<VerificationError>, NativeError<S::Error>> {
        let error = partial
            .due_to(reason)
            .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?;
        self.failure_full(error, state, false)
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
        self.checkpoint()
    }
    fn close_evaluation(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn open_evaluation_scope(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        expression: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        self.checkpoint()?;
        self.open_logged_scope(state, expression, LoggedScopeKind::Evaluate)
    }
    fn close_evaluation_scope(&mut self, id: Option<i32>) -> Result<(), Self::Error> {
        self.close_logged_scope(id)
    }
    fn open_implies_scope(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        expression: Option<&Exp>,
        environment: &str,
    ) -> Result<Option<i32>, Self::Error> {
        let Some(log) = &self.member_log else {
            return Ok(None);
        };
        if log.when_enabled(|| ()).is_none() {
            return Ok(None);
        }
        let factory = self
            .record_factory
            .as_ref()
            .ok_or(NativeError::Unsupported(
                "active symbolic logger requires record factory",
            ))?;
        let record = factory.implies(expression, state, &self.base.decider.pcs, environment);
        let renderer = crate::logger::state_reporting::NativeStateRecordRenderer {
            factory: &self.factory,
        };
        log.open_scope(record, &renderer)
            .map(Some)
            .map_err(|error| NativeError::Diagnostic(format!("symbolic logging: {error:?}")))
    }
    fn open_conditional_scope(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        expression: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        let Some(log) = &self.member_log else {
            return Ok(None);
        };
        if log.when_enabled(|| ()).is_none() {
            return Ok(None);
        }
        let factory = self
            .record_factory
            .as_ref()
            .ok_or(NativeError::Unsupported(
                "active symbolic logger requires record factory",
            ))?;
        let record =
            factory.conditional_expression(expression, state, &self.base.decider.pcs, "CondExp");
        let renderer = crate::logger::state_reporting::NativeStateRecordRenderer {
            factory: &self.factory,
        };
        log.open_scope(record, &renderer)
            .map(Some)
            .map_err(|error| NativeError::Diagnostic(format!("symbolic logging: {error:?}")))
    }
    fn close_expression_scope(&mut self, id: Option<i32>) -> Result<(), Self::Error> {
        self.close_logged_scope(id)
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
            &state,
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
            &state,
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
            &state,
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
            &state,
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
        yes: crate::rules::evaluator::EvaluationBranchAction<Self::PartialError>,
        no: crate::rules::evaluator::EvaluationBranchAction<Self::PartialError>,
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
        let joining_scope = self
            .open_joining_scope(&state)
            .map_err(EvaluationError::Context)?;
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
            let run =
                |this: &mut Self,
                 active: bool,
                 positive: bool,
                 action: crate::rules::evaluator::EvaluationBranchAction<Self::PartialError>|
                 -> Result<
                    (
                        VerificationResult<VerificationError>,
                        Vec<JoinDataEntry<PD, FD, JoinMode, (Term, Option<Exp>)>>,
                    ),
                    EvaluationError<Self::Error>,
                > {
                    if !active {
                        return Ok((VerificationResult::unreachable(), Vec::new()));
                    }
                    let mut entries = Vec::new();
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
                        crate::rules::evaluator::execute_branch_action(
                            this,
                            branch_state,
                            action,
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
                        (Ok(result), Ok(())) => Ok((result, entries)),
                        (Err(e), Err(cleanup)) => Err(coalesce_evaluation_cleanup(e, cleanup)),
                        (Err(e), Ok(())) => Err(e),
                        (Ok(_), Err(cleanup)) => Err(EvaluationError::Context(cleanup)),
                    }
                };
            // The synchronous else future is lazy and is forced by combine after the then branch.
            let (then_result, mut entries) = run(self, decision.execute_then, true, yes)?;
            let branch_result = if then_result.continue_verification() {
                let (else_result, else_entries) = run(self, decision.execute_else, false, no)?;
                entries.extend(else_entries);
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
                return Err(coalesce_evaluation_cleanup(e, cleanup));
            }
            (Err(e), Ok(())) => return Err(e),
            (Ok(_), Err(cleanup)) => return Err(EvaluationError::Context(cleanup)),
        };
        let result = VerificationResult::success().and_then(|| result);
        if !result.continue_verification() {
            return Ok(result);
        }
        self.close_logged_scope(joining_scope)
            .map_err(EvaluationError::Context)?;
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
        if self.options.mask_heap_mode {
            let factory = self.factory.clone();
            let timeout = self.base.decider.assert_timeout;
            let result = crate::rules::mask_heap_supporter::read_field(
                &factory,
                &state.h,
                &resource,
                receiver.clone(),
                |goal| {
                    self.base
                        .decider
                        .assert_with(&goal, timeout, |v| v)
                        .map_err(NativeError::Decider)
                },
            )
            .map_err(|e| {
                EvaluationError::Context(NativeError::Chunk(format!("mask field read: {e:?}")))
            })?;
            return match result {
                crate::rules::mask_heap_supporter::MaskFieldRead::Value { value, snapshot } => {
                    let mut state = state;
                    state.function_recorder = state.function_recorder.record_location_snapshot(
                        field_exp,
                        self.base.decider.pcs.recorded().branch_conditions(),
                        snapshot,
                    );
                    continuation(self, state, value)
                }
                crate::rules::mask_heap_supporter::MaskFieldRead::Insufficient { .. } => self
                    .failure_full(full, &state, false)
                    .map_err(EvaluationError::Context),
            };
        }
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
        if self.options.mask_heap_mode {
            let amount = crate::rules::mask_heap_supporter::current_permission::<
                NativeError<S::Error>,
            >(&self.factory, &heap, resource, args)
            .map_err(|e| {
                EvaluationError::Context(NativeError::Chunk(format!(
                    "mask current permission: {e:?}"
                )))
            })?;
            return continuation(self, state, amount);
        }
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
            &state,
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
        let joining_scope = self
            .open_joining_scope(&state)
            .map_err(EvaluationError::Context)?;
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
                return Err(coalesce_evaluation_cleanup(e, cleanup));
            }
            (Ok(_), Err(cleanup)) => return Err(EvaluationError::Context(cleanup)),
        };
        let result = VerificationResult::success().and_then(|| result);
        if !result.continue_verification() {
            return Ok(result);
        }
        self.close_logged_scope(joining_scope)
            .map_err(EvaluationError::Context)?;
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
        caller_store: &Arc<crate::state::store::MapBackedStore>,
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
        let partial =
            partial.with_example_transformer(self.store_counterexample_transformer(caller_store));
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
        if self.options.mask_heap_mode {
            let resources = self.mask_resource_sequence(&function.pres, &state.program)?;
            return crate::rules::mask_heap_supporter::function_app_snapshot::<NativeError<S::Error>>(
                &self.factory, &state.h, &resources,
            )
            .map_err(|e| NativeError::Chunk(format!("function heap snapshot: {e:?}")));
        }
        let snapshot = self.factory.sort_wrapper(snapshot.clone(), Sort::Snap);
        Ok((vec![snapshot.clone()], snapshot))
    }
    fn heap_function(
        &mut self,
        function: &ferrum_silver::ast::program::Function,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<crate::state::terms::Applicable, Self::Error> {
        let resources = if self.options.mask_heap_mode {
            Some(self.mask_resource_sequence(&function.pres, program)?)
        } else {
            None
        };
        self.base
            .symbol_converter
            .heap_dependent_function(function, program, resources.as_deref())
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
        if self.options.mask_heap_mode {
            let condition = crate::rules::mask_heap_supporter::forperm_mask_condition::<
                NativeError<S::Error>,
            >(&factory, &state.h, resource, args)
            .map_err(|e| NativeError::Chunk(format!("forperm mask: {e:?}")))?;
            return Ok(condition
                .into_iter()
                .map(|(condition, trigger)| ForPermCondition {
                    condition,
                    original: name("chunk has non-zero permission"),
                    rewritten: None,
                    variables: variables.iter().map(|(term, _)| term.clone()).collect(),
                    definitions: MapBackedStore::new(),
                    triggers: vec![trigger],
                })
                .collect());
        }
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
                                    &state,
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
        if !self.options.mask_heap_mode {
            return Ok(snapshot);
        }
        let resources = self.mask_resource_sequence(assertions, &state.program)?;
        let term = self.snapshot_term(&snapshot, Sort::Snap)?;
        let factory = self.factory.clone();
        let converter = self.base.symbol_converter.clone();
        let supporter =
            crate::supporters::mask_heap_snapshot_supporter::MaskHeapSnapshotSupporter {
                factory: &factory,
            };
        let adapted = supporter
            .adapt_produce_snapshot(term, &resources, &converter, |term| {
                self.mask_term_alias(state, term)
            })
            .map_err(|e| NativeError::Snapshot(format!("mask producer snapshot: {e:?}")))?;
        Ok(NativeSnapshot::Projection(adapted))
    }
    fn split_snapshot(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        snapshot: &Self::Snapshot,
        first: &Exp,
        rest: &[Exp],
    ) -> Result<Option<(Self::Snapshot, Self::Snapshot)>, Self::Error> {
        if self.options.mask_heap_mode {
            return Ok(Some((snapshot.clone(), snapshot.clone())));
        }
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
        self.checkpoint()
    }
    fn close_produce(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn open_produce_scope(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        assertion: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        self.checkpoint()?;
        self.open_logged_scope(state, assertion, LoggedScopeKind::Produce)
    }
    fn close_produce_scope(&mut self, id: Option<i32>) -> Result<(), Self::Error> {
        self.close_logged_scope(id)
    }
    fn open_production_conditional_scope(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        assertion: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        self.open_assertion_conditional_scope(state, assertion, "produce")
    }
    fn close_production_conditional_scope(&mut self, id: Option<i32>) -> Result<(), Self::Error> {
        self.close_logged_scope(id)
    }

    fn assume_empty_snapshot(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        snapshot: &Self::Snapshot,
    ) -> Result<(), Self::Error> {
        if self.options.mask_heap_mode {
            return Ok(());
        }
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
        if self.options.mask_heap_mode {
            return match snapshot {
                NativeSnapshot::Projection(term) => Ok(term.clone()),
                NativeSnapshot::Fresh => Err(NativeError::Unsupported("unadapted mask snapshot")),
            };
        }
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
                &state,
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
        if self.options.mask_heap_mode {
            let state = self
                .produce_native_mask_single(state, resource, arguments, snapshot, gain)
                .map_err(ProductionError::Context)?;
            return continuation(self, state);
        }
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
        if self.options.mask_heap_mode {
            use crate::rules::mask_heap_supporter::{
                MaskQuantifiedInputs, MaskQuantifiedProduction,
            };
            let (_, _, access) = ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(forall)
                .ok_or(ProductionError::Context(NativeError::Unsupported("quantified permission shape")))?;
            let permission_exp = access.permission_or_full().ok_or(ProductionError::Context(
                NativeError::Unsupported("quantified permission expression"),
            ))?;
            let explicit =
                matches!(forall.kind(), ExpKind::Forall(_, triggers, _) if !triggers.is_empty());
            let snap = match snapshot {
                NativeSnapshot::Projection(value) => value.clone(),
                NativeSnapshot::Fresh => {
                    return Err(ProductionError::Context(NativeError::Unsupported(
                        "unadapted mask quantified snapshot",
                    )));
                }
            };
            let input = MaskQuantifiedInputs {
                resource: resource.clone(),
                qvars: data.qvars.clone(),
                qvar_expressions: data.qvar_expressions.clone(),
                formal_qvars: formals,
                formal_qvar_expressions: None,
                condition: data.condition.clone(),
                condition_expression: data.condition_exp.clone(),
                arguments: data.arguments.clone(),
                argument_expressions: data.argument_expressions.clone(),
                permission: data.permission.clone(),
                permission_expression: data.permission_exp.clone(),
                scaling: state.permission_scaling_factor.clone(),
                snapshot: Some(snap),
                explicit_triggers: explicit.then(|| data.triggers.clone()),
                translated_triggers: data.triggers.clone(),
                auxiliary_globals: data.auxiliary_globals.clone(),
                auxiliary_non_globals: data.auxiliary_non_globals.clone(),
                auxiliary_debug: data.auxiliary_debug.clone(),
                qid: qid.into(),
                quantifier: forall.clone(),
            };
            let factory = self.factory.clone();
            let heap = state.h.clone();
            let mut adapter = NativeMaskQuantified {
                context: self,
                state: &state,
                recorder: state.function_recorder.clone(),
            };
            let outcome = crate::rules::mask_heap_supporter::produce_quantified(
                &factory,
                &heap,
                &input,
                state.may_assume_upper_bounds(),
                adapter.context.options.assume_injectivity_on_inhale,
                &mut adapter,
            )
            .map_err(|e| {
                ProductionError::Context(NativeError::Chunk(format!(
                    "mask quantified production: {e:?}"
                )))
            })?;
            let recorder = adapter.recorder;
            return match outcome {
                MaskQuantifiedProduction::Complete { heap } => {
                    let mut state = state;
                    state.h = Arc::new(heap);
                    state.function_recorder = recorder;
                    continuation(self, state)
                }
                MaskQuantifiedProduction::NegativePermission { .. } => self
                    .failure(
                        error,
                        ErrorReason::NegativePermission(permission_exp),
                        &state,
                    )
                    .map_err(ProductionError::Context),
                MaskQuantifiedProduction::NonInjective { .. } => {
                    use ferrum_silver::ast::utility::nodes::Node;
                    let node = match access.kind() {
                        ExpKind::FieldAccessPredicate(location, _) => {
                            Node::FieldAccess(location.clone())
                        }
                        ExpKind::PredicateAccessPredicate(location) => {
                            Node::PredicateAccess(location.location.clone())
                        }
                        ExpKind::MagicWand(..) => Node::Exp(access.clone()),
                        _ => {
                            return Err(ProductionError::Context(NativeError::Unsupported(
                                "quantified injectivity error location",
                            )));
                        }
                    };
                    self.failure(error, ErrorReason::QPAssertionNotInjective(node), &state)
                        .map_err(ProductionError::Context)
                }
            };
        }
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
        let resources = if self.options.mask_heap_mode {
            Some(self.mask_resource_sequence(&function.pres, program)?)
        } else { None };
        self.base.symbol_converter.heap_dependent_function(function, program, resources.as_deref()).map_err(NativeError::Sort)
    }

    fn translate_heap_function_application(&mut self, function: crate::state::terms::Applicable, snapshot: Term, args: Vec<Term>, source_function: &ferrum_silver::ast::program::Function, program: &ferrum_silver::ast::program::Program) -> Result<Term, Self::Error> {
        if self.options.mask_heap_mode {
            let resources = self.mask_resource_sequence(&source_function.pres, program)?;
            return crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::translate_application(
                &self.factory, &self.base.symbol_converter, &function, &snapshot, &args, &resources,
            ).map_err(|e| NativeError::Execution(format!("mask function application: {e:?}")));
        }
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
    fn cancellation_checkpoint(&self) -> Result<(), Self::Error> {
        self.checkpoint()
    }
    fn unit_snapshot(&self) -> Term {
        if self.options.mask_heap_mode {
            self.factory.mask_map_term([])
        } else {
            self.factory.unit()
        }
    }
    fn combine_snapshots(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        first: Term,
        second: Term,
        assertion: &Exp,
        rest: &[Exp],
    ) -> Result<Term, Self::Error> {
        if !self.options.mask_heap_mode {
            return Ok(self.factory.combine(first, second));
        }
        let first_resources =
            self.mask_resource_sequence(std::slice::from_ref(assertion), &state.program)?;
        let rest_resources = self.mask_resource_sequence(rest, &state.program)?;
        let factory = self.factory.clone();
        let supporter =
            crate::supporters::mask_heap_snapshot_supporter::MaskHeapSnapshotSupporter {
                factory: &factory,
            };
        supporter.combine_snapshots(
            &first,
            &second,
            |term| {
                Ok::<_, NativeError<S::Error>>(
                    crate::rules::mask_heap_supporter::masks_from_snapshot(
                        &factory,
                        term.clone(),
                        &first_resources,
                    ),
                )
            },
            |term| {
                Ok::<_, NativeError<S::Error>>(
                    crate::rules::mask_heap_supporter::masks_from_snapshot(
                        &factory,
                        term.clone(),
                        &rest_resources,
                    ),
                )
            },
        )
    }
    fn finalize_snapshot(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        original_heap: &Arc<ListBackedHeap>,
        snapshot: Term,
        assertions: &[Exp],
    ) -> Result<Term, Self::Error> {
        if !self.options.mask_heap_mode {
            return Ok(snapshot);
        }
        let resources = self.mask_resource_sequence(assertions, &state.program)?;
        let mut eval_state = state.clone();
        if !state.exhale_ext {
            eval_state.h = original_heap.clone();
        }
        let heap = crate::rules::magic_wand_supporter::evaluation_heap(self, &eval_state)
            .map_err(|e| NativeError::Snapshot(format!("mask evaluation heap: {e:?}")))?;
        let factory = self.factory.clone();
        let supporter =
            crate::supporters::mask_heap_snapshot_supporter::MaskHeapSnapshotSupporter {
                factory: &factory,
            };
        supporter
            .finalize_consumed_snapshot(&snapshot, &resources, &heap, |term| {
                self.mask_term_alias(state, term)
            })
            .map_err(|e| NativeError::Snapshot(format!("mask consumption snapshot: {e:?}")))
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
                crate::rules::consumer::consume_one_logged(
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
    fn open_consumption_scope(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        assertion: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        self.open_logged_scope(state, assertion, LoggedScopeKind::Consume)
    }
    fn close_consumption_scope(&mut self, id: Option<i32>) -> Result<(), Self::Error> {
        self.close_logged_scope(id)
    }
    fn open_consumption_conditional_scope(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        assertion: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        self.open_assertion_conditional_scope(state, assertion, "consume")
    }
    fn close_consumption_conditional_scope(&mut self, id: Option<i32>) -> Result<(), Self::Error> {
        self.close_logged_scope(id)
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
                &state,
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
        if self.options.mask_heap_mode {
            use crate::rules::mask_heap_supporter::MaskConsumption;
            if state.exhale_ext {
                let mut callback_error = None;
                let result = self.consume_mask_transfer(
                    state,
                    resource,
                    args,
                    loss,
                    return_snapshot,
                    full,
                    &mut |ctx, state, heap, snapshot| match continuation(ctx, state, heap, snapshot)
                    {
                        Ok(v) => Ok(v),
                        Err(e) => {
                            callback_error = Some(e);
                            Err(NativeError::ContinuationAbort)
                        }
                    },
                );
                if let Some(e) = callback_error {
                    return Err(e);
                }
                return result.map_err(ConsumptionError::Context);
            }
            return match self
                .consume_native_mask_single(&state, &heap, resource, args, loss, return_snapshot)
                .map_err(ConsumptionError::Context)?
            {
                MaskConsumption::Complete { heap, snapshot } => {
                    continuation(self, state, Arc::new(heap), snapshot)
                }
                MaskConsumption::Insufficient { .. } => self
                    .failure_full(full, &state, false)
                    .map_err(ConsumptionError::Context),
            };
        }
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
        self.failure(error, ErrorReason::AssertionFalse(original.clone()), &state)
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
        if self.options.mask_heap_mode {
            use crate::rules::mask_heap_supporter::{
                MaskQuantifiedConsumption, MaskQuantifiedInputs,
            };
            let input = MaskQuantifiedInputs {
                resource: resource.clone(),
                qvars: data.qvars.clone(),
                qvar_expressions: data.qvar_expressions.clone(),
                formal_qvars: formals,
                formal_qvar_expressions: None,
                condition: data.condition.clone(),
                condition_expression: data.condition_exp.clone(),
                arguments: data.arguments.clone(),
                argument_expressions: data.argument_expressions.clone(),
                permission: data.permission.clone(),
                permission_expression: data.permission_exp.clone(),
                scaling: state.permission_scaling_factor.clone(),
                snapshot: None,
                explicit_triggers: has_explicit_triggers.then(|| data.triggers.clone()),
                translated_triggers: data.triggers.clone(),
                auxiliary_globals: data.auxiliary_globals.clone(),
                auxiliary_non_globals: data.auxiliary_non_globals.clone(),
                auxiliary_debug: data.auxiliary_debug.clone(),
                qid: qid.into(),
                quantifier: forall.clone(),
            };
            let factory = self.factory.clone();
            let converter = self.base.symbol_converter.clone();
            let loss = factory.perm_times(input.permission.clone(), input.scaling.clone());
            let constrain =
                !crate::state::terms::consume_exact_read(&loss, &state.constrainable_arps);
            let recording = !matches!(state.function_recorder, FunctionRecorder::Noop);
            let simplify = self.options.simplify_on_consume;
            if state.exhale_ext {
                use crate::rules::consumption_result::ConsumptionResult;
                use crate::rules::magic_wand_supporter::WandTransferError;
                use crate::rules::mask_heap_supporter::MaskQuantifiedPreparation;
                let mut adapter = NativeMaskQuantified {
                    context: self,
                    state: &state,
                    recorder: state.function_recorder.clone(),
                };
                let prepared = crate::rules::mask_heap_supporter::prepare_quantified_consumption(
                    &factory,
                    &input,
                    &mut adapter,
                )
                .map_err(|e| {
                    ConsumptionError::Context(NativeError::Chunk(format!(
                        "mask quantified preparation: {e:?}"
                    )))
                })?;
                let prepared = match prepared {
                    MaskQuantifiedPreparation::Ready(value) => value,
                    MaskQuantifiedPreparation::NegativePermission { .. } => {
                        return self
                            .failure(
                                error,
                                ErrorReason::NegativePermission(failure.permission.clone()),
                                &state,
                            )
                            .map_err(ConsumptionError::Context);
                    }
                    MaskQuantifiedPreparation::NonInjective { .. } => {
                        use ferrum_silver::ast::utility::nodes::Node;
                        let node = match failure.access.kind() {
                            ExpKind::FieldAccessPredicate(location, _) => {
                                Node::FieldAccess(location.clone())
                            }
                            ExpKind::PredicateAccessPredicate(location) => {
                                Node::PredicateAccess(location.location.clone())
                            }
                            ExpKind::MagicWand(..) => Node::Exp(failure.access.clone()),
                            _ => {
                                return Err(ConsumptionError::Context(NativeError::Unsupported(
                                    "quantified injectivity error location",
                                )));
                            }
                        };
                        return self
                            .failure(error, ErrorReason::QPAssertionNotInjective(node), &state)
                            .map_err(ConsumptionError::Context);
                    }
                };
                let reason = match failure.access.kind() {
                    ExpKind::FieldAccessPredicate(location, _) => {
                        ErrorReason::InsufficientPermission(
                            ferrum_silver::ast::utility::nodes::Node::FieldAccess(location.clone()),
                        )
                    }
                    ExpKind::PredicateAccessPredicate(location) => {
                        ErrorReason::InsufficientPermission(
                            ferrum_silver::ast::utility::nodes::Node::PredicateAccess(
                                location.location.clone(),
                            ),
                        )
                    }
                    ExpKind::MagicWand(..) => {
                        ErrorReason::MagicWandChunkNotFound(failure.access.clone())
                    }
                    _ => {
                        return Err(ConsumptionError::Context(NativeError::Unsupported(
                            "quantified permission failure reason",
                        )));
                    }
                };
                let full = error.due_to(reason).map_err(|e| {
                    ConsumptionError::Context(NativeError::Diagnostic(format!("{e:?}")))
                })?;
                let failure_result = self
                    .failure_full(full, &state, true)
                    .map_err(ConsumptionError::Context)?;
                let original_recorder = state.function_recorder.clone();
                let mut callback_error = None;
                let result = crate::rules::magic_wand_supporter::transfer(
                    &factory,
                    self,
                    state,
                    prepared.loss_at.clone(),
                    None,
                    failure_result,
                    &input.formal_qvars,
                    &mut |ctx, mut state, heap, remaining, debug| {
                        if debug.is_some() {
                            return Err(NativeError::Unsupported(
                                "mask quantified wand transfer debugging",
                            ));
                        }
                        let mut service = NativeMaskQuantified {
                            context: ctx,
                            state: &state,
                            recorder: original_recorder.clone(),
                        };
                        let step = crate::rules::mask_heap_supporter::transfer_quantified_step(
                            &factory,
                            &heap,
                            resource,
                            &input.formal_qvars,
                            prepared.condition_at.clone(),
                            remaining,
                            constrain,
                            &prepared.inverse,
                            &mut service,
                        )
                        .map_err(|e| {
                            NativeError::Chunk(format!("mask quantified wand transfer: {e:?}"))
                        })?;
                        if step.consumed.is_some() {
                            state.function_recorder = service.recorder;
                        }
                        let outcome = match step.remaining {
                            None => ConsumptionResult::Complete,
                            Some(perms_needed) => ConsumptionResult::Incomplete {
                                perms_needed,
                                perms_needed_exp: None,
                            },
                        };
                        Ok((outcome, state, Arc::new(step.heap), step.consumed))
                    },
                    &mut |ctx, state, chunks| {
                        let snapshot = if return_snapshot {
                            let mut mask = None;
                            for chunk in chunks {
                                let Chunk::MaskHeap(chunk) = chunk else {
                                    return Err(WandTransferError::Service(
                                        NativeError::Unsupported("non-mask transferred chunk"),
                                    ));
                                };
                                mask = Some(match mask {
                                    None => chunk.mask,
                                    Some(old) => factory.mask_sum(old, chunk.mask),
                                });
                            }
                            let mask = mask.unwrap_or_else(|| {
                                if matches!(resource, ResourceKey::Field(_)) {
                                    factory.zero_mask()
                                } else {
                                    factory.pred_zero_mask()
                                }
                            });
                            Some(factory.mask_map_term([(resource.clone(), mask)]))
                        } else {
                            None
                        };
                        let heap = state.h.clone();
                        match continuation(ctx, state, heap, snapshot) {
                            Ok(value) => Ok(value),
                            Err(e) => {
                                callback_error = Some(e);
                                Err(WandTransferError::Service(NativeError::ContinuationAbort))
                            }
                        }
                    },
                );
                if let Some(e) = callback_error {
                    return Err(e);
                }
                return result.map_err(|e| {
                    ConsumptionError::Context(NativeError::Chunk(format!(
                        "mask quantified wand transfer: {e:?}"
                    )))
                });
            }
            let mut adapter = NativeMaskQuantified {
                context: self,
                state: &state,
                recorder: state.function_recorder.clone(),
            };
            let outcome = crate::rules::mask_heap_supporter::consume_quantified(
                &factory,
                &heap,
                &input,
                &state.program,
                &converter,
                constrain,
                state.assert_read_access_only,
                recording,
                state.may_assume_upper_bounds(),
                return_snapshot,
                simplify,
                &mut adapter,
            )
            .map_err(|e| {
                ConsumptionError::Context(NativeError::Chunk(format!(
                    "mask quantified consumption: {e:?}"
                )))
            })?;
            let recorder = adapter.recorder;
            return match outcome {
                MaskQuantifiedConsumption::Complete { heap, snapshot } => {
                    let mut state = state;
                    state.function_recorder = recorder;
                    let heap = Arc::new(heap);
                    state.partially_consumed_heap = Some(heap.clone());
                    continuation(self, state, heap, snapshot)
                }
                MaskQuantifiedConsumption::NegativePermission { .. } => self
                    .failure(
                        error,
                        ErrorReason::NegativePermission(failure.permission),
                        &state,
                    )
                    .map_err(ConsumptionError::Context),
                MaskQuantifiedConsumption::NonInjective { .. } => {
                    use ferrum_silver::ast::utility::nodes::Node;
                    let node = match failure.access.kind() {
                        ExpKind::FieldAccessPredicate(location, _) => {
                            Node::FieldAccess(location.clone())
                        }
                        ExpKind::PredicateAccessPredicate(location) => {
                            Node::PredicateAccess(location.location.clone())
                        }
                        ExpKind::MagicWand(..) => Node::Exp(failure.access.clone()),
                        _ => {
                            return Err(ConsumptionError::Context(NativeError::Unsupported(
                                "quantified injectivity error location",
                            )));
                        }
                    };
                    self.failure(error, ErrorReason::QPAssertionNotInjective(node), &state)
                        .map_err(ConsumptionError::Context)
                }
                MaskQuantifiedConsumption::Insufficient { .. } => crate::rules::quantified_chunk_support::GeneralConsumptionExecution::general_insufficient_permission(self, &state, &failure)
                    .map_err(ConsumptionError::Context),
            };
        }

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
struct NativeFrameTranslator<'a, S: Prover, PD, FD> {
    context: &'a mut NativeVerifierContext<S, PD, FD>,
    data: &'a crate::supporters::functions::function_data::FunctionData<FD>,
    resources: &'a [ResourceKey],
}

impl<S: Prover, PD, FD: Clone>
    crate::supporters::functions::mask_heap_function_encoding::FrameExpressionTranslator
    for NativeFrameTranslator<'_, S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;

    fn translate_frame_expression(&mut self, expression: &Exp) -> Result<Term, Self::Error> {
        use crate::supporters::{
            expression_translator::ExpressionTranslator,
            functions::{
                heap_access_replacing_expression_translator::HeapAccessReplacingTranslator,
                mask_heap_function_encoding::MaskHeapFunctionEncoding,
            },
        };
        let factory = self.context.factory.clone();
        let converter = self.context.base.symbol_converter.clone();
        let translator = ExpressionTranslator::new(&factory, &converter, |sort: &Sort| {
            Ok::<_, NativeError<S::Error>>(sort.to_string())
        });
        let prior = self
            .context
            .failed_functions
            .contains(&self.data.program_function.name);
        let mut replacing = HeapAccessReplacingTranslator {
            program: &self.data.program,
            data: self.data,
            services: self.context,
            failed: false,
            prior_verification_failures: prior,
            ignore_access_predicates: false,
            context: vec![],
            check_inner_contexts: false,
        };
        let translated = replacing
            .translate_postconditions(&translator, std::slice::from_ref(expression))
            .map_err(|e| NativeError::Execution(format!("frame expression: {e:?}")))?;
        let term = translated
            .into_iter()
            .next()
            .ok_or(NativeError::Unsupported("empty frame translation"))?;
        MaskHeapFunctionEncoding::adapt_axiom(
            &factory,
            &converter,
            &term,
            self.resources,
            &self.data.state_args,
        )
        .map_err(|e| NativeError::Execution(format!("frame adaptation: {e:?}")))
    }
}

impl<S: Prover, PD, FD: Clone> NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn mask_function_frame(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<
        crate::supporters::functions::mask_heap_function_encoding::FrameInfo,
        NativeError<S::Error>,
    > {
        let identity = data.identity();
        if let Some(frame) = self.mask_frames.get(&identity) {
            return Ok(frame);
        }
        if self
            .mask_frames_in_progress
            .iter()
            .any(|key| Arc::ptr_eq(key, &identity))
        {
            return Err(NativeError::Unsupported(
                "recursive mask frame construction",
            ));
        }
        let resources = self.mask_resource_sequence(&data.program_function.pres, &data.program)?;
        let factory = self.factory.clone();
        self.mask_frames_in_progress.push(identity.clone());
        let result = {
            let mut translator = NativeFrameTranslator {
                context: self,
                data,
                resources: &resources,
            };
            crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::compute_frame(
                &factory, &mut translator, data, &resources,
            )
                .map_err(|e| NativeError::Execution(format!("mask function frame: {e:?}")))
        };
        self.mask_frames_in_progress.pop();
        if let Ok(frame) = &result {
            self.mask_frames.insert(identity, frame.clone());
        }
        result
    }

    fn mask_recursive_predicate_triggers(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<crate::state::package::OrderedMap<String, Term>, NativeError<S::Error>> {
        use crate::supporters::{
            expression_translator::ExpressionTranslator,
            functions::{
                heap_access_replacing_expression_translator::HeapAccessReplacingTranslator,
                mask_heap_function_encoding::MaskHeapFunctionEncoding,
            },
        };
        let identity = data.identity();
        if let Some((_, triggers)) = self
            .mask_predicate_triggers
            .iter()
            .find(|(key, _)| Arc::ptr_eq(key, &identity))
        {
            return Ok(triggers.clone());
        }
        let calls =
            ferrum_silver::ast::utility::functions::recursive_calls_and_surrounding_unfoldings(
                &data.program_function,
            )
            .map_err(|e| NativeError::Execution(format!("recursive function analysis: {e:?}")))?;
        let resources = self.mask_resource_sequence(&data.program_function.pres, &data.program)?;
        let factory = self.factory.clone();
        let converter = self.base.symbol_converter.clone();
        let translator = ExpressionTranslator::new(&factory, &converter, |sort: &Sort| {
            Ok::<_, NativeError<S::Error>>(sort.to_string())
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
        let mut triggers = crate::state::package::OrderedMap::default();
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
                        NativeError::Diagnostic(format!("recursive trigger free variables: {e:?}"))
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
                    Sort::PredHeap,
                )
                .map_err(NativeError::Sort)?;
            let heap = MaskHeapFunctionEncoding::predicate_trigger_state_arg(
                predicate,
                &resources,
                &data.state_args,
            )
            .map_err(|e| NativeError::Execution(format!("recursive predicate heap: {e:?}")))?;
            let args = replacing
                .translate_preconditions(&translator, &location.args)
                .map_err(|e| {
                    NativeError::Execution(format!("recursive predicate arguments: {e:?}"))
                })?;
            triggers.insert(
                predicate.name.clone(),
                factory.app(
                    predicate_data.trigger_function,
                    std::iter::once(heap).chain(args).collect(),
                ),
            );
        }
        self.mask_predicate_triggers
            .push((identity, triggers.clone()));
        Ok(triggers)
    }

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
        self.merge_native_mask_heaps(state, first, second)
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
            let cached = (!self.options.disable_caches)
                .then(|| state.ss_cache.get(&key))
                .flatten();
            let sum = if let Some(summary) = cached {
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
            .failure_full(full, &state, false)
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
        self.failure_full(error, state, generate_model)
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
        let cache_options = self.options.clone();
        let (state, snapshot, permission) =
            crate::rules::quantified_chunk_support::heap_summarising_maps(
                &factory,
                self,
                state,
                resource,
                source,
                &formals,
                &chunks,
                None,
                None,
                trigger,
                cache_options.disable_isc_triggers,
                cache_options.disable_value_map_caching,
                cache_options.disable_caches,
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
        let cached = (!self.options.disable_value_map_caching)
            .then(|| state.sm_cache.get(&key, None))
            .flatten()
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
            let cache_options = self.options.clone();
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
                    cache_options.disable_isc_triggers,
                    cache_options.disable_value_map_caching,
                    cache_options.disable_caches,
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
                .failure_full(failure, &state, false)
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
            let candidates = if ctx.options.disable_chunk_order_heuristics {
                relevant.clone()
            } else {
                let hints = qp::extract_hints(&factory, None, std::slice::from_ref(receiver))
                    .map_err(|e| {
                        ChunkExecutionError::Context(NativeError::Chunk(format!(
                            "field assignment hints: {e:?}"
                        )))
                    })?;
                qp::single_receiver_chunk_order(
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
                })?
            };
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
            let disable_isc_triggers = ctx.options.disable_isc_triggers;
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
                disable_isc_triggers,
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
                    .failure_full(failure, &state, false)
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
        self.checkpoint()
    }
    fn close_statement(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn open_statement_scope(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        statement: &Stmt,
    ) -> Result<Option<i32>, Self::Error> {
        self.checkpoint()?;
        let Some(log) = &self.member_log else {
            return Ok(None);
        };
        if log.when_enabled(|| ()).is_none() {
            return Ok(None);
        }
        let factory = self
            .record_factory
            .as_ref()
            .ok_or(NativeError::Unsupported(
                "active symbolic logger requires record factory",
            ))?;
        let record = factory.execute(statement, state, &self.base.decider.pcs);
        let renderer = crate::logger::state_reporting::NativeStateRecordRenderer {
            factory: &self.factory,
        };
        log.open_scope(record, &renderer)
            .map(Some)
            .map_err(|error| NativeError::Diagnostic(format!("symbolic logging: {error:?}")))
    }
    fn close_statement_scope(&mut self, id: Option<i32>) -> Result<(), Self::Error> {
        self.close_logged_scope(id)
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
        if self.options.mask_heap_mode {
            let factory = self.factory.clone();
            let resource = ResourceKey::Field(Arc::new(field.field.clone()));
            let timeout = self.base.decider.assert_timeout;
            let result = crate::rules::mask_heap_supporter::write_field(
                &factory,
                &state.h,
                &resource,
                receiver.clone(),
                snapshot.clone(),
                |goal| {
                    self.base
                        .decider
                        .assert_with(&goal, timeout, |v| v)
                        .map_err(NativeError::Decider)
                },
            )
            .map_err(|e| {
                ExecutionError::Context(NativeError::Chunk(format!("mask field write: {e:?}")))
            })?;
            return match result {
                crate::rules::mask_heap_supporter::MaskFieldWrite::Updated(heap) => {
                    let mut state = state;
                    state.h = Arc::new(heap);
                    continuation(self, state)
                }
                crate::rules::mask_heap_supporter::MaskFieldWrite::Insufficient { .. } => self
                    .failure_full(error, &state, false)
                    .map_err(ExecutionError::Context),
            };
        }
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
        if self.options.mask_heap_mode {
            let state = self
                .produce_native_mask_single(
                    state,
                    &resource,
                    std::slice::from_ref(receiver),
                    snapshot,
                    self.factory.full_perm(),
                )
                .map_err(ExecutionError::Context)?;
            return continuation(self, state);
        }
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
        if self.options.mask_heap_mode {
            return Ok(());
        }
        use crate::state::heap::Heap;
        let used = state.reserve_heaps.first().ok_or_else(|| {
            NativeError::Execution("wand assertion is missing its used reserve heap".into())
        })?;
        if !state.h.values().is_empty() || !used.values().is_empty() {
            return Err(NativeError::Execution(
                "wand assertion requires empty execution and used reserve heaps".into(),
            ));
        }
        Ok(())
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
                        &state,
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
        caller_store: &Arc<crate::state::store::MapBackedStore>,
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
        let partial =
            partial.with_example_transformer(self.store_counterexample_transformer(caller_store));
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
                                &state,
                            )
                            .map_err(EvaluationError::Context);
                    }
                    let disable_isc_triggers = ctx.options.disable_isc_triggers;
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
                        disable_isc_triggers,
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
                    let heap = ctx
                        .native_havoc_resource(&state, &condition, &key, &helper)
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
                            let heap = ctx
                                .native_havoc_resource(
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
                    let operations = if ctx.options.mask_heap_mode {
                        Arc::new(
                            crate::rules::mask_heap_supporter::add_wand_chunk::<
                                NativeError<S::Error>,
                            >(&factory, &state.reserve_heaps[0], &chunk)
                            .map_err(|e| {
                                PE::Service(NativeError::Chunk(format!("mask add wand: {e:?}")))
                            })?,
                        )
                    } else {
                        Arc::new(state.reserve_heaps[0].with_chunk(chunk))
                    };
                    if original.exhale_ext {
                        if original.reserve_heaps.is_empty() {
                            return Err(PE::MissingReserveHeap);
                        }
                        let mut reserve = vec![original.reserve_heaps[0].clone(), operations];
                        reserve.extend_from_slice(&state.reserve_heaps[1..]);
                        state.h = Arc::new(
                            ctx.native_empty_heap(&state.program, true)
                                .map_err(PE::Service)?,
                        );
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
                                        &state,
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
        self.checkpoint()?;
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
        yes: crate::rules::executor::CfgJoinBranch,
        no: crate::rules::executor::CfgJoinBranch,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<Self::Error>> {
        if self.joined_branch_scheduler_enabled
            && state.parallelize_branches
            && self.joined_branch_scheduler.is_some()
        {
            return self.join_owned_branches_parallel(
                state,
                condition,
                original,
                rewritten,
                super::verification_pool_manager::NativeJoinAction::Cfg(yes),
                super::verification_pool_manager::NativeJoinAction::Cfg(no),
                true,
                continuation,
            );
        }
        let error = std::cell::RefCell::new(None);
        let result = self.join_impure_branches(
            state,
            condition,
            original,
            rewritten,
            &mut |ctx, state, done| match crate::rules::executor::execute_cfg_join_branch(
                ctx,
                state,
                &yes,
                &mut |ctx, state| done(ctx, state, ()).map_err(ExecutionError::Context),
            ) {
                Ok(value) => Ok(value),
                Err(e) => {
                    *error.borrow_mut() = Some(e);
                    Err(NativeError::ContinuationAbort)
                }
            },
            &mut |ctx, state, done| match crate::rules::executor::execute_cfg_join_branch(
                ctx,
                state,
                &no,
                &mut |ctx, state| done(ctx, state, ()).map_err(ExecutionError::Context),
            ) {
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
        Ok(Arc::new(self.native_empty_heap(&state.program, true)?))
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
        self.open_member_log(ferrum_silver::ast::program::Member::Method(method.clone()))
    }
    fn close_method_log(&mut self) -> Result<(), Self::Error> {
        self.close_member_log()
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
        Ok(Arc::new(self.native_empty_heap(&state.program, true)?))
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
        self.write_cfg_output(&format!("{}.dot", method.name), cfg)
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
        continuation: crate::supporters::method_supporter::MethodCfgContinuation,
    ) -> Result<VerificationResult<VerificationError>, MethodVerificationError<Self::Error>> {
        {
            let mut callback_error = None;
            let result =
                crate::rules::executor::execute_cfg(self, state, cfg, &mut |ctx, state| {
                    match crate::supporters::method_supporter::complete_method_cfg(
                        ctx,
                        state,
                        &continuation,
                    ) {
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
        self.open_member_log(ferrum_silver::ast::program::Member::Predicate(
            predicate.clone(),
        ))
    }
    fn close_predicate_verification(&mut self) -> Result<(), Self::Error> {
        self.close_member_log()
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
        Ok(Arc::new(self.native_empty_heap(&state.program, true)?))
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
                        // Recorded path-condition views are newest first; predicate
                        // trees require the source's outermost-first order.
                        conditions: pcs.branch_conditions().into_iter().rev().collect(),
                        condition_exps: pcs.branch_condition_exps().into_iter().rev().collect(),
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
        // PredicateVerificationUnit already merges the recorder into the predicate's
        // collected fresh symbols before invoking this hook. The source does not retain
        // the recorder separately after addRecorders.
        let _ = (predicate, recorder);
        Ok(())
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
    /// Explore an owned evaluation branch on a worker with its own prover.
    pub(crate) fn verify_worker_evaluation_branch(
        &mut self,
        analysis: &NativeWorkerAnalysis,
        branch: super::verification_pool_manager::NativeEvaluationBranch,
    ) -> Result<super::verification_pool_manager::NativeEvaluationBranchOutput, NativeError<S::Error>>
    {
        use crate::rules::{
            evaluator,
            joiner::{self, JoinDataEntry},
        };
        self.checkpoint()?;
        self.active_program = Some(analysis.program.clone());
        self.predicate_contents = analysis.predicates.clone();
        self.function_handles = analysis.function_handles.clone();
        self.function_owners = analysis.function_owners.clone();
        self.function_heights = analysis.function_heights.clone();
        self.function_fresh_variables = analysis.function_fresh_variables.clone();
        self.failed_functions = analysis.failed_functions.clone();
        self.predicate_snapshots.snap_map = analysis.snapshot_sorts.clone();
        self.predicate_snapshots.formal_var_map = analysis.snapshot_formals.clone();
        let remote = self.base.unique_id != branch.source_worker_id;
        let saved_worker = remote.then(|| {
            crate::rules::brancher::BranchTransferSnapshot::capture(
                &self.base.decider,
                self.base
                    .errors_reported
                    .load(std::sync::atomic::Ordering::SeqCst),
            )
        });
        let saturation = self.options.after_inhale_timeout.map(|timeout_ms| {
            crate::interfaces::decider::prover::ProverStateSaturationTimeout {
                timeout_ms,
                comment: "after inhale".into(),
            }
        });
        let restore = if remote {
            match branch
                .snapshot
                .install(&mut self.base.decider, &self.base.errors_reported)
            {
                Ok(restore) => Some(restore),
                Err(primary) => {
                    let cleanup = saved_worker
                        .as_ref()
                        .unwrap()
                        .restore_after_cooperative_join(
                            saved_worker.as_ref().unwrap(),
                            &mut self.base.decider,
                            &self.base.errors_reported,
                            saturation.as_ref(),
                        );
                    return Err(match cleanup {
                        Ok(()) => NativeError::Evaluation(format!("branch setup: {primary:?}")),
                        Err(cleanup) => NativeError::Cleanup(format!(
                            "branch setup: {primary:?}; worker restore: {cleanup:?}"
                        )),
                    });
                }
            }
        } else {
            None
        };
        let under_join = branch.state.under_join;
        let warning_start = self.warnings.len();
        let result = (|| {
            self.base
                .decider
                .push_scope()
                .map_err(NativeError::Decider)?;
            let mut entries = Vec::new();
            let evaluated = (|| {
                self.base
                    .decider
                    .set_branch_condition(
                        branch.condition,
                        (branch.original, branch.rewritten),
                        None,
                    )
                    .map_err(|e| EvaluationError::Context(NativeError::Decider(e)))?;
                if let (true, Some(timeout)) = (remote, self.options.after_inhale_timeout) {
                    self.base
                        .decider
                        .prover
                        .saturate(timeout, "after inhale")
                        .map_err(|e| {
                            EvaluationError::Context(NativeError::Decider(DeciderError::Prover(e)))
                        })?;
                }
                let state = self
                    .consolidate_optional(branch.state)
                    .map_err(EvaluationError::Context)?;
                evaluator::execute_branch_action(
                    self,
                    state,
                    branch.action,
                    &mut |context, state, value, debug| {
                        let path = context
                            .base
                            .decider
                            .pcs
                            .after(branch.mark)
                            .map_err(EvaluationError::Path)?;
                        entries.push(JoinDataEntry {
                            state: joiner::restore_state(state, &branch.initial_state),
                            data: (value, debug),
                            path_conditions: path,
                        });
                        Ok(VerificationResult::success())
                    },
                )
            })();
            let cleanup = self.base.decider.pop_scope().map_err(NativeError::Decider);
            match (evaluated, cleanup) {
                (Ok(result), Ok(())) => Ok((result, entries)),
                (Err(EvaluationError::Context(NativeError::Cancelled)), Ok(())) => {
                    Err(NativeError::Cancelled)
                }
                (Err(e), Ok(())) => {
                    Err(NativeError::Evaluation(format!("branch evaluation: {e:?}")))
                }
                (Err(e), Err(cleanup)) => Err(NativeError::Evaluation(format!(
                    "branch evaluation: {:?}",
                    coalesce_evaluation_cleanup(e, cleanup)
                ))),
                (Ok(_), Err(cleanup)) => Err(cleanup),
            }
        })();
        let cleanup = match restore {
            Some(restore) => restore
                .finish(&mut self.base.decider, under_join)
                .map_err(NativeError::Decider),
            None => Ok(crate::rules::brancher::BranchJoinDeclarations::default()),
        };
        let outcome = match (result, cleanup) {
            (Ok((result, entries)), Ok(declarations)) => Ok(
                super::verification_pool_manager::NativeEvaluationBranchOutput {
                    result,
                    entries,
                    declarations,
                    warnings: Vec::new(),
                },
            ),
            (Err(primary), Ok(_)) => Err(primary),
            (Ok(_), Err(cleanup)) => Err(cleanup),
            (Err(primary), Err(cleanup)) => Err(NativeError::Cleanup(format!(
                "branch failed: {primary:?}; option restoration failed: {cleanup:?}"
            ))),
        };
        let state_cleanup = match &saved_worker {
            Some(saved) => saved
                .restore_after_cooperative_join(
                    saved,
                    &mut self.base.decider,
                    &self.base.errors_reported,
                    saturation.as_ref(),
                )
                .map_err(NativeError::Decider),
            None => Ok(()),
        };
        let outcome = match (outcome, state_cleanup) {
            (outcome, Ok(())) => outcome,
            (Ok(_), Err(cleanup)) => Err(cleanup),
            (Err(primary), Err(cleanup)) => Err(NativeError::Cleanup(format!(
                "branch: {primary:?}; worker restore: {cleanup:?}"
            ))),
        };
        let warnings = self.warnings.split_off(warning_start);
        match outcome {
            Ok(mut output) => {
                output.warnings = warnings;
                Ok(output)
            }
            Err(primary) if !warnings.is_empty() => Err(NativeError::BranchWarnings {
                primary: Box::new(primary),
                warnings,
            }),
            Err(primary) => Err(primary),
        }
    }

    /// Execute one transferred branch until its owned join point.
    pub(crate) fn verify_worker_join(
        &mut self,
        analysis: &NativeWorkerAnalysis,
        branch: super::verification_pool_manager::NativeJoinJob,
    ) -> Result<super::verification_pool_manager::NativeJoinOutput, NativeError<S::Error>> {
        use crate::rules::joiner::JoinDataEntry;
        self.checkpoint()?;
        self.active_program = Some(analysis.program.clone());
        self.predicate_contents = analysis.predicates.clone();
        self.function_handles = analysis.function_handles.clone();
        self.function_owners = analysis.function_owners.clone();
        self.function_heights = analysis.function_heights.clone();
        self.function_fresh_variables = analysis.function_fresh_variables.clone();
        self.failed_functions = analysis.failed_functions.clone();
        self.predicate_snapshots.snap_map = analysis.snapshot_sorts.clone();
        self.predicate_snapshots.formal_var_map = analysis.snapshot_formals.clone();
        let remote = self.base.unique_id != branch.source_worker_id;
        // An unrelated queued branch may run while this worker is suspended.
        // Restore its original PCS and error count before returning to that task.
        let saved_worker = remote.then(|| {
            crate::rules::brancher::BranchTransferSnapshot::capture(
                &self.base.decider,
                self.base
                    .errors_reported
                    .load(std::sync::atomic::Ordering::SeqCst),
            )
        });
        let saturation = self.options.after_inhale_timeout.map(|timeout_ms| {
            crate::interfaces::decider::prover::ProverStateSaturationTimeout {
                timeout_ms,
                comment: "after inhale".into(),
            }
        });
        let restore = if remote {
            match branch
                .snapshot
                .install(&mut self.base.decider, &self.base.errors_reported)
            {
                Ok(restore) => Some(restore),
                Err(primary) => {
                    let cleanup = saved_worker
                        .as_ref()
                        .unwrap()
                        .restore_after_cooperative_join(
                            saved_worker.as_ref().unwrap(),
                            &mut self.base.decider,
                            &self.base.errors_reported,
                            saturation.as_ref(),
                        );
                    return Err(match cleanup {
                        Ok(()) => {
                            NativeError::Execution(format!("joined branch setup: {primary:?}"))
                        }
                        Err(cleanup) => NativeError::Cleanup(format!(
                            "joined branch setup: {primary:?}; worker restore: {cleanup:?}"
                        )),
                    });
                }
            }
        } else {
            None
        };
        let under_join = branch.state.under_join;
        let warning_start = self.warnings.len();
        let result = (|| {
            self.base
                .decider
                .push_scope()
                .map_err(NativeError::Decider)?;
            let mut entries = Vec::new();
            let executed = (|| {
                self.base
                    .decider
                    .set_branch_condition(
                        branch.condition,
                        (branch.original, branch.rewritten),
                        None,
                    )
                    .map_err(|e| ExecutionError::Context(NativeError::Decider(e)))?;
                if let (true, Some(timeout)) = (remote, self.options.after_inhale_timeout) {
                    self.base
                        .decider
                        .prover
                        .saturate(timeout, "after inhale")
                        .map_err(|e| {
                            ExecutionError::Context(NativeError::Decider(DeciderError::Prover(e)))
                        })?;
                }
                #[cfg(test)]
                if let Some(goal) = &branch.replay_check {
                    let valid = self
                        .base
                        .decider
                        .prover
                        .assert_goal(goal, None)
                        .map_err(|e| {
                            ExecutionError::Context(NativeError::Decider(DeciderError::Prover(e)))
                        })?;
                    assert!(valid, "transferred path was not replayed");
                }
                #[cfg(test)]
                if let Some(hook) = &branch.after_start {
                    hook();
                }
                self.checkpoint().map_err(ExecutionError::Context)?;
                let state = self
                    .consolidate_optional(branch.state)
                    .map_err(ExecutionError::Context)?;
                self.execute_join_action(state, &branch.action, &mut |context, state| {
                    let path_conditions =
                        context.base.decider.pcs.after(branch.mark).map_err(|e| {
                            ExecutionError::Context(NativeError::Decider(DeciderError::Path(e)))
                        })?;
                    entries.push(JoinDataEntry {
                        state,
                        data: (),
                        path_conditions,
                    });
                    Ok(VerificationResult::success())
                })
            })();
            let cleanup = self.base.decider.pop_scope().map_err(NativeError::Decider);
            match (executed, cleanup) {
                (Ok(result), Ok(())) => Ok((result, entries)),
                (Err(ExecutionError::Context(NativeError::Cancelled)), Ok(())) => {
                    Err(NativeError::Cancelled)
                }
                (Err(e), Ok(())) => Err(NativeError::Execution(format!("joined branch: {e:?}"))),
                (Err(primary), Err(cleanup)) => Err(NativeError::Cleanup(format!(
                    "joined branch: {primary:?}; scope cleanup: {cleanup:?}"
                ))),
                (Ok(_), Err(cleanup)) => Err(cleanup),
            }
        })();
        let cleanup = match restore {
            Some(restore) => restore
                .finish(&mut self.base.decider, under_join)
                .map_err(NativeError::Decider),
            None => Ok(crate::rules::brancher::BranchJoinDeclarations::default()),
        };
        let result = match (result, cleanup) {
            (Ok((result, entries)), Ok(declarations)) => {
                Ok(super::verification_pool_manager::NativeJoinOutput {
                    result,
                    entries,
                    declarations,
                    warnings: Vec::new(),
                })
            }
            (Err(primary), Ok(_)) => Err(primary),
            (Ok(_), Err(cleanup)) => Err(cleanup),
            (Err(primary), Err(cleanup)) => Err(NativeError::Cleanup(format!(
                "joined branch: {primary:?}; options cleanup: {cleanup:?}"
            ))),
        };
        let state_cleanup = match &saved_worker {
            Some(saved) => saved
                .restore_after_cooperative_join(
                    saved,
                    &mut self.base.decider,
                    &self.base.errors_reported,
                    saturation.as_ref(),
                )
                .map_err(NativeError::Decider),
            None => Ok(()),
        };
        let result = match (result, state_cleanup) {
            (result, Ok(())) => result,
            (Ok(_), Err(cleanup)) => Err(cleanup),
            (Err(primary), Err(cleanup)) => Err(NativeError::Cleanup(format!(
                "joined branch: {primary:?}; worker restore: {cleanup:?}"
            ))),
        };
        let warnings = self.warnings.split_off(warning_start);
        match result {
            Ok(mut output) => {
                output.warnings = warnings;
                Ok(output)
            }
            Err(primary) if !warnings.is_empty() => Err(NativeError::BranchWarnings {
                primary: Box::new(primary),
                warnings,
            }),
            Err(primary) => Err(primary),
        }
    }

    /// Verify one method with an already-started worker prover and replayed preamble.
    pub(crate) fn verify_worker_method(
        &mut self,
        analysis: &NativeWorkerAnalysis,
        method: &Method,
    ) -> Result<Vec<VerificationResult<VerificationError>>, NativeError<S::Error>> {
        self.checkpoint()?;
        self.active_program = Some(analysis.program.clone());
        self.predicate_contents = analysis.predicates.clone();
        self.function_handles = analysis.function_handles.clone();
        self.function_owners = analysis.function_owners.clone();
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
        let mut state = self.initial_state(
            &analysis.program,
            &local,
            ferrum_silver::ast::program::Member::Method(method.clone()),
        )?;
        state.parallelize_branches = self.joined_branch_scheduler_enabled;
        let results = crate::supporters::method_supporter::verify_method(self, state, method)
            .map(flatten_results)
            .map_err(|e| match e {
                crate::supporters::method_supporter::MethodVerificationError::Service(
                    NativeError::Cancelled,
                ) => NativeError::Cancelled,
                other => NativeError::Execution(format!("worker method verification: {other:?}")),
            })?;
        Ok(results)
    }

    /// Verify an externally supplied CFG on an initialized worker solver.
    pub(crate) fn verify_worker_cfg(
        &mut self,
        analysis: &NativeWorkerAnalysis,
        cfg: &SilverCfg,
    ) -> Result<Vec<VerificationResult<VerificationError>>, NativeError<S::Error>> {
        self.checkpoint()?;
        self.active_program = Some(analysis.program.clone());
        self.predicate_contents = analysis.predicates.clone();
        self.function_handles = analysis.function_handles.clone();
        self.function_owners = analysis.function_owners.clone();
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
            .map_err(|e| match e {
                crate::supporters::cfg_supporter::CfgVerificationError::Service(
                    NativeError::Cancelled,
                ) => NativeError::Cancelled,
                other => NativeError::Execution(format!("worker CFG verification: {other:?}")),
            })
    }

    /// Verify a function before reporting and scope assignment in a pool orchestrator.
    pub fn verify_function_unscoped(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
        function: &ferrum_silver::ast::program::Function,
    ) -> Result<Vec<VerificationResult<VerificationError>>, NativeError<S::Error>> {
        self.checkpoint()?;
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
        self.checkpoint()?;
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
        self.checkpoint()?;
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
        self.checkpoint()?;
        use ferrum_silver::ast::{
            expression::ExpKind,
            r#type::Type,
            utility::nodes::{Node, subnodes},
        };
        if !program.extensions.is_empty() {
            return Err(NativeError::Unsupported("program extension analysis"));
        }
        self.quantifier_trigger_events.clear();
        let triggered = crate::utils::ast::auto_trigger_program_with_callback(program, |event| {
            use ferrum_silver::reporter::message::Message;
            if let Some(reporter) = &self.preprocessing_reporter {
                if event.triggers.is_empty() {
                    use ferrum_silver::verifier::verification_result::{
                        FrontendError, FrontendErrorKind,
                    };
                    reporter
                        .report(Message::WarningsDuringVerification {
                            warnings: vec![FrontendError::new(
                                FrontendErrorKind::VerifierWarning(
                                    "No triggers provided or inferred for quantifier.".into(),
                                ),
                                event.rewritten.metadata().position.clone(),
                            )],
                        })
                        .map_err(|e| {
                            NativeError::Diagnostic(format!("quantifier warning reporter: {e:?}"))
                        })?;
                }
                reporter
                    .report(Message::QuantifierChosenTriggers {
                        quantifier: event.rewritten.clone(),
                        triggers: event.triggers.clone(),
                        old_triggers: event.old_triggers.clone(),
                    })
                    .map_err(|e| {
                        NativeError::Diagnostic(format!("quantifier trigger reporter: {e:?}"))
                    })?;
            } else if event.triggers.is_empty() {
                self.warnings
                    .push("No triggers provided or inferred for quantifier.".into());
            }
            self.quantifier_trigger_events.push(event.clone());
            Ok::<_, NativeError<S::Error>>(())
        })
        .map_err(|e| match e {
            crate::utils::ast::AutoTriggerWithCallbackError::Preprocessing(e) => {
                NativeError::Diagnostic(format!("quantifier trigger preprocessing: {e:?}"))
            }
            crate::utils::ast::AutoTriggerWithCallbackError::Callback(e) => e,
        })?;
        let program = &triggered;
        let rewritten = if self.options.conditionalize_permissions {
            Some(
                crate::extensions::conditional_permission_rewriter::rewrite(
                    program,
                    !self.options.respect_function_pre_permission_amounts,
                )
                .map_err(|e| {
                    NativeError::Diagnostic(format!("conditional permission rewriting: {e:?}"))
                })?,
            )
        } else {
            None
        };
        let program = rewritten.as_ref().unwrap_or(program);
        if self.options.mask_heap_mode {
            // The pinned mask encoding declares ordinary functions without the
            // snapshot argument used by domain-axiom translation. Scala reaches
            // a prover signature error for this combination; reject it explicitly.
            fn contains_function(node: &Node) -> Result<bool, &'static str> {
                if matches!(node, Node::Exp(exp) if matches!(exp.kind(), ExpKind::FuncApp(..))) {
                    return Ok(true);
                }
                for child in subnodes(node).map_err(|_| "domain axiom traversal")? {
                    if contains_function(&child)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            for domain in &program.domains {
                for axiom in &domain.axioms {
                    if contains_function(&Node::DomainAxiom(axiom.clone()))
                        .map_err(NativeError::Unsupported)?
                    {
                        return Err(NativeError::Unsupported(
                            "ordinary function in mask-mode domain axiom",
                        ));
                    }
                }
            }
        }
        if self.options.print_translated_program {
            let rendered = ferrum_silver::ast::pretty::pretty_printer::pretty_node(&Node::Program(
                program.clone(),
            ))
            .map_err(|e| NativeError::Diagnostic(format!("translated program rendering: {e:?}")))?;
            println!("{rendered}");
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
        // Custom sources are loaded only during contributor analysis, avoiding a
        // second read between preflight and the emitted solver preamble.
        let custom_sources = self.options.collection_axiomatization_sources();
        let uses_custom = custom_sources.sequences.is_some()
            || custom_sources.sets.is_some()
            || custom_sources.multisets.is_some()
            || custom_sources.maps.is_some();
        if !uses_custom
            && !general
            && (has_sequence || has_set || has_map || has_multiset || has_quantified)
        {
            crate::verifier::native_preamble::analyze_collections_with_sources(
                program,
                &self.base.symbol_converter,
                &self.factory,
                self.factory.options().use_old_axiomatization,
                &self.options.collection_axiomatization_sources(),
            )
            .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
        }
        if !uses_custom && general {
            crate::verifier::native_preamble::analyze_general_with_sources(
                program,
                &self.base.symbol_converter,
                &self.factory,
                self.factory.options().use_old_axiomatization,
                1,
                &self.options.collection_axiomatization_sources(),
            )
            .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
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
        self.checkpoint()?;
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
        self.checkpoint()?;
        Ok(())
    }
    fn emit_static_preamble(&mut self) -> Result<(), Self::Error> {
        self.checkpoint()?;
        Ok(())
    }
    fn analyze_and_emit_contributions(
        &mut self,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<NativeAnalysis, Self::Error> {
        self.checkpoint()?;
        let general = use_general_preamble(program, &self.base.symbol_converter, &self.factory)
            .map_err(NativeError::Preamble)?;
        let mut contributed_sorts = Vec::new();
        let mut general_preamble = None;
        let mut legacy_preamble = None;
        if general {
            let preamble = crate::verifier::native_preamble::analyze_general_with_sources(
                program,
                &self.base.symbol_converter,
                &self.factory,
                self.factory.options().use_old_axiomatization,
                1,
                &self.options.collection_axiomatization_sources(),
            )
            .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            preamble
                .declare_sorts(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            preamble
                .declare_symbols(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            contributed_sorts.extend(preamble.sorts().cloned());
            general_preamble = Some(preamble);
        } else {
            let (has_sequence, has_set, has_map, has_multiset) =
                collection_program(program).map_err(NativeError::Preamble)?;
            let has_quantified =
                crate::verifier::native_preamble::uses_quantified_resource(program)
                    .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            let collections =
                if has_sequence || has_set || has_map || has_multiset || has_quantified {
                    Some(
                        crate::verifier::native_preamble::analyze_collections_with_sources(
                            program,
                            &self.base.symbol_converter,
                            &self.factory,
                            self.factory.options().use_old_axiomatization,
                            &self.options.collection_axiomatization_sources(),
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
            contributed_sorts.extend(domain_preamble.sorts().cloned());
            if let Some(preamble) = &collections {
                contributed_sorts.extend(preamble.sorts().cloned());
            }
            legacy_preamble = Some((domain_preamble, collections));
        }
        let predicates = crate::supporters::predicate_verification_unit::analyze_predicates(
            program,
            &self.base.symbol_converter,
            &self.factory,
            if self.options.mask_heap_mode {
                Sort::PredHeap
            } else {
                Sort::Snap
            },
        )
        .map_err(NativeError::Sort)?;
        self.predicate_contents = predicates.clone();
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
        let mut mask_functions = crate::supporters::qps::mask_heap_functions_contributor::MaskHeapFunctionsContributor::default();
        if self.options.mask_heap_mode {
            mask_functions
                .analyze(
                    program,
                    true,
                    &self.base.symbol_converter,
                    &mut self.base.term_converter,
                    &reader,
                    |sort| Ok::<_, String>(sort.to_string()),
                    |predicate| {
                        ferrum_silver::ast::pretty::pretty_printer::pretty_node(
                            &ferrum_silver::ast::utility::nodes::Node::Member(
                                ferrum_silver::ast::program::Member::Predicate(predicate.clone()),
                            ),
                        )
                        .map_err(|e| format!("{e:?}"))
                    },
                )
                .map_err(|e| NativeError::Preamble(format!("mask heap functions: {e:?}")))?;
        }
        let mut field_maps = crate::supporters::qps::field_value_functions_contributor::FieldValueFunctionsContributor::default();
        let mut predicate_maps = crate::supporters::qps::predicate_and_wand_snap_functions_contributor::PredicateAndWandSnapFunctionsContributor::default();
        if has_quantified {
            field_maps
                .analyze(
                    program,
                    &self.base.symbol_converter,
                    &mut self.base.term_converter,
                    &reader,
                    self.options.disable_isc_triggers,
                    |sort| Ok::<_, String>(sort.to_string()),
                )
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            predicate_maps
                .analyze(
                    program,
                    &self.predicate_snapshots,
                    &mut self.base.term_converter,
                    &reader,
                    self.options.disable_isc_triggers,
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
        if self.options.mask_heap_mode {
            mask_functions
                .declare_sorts(&self.factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        let mut wrapper_sorts = vec![Sort::Int, Sort::Bool, Sort::Ref, Sort::Perm];
        wrapper_sorts.extend(contributed_sorts);
        wrapper_sorts.extend(wand_functions.sorts.iter().cloned());
        wrapper_sorts.extend(field_maps.sorts.iter().cloned());
        wrapper_sorts.extend(mask_functions.heap_sorts.iter().cloned());
        wrapper_sorts.extend(mask_functions.predicate_sorts.iter().cloned());
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
            &mask_functions.function_blocks,
            &predicate_maps.function_blocks,
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
        let mut mask_identifiers = self.base.identifiers.clone();
        let mask_resources = &mut self.mask_resources;
        let converter = self.base.symbol_converter.clone();
        let mask_mode = self.options.mask_heap_mode;
        functions.analyze(&factory, &self.base.symbol_converter, &mut self.base.identifiers, program, self.options.alternative_function_verification_order, false,
            |function, program| {
                if mask_mode {
                    let resources = mask_resources.resources(&function.pres, program)
                        .map_err(|e| format!("mask function resources: {e:?}"))?;
                    let args = crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::state_args(
                        &factory, &converter, &mut mask_identifiers, &resources,
                    ).map_err(|e| format!("mask function state arguments: {e:?}"))?;
                    Ok::<_, String>((args, Some(resources)))
                } else {
                    Ok((crate::supporters::functions::function_encoding::DefaultFunctionEncoding::state_args(&factory), None))
                }
            })
            .map_err(|e| NativeError::Execution(format!("function analysis: {e:?}")))?;
        if !program.functions.is_empty() {
            functions
                .declare_analysis_symbols(&factory, &mut self.base.decider.prover, |data| {
                    if mask_mode {
                        crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::auxiliary_functions(
                            &factory, &data.function, data.state_args.len(),
                        )
                    } else {
                        vec![]
                    }
                })
                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
        }
        // Domain axioms can mention ordinary function and precondition symbols, so
        // emit them only after all contributor symbols have been declared.
        if let Some(preamble) = &general_preamble {
            preamble
                .emit_axioms(&factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
        }
        if let Some((domains, collections)) = &legacy_preamble {
            domains
                .emit_uniqueness(&factory, &mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            if let Some(collections) = collections {
                collections
                    .emit_axioms(&mut self.base.decider.prover)
                    .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
            }
            domains
                .emit_domain_axioms(&mut self.base.decider.prover)
                .map_err(|e| NativeError::Preamble(format!("{e:?}")))?;
        }
        for blocks in [
            &field_maps.axiom_blocks,
            &mask_functions.axiom_blocks,
            &predicate_maps.axiom_blocks,
        ] {
            crate::supporters::qps::field_value_functions_contributor::FieldValueFunctionsContributor::emit_blocks(blocks, &mut self.base.decider.prover)
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
        self.function_owners = functions.data.clone();
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
        self.checkpoint()?;
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
        let warning_start = self.warnings.len();
        let started = std::time::Instant::now();
        let outcome = self.verify_function_unscoped(program, analysis, &unit);
        let delivery = report_single_warnings(
            self.preprocessing_reporter.as_deref(),
            &self.warnings[warning_start..],
        );
        let results = combine_single_delivery(outcome, delivery)?;
        if let Some(reporter) = &self.preprocessing_reporter {
            super::verification_pool_manager::report_member_results(
                reporter.as_ref(),
                Some(Arc::new(ferrum_silver::ast::program::Member::Function(
                    unit.clone(),
                ))),
                started.elapsed(),
                &results,
            )
            .map_err(|error| {
                NativeError::Diagnostic(format!("function result reporter: {error:?}"))
            })?;
        }
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
        let warning_start = self.warnings.len();
        let started = std::time::Instant::now();
        let outcome = self.verify_predicate_unscoped(program, analysis, &unit);
        let delivery = report_single_warnings(
            self.preprocessing_reporter.as_deref(),
            &self.warnings[warning_start..],
        );
        let results = combine_single_delivery(outcome, delivery)?;
        if let Some(reporter) = &self.preprocessing_reporter {
            super::verification_pool_manager::report_member_results(
                reporter.as_ref(),
                Some(Arc::new(ferrum_silver::ast::program::Member::Predicate(
                    unit.clone(),
                ))),
                started.elapsed(),
                &results,
            )
            .map_err(|error| {
                NativeError::Diagnostic(format!("predicate result reporter: {error:?}"))
            })?;
        }
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
        self.checkpoint()
    }
    fn declare_predicate_sorts(&mut self) -> Result<(), Self::Error> {
        self.checkpoint()
    }
    fn declare_function_sorts(&mut self) -> Result<(), Self::Error> {
        self.checkpoint()
    }
    fn declare_predicate_symbols(&mut self) -> Result<(), Self::Error> {
        self.checkpoint()
    }
    fn declare_function_symbols(&mut self) -> Result<(), Self::Error> {
        self.checkpoint()
    }
    fn emit_predicate_axioms(&mut self) -> Result<(), Self::Error> {
        self.checkpoint()
    }
    fn emit_function_axioms(&mut self) -> Result<(), Self::Error> {
        self.checkpoint()
    }
    fn end_worker_preamble(&mut self) -> Result<(), Self::Error> {
        self.checkpoint()
    }
    fn excluded_method(&mut self, method: &ferrum_silver::ast::program::Method) -> bool {
        !self.options.include_methods.is_match(&method.name)
            || self.options.exclude_methods.is_match(&method.name)
    }
    fn queue_method(
        &mut self,
        method: &ferrum_silver::ast::program::Method,
        program: &ferrum_silver::ast::program::Program,
        analysis: &NativeAnalysis,
    ) -> Result<Self::Task, Self::Error> {
        self.checkpoint()?;
        let warning_start = self.warnings.len();
        let mut started = None;
        let outcome = (|| {
            let state = self.initial_state(
                program,
                analysis,
                ferrum_silver::ast::program::Member::Method(method.clone()),
            )?;
            started = Some(std::time::Instant::now());
            crate::supporters::method_supporter::verify_method(self, state, method)
                .map_err(|e| NativeError::Execution(format!("{e:?}")))
        })();
        let delivery = report_single_warnings(
            self.preprocessing_reporter.as_deref(),
            &self.warnings[warning_start..],
        );
        let results = combine_single_delivery(outcome, delivery)?;
        if let Some(reporter) = &self.preprocessing_reporter {
            super::verification_pool_manager::report_member_results(
                reporter.as_ref(),
                Some(Arc::new(ferrum_silver::ast::program::Member::Method(
                    method.clone(),
                ))),
                started.expect("method verification started").elapsed(),
                &flatten_results(results.clone()),
            )
            .map_err(|error| {
                NativeError::Diagnostic(format!("method result reporter: {error:?}"))
            })?;
        }
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
        self.checkpoint()?;
        let warning_start = self.warnings.len();
        let state = self.initial_cfg_state(program, analysis);
        let started = std::time::Instant::now();
        let outcome =
            crate::supporters::cfg_supporter::verify_cfg(self, state, Arc::new(cfg.clone()))
                .map_err(|e| NativeError::Execution(format!("CFG verification: {e:?}")));
        let delivery = report_single_warnings(
            self.preprocessing_reporter.as_deref(),
            &self.warnings[warning_start..],
        );
        let results = combine_single_delivery(outcome, delivery)?;
        if let Some(reporter) = &self.preprocessing_reporter {
            super::verification_pool_manager::report_member_results(
                reporter.as_ref(),
                None,
                started.elapsed(),
                &flatten_results(results.clone()),
            )
            .map_err(|error| NativeError::Diagnostic(format!("CFG result reporter: {error:?}")))?;
        }
        Ok(results)
    }
    fn await_task(&mut self, task: Self::Task) -> Result<Vec<Self::Result>, Self::Error> {
        Ok(flatten_results(task))
    }
    fn report_termination_and_optional_trace(&mut self) -> Result<(), Self::Error> {
        if let Some(reporter) = &self.preprocessing_reporter {
            reporter
                .report(ferrum_silver::reporter::message::Message::VerificationTermination)
                .map_err(|error| {
                    NativeError::Diagnostic(format!("termination reporter: {error:?}"))
                })?;
        }
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
pub(super) fn report_single_warnings<E>(
    reporter: Option<&dyn ferrum_silver::reporter::reporter::Reporter>,
    warnings: &[String],
) -> Result<(), NativeError<E>> {
    use ferrum_silver::{
        ast::position::Position,
        reporter::message::Message,
        verifier::verification_result::{FrontendError, FrontendErrorKind},
    };
    if let Some(reporter) = reporter.filter(|_| !warnings.is_empty()) {
        reporter
            .report(Message::WarningsDuringVerification {
                warnings: warnings
                    .iter()
                    .cloned()
                    .map(|warning| {
                        FrontendError::new(
                            FrontendErrorKind::VerifierWarning(warning),
                            Position::NoPosition,
                        )
                    })
                    .collect(),
            })
            .map_err(|error| NativeError::Diagnostic(format!("warning reporter: {error:?}")))?;
    }
    Ok(())
}
pub(super) fn combine_single_delivery<T, E: std::fmt::Debug>(
    outcome: Result<T, NativeError<E>>,
    delivery: Result<(), NativeError<E>>,
) -> Result<T, NativeError<E>> {
    match (outcome, delivery) {
        (result, Ok(())) => result,
        (Ok(_), Err(error)) => Err(error),
        (Err(primary), Err(error)) => Err(NativeError::BranchWarnings {
            primary: Box::new(primary),
            warnings: vec![format!("warning delivery failed: {error:?}")],
        }),
    }
}
#[cfg(test)]
#[test]
fn reporting_failure_preserves_primary_native_error() {
    let outcome: Result<(), NativeError<()>> = Err(NativeError::Cancelled);
    let delivery = Err(NativeError::Diagnostic("reporter failed".into()));
    match combine_single_delivery(outcome, delivery) {
        Err(NativeError::BranchWarnings { primary, warnings }) => {
            assert!(matches!(*primary, NativeError::Cancelled));
            assert!(
                warnings
                    .iter()
                    .any(|message| message.contains("reporter failed"))
            );
        }
        other => panic!("lost primary or reporter error: {other:?}"),
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
        if self.options.mask_heap_mode {
            let state = self
                .produce_native_mask_single(state, &resource, args, snapshot, permission)
                .map_err(PE::Service)?;
            return continuation(self, state);
        }
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
        if self.options.mask_heap_mode {
            use crate::rules::mask_heap_supporter::MaskConsumption;
            if state.exhale_ext {
                let mut callback_error = None;
                let result = self.consume_mask_transfer(
                    state,
                    &resource,
                    args,
                    permission.clone(),
                    true,
                    full,
                    &mut |ctx, state, heap, snapshot| match continuation(ctx, state, heap, snapshot)
                    {
                        Ok(v) => Ok(v),
                        Err(e) => {
                            callback_error = Some(e);
                            Err(NativeError::ContinuationAbort)
                        }
                    },
                );
                if let Some(e) = callback_error {
                    return Err(e);
                }
                return result.map_err(PE::Service);
            }
            return match self
                .consume_native_mask_single(
                    &state,
                    &heap,
                    &resource,
                    args,
                    permission.clone(),
                    true,
                )
                .map_err(PE::Service)?
            {
                MaskConsumption::Complete { heap, snapshot } => {
                    continuation(self, state, Arc::new(heap), snapshot)
                }
                MaskConsumption::Insufficient { .. } => {
                    self.failure_full(full, &state, false).map_err(PE::Service)
                }
            };
        }
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
        if self.options.mask_heap_mode {
            let resource = ResourceKey::Predicate(Arc::new(predicate.clone()));
            return crate::rules::mask_heap_supporter::folded_predicate_snapshot::<
                NativeError<S::Error>,
            >(&self.factory, &resource, args, snapshot.clone())
            .map_err(|e| NativeError::Snapshot(format!("mask folded predicate: {e:?}")));
        }
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
        let Some(data) = self.predicate_contents.get(&predicate.name) else {
            return Ok(None);
        };
        let contents = data.contents.lock().expect("predicate contents poisoned");
        match (&contents.tree, &contents.params) {
            (Some(tree), Some(params)) => Ok(Some((tree.clone(), params.clone()))),
            (None, _) => Ok(None),
            (Some(_), None) => Err(NativeError::Unsupported("cached predicate parameters")),
        }
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
        let factory = self.factory.clone();
        crate::rules::predicate_supporter::produce_predicate_contents(
            &factory,
            self,
            state,
            tree,
            replacements,
            false,
            continuation,
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
        let projection = if self.options.mask_heap_mode {
            let mut eval_state = state.clone();
            eval_state.h = Arc::new(pre_heap.clone());
            let heap = crate::rules::magic_wand_supporter::evaluation_heap(self, &eval_state)
                .map_err(|e| {
                    PE::Service(NativeError::Snapshot(format!(
                        "mask predicate evaluation heap: {e:?}"
                    )))
                })?;
            let resource = ResourceKey::Predicate(Arc::new(predicate.clone()));
            let factory = self.factory.clone();
            crate::rules::mask_heap_supporter::unfolded_predicate_snapshot(
                &factory,
                &resource,
                args,
                snapshot.clone(),
                &heap,
                |term| self.mask_term_alias(&state, term),
            )
            .map_err(|e| {
                PE::Service(NativeError::Snapshot(format!(
                    "mask unfolded predicate: {e:?}"
                )))
            })?
        } else {
            snapshot.clone()
        };
        let result = crate::rules::producer::produce_all(
            self,
            state,
            NativeSnapshot::Projection(projection),
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
            if self.options.mask_heap_mode {
                Sort::PredHeap
            } else {
                Sort::Snap
            },
        )
        .map_err(NativeError::Sort)?;
        let trigger_snapshot = if self.options.mask_heap_mode {
            let resource = ResourceKey::Predicate(Arc::new(predicate.clone()));
            crate::rules::mask_heap_supporter::find_chunk::<NativeError<S::Error>>(heap, &resource)
                .map_err(|e| NativeError::Chunk(format!("mask predicate trigger: {e:?}")))?
                .ok_or(NativeError::Unsupported("missing predicate mask chunk"))?
                .heap
                .clone()
        } else {
            self.factory.sort_wrapper(snapshot.clone(), Sort::Snap)
        };
        let mut terms = vec![trigger_snapshot];
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
                    let mut finish = |ctx: &mut Self, mut state: State<PD, FD, JoinMode>| {
                        state.g = scaled.g.clone();
                        state.function_recorder = state.function_recorder.change_depth_by(-1);
                        state.record_visited = outer.record_visited;
                        state.permission_scaling_factor = outer.permission_scaling_factor.clone();
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
                                    Err(ProductionError::Context(NativeError::ContinuationAbort))
                                }
                            },
                            Err(e) => Err(ProductionError::Context(e)),
                        }
                    };
                    let cached = crate::rules::predicate_supporter::PredicateExecutionServices::cached_predicate_contents(ctx, &bound, predicate)
                        .map_err(EvaluationError::Context)?;
                    let result = if let Some((tree, params)) = cached {
                        let replacements = params
                            .into_iter()
                            .zip(std::iter::once(snapshot.clone()).chain(args.iter().cloned()))
                            .collect();
                        let factory = ctx.factory.clone();
                        crate::rules::predicate_supporter::produce_predicate_contents(
                            &factory, ctx, bound, &tree, &replacements, true,
                            &mut |ctx, state| finish(ctx, state).map_err(|e| crate::rules::predicate_supporter::PredicateExecutionError::Service(NativeError::Production(format!("{e:?}")))),
                        ).map_err(|e| ProductionError::Context(NativeError::Production(format!("{e:?}"))))
                    } else {
                        let body_snapshot = if ctx.options.mask_heap_mode {
                            let eval_heap =
                                crate::rules::magic_wand_supporter::evaluation_heap(ctx, &bound)
                                    .map_err(|e| {
                                        EvaluationError::Context(NativeError::Snapshot(format!(
                                            "mask unfolding evaluation heap: {e:?}"
                                        )))
                                    })?;
                            let resource = ResourceKey::Predicate(Arc::new(predicate.clone()));
                            let factory = ctx.factory.clone();
                            crate::rules::mask_heap_supporter::unfolded_predicate_snapshot(
                                &factory,
                                &resource,
                                args,
                                snapshot,
                                &eval_heap,
                                |term| ctx.mask_term_alias(&bound, term),
                            )
                            .map_err(|e| {
                                EvaluationError::Context(NativeError::Snapshot(format!(
                                    "mask unfolding snapshot: {e:?}"
                                )))
                            })?
                        } else {
                            snapshot
                        };
                        crate::rules::producer::produce_all(
                            ctx,
                            bound,
                            NativeSnapshot::Projection(body_snapshot),
                            std::slice::from_ref(predicate_body),
                            &|_| error.clone(),
                            &mut finish,
                        )
                    };
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
        let joining_scope = self
            .open_joining_scope(&state)
            .map_err(EvaluationError::Context)?;
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
                return Err(coalesce_evaluation_cleanup(e, cleanup));
            }
            (Err(e), Ok(())) => return Err(e),
            (Ok(_), Err(cleanup)) => return Err(EvaluationError::Context(cleanup)),
        };
        let block = VerificationResult::success().and_then(|| block);
        if !block.continue_verification() {
            return Ok(block);
        }
        self.close_logged_scope(joining_scope)
            .map_err(EvaluationError::Context)?;
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
        let joining_scope = self
            .open_joining_scope(&state)
            .map_err(EvaluationError::Context)?;
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
                return Err(coalesce_evaluation_cleanup(e, cleanup));
            }
            (Err(e), Ok(())) => return Err(e),
            (Ok(_), Err(cleanup)) => return Err(EvaluationError::Context(cleanup)),
        };
        let block = VerificationResult::success().and_then(|| block);
        if !block.continue_verification() {
            return Ok(block);
        }
        self.close_logged_scope(joining_scope)
            .map_err(EvaluationError::Context)?;
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
                return Err(coalesce_evaluation_cleanup(e, cleanup));
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
        if self.options.mask_heap_mode {
            let factory = self.factory.clone();
            return crate::supporters::functions::mask_heap_function_encoding::adapt_trigger_terms(
                &factory,
                &terms,
                |function, args, heaps| {
                    let name = match &function.data().id {
                        crate::state::identifiers::Identifier::Suffixed { prefix, .. } => {
                            prefix.name()
                        }
                        identifier => identifier.name(),
                    };
                    if !state
                        .program
                        .functions
                        .iter()
                        .any(|source| source.name == name)
                        || state.function_data.get(&name).is_none()
                    {
                        return Ok::<_, NativeError<S::Error>>(None);
                    }
                    let Some((_, owner)) =
                        self.function_owners.iter().find(|(key, _)| key == &name)
                    else {
                        return Err(NativeError::Unsupported("missing mask function data owner"));
                    };
                    let owner = owner.clone();
                    let data = if let Some(active) = self
                        .active_function_snapshot
                        .as_ref()
                        .filter(|active| active.program_function.name == name)
                    {
                        active.phase_snapshot()
                    } else {
                        owner
                            .lock()
                            .map_err(|_| {
                                NativeError::Execution("function data lock poisoned".into())
                            })?
                            .phase_snapshot()
                    };
                    let info = self.mask_function_frame(&data)?;
                    let frame = info
                        .instantiated_frame(&factory, &data, args, heaps)
                        .map_err(|e| {
                            NativeError::Execution(format!("mask trigger frame: {e:?}"))
                        })?;
                    Ok(Some(frame))
                },
            )
            .map_err(|e| NativeError::Execution(format!("mask trigger adaptation: {e:?}")));
        }
        Ok(terms)
    }
    fn warn_trigger(&mut self, expression: &Exp) -> Result<(), Self::Error> {
        self.warnings
            .push(format!("Might not be able to use trigger: {expression:?}"));
        Ok(())
    }
    fn handles_resource_trigger(&self, state: &State<PD, FD, JoinMode>, expression: &Exp) -> bool {
        if self.options.mask_heap_mode {
            return matches!(
                expression.kind(),
                ExpKind::FieldAccess(..) | ExpKind::PredicateAccess(..) | ExpKind::MagicWand(..)
            );
        }
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
        if self.options.mask_heap_mode {
            let chunk = crate::rules::mask_heap_supporter::find_chunk::<NativeError<S::Error>>(
                &state.h, &resource,
            )
            .map_err(|e| NativeError::Chunk(format!("mask trigger lookup: {e:?}")))?;
            if chunk.is_none() && matches!(resource, ResourceKey::Wand(_)) {
                return Ok((state, vec![], vec![vec![]], vec![]));
            }
            let mut trigger_state = state.clone();
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
            .map_err(|e| NativeError::Evaluation(format!("mask trigger arguments: {e:?}")))?;
            // Source ignores the verification result here: absent a reached callback,
            // the single empty trigger variant remains in place.
            let _ = result;
            let Some(terms) = evaluated else {
                return Ok((state, vec![], vec![vec![]], vec![]));
            };
            let variants = crate::rules::mask_heap_supporter::resource_trigger_variants::<
                NativeError<S::Error>,
            >(&self.factory, &state.h, &resource, &terms)
            .map_err(|e| NativeError::Chunk(format!("mask trigger variants: {e:?}")))?;
            return Ok((state, vec![], variants, vec![]));
        }
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
    fn execute_join_action(
        &mut self,
        state: State<PD, FD, JoinMode>,
        action: &super::verification_pool_manager::NativeJoinAction,
        done: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<NativeError<S::Error>>> {
        use crate::rules::predicate_supporter::PredicateExecutionError as PE;
        match action {
            super::verification_pool_manager::NativeJoinAction::Cfg(action) => {
                crate::rules::executor::execute_cfg_join_branch(self, state, action, done)
            }
            super::verification_pool_manager::NativeJoinAction::Predicate(action) => {
                let result = crate::rules::predicate_supporter::execute_predicate_contents_action(
                    self,
                    state,
                    action,
                    &mut |ctx, state| {
                        done(ctx, state).map_err(|e| match e {
                            ExecutionError::Context(error) => PE::Service(error),
                            other => PE::Service(NativeError::Execution(format!(
                                "predicate join continuation: {other:?}"
                            ))),
                        })
                    },
                );
                result.map_err(|e| match e {
                    PE::Service(error) => ExecutionError::Context(error),
                    other => ExecutionError::Context(NativeError::Production(format!(
                        "predicate contents: {other:?}"
                    ))),
                })
            }
        }
    }

    /// Schedule source-eligible CFG and predicate joins; other joins remain synchronous.
    fn join_owned_branches_parallel(
        &mut self,
        mut state: State<PD, FD, JoinMode>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        yes: super::verification_pool_manager::NativeJoinAction,
        no: super::verification_pool_manager::NativeJoinAction,
        consolidate_join: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<PD, FD, JoinMode>,
        ) -> Result<
            VerificationResult<VerificationError>,
            ExecutionError<NativeError<S::Error>>,
        >,
    ) -> Result<VerificationResult<VerificationError>, ExecutionError<NativeError<S::Error>>> {
        use crate::rules::{
            brancher,
            joiner::{self, JoinDataEntry},
        };
        let factory = self.factory.clone();
        self.base
            .decider
            .push_scope()
            .map_err(|e| ExecutionError::Context(NativeError::Decider(e)))?;
        let mark = self.base.decider.pcs.mark();
        state.under_join = true;
        let block = (|| {
            let qvars = state
                .quantified_variables
                .iter()
                .map(|(term, _)| term.clone())
                .collect::<Vec<_>>();
            let decision = brancher::decide(&factory, &condition, &qvars, false, true, |term| {
                self.base
                    .decider
                    .check(term, self.base.decider.check_timeout)
            })
            .map_err(|e| match e {
                brancher::BranchError::Solver(e) => {
                    ExecutionError::Context(NativeError::Decider(e))
                }
                brancher::BranchError::Traversal(e) => {
                    ExecutionError::Context(NativeError::BranchTraversal(format!("{e:?}")))
                }
            })?;
            let snapshot = decision.parallelize_else.then(|| {
                brancher::BranchTransferSnapshot::capture(
                    &self.base.decider,
                    self.base
                        .errors_reported
                        .load(std::sync::atomic::Ordering::SeqCst),
                )
            });
            let future = if let Some(snapshot) = &snapshot {
                let job = super::verification_pool_manager::NativeJoinJob {
                    source_worker_id: self.base.unique_id.clone(),
                    snapshot: snapshot.clone(),
                    state: state.clone(),
                    mark,
                    condition: factory.not(condition.clone()),
                    original: Exp::new(ExpKind::Not(original.clone()), Default::default()),
                    rewritten: rewritten
                        .map(|e| Exp::new(ExpKind::Not(e.clone()), Default::default())),
                    action: no.clone(),
                    #[cfg(test)]
                    after_start: None,
                    #[cfg(test)]
                    replay_check: None,
                };
                Some(
                    self.joined_branch_scheduler
                        .as_ref()
                        .expect("scheduler")
                        .submit(job)
                        .map_err(|e| {
                            ExecutionError::Context(NativeError::Diagnostic(format!(
                                "joined branch submission: {e:?}"
                            )))
                        })?,
                )
            } else {
                None
            };
            let run = |this: &mut Self,
                       active: bool,
                       positive: bool,
                       action: &super::verification_pool_manager::NativeJoinAction|
             -> Result<
                (
                    VerificationResult<VerificationError>,
                    Vec<JoinDataEntry<PD, FD, JoinMode, ()>>,
                ),
                ExecutionError<NativeError<S::Error>>,
            > {
                if !active {
                    return Ok((VerificationResult::unreachable(), Vec::new()));
                }
                this.base
                    .decider
                    .push_scope()
                    .map_err(|e| ExecutionError::Context(NativeError::Decider(e)))?;
                let guard = if positive {
                    condition.clone()
                } else {
                    factory.not(condition.clone())
                };
                let exp = if positive {
                    original.clone()
                } else {
                    Exp::new(ExpKind::Not(original.clone()), Default::default())
                };
                let debug = if positive {
                    rewritten.cloned()
                } else {
                    rewritten.map(|e| Exp::new(ExpKind::Not(e.clone()), Default::default()))
                };
                let mut entries = Vec::new();
                let result = (|| {
                    this.base
                        .decider
                        .set_branch_condition(guard, (exp, debug), None)
                        .map_err(|e| ExecutionError::Context(NativeError::Decider(e)))?;
                    let state = this
                        .consolidate_optional(state.clone())
                        .map_err(ExecutionError::Context)?;
                    this.execute_join_action(state, action, &mut |context, state| {
                        let path_conditions =
                            context.base.decider.pcs.after(mark).map_err(|e| {
                                ExecutionError::Context(NativeError::Decider(DeciderError::Path(e)))
                            })?;
                        entries.push(JoinDataEntry {
                            state,
                            data: (),
                            path_conditions,
                        });
                        Ok(VerificationResult::success())
                    })
                })();
                let cleanup = this.base.decider.pop_scope().map_err(NativeError::Decider);
                match (result, cleanup) {
                    (Ok(result), Ok(())) => Ok((result, entries)),
                    (Err(e), Ok(())) => Err(e),
                    (Ok(_), Err(e)) => Err(ExecutionError::Context(e)),
                    (Err(e), Err(cleanup)) => Err(ExecutionError::Context(NativeError::Cleanup(
                        format!("joined branch: {e:?}; scope cleanup: {cleanup:?}"),
                    ))),
                }
            };
            let then_result = run(self, decision.execute_then, true, &yes);
            let then_report_error = if state.is_last_retry() {
                match &then_result {
                    Ok((result, _)) => {
                        self.joined_branch_scheduler.as_ref().and_then(|scheduler| {
                            scheduler
                                .report_failure(state.current_member.as_ref(), result)
                                .err()
                        })
                    }
                    Err(_) => None,
                }
            } else {
                None
            };
            if let Some(future) = future {
                let after_then = brancher::BranchTransferSnapshot::capture(
                    &self.base.decider,
                    self.base
                        .errors_reported
                        .load(std::sync::atomic::Ordering::SeqCst),
                );
                let pcs_before = self.base.decider.path_condition_identity();
                let waited = future.wait(self);
                let restoration = if !std::sync::Arc::ptr_eq(
                    &pcs_before,
                    &self.base.decider.path_condition_identity(),
                ) && !waited.awaited_executed_on_current_worker
                {
                    let saturation = self.options.after_inhale_timeout.map(|timeout_ms| {
                        crate::interfaces::decider::prover::ProverStateSaturationTimeout {
                            timeout_ms,
                            comment: "after inhale".into(),
                        }
                    });
                    after_then
                        .restore_after_cooperative_join(
                            snapshot.as_ref().unwrap(),
                            &mut self.base.decider,
                            &self.base.errors_reported,
                            saturation.as_ref(),
                        )
                        .err()
                        .map(NativeError::Decider)
                } else {
                    None
                };
                let other = match waited.result {
                    Ok(mut output) => {
                        self.warnings.append(&mut output.warnings);
                        Ok(output)
                    }
                    Err(super::verification_pool_manager::ThreadPoolError::Worker(
                        NativeError::BranchWarnings { primary, warnings },
                    )) => {
                        self.warnings.extend(warnings);
                        Err(*primary)
                    }
                    Err(super::verification_pool_manager::ThreadPoolError::Worker(error)) => {
                        Err(error)
                    }
                    Err(super::verification_pool_manager::ThreadPoolError::Cancelled) => {
                        Err(NativeError::Cancelled)
                    }
                    Err(error) => Err(NativeError::Diagnostic(format!(
                        "joined branch wait: {error:?}"
                    ))),
                };
                match (then_result, other, restoration, then_report_error) {
                    (Ok((result, mut entries)), Ok(other), None, None) => {
                        if state.is_last_retry() {
                            self.joined_branch_scheduler
                                .as_ref()
                                .expect("scheduler")
                                .report_failure(state.current_member.as_ref(), &other.result)
                                .map_err(ExecutionError::Context)?;
                        }
                        other
                            .declarations
                            .declare_on(&mut self.base.decider)
                            .map_err(|e| ExecutionError::Context(NativeError::Decider(e)))?;
                        entries.extend(other.entries);
                        Ok((entries, result.combine(|| other.result, true)))
                    }
                    (Err(error), Ok(_), None, None) => Err(error),
                    (Ok(_), Err(error), None, None) => Err(ExecutionError::Context(error)),
                    (Ok(_), Ok(_), Some(error), None) | (Ok(_), Ok(_), None, Some(error)) => {
                        Err(ExecutionError::Context(error))
                    }
                    (then, other, restoration, reporting) => {
                        Err(ExecutionError::Context(NativeError::Cleanup(format!(
                            "joined branch: then={:?}, else={:?}, restoration={restoration:?}, reporting={reporting:?}",
                            then.err(),
                            other.err()
                        ))))
                    }
                }
            } else {
                if let Some(error) = then_report_error {
                    return Err(ExecutionError::Context(error));
                }
                let (then_result, mut entries) = then_result?;
                let result = if then_result.continue_verification() {
                    let (other, other_entries) = run(self, decision.execute_else, false, &no)?;
                    if state.is_last_retry() {
                        self.joined_branch_scheduler
                            .as_ref()
                            .expect("scheduler")
                            .report_failure(state.current_member.as_ref(), &other)
                            .map_err(ExecutionError::Context)?;
                    }
                    entries.extend(other_entries);
                    then_result.combine(|| other, false)
                } else {
                    then_result
                };
                Ok((entries, result))
            }
        })();
        let cleanup = self.base.decider.pop_scope().map_err(NativeError::Decider);
        let (entries, result) = match (block, cleanup) {
            (Ok(value), Ok(())) => value,
            (Err(e), Ok(())) => return Err(e),
            (Ok(_), Err(e)) => return Err(ExecutionError::Context(e)),
            (Err(e), Err(cleanup)) => {
                return Err(ExecutionError::Context(NativeError::Cleanup(format!(
                    "joined branch: {e:?}; cleanup: {cleanup:?}"
                ))));
            }
        };
        let result = VerificationResult::success().and_then(|| result);
        if !result.continue_verification() {
            return Ok(result);
        }
        if entries.is_empty() {
            return Ok(result.combine(VerificationResult::success, false));
        }
        let (assumptions, feasible) = joiner::joined_conditions(&entries, &factory);
        let state = match entries.as_slice() {
            [one] => one.state.clone(),
            [first, second] => {
                let merged = first
                    .state
                    .merge_recorded(
                        &first.path_conditions,
                        &second.state,
                        &second.path_conditions,
                        &factory,
                        false,
                        &mut |warning| self.warnings.push(warning),
                    )
                    .map_err(|e| ExecutionError::Context(NativeError::State(e)))?;
                if consolidate_join {
                    let choice = self
                        .consolidation_choice(&merged)
                        .map_err(ExecutionError::Context)?;
                    crate::rules::state_consolidator::consolidate(
                        &factory, self, merged, choice, false,
                    )
                    .map_err(|e| {
                        ExecutionError::Context(NativeError::Consolidation(format!(
                            "CFG join: {e:?}"
                        )))
                    })?
                } else {
                    merged
                }
            }
            _ => {
                return Err(ExecutionError::Context(NativeError::Unsupported(
                    "unexpected CFG join entries",
                )));
            }
        };
        for group in assumptions {
            for term in group {
                self.assume_term(&term).map_err(ExecutionError::Context)?;
            }
        }
        self.assume_term(&feasible)
            .map_err(ExecutionError::Context)?;
        let next = continuation(self, state)?;
        Ok(result.combine(|| next, false))
    }

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
        let joining_scope = self.open_joining_scope(&state)?;
        self.base
            .decider
            .push_scope()
            .map_err(NativeError::Decider)?;
        let mark = self.base.decider.pcs.mark();
        let mut state = state;
        state.under_join = true;
        let mut then_entries = Vec::<JoinDataEntry<PD, FD, JoinMode, T>>::new();
        let mut else_entries = Vec::<JoinDataEntry<PD, FD, JoinMode, T>>::new();
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
                    then_entries.push(JoinDataEntry {
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
                    else_entries.push(JoinDataEntry {
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
        self.close_logged_scope(joining_scope)?;
        let mut entries = then_entries;
        entries.extend(else_entries);
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
        Ok(Arc::new(self.native_empty_heap(&state.program, false)?))
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
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
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
            .map_err(NativeError::Decider)?;
        self.open_member_log(ferrum_silver::ast::program::Member::Function(
            function.clone(),
        ))?;
        self.active_function_snapshot = Some(data.phase_snapshot());
        Ok(())
    }
    fn complete_function_log(&mut self) -> Result<(), Self::Error> {
        self.close_member_log()
    }
    fn end_function(&mut self) -> Result<(), Self::Error> {
        self.active_function_snapshot = None;
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
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<Vec<crate::state::terms::Declaration>, Self::Error> {
        self.active_function_snapshot = Some(data.phase_snapshot());
        if self.options.mask_heap_mode {
            Ok(self.mask_function_frame(data)?.declarations(&self.factory))
        } else {
            Ok(vec![])
        }
    }
    fn build_phase_one_auxiliary_axioms(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<Vec<Term>, Self::Error> {
        let factory = self.factory.clone();
        let resources = if self.options.mask_heap_mode {
            Some(self.mask_resource_sequence(&data.program_function.pres, &data.program)?)
        } else {
            None
        };
        let auxiliary_axioms = if let Some(resources) = &resources {
            use crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding;
            let has_predicate_triggers = self
                .mask_recursive_predicate_triggers(data)?
                .iter()
                .next()
                .is_some();
            let info = self.mask_function_frame(data)?;
            let mut axioms = MaskHeapFunctionEncoding::frame_axioms(
                &factory,
                data,
                info.frame.clone(),
                resources.len(),
                has_predicate_triggers,
            )
            .map_err(|e| NativeError::Execution(format!("mask frame axioms: {e:?}")))?;
            let mut identifiers = self.base.identifiers.clone();
            let mut translator = NativeFrameTranslator {
                context: self,
                data,
                resources,
            };
            axioms.extend(
                MaskHeapFunctionEncoding::quantified_frame_axioms(
                    &factory,
                    &mut translator,
                    &mut identifiers,
                    data,
                    resources,
                    &info,
                )
                .map_err(|e| {
                    NativeError::Execution(format!("mask quantified frame axioms: {e:?}"))
                })?,
            );
            axioms
        } else {
            vec![]
        };
        Ok(auxiliary_axioms)
    }
    fn build_phase_one_post_axiom(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<(Option<Term>, Vec<Term>), Self::Error> {
        let factory = self.factory.clone();
        let resources = if self.options.mask_heap_mode {
            Some(self.mask_resource_sequence(&data.program_function.pres, &data.program)?)
        } else {
            None
        };
        let (posts, _) = self.translate_function_terms(data, false)?;
        let converter = self.base.symbol_converter.clone();
        let adapt = |term: Term| -> Result<Term, Self::Error> {
            if let Some(resources) = &resources {
                crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::adapt_axiom(
                    &factory, &converter, &term, resources, &data.state_args,
                ).map_err(|e| NativeError::Execution(format!("mask function axiom: {e:?}")))
            } else {
                Ok(term)
            }
        };
        let nested: Vec<_> = data
            .nested_definitional_axioms()
            .map_err(|e| NativeError::Execution(format!("function nested axioms: {e:?}")))?
            .into_iter()
            .collect();
        let post_axiom = data
            .post_axiom(&factory, &posts, &nested, &adapt)
            .map_err(|e| NativeError::Execution(format!("function post axiom: {e:?}")))?;
        Ok((post_axiom, posts))
    }
    fn build_phase_one_post_precondition_axioms(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
        posts: &[Term],
    ) -> Result<Vec<Term>, Self::Error> {
        let factory = self.factory.clone();
        let resources = if self.options.mask_heap_mode {
            Some(self.mask_resource_sequence(&data.program_function.pres, &data.program)?)
        } else {
            None
        };
        let converter = self.base.symbol_converter.clone();
        let adapt = |term: Term| -> Result<Term, Self::Error> {
            if let Some(resources) = &resources {
                crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::adapt_axiom(
                    &factory, &converter, &term, resources, &data.state_args,
                ).map_err(|e| NativeError::Execution(format!("mask function axiom: {e:?}")))
            } else {
                Ok(term)
            }
        };
        let post_precondition_axioms = data
            .post_precondition_axioms(
                &factory,
                posts,
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
                &adapt,
            )
            .map_err(|e| NativeError::Execution(format!("function post propagation: {e:?}")))?;
        Ok(post_precondition_axioms)
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
        self.active_function_snapshot = Some(data.phase_snapshot());
        crate::supporters::functions::function_verification_unit::check_function_body(
            self, data, paths,
        )
        .map_err(|e| NativeError::Execution(format!("function body phase: {e:?}")))
    }
    fn build_phase_two_definition(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
    ) -> Result<(Option<Term>, Option<Term>), Self::Error> {
        self.active_function_snapshot = Some(data.phase_snapshot());
        let calls = if self.options.mask_heap_mode {
            Vec::new()
        } else {
            ferrum_silver::ast::utility::functions::recursive_calls_and_surrounding_unfoldings(
                &data.program_function,
            )
            .map_err(|e| NativeError::Execution(format!("recursive function analysis: {e:?}")))?
        };
        let factory = self.factory.clone();
        let (_, body) = self.translate_function_terms(data, true)?;
        let mask_resources = if self.options.mask_heap_mode {
            Some(self.mask_resource_sequence(&data.program_function.pres, &data.program)?)
        } else {
            None
        };
        let mut predicate_triggers = crate::state::package::OrderedMap::<String, Term>::default();
        if body.is_some() && !self.options.mask_heap_mode {
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
                        if mask_resources.is_some() {
                            Sort::PredHeap
                        } else {
                            Sort::Snap
                        },
                    )
                    .map_err(NativeError::Sort)?;
                let location_exp = Exp::new(
                    ExpKind::PredicateAccess(location.clone()),
                    location.meta.clone(),
                );
                let snapshot = if let Some(resources) = &mask_resources {
                    crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::predicate_trigger_state_arg(
                        predicate, resources, &data.state_args,
                    ).map_err(|e| NativeError::Execution(format!("recursive predicate heap: {e:?}")))?
                } else {
                    replacing
                        .resolve_location(&translator, &location_exp, Sort::Snap)
                        .map_err(|e| {
                            NativeError::Execution(format!("recursive predicate snapshot: {e:?}"))
                        })?
                };
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
        if body.is_some() && self.options.mask_heap_mode {
            predicate_triggers = self.mask_recursive_predicate_triggers(data)?;
        }
        let nested: Vec<_> = data
            .nested_definitional_axioms()
            .map_err(|e| NativeError::Execution(format!("function nested axioms: {e:?}")))?
            .into_iter()
            .collect();
        let resources = mask_resources;
        let converter = self.base.symbol_converter.clone();
        let adapt = |term: Term| -> Result<Term, Self::Error> {
            if let Some(resources) = &resources {
                crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::adapt_axiom(
                    &factory, &converter, &term, resources, &data.state_args,
                ).map_err(|e| NativeError::Execution(format!("mask function axiom: {e:?}")))
            } else {
                Ok(term)
            }
        };
        let triggers = predicate_triggers
            .iter()
            .map(|(_, value)| value.clone())
            .collect::<Vec<_>>();
        let definition = data
            .definitional_axiom_with_encoding(
                &factory, body.clone(), &nested, &triggers,
                |body, triggers| {
                    if self.options.mask_heap_mode {
                        crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::definitional_axiom(
                            &factory, data, body, triggers,
                        ).map_err(|e| crate::supporters::functions::function_data::FunctionAxiomError::Adapt(
                            NativeError::Execution(format!("mask function definition: {e:?}"))))
                    } else {
                        crate::supporters::functions::function_encoding::DefaultFunctionEncoding::definitional_axiom(
                            &factory, data.arguments.clone(), body, data.function_application.clone(), data.trigger_application.clone(), triggers,
                        ).map_err(crate::supporters::functions::function_data::FunctionAxiomError::Transform)
                    }
                }, &adapt,
            )
            .map_err(|e| NativeError::Execution(format!("function definition: {e:?}")))?;
        Ok((definition, body))
    }
    fn build_phase_two_precondition_axioms(
        &mut self,
        data: &crate::supporters::functions::function_data::FunctionData<FD>,
        body: Option<&Term>,
    ) -> Result<Vec<Term>, Self::Error> {
        let factory = self.factory.clone();
        let resources = if self.options.mask_heap_mode {
            Some(self.mask_resource_sequence(&data.program_function.pres, &data.program)?)
        } else {
            None
        };
        let converter = self.base.symbol_converter.clone();
        let adapt = |term: Term| -> Result<Term, Self::Error> {
            if let Some(resources) = &resources {
                crate::supporters::functions::mask_heap_function_encoding::MaskHeapFunctionEncoding::adapt_axiom(&factory, &converter, &term, resources, &data.state_args)
                    .map_err(|e| NativeError::Execution(format!("mask function axiom: {e:?}")))
            } else {
                Ok(term)
            }
        };
        let propagation = data
            .body_precondition_axioms(
                &factory,
                body,
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
                &adapt,
            )
            .map_err(|e| NativeError::Execution(format!("function body propagation: {e:?}")))?;
        Ok(propagation)
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
        let disable_isc_triggers = self.options.disable_isc_triggers;
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
                disable_isc_triggers,
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
        let cached = (!state.exhale_ext && !self.options.disable_caches)
            .then(|| state.sm_cache.get(&key, None))
            .flatten()
            .map(|(definition, _)| definition.clone());
        let factory = self.factory.clone();
        let mut cache = state.sm_cache.clone();
        let definition = if let Some(cached) = cached {
            cached
        } else {
            let disable_isc_triggers = self.options.disable_isc_triggers;
            let (snapshot_map, value_definitions, domain_definitions) =
                crate::rules::quantified_chunk_support::summarise_snapshot_map(
                    &factory,
                    self,
                    state,
                    resource,
                    formals,
                    &chunks,
                    None,
                    true,
                    disable_isc_triggers,
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
            if !self.options.disable_value_map_caching {
                cache = cache.with_entry(key, definition.clone(), total, None);
            }
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
        self.failure_full(error, &state, false)
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
        let cached = (!state.exhale_ext && !self.options.disable_caches)
            .then(|| state.sm_cache.get(&key, None))
            .flatten()
            .map(|(definition, _)| definition.clone());
        let factory = self.factory.clone();
        let mut cache = state.sm_cache.clone();
        let definition = if let Some(definition) = cached {
            definition
        } else {
            let disable_isc_triggers = self.options.disable_isc_triggers;
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
                    disable_isc_triggers,
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
            if !self.options.disable_value_map_caching {
                cache = cache.with_entry(key, definition.clone(), total, None);
            }
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
        self.options.disable_chunk_order_heuristics
    }
    fn disable_quantified_triggers(&self) -> bool {
        self.options.disable_isc_triggers
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
        self.failure(&error.partial, reason, state)
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
        self.options.disable_isc_triggers
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
        self.options.disable_isc_triggers
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
        self.failure(&error.partial, reason, state)
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
        let cached = (!state.exhale_ext && !self.options.disable_caches)
            .then(|| state.sm_cache.get(&key, domain_condition))
            .flatten()
            .map(|(definition, _)| definition.clone());
        let factory = self.factory.clone();
        let mut cache = state.sm_cache.clone();
        let definition = if let Some(definition) = cached {
            definition
        } else {
            let disable_isc_triggers = self.options.disable_isc_triggers;
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
                    disable_isc_triggers,
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
            if !self.options.disable_value_map_caching {
                cache = cache.with_entry(key, definition.clone(), total, domain_condition.cloned());
            }
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
        self.options.disable_chunk_order_heuristics
    }
    fn disable_general_isc_triggers(&self) -> bool {
        self.options.disable_isc_triggers
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
        let cache_options = self.options.clone();
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
            cache_options.disable_isc_triggers,
            cache_options.disable_value_map_caching,
            cache_options.disable_caches,
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
        state: &State<PD, FD, JoinMode>,
        used: &ListBackedHeap,
        operations: &ListBackedHeap,
        lhs: &ListBackedHeap,
    ) -> Result<ListBackedHeap, Self::Error> {
        if self.options.mask_heap_mode {
            let merged = self.merge_native_mask_heaps(state, used, operations)?;
            self.merge_native_mask_heaps(state, &merged, lhs)
        } else {
            Ok(used.with_heap(operations).with_heap(lhs))
        }
    }
    fn empty_wand_heap(
        &mut self,
        state: &State<PD, FD, JoinMode>,
    ) -> Result<ListBackedHeap, Self::Error> {
        self.native_empty_heap(&state.program, true)
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
    fn applied_wand_snapshot(
        &mut self,
        factory: &TermFactory,
        wand: &Term,
        lhs: Term,
    ) -> Result<Term, Self::Error> {
        Ok(if self.options.mask_heap_mode {
            crate::rules::mask_heap_supporter::applied_wand_snapshot(factory, wand, lhs)
        } else {
            crate::rules::heap_supporter::applied_wand_snapshot(factory, wand, lhs)
        })
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
        if self.options.mask_heap_mode {
            let mut merged = heap.clone();
            for chunk in chunks {
                let singleton = ListBackedHeap::from_chunks(std::iter::once(chunk.clone()));
                merged = self.merge_native_mask_heaps(state, &merged, &singleton)?;
            }
            return Ok((state.function_recorder.clone(), merged));
        }
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
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        Ok(Arc::new(self.native_empty_heap(&state.program, true)?))
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
        if self.options.mask_heap_mode {
            let crate::state::terms::TermKind::MagicWandSnapshot(function) = snapshot.kind() else {
                return Err(NativeError::Chunk("expected magic wand snapshot".into()));
            };
            let at = self.factory.to_snap_tree(args.iter().cloned());
            let mask = self.factory.mask_add(
                self.factory.pred_zero_mask(),
                at.clone(),
                self.factory.full_perm(),
            );
            let heap = self
                .factory
                .heap_singleton(at, function.clone(), Sort::WandHeap);
            return Ok(Chunk::MaskHeap(crate::state::chunks::BasicMaskHeapChunk {
                resource_id: crate::resources::resources::ResourceId::MagicWand,
                resource: ResourceKey::Wand(id),
                mask,
                heap,
            }));
        }
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
        if let Some(summary) = (!self.options.disable_caches)
            .then(|| state.ss_cache.get(&key))
            .flatten()
            .cloned()
        {
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
        state: &State<PD, FD, JoinMode>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error> {
        Ok(Arc::new(self.native_empty_heap(&state.program, true)?))
    }
    fn output_cfg(&mut self, cfg: &SilverCfg) -> Result<(), Self::Error> {
        self.write_cfg_output(&format!("CFG{}.dot", cfg.output_id()), cfg)
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

impl<S: Prover, PD, FD: Clone>
    crate::rules::predicate_supporter::PredicateLeafQuantification<PD, FD, JoinMode>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn predicate_leaf_debugging(&self) -> bool {
        false
    }
    fn formal_resource_variables(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        resource: &ResourceKey,
    ) -> Result<Vec<Term>, Self::Error> {
        match resource {
            ResourceKey::Field(_) => Ok(vec![self.factory.predef_receiver_var()]),
            ResourceKey::Predicate(p) => state
                .predicate_formal_var_map
                .get(&p.name)
                .cloned()
                .ok_or(NativeError::Unsupported("predicate formal variables")),
            ResourceKey::Wand(w) => w
                .ghost_free_wand
                .magic_wand_subexpressions(&state.program)
                .map_err(|e| NativeError::Execution(format!("{e:?}")))?
                .iter()
                .enumerate()
                .map(|(i, exp)| {
                    let sort = self
                        .base
                        .symbol_converter
                        .to_sort(
                            &exp.typ()
                                .map_err(|e| NativeError::Diagnostic(format!("{e:?}")))?,
                        )
                        .map_err(NativeError::Sort)?;
                    Ok(self.factory.var(
                        crate::state::identifiers::Identifier::new(format!("x{i}")),
                        sort,
                        false,
                    ))
                })
                .collect(),
        }
    }
    fn assume_leaf_snapshot_definition(&mut self, definition: &Term) -> Result<(), Self::Error> {
        self.base
            .decider
            .assume([(definition.clone(), None)], false, true)
            .map_err(NativeError::Decider)
    }
}

impl<S: Prover, PD, FD: Clone>
    crate::rules::predicate_supporter::PredicateTreeServices<PD, FD, VerificationError>
    for NativeVerifierContext<S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn assume_predicate_contents(&mut self, assumptions: &[Term]) -> Result<(), Self::Error> {
        self.base
            .decider
            .assume(assumptions.iter().cloned().map(|t| (t, None)), false, false)
            .map_err(NativeError::Decider)
    }
    fn quantify_predicate_leaf_chunk(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        recorder: FunctionRecorder<FD>,
        chunk: Chunk,
    ) -> Result<(FunctionRecorder<FD>, Chunk), Self::Error> {
        let factory = self.factory.clone();
        crate::rules::predicate_supporter::quantify_predicate_leaf_chunk(
            &factory, self, state, recorder, chunk,
        )
        .map_err(|e| NativeError::Chunk(format!("predicate leaf quantification: {e:?}")))
    }
    fn merge_predicate_contents(
        &mut self,
        state: &State<PD, FD, JoinMode>,
        recorder: FunctionRecorder<FD>,
        heap: &ListBackedHeap,
    ) -> Result<(FunctionRecorder<FD>, ListBackedHeap), Self::Error> {
        let factory = self.factory.clone();
        let choice = self.consolidation_choice(state)?;
        crate::rules::state_consolidator::merge_heaps(
            &factory, self, state, recorder, &state.h, heap, choice,
        )
        .map_err(|e| NativeError::Consolidation(format!("predicate leaf merge: {e:?}")))
    }
    fn branch_predicate_contents(
        &mut self,
        state: State<PD, FD, JoinMode>,
        condition: Term,
        condition_exp: &(Exp, Option<Exp>),
        join: bool,
        left: crate::rules::predicate_supporter::PredicateContentsAction,
        right: crate::rules::predicate_supporter::PredicateContentsAction,
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
        if join
            && self.joined_branch_scheduler_enabled
            && state.parallelize_branches
            && self.joined_branch_scheduler.is_some()
        {
            let error = std::cell::RefCell::new(None);
            let result = self.join_owned_branches_parallel(
                state,
                condition,
                &condition_exp.0,
                condition_exp.1.as_ref(),
                super::verification_pool_manager::NativeJoinAction::Predicate(left),
                super::verification_pool_manager::NativeJoinAction::Predicate(right),
                false,
                &mut |context, state| match continuation(context, state) {
                    Ok(result) => Ok(result),
                    Err(e) => {
                        *error.borrow_mut() = Some(e);
                        Err(ExecutionError::Context(NativeError::ContinuationAbort))
                    }
                },
            );
            if let Some(error) = error.into_inner() {
                return Err(error);
            }
            return result.map_err(|e| match e {
                ExecutionError::Context(error) => PE::Service(error),
                other => PE::Service(NativeError::Execution(format!("predicate join: {other:?}"))),
            });
        }
        let error = std::cell::RefCell::new(None);
        let result = crate::rules::producer::ProductionContext::branch_production(
            self,
            state,
            condition,
            &condition_exp.0,
            condition_exp.1.as_ref(),
            join,
            false,
            &mut |ctx, state, done| {
                match crate::rules::predicate_supporter::execute_predicate_contents_action(
                    ctx,
                    state,
                    &left,
                    &mut |ctx, state| {
                        done(ctx, state)
                            .map_err(|e| PE::Service(NativeError::Production(format!("{e:?}"))))
                    },
                ) {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        if error.borrow().is_none() {
                            *error.borrow_mut() = Some(e);
                        }
                        Err(ProductionError::Context(NativeError::ContinuationAbort))
                    }
                }
            },
            &mut |ctx, state, done| {
                match crate::rules::predicate_supporter::execute_predicate_contents_action(
                    ctx,
                    state,
                    &right,
                    &mut |ctx, state| {
                        done(ctx, state)
                            .map_err(|e| PE::Service(NativeError::Production(format!("{e:?}"))))
                    },
                ) {
                    Ok(v) => Ok(v),
                    Err(e) => {
                        if error.borrow().is_none() {
                            *error.borrow_mut() = Some(e);
                        }
                        Err(ProductionError::Context(NativeError::ContinuationAbort))
                    }
                }
            },
            &mut |ctx, state| match continuation(ctx, state) {
                Ok(v) => Ok(v),
                Err(e) => {
                    if error.borrow().is_none() {
                        *error.borrow_mut() = Some(e);
                    }
                    Err(ProductionError::Context(NativeError::ContinuationAbort))
                }
            },
        );
        if let Some(e) = error.into_inner() {
            return Err(e);
        }
        result.map_err(|e| PE::Service(NativeError::Production(format!("{e:?}"))))
    }
}

struct NativeMaskMerge<'a, S: Prover, PD, FD> {
    context: &'a mut NativeVerifierContext<S, PD, FD>,
    state: &'a State<PD, FD, JoinMode>,
}
impl<S: Prover, PD, FD> crate::rules::mask_heap_supporter::MaskHeapMergeService
    for NativeMaskMerge<'_, S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn alias(&mut self, term: Term) -> Result<Term, Self::Error> {
        self.context.mask_term_alias(self.state, term)
    }
    fn assume_upper_bound(&mut self, mask: Term) -> Result<(), Self::Error> {
        let factory = self.context.factory.clone();
        let bound =
            crate::rules::mask_heap_supporter::upper_bound_assertion(&factory, mask, |sort| {
                self.context
                    .base
                    .decider
                    .fresh_variable(&factory, "$t", &sort, false, None)
                    .map_err(NativeError::Decider)
            })
            .map_err(|e| NativeError::Chunk(format!("mask upper bound: {e:?}")))?;
        self.context.assume_term(&bound)
    }
}

struct NativeMaskProduction<'a, S: Prover, PD, FD> {
    context: &'a mut NativeVerifierContext<S, PD, FD>,
    state: &'a State<PD, FD, JoinMode>,
    simplify_state: Option<&'a State<PD, FD, JoinMode>>,
}
impl<S: Prover, PD, FD> crate::rules::mask_heap_supporter::MaskHeapProductionService
    for NativeMaskProduction<'_, S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn fresh(&mut self, name: &str, sort: Sort) -> Result<Term, Self::Error> {
        self.context
            .base
            .decider
            .fresh_variable(&self.context.factory, name, &sort, false, None)
            .map_err(NativeError::Decider)
    }
    fn alias(&mut self, term: Term) -> Result<Term, Self::Error> {
        self.context.mask_term_alias(self.state, term)
    }
    fn assume(&mut self, term: Term) -> Result<(), Self::Error> {
        self.context.assume_term(&term)
    }
}

impl<S: Prover, PD, FD> crate::rules::mask_heap_supporter::MaskHeapConsumptionService
    for NativeMaskProduction<'_, S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn simplify_alias(&mut self, term: Term) -> Result<Term, Self::Error> {
        self.context
            .mask_term_alias(self.simplify_state.unwrap_or(self.state), term)
    }
    fn check(&mut self, term: Term, timeout_ms: i32) -> Result<bool, Self::Error> {
        self.context
            .base
            .decider
            .check(&term, Some(timeout_ms))
            .map_err(NativeError::Decider)
    }
    fn assert_goal(&mut self, term: Term) -> Result<bool, Self::Error> {
        let timeout = self.context.base.decider.assert_timeout;
        self.context
            .base
            .decider
            .assert_with(&term, timeout, |value| value)
            .map_err(NativeError::Decider)
    }
    fn transform_precondition(&mut self, term: Term) -> Result<Term, Self::Error> {
        let factory = self.context.factory.clone();
        crate::state::function_precondition_transformer::transform(&factory, &term, &mut |fun| {
            Ok::<_, Self::Error>(crate::rules::function_supporter::precondition_version(
                &factory, fun,
            ))
        })
        .map_err(|e| NativeError::Chunk(format!("mask precondition: {e:?}")))
    }
    fn assume_definition(&mut self, term: Term) -> Result<(), Self::Error> {
        self.context
            .base
            .decider
            .assume([(term, None)], false, true)
            .map_err(NativeError::Decider)
    }
}

/// Avoid nesting the same solver cleanup failure once per unwound branch scope.
/// Distinct cleanup failures remain attached in source order.
fn coalesce_evaluation_cleanup<E: std::fmt::Debug>(
    evaluation: EvaluationError<E>,
    cleanup: E,
) -> EvaluationError<E> {
    if let EvaluationError::TriggerCleanup { cleanup: prior, .. } = &evaluation {
        if format!("{prior:?}") == format!("{cleanup:?}") {
            return evaluation;
        }
    }
    EvaluationError::TriggerCleanup {
        evaluation: Box::new(evaluation),
        cleanup,
    }
}

#[cfg(test)]
mod cleanup_coalescing_tests {
    use super::{EvaluationError, coalesce_evaluation_cleanup};

    #[test]
    fn coalesces_only_adjacent_equal_cleanup_failures() {
        let primary = EvaluationError::Context("primary".to_string());
        let first = coalesce_evaluation_cleanup(primary, "closed".to_string());
        let duplicate = coalesce_evaluation_cleanup(first, "closed".to_string());
        let distinct = coalesce_evaluation_cleanup(duplicate, "different".to_string());
        match distinct {
            EvaluationError::TriggerCleanup {
                evaluation,
                cleanup,
            } => {
                assert_eq!(cleanup, "different");
                match *evaluation {
                    EvaluationError::TriggerCleanup {
                        evaluation,
                        cleanup,
                    } => {
                        assert_eq!(cleanup, "closed");
                        assert!(
                            matches!(*evaluation, EvaluationError::Context(ref e) if e == "primary")
                        );
                    }
                    _ => panic!("original cleanup was lost"),
                }
            }
            _ => panic!("distinct cleanup was lost"),
        }
    }
}

struct NativeMaskQuantified<'a, S: Prover, PD, FD> {
    context: &'a mut NativeVerifierContext<S, PD, FD>,
    state: &'a State<PD, FD, JoinMode>,
    recorder: FunctionRecorder<FD>,
}
impl<S: Prover, PD, FD> crate::rules::mask_heap_supporter::MaskHeapProductionService
    for NativeMaskQuantified<'_, S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    type Error = NativeError<S::Error>;
    fn fresh(&mut self, name: &str, sort: Sort) -> Result<Term, Self::Error> {
        self.context
            .base
            .decider
            .fresh_variable(&self.context.factory, name, &sort, false, None)
            .map_err(NativeError::Decider)
    }
    fn alias(&mut self, term: Term) -> Result<Term, Self::Error> {
        self.context.mask_term_alias(self.state, term)
    }
    fn assume(&mut self, term: Term) -> Result<(), Self::Error> {
        self.context.assume_term(&term)
    }
}
impl<S: Prover, PD, FD: Clone> crate::rules::mask_heap_supporter::MaskQuantifiedProductionService
    for NativeMaskQuantified<'_, S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn fresh_inverse(
        &mut self,
        input: &crate::rules::mask_heap_supporter::MaskQuantifiedInputs,
    ) -> Result<
        (
            crate::rules::quantified_chunk_support::InverseFunctions,
            Vec<Term>,
        ),
        Self::Error,
    > {
        let factory = self.context.factory.clone();
        let additional = self
            .state
            .relevant_quantified_variables_in(&input.arguments)
            .map_err(|e| NativeError::Chunk(format!("mask quantified variables: {e:?}")))?
            .into_iter()
            .map(|(t, _)| t)
            .collect();
        let mut state_vars = Vec::new();
        for (var, _) in &self.state.quantified_variables {
            let mut occurs = input
                .condition
                .contains(var)
                .map_err(|e| NativeError::Chunk(format!("mask variable: {e:?}")))?;
            for arg in &input.arguments {
                if arg
                    .contains(var)
                    .map_err(|e| NativeError::Chunk(format!("mask variable: {e:?}")))?
                {
                    occurs = true;
                    break;
                }
            }
            if occurs {
                state_vars.push(var.clone());
            }
        }
        let condition = factory.and([
            input.condition.clone(),
            factory.is_positive_perm(input.permission.clone()),
        ]);
        let disabled = self.context.options.disable_isc_triggers;
        crate::rules::quantified_chunk_support::fresh_inverse_functions(
            &factory,
            self.context,
            &input.qvars,
            input.qvar_expressions.clone(),
            condition,
            input.arguments.clone(),
            input.argument_expressions.clone(),
            &input.formal_qvars,
            additional,
            &state_vars,
            input.explicit_triggers.as_deref(),
            &input.qid,
            disabled,
        )
        .map_err(|e| NativeError::Chunk(format!("mask inverse: {e:?}")))
    }
    fn injectivity(
        &mut self,
        input: &crate::rules::mask_heap_supporter::MaskQuantifiedInputs,
    ) -> Result<Term, Self::Error> {
        crate::rules::quantified_chunk_support::injectivity_axiom(
            &self.context.factory,
            &input.qvars,
            &input.condition,
            &input.permission,
            &input.arguments,
            vec![],
            &input.qid,
        )
        .map_err(|e| NativeError::Chunk(format!("mask injectivity: {e:?}")))
    }
    fn transform_precondition(&mut self, term: Term) -> Result<Term, Self::Error> {
        let factory = self.context.factory.clone();
        crate::state::function_precondition_transformer::transform(&factory, &term, &mut |fun| {
            Ok::<_, Self::Error>(crate::rules::function_supporter::precondition_version(
                &factory, fun,
            ))
        })
        .map_err(|e| NativeError::Chunk(format!("mask precondition: {e:?}")))
    }
    fn assert_goal(&mut self, term: Term) -> Result<bool, Self::Error> {
        let timeout = self.context.base.decider.assert_timeout;
        self.context
            .base
            .decider
            .assert_with(&term, timeout, |v| v)
            .map_err(NativeError::Decider)
    }
    fn assume_definition(&mut self, term: Term) -> Result<(), Self::Error> {
        self.context
            .base
            .decider
            .assume([(term, None)], false, true)
            .map_err(NativeError::Decider)
    }
    fn no_triggers(&mut self, quantifier: &Exp) -> Result<(), Self::Error> {
        let message = format!(
            "No triggers available for quantifier at {}",
            quantifier.metadata().position
        );
        if let Some(reporter) = &self.context.preprocessing_reporter {
            reporter
                .report(ferrum_silver::reporter::message::Message::Simple {
                    kind: ferrum_silver::reporter::message::SimpleMessageKind::InternalWarning,
                    text: message,
                })
                .map_err(|e| {
                    NativeError::Diagnostic(format!("mask trigger warning reporter: {e:?}"))
                })?;
        } else {
            self.context.warnings.push(message);
        }
        Ok(())
    }
    fn record_inverse_and_mask(
        &mut self,
        inverse: crate::rules::quantified_chunk_support::InverseFunctions,
        mask: Term,
        definition: Term,
    ) -> Result<(), Self::Error> {
        self.recorder = self
            .recorder
            .record_field_inv(inverse)
            .record_constrained_var(mask, definition);
        Ok(())
    }
}

impl<S: Prover, PD, FD: Clone> crate::rules::mask_heap_supporter::MaskHeapConsumptionService
    for NativeMaskQuantified<'_, S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn check(&mut self, term: Term, timeout_ms: i32) -> Result<bool, Self::Error> {
        self.context
            .base
            .decider
            .check(&term, Some(timeout_ms))
            .map_err(NativeError::Decider)
    }
    fn assert_goal(&mut self, term: Term) -> Result<bool, Self::Error> {
        <Self as crate::rules::mask_heap_supporter::MaskQuantifiedProductionService>::assert_goal(
            self, term,
        )
    }
    fn transform_precondition(&mut self, term: Term) -> Result<Term, Self::Error> {
        <Self as crate::rules::mask_heap_supporter::MaskQuantifiedProductionService>::transform_precondition(self, term)
    }
    fn assume_definition(&mut self, term: Term) -> Result<(), Self::Error> {
        <Self as crate::rules::mask_heap_supporter::MaskQuantifiedProductionService>::assume_definition(self, term)
    }
}
impl<S: Prover, PD, FD: Clone> crate::rules::mask_heap_supporter::MaskQuantifiedConsumptionService
    for NativeMaskQuantified<'_, S, PD, FD>
where
    S::Error: std::fmt::Debug,
{
    fn fresh_inverse(
        &mut self,
        input: &crate::rules::mask_heap_supporter::MaskQuantifiedInputs,
    ) -> Result<
        (
            crate::rules::quantified_chunk_support::InverseFunctions,
            Vec<Term>,
        ),
        Self::Error,
    > {
        <Self as crate::rules::mask_heap_supporter::MaskQuantifiedProductionService>::fresh_inverse(
            self, input,
        )
    }
    fn injectivity(
        &mut self,
        input: &crate::rules::mask_heap_supporter::MaskQuantifiedInputs,
    ) -> Result<Term, Self::Error> {
        <Self as crate::rules::mask_heap_supporter::MaskQuantifiedProductionService>::injectivity(
            self, input,
        )
    }
    fn record_inverse_and_mask(
        &mut self,
        inverse: crate::rules::quantified_chunk_support::InverseFunctions,
        mask: Term,
        definition: Term,
    ) -> Result<(), Self::Error> {
        <Self as crate::rules::mask_heap_supporter::MaskQuantifiedProductionService>::record_inverse_and_mask(self, inverse, mask, definition)
    }
}

#[cfg(test)]
mod owned_branch_worker_tests {
    use super::*;
    use crate::{
        config::Config,
        decider::z3_prover_std_io,
        rules::{brancher::BranchTransferSnapshot, evaluator::EvaluationBranchAction},
        verifier::verification_pool_manager::{
            NativeEvaluationBranch, NativeWorkerOutput, NativeWorkerTarget, NativeWorkerTask,
            ThreadBoundWorker, ThreadVerificationPool, native_method_worker,
        },
    };

    #[test]
    fn real_pool_runs_owned_evaluation_branch() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        let config = Config::default();
        let options = NativeOptions::from_config(&config).unwrap();
        let factory = TermFactory::new(crate::state::terms::TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let make = |id: String, factory: TermFactory| {
            let prover = z3_prover_std_io::new(
                id.clone(),
                z3_prover_std_io::settings(std::path::PathBuf::from(&z3)),
                factory.clone(),
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            native_method_worker(id, prover, identifiers, factory, options.clone(), &config)
        };
        let mut source = make("source".into(), factory.clone());
        source.start().unwrap();
        source
            .context
            .base
            .decider
            .set_options(
                [("smt.random_seed".into(), "42".into())]
                    .into_iter()
                    .collect(),
            )
            .unwrap();
        source.context.base.decider.push_scope().unwrap();
        let variable = factory.var(
            crate::state::identifiers::Identifier::new("ownedBranchInput"),
            Sort::Bool,
            false,
        );
        let declaration = factory.function_decl_target(
            crate::state::terms::ApplicationTarget::Variable(variable.clone()),
        );
        source
            .context
            .base
            .decider
            .declare_fresh_functions([declaration])
            .unwrap();
        source
            .context
            .base
            .decider
            .assume([(variable.clone(), None)], false, false)
            .unwrap();
        let mark = source.context.base.decider.pcs.mark();
        let snapshot = BranchTransferSnapshot::capture(&source.context.base.decider, 0);
        let program = ferrum_silver::ast::program::Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Default::default(),
        );
        let analysis = Arc::new(NativeWorkerAnalysis {
            program: program.clone(),
            function_owners: vec![],
            function_handles: Default::default(),
            predicates: Default::default(),
            snapshot_sorts: Default::default(),
            snapshot_formals: Default::default(),
            function_heights: Default::default(),
            function_fresh_variables: vec![],
            failed_functions: Default::default(),
        });
        let mut state = State::new(
            program,
            Default::default(),
            Default::default(),
            config.more_joins,
            &factory,
            false,
            false,
        );
        state.under_join = true;
        let local_exp = Exp::new(
            ExpKind::LocalVar(ferrum_silver::ast::expression::LocalVar::new(
                "branchInput".into(),
                ferrum_silver::ast::r#type::Type::Bool,
                Default::default(),
            )),
            Default::default(),
        );
        state.g = Arc::new(state.g.with_binding(
            crate::state::store::AbstractLocalVar::new(local_exp.clone()),
            (variable, None),
        ));
        let conditional = Exp::new(
            ExpKind::CondExp(
                local_exp,
                Exp::new(ExpKind::TrueLit, Default::default()),
                Exp::new(ExpKind::FalseLit, Default::default()),
            ),
            Default::default(),
        );
        let branch = NativeEvaluationBranch {
            source_worker_id: "source".into(),
            snapshot,
            state: state.clone(),
            initial_state: state,
            mark,
            condition: factory.boolean(true),
            original: Exp::new(ExpKind::TrueLit, Default::default()),
            rewritten: None,
            action: EvaluationBranchAction::Evaluate { expression: conditional, error: ferrum_silver::verifier::verification_error::PartialVerificationError::for_kind(ferrum_silver::verifier::verification_error::VerificationErrorKind::Internal(None)) },
        };
        let local = source
            .context
            .verify_worker_evaluation_branch(&analysis, branch.clone())
            .unwrap();
        assert!(!local.result.is_fatal());
        assert_eq!(local.entries.len(), 1);
        assert!(local.declarations.functions.is_empty());
        let cancelled_branch = branch.clone();
        let cancelled_analysis = analysis.clone();
        let cancellation =
            crate::verifier::verification_pool_manager::CancellationController::default();
        let worker_cancellation = cancellation.clone();
        let pool_z3 = std::path::PathBuf::from(z3);
        let pool_factory = factory.clone();
        let pool_options = options.clone();
        let pool_config = config.clone();
        struct OptionCheckedWorker(
            crate::verifier::verification_pool_manager::NativeMethodWorker<
                crate::decider::prover_std_io::ProverStdIo,
            >,
        );
        impl ThreadBoundWorker for OptionCheckedWorker {
            type Error = <crate::verifier::verification_pool_manager::NativeMethodWorker<
                crate::decider::prover_std_io::ProverStdIo,
            > as ThreadBoundWorker>::Error;
            type Broadcast = <crate::verifier::verification_pool_manager::NativeMethodWorker<
                crate::decider::prover_std_io::ProverStdIo,
            > as ThreadBoundWorker>::Broadcast;
            type BroadcastResult = <crate::verifier::verification_pool_manager::NativeMethodWorker<
                crate::decider::prover_std_io::ProverStdIo,
            > as ThreadBoundWorker>::BroadcastResult;
            type Task = NativeWorkerTask;
            type Output = NativeWorkerOutput;
            fn start(&mut self) -> Result<(), Self::Error> {
                self.0.start()?;
                self.0
                    .context
                    .base
                    .decider
                    .set_options(
                        [("smt.random_seed".into(), "43".into())]
                            .into_iter()
                            .collect(),
                    )
                    .map_err(NativeError::Decider)
            }
            fn broadcast(
                &mut self,
                value: Self::Broadcast,
            ) -> Result<Self::BroadcastResult, Self::Error> {
                self.0.broadcast(value)
            }
            fn verify(&mut self, task: Self::Task) -> Result<Self::Output, Self::Error> {
                let result = self.0.verify(task);
                assert_eq!(
                    self.0
                        .context
                        .base
                        .decider
                        .options()
                        .get("smt.random_seed")
                        .map(String::as_str),
                    Some("43")
                );
                result
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                self.0.reset()
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                self.0.stop()
            }
        }
        let mut pool = ThreadVerificationPool::start(1, move |id| {
            let name = format!("worker-{id}");
            let prover = z3_prover_std_io::new(
                name.clone(),
                z3_prover_std_io::settings(pool_z3.clone()),
                pool_factory.clone(),
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            let mut worker = native_method_worker(
                name,
                prover,
                identifiers,
                pool_factory.clone(),
                pool_options.clone(),
                &pool_config,
            );
            worker.set_cancellation(worker_cancellation.clone());
            Ok(OptionCheckedWorker(worker))
        })
        .unwrap();
        let output = pool
            .submit(NativeWorkerTask {
                analysis,
                target: NativeWorkerTarget::EvaluationBranch(Box::new(branch)),
                reporter: None,
                warning_sink: None,
            })
            .unwrap()
            .wait()
            .unwrap();
        let NativeWorkerOutput::EvaluationBranch(output) = output else {
            panic!("unexpected worker output")
        };
        assert!(!output.result.is_fatal());
        assert_eq!(output.entries.len(), 1);
        assert_eq!(output.entries[0].data.0, factory.boolean(true));
        assert!(output.declarations.functions.is_empty());
        cancellation.cancel();
        let cancelled = pool
            .submit(NativeWorkerTask {
                analysis: cancelled_analysis,
                target: NativeWorkerTarget::EvaluationBranch(Box::new(cancelled_branch)),
                reporter: None,
                warning_sink: None,
            })
            .unwrap()
            .wait();
        assert!(matches!(
            cancelled,
            Err(
                crate::verifier::verification_pool_manager::ThreadPoolError::Worker(
                    NativeError::Cancelled
                )
            )
        ));
        pool.shutdown().unwrap();
        source.context.base.decider.pop_scope().unwrap();
        source.stop().unwrap();
    }
}

#[cfg(test)]
mod queued_cfg_isolation_tests {
    use super::*;
    use crate::{
        config::Config,
        decider::{prover_std_io::ProverStdIo, z3_prover_std_io},
        rules::{brancher::BranchTransferSnapshot, executor::CfgJoinBranch},
        verifier::verification_pool_manager::{
            NativeJoinJob, NativeMethodWorker, NativeWorkerOutput, NativeWorkerTarget,
            NativeWorkerTask, ThreadBoundWorker, ThreadVerificationPool, WorkerPreambleCommand,
            WorkerQueueHandle, execute_intervening_native_worker_task, execute_native_worker_task,
            native_method_worker,
        },
    };
    use ferrum_silver::frontend::{
        frontend::FrontendPhases,
        sil_front_end_config::SilFrontendConfig,
        sil_frontend::{SilFrontendPhases, standard_plugin_manager},
    };
    use std::sync::{Condvar, Mutex};

    enum Job {
        Parent(NativeWorkerTask),
        CancelParent(NativeWorkerTask),
        Remote(NativeWorkerTask),
        Intervening(NativeWorkerTask),
        OwnSequence {
            foreign: NativeWorkerTask,
            own: NativeWorkerTask,
        },
        Inline(NativeWorkerTask),
    }
    struct TestWorker {
        native: NativeMethodWorker<ProverStdIo>,
        started: Arc<(Mutex<bool>, Condvar)>,
        parent_ready: std::sync::mpsc::Sender<()>,
        release_tx: std::sync::mpsc::Sender<()>,
        release_rx: Arc<Mutex<std::sync::mpsc::Receiver<()>>>,
        requirement: Term,
    }
    impl ThreadBoundWorker for TestWorker {
        type Error =
            NativeError<<ProverStdIo as crate::interfaces::decider::prover::TextEmitter>::Error>;
        type Broadcast = WorkerPreambleCommand;
        type BroadcastResult = Option<String>;
        type Task = Job;
        type Output = bool;
        fn start(&mut self) -> Result<(), Self::Error> {
            self.native.start()?;
            assert_eq!(
                self.native
                    .context
                    .base
                    .decider
                    .prover
                    .push_pop_scope_depth(),
                0
            );
            self.native
                .context
                .base
                .decider
                .set_options(
                    [("smt.random_seed".into(), "42".into())]
                        .into_iter()
                        .collect(),
                )
                .map_err(NativeError::Decider)
        }
        fn broadcast(
            &mut self,
            command: Self::Broadcast,
        ) -> Result<Self::BroadcastResult, Self::Error> {
            self.native.broadcast(command)
        }
        fn verify(&mut self, _: Job) -> Result<bool, Self::Error> {
            Err(NativeError::Unsupported("missing cooperative queue"))
        }
        fn verify_cooperative(
            &mut self,
            job: Job,
            queue: &WorkerQueueHandle<Self>,
        ) -> Result<bool, Self::Error> {
            self.native.ensure_preamble_frame()?;
            match job {
                Job::Parent(remote) => {
                    let future = queue
                        .submit(Job::Remote(remote))
                        .map_err(|e| NativeError::Diagnostic(format!("submit: {e:?}")))?;
                    let (lock, wake) = &*self.started;
                    let mut started = lock.lock().unwrap();
                    while !*started {
                        started = wake.wait(started).unwrap();
                    }
                    drop(started);
                    // A method's precondition is produced in the first member scope.
                    self.native
                        .context
                        .base
                        .decider
                        .push_scope()
                        .map_err(NativeError::Decider)?;
                    assert_eq!(
                        self.native
                            .context
                            .base
                            .decider
                            .prover
                            .push_pop_scope_depth(),
                        2
                    );
                    let requirement = self.requirement.clone();
                    self.native
                        .context
                        .base
                        .decider
                        .assume([(requirement.clone(), None)], false, false)
                        .map_err(NativeError::Decider)?;
                    self.native
                        .context
                        .base
                        .errors_reported
                        .store(7, std::sync::atomic::Ordering::SeqCst);
                    self.parent_ready.send(()).unwrap();
                    let waited = queue.wait_cooperatively_with(future, |work| match work {
                        Job::Intervening(task) => {
                            let output = execute_intervening_native_worker_task(
                                &mut self.native.context,
                                task,
                            )?;
                            let NativeWorkerOutput::Member(results) = output else {
                                return Err(NativeError::Unsupported(
                                    "unexpected intervening output",
                                ));
                            };
                            let failed = results.iter().any(|r| r.is_fatal());
                            self.release_tx.send(()).unwrap();
                            Ok(failed)
                        }
                        _ => Err(NativeError::Unsupported("unexpected cooperative task")),
                    });
                    assert!(waited.executed_other_task);
                    assert!(!waited.awaited_executed_on_current_worker);
                    assert!(
                        waited
                            .result
                            .map_err(|e| NativeError::Diagnostic(format!("wait: {e:?}")))?
                    );
                    assert!(
                        self.native
                            .context
                            .base
                            .decider
                            .prover
                            .assert_goal(&requirement, None)
                            .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?
                    );
                    assert_eq!(
                        self.native
                            .context
                            .base
                            .decider
                            .options()
                            .get("smt.random_seed")
                            .map(String::as_str),
                        Some("42")
                    );
                    assert_eq!(
                        self.native
                            .context
                            .base
                            .errors_reported
                            .load(std::sync::atomic::Ordering::SeqCst),
                        7
                    );
                    self.native
                        .context
                        .base
                        .decider
                        .pop_scope()
                        .map_err(NativeError::Decider)?;
                    Ok(true)
                }
                Job::OwnSequence { foreign, mut own } => {
                    self.native
                        .context
                        .base
                        .decider
                        .push_scope()
                        .map_err(NativeError::Decider)?;
                    let opposite = self.native.context.factory.not(self.requirement.clone());
                    self.native
                        .context
                        .base
                        .decider
                        .assume([(opposite.clone(), None)], false, false)
                        .map_err(NativeError::Decider)?;
                    let mark = self.native.context.base.decider.pcs.mark();
                    let NativeWorkerTarget::Join(job) = &mut own.target else {
                        return Err(NativeError::Unsupported("expected own CFG job"));
                    };
                    job.source_worker_id = self.native.context.base.unique_id.clone();
                    job.snapshot =
                        BranchTransferSnapshot::capture(&self.native.context.base.decider, 0);
                    job.mark = mark;
                    job.replay_check = Some(opposite.clone());
                    let _foreign = queue
                        .submit(Job::Inline(foreign))
                        .map_err(|e| NativeError::Diagnostic(format!("foreign submit: {e:?}")))?;
                    let own = queue
                        .submit(Job::Inline(own))
                        .map_err(|e| NativeError::Diagnostic(format!("own submit: {e:?}")))?;
                    let waited = queue.wait_cooperatively_with(own, |job| match job {
                        Job::Inline(task) => {
                            let output =
                                execute_native_worker_task(&mut self.native.context, task)?;
                            let NativeWorkerOutput::Join(output) = output else {
                                return Err(NativeError::Unsupported("unexpected branch output"));
                            };
                            let restored = self
                                .native
                                .context
                                .base
                                .decider
                                .prover
                                .assert_goal(&opposite, None)
                                .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
                            assert!(
                                restored,
                                "foreign branch replaced parent path before own else"
                            );
                            Ok(!output.result.is_fatal())
                        }
                        _ => Err(NativeError::Unsupported("unexpected queued task")),
                    });
                    assert!(
                        waited.executed_other_task && waited.awaited_executed_on_current_worker
                    );
                    let result = waited
                        .result
                        .map_err(|e| NativeError::Diagnostic(format!("wait: {e:?}")))?;
                    self.native
                        .context
                        .base
                        .decider
                        .pop_scope()
                        .map_err(NativeError::Decider)?;
                    Ok(result)
                }
                Job::CancelParent(remote) => {
                    let future = queue
                        .submit(Job::Remote(remote))
                        .map_err(|e| NativeError::Diagnostic(format!("submit: {e:?}")))?;
                    let (lock, wake) = &*self.started;
                    let mut started = lock.lock().unwrap();
                    while !*started {
                        started = wake.wait(started).unwrap();
                    }
                    drop(started);
                    self.release_tx.send(()).unwrap();
                    let waited = queue.wait_cooperatively_with(future, |_| {
                        Err(NativeError::Unsupported("unexpected queued task"))
                    });
                    match waited.result {
                        Err(
                            crate::verifier::verification_pool_manager::ThreadPoolError::Worker(
                                NativeError::Cancelled,
                            ),
                        ) => Err(NativeError::Cancelled),
                        Err(e) => Err(NativeError::Diagnostic(format!(
                            "unexpected wait failure: {e:?}"
                        ))),
                        Ok(_) => Err(NativeError::Unsupported("cancelled branch succeeded")),
                    }
                }
                Job::Remote(task) => {
                    let (lock, wake) = &*self.started;
                    *lock.lock().unwrap() = true;
                    wake.notify_all();
                    self.release_rx.lock().unwrap().recv().unwrap();
                    let output = execute_native_worker_task(&mut self.native.context, task)?;
                    let NativeWorkerOutput::Join(output) = output else {
                        return Err(NativeError::Unsupported("unexpected CFG branch output"));
                    };
                    let retained = self
                        .native
                        .context
                        .base
                        .decider
                        .prover
                        .assert_goal(&self.requirement, None)
                        .map_err(|e| NativeError::Decider(DeciderError::Prover(e)))?;
                    Ok(!output.result.is_fatal() && output.entries.len() == 1 && !retained)
                }
                Job::Intervening(_) | Job::Inline(_) => {
                    Err(NativeError::Unsupported("unexpected top-level task"))
                }
            }
        }
        fn reset(&mut self) -> Result<(), Self::Error> {
            self.native.reset()?;
            assert_eq!(
                self.native
                    .context
                    .base
                    .decider
                    .prover
                    .push_pop_scope_depth(),
                0
            );
            self.native
                .context
                .base
                .decider
                .set_options(
                    [("smt.random_seed".into(), "42".into())]
                        .into_iter()
                        .collect(),
                )
                .map_err(NativeError::Decider)
        }
        fn stop(&mut self) -> Result<(), Self::Error> {
            self.native.stop()
        }
    }

    #[test]
    fn cooperative_cfg_join_isolates_queued_members_and_cfgs() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        let config = Config::default();
        let options = NativeOptions::from_config(&config).unwrap();
        let factory = TermFactory::new(crate::state::terms::TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let mut phases = SilFrontendPhases::new(
            std::path::PathBuf::from("queued.vpr"),
            standard_plugin_manager(&SilFrontendConfig::new("test")).unwrap(),
        );
        let parsed = phases
            .parse("domain D { function f(): Int } method unrelated() { assert f() == 0; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        let method = program.methods[0].clone();
        let cfg = ferrum_silver::cfg::silver::cfg_generator::statement_to_cfg(
            method.body.as_ref().unwrap(),
            true,
            true,
        )
        .unwrap();
        let analysis = Arc::new(NativeWorkerAnalysis {
            program: program.clone(),
            function_owners: vec![],
            function_handles: Default::default(),
            predicates: Default::default(),
            snapshot_sorts: Default::default(),
            snapshot_formals: Default::default(),
            function_heights: Default::default(),
            function_fresh_variables: vec![],
            failed_functions: Default::default(),
        });
        let mut source = {
            let prover = z3_prover_std_io::new(
                "source".into(),
                z3_prover_std_io::settings(std::path::PathBuf::from(&z3)),
                factory.clone(),
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            native_method_worker(
                "source".into(),
                prover,
                identifiers,
                factory.clone(),
                options.clone(),
                &config,
            )
        };
        source.start().unwrap();
        source.ensure_preamble_frame().unwrap();
        let applicable = source
            .context
            .base
            .symbol_converter
            .domain_function(&analysis.program.domains[0].functions[0], &analysis.program)
            .unwrap();
        let declaration = factory.function_decl(applicable.clone());
        let requirement = factory.equals(factory.app(applicable, vec![]), factory.int_literal(0));
        source
            .broadcast(WorkerPreambleCommand::Declare(declaration.clone()))
            .unwrap();
        source.context.base.decider.push_scope().unwrap();
        source
            .context
            .base
            .decider
            .assume([(requirement.clone(), None)], false, false)
            .unwrap();
        let mark = source.context.base.decider.pcs.mark();
        let snapshot = BranchTransferSnapshot::capture(&source.context.base.decider, 0);
        let mut state = State::new(
            program,
            Default::default(),
            Default::default(),
            config.more_joins,
            &factory,
            false,
            false,
        );
        state.under_join = true;
        let from = ferrum_silver::cfg::block::Block::statement(vec![]);
        let join = ferrum_silver::cfg::block::Block::statement(vec![]);
        let edge = ferrum_silver::cfg::edge::Edge::Unconditional {
            source: from,
            target: join.clone(),
            kind: ferrum_silver::cfg::edge::Kind::Normal,
        };
        let action = CfgJoinBranch::for_test(edge, join);
        for use_cfg in [false, true] {
            let started = Arc::new((Mutex::new(false), Condvar::new()));
            let inspect_started = started.clone();
            let (ready_tx, ready_rx) = std::sync::mpsc::channel();
            let (release_tx, release_rx) = std::sync::mpsc::channel();
            let release_rx = Arc::new(Mutex::new(release_rx));
            let worker_requirement = requirement.clone();
            let worker_factory = factory.clone();
            let worker_options = options.clone();
            let worker_config = config.clone();
            let path = std::path::PathBuf::from(&z3);
            let mut pool = ThreadVerificationPool::start(2, move |id| {
                let name = format!("queued-{id}");
                let prover = z3_prover_std_io::new(
                    name.clone(),
                    z3_prover_std_io::settings(path.clone()),
                    worker_factory.clone(),
                    |_| {},
                );
                let identifiers = prover.identifier_factory();
                Ok(TestWorker {
                    native: native_method_worker(
                        name,
                        prover,
                        identifiers,
                        worker_factory.clone(),
                        worker_options.clone(),
                        &worker_config,
                    ),
                    started: started.clone(),
                    parent_ready: ready_tx.clone(),
                    release_tx: release_tx.clone(),
                    release_rx: release_rx.clone(),
                    requirement: worker_requirement.clone(),
                })
            })
            .unwrap();
            for epoch in 0..2 {
                if epoch != 0 {
                    pool.reset().unwrap();
                }
                pool.broadcast(WorkerPreambleCommand::Declare(declaration.clone()))
                    .unwrap();
                *inspect_started.0.lock().unwrap() = false;
                let remote = NativeWorkerTask {
                    analysis: analysis.clone(),
                    target: NativeWorkerTarget::Join(Box::new(NativeJoinJob {
                        source_worker_id: "source".into(),
                        snapshot: snapshot.clone(),
                        state: state.clone(),
                        mark,
                        condition: factory.boolean(true),
                        original: Exp::new(ExpKind::TrueLit, Default::default()),
                        rewritten: None,
                        action: crate::verifier::verification_pool_manager::NativeJoinAction::Cfg(
                            action.clone(),
                        ),
                        after_start: None,
                        replay_check: Some(requirement.clone()),
                    })),
                    reporter: None,
                    warning_sink: None,
                };
                let parent = pool.submit(Job::Parent(remote)).unwrap();
                ready_rx.recv().unwrap();
                let target = if use_cfg {
                    NativeWorkerTarget::Cfg(cfg.clone())
                } else {
                    NativeWorkerTarget::Method(method.clone())
                };
                let intervening = pool
                    .submit(Job::Intervening(NativeWorkerTask {
                        analysis: analysis.clone(),
                        target,
                        reporter: None,
                        warning_sink: None,
                    }))
                    .unwrap();
                assert!(parent.wait().unwrap());
                assert!(
                    intervening.wait().unwrap(),
                    "unrelated task inherited suspended state: cfg={use_cfg}, epoch={epoch}"
                );
            }
            pool.shutdown().unwrap();
        }
        // A parent can help a foreign branch before its own queued else runs.
        // The foreign branch must restore the parent's contradictory path first.
        {
            let make_job = || NativeWorkerTask {
                analysis: analysis.clone(),
                target: NativeWorkerTarget::Join(Box::new(NativeJoinJob {
                    source_worker_id: "source".into(),
                    snapshot: snapshot.clone(),
                    state: state.clone(),
                    mark,
                    condition: factory.boolean(true),
                    original: Exp::new(ExpKind::TrueLit, Default::default()),
                    rewritten: None,
                    action: crate::verifier::verification_pool_manager::NativeJoinAction::Cfg(
                        action.clone(),
                    ),
                    after_start: None,
                    replay_check: Some(requirement.clone()),
                })),
                reporter: None,
                warning_sink: None,
            };
            let started = Arc::new((Mutex::new(false), Condvar::new()));
            let (ready_tx, _ready_rx) = std::sync::mpsc::channel();
            let (release_tx, release_rx) = std::sync::mpsc::channel();
            let release_rx = Arc::new(Mutex::new(release_rx));
            let worker_requirement = requirement.clone();
            let worker_factory = factory.clone();
            let worker_options = options.clone();
            let worker_config = config.clone();
            let path = std::path::PathBuf::from(&z3);
            let mut pool = ThreadVerificationPool::start(1, move |id| {
                let name = format!("own-sequence-{id}");
                let prover = z3_prover_std_io::new(
                    name.clone(),
                    z3_prover_std_io::settings(path.clone()),
                    worker_factory.clone(),
                    |_| {},
                );
                let identifiers = prover.identifier_factory();
                Ok(TestWorker {
                    native: native_method_worker(
                        name,
                        prover,
                        identifiers,
                        worker_factory.clone(),
                        worker_options.clone(),
                        &worker_config,
                    ),
                    started: started.clone(),
                    parent_ready: ready_tx.clone(),
                    release_tx: release_tx.clone(),
                    release_rx: release_rx.clone(),
                    requirement: worker_requirement.clone(),
                })
            })
            .unwrap();
            pool.broadcast(WorkerPreambleCommand::Declare(declaration.clone()))
                .unwrap();
            assert!(
                pool.submit(Job::OwnSequence {
                    foreign: make_job(),
                    own: make_job()
                })
                .unwrap()
                .wait()
                .unwrap()
            );
            pool.shutdown().unwrap();
        }
        // A completed foreign branch must not contaminate the next ordinary
        // method or CFG dispatched on its worker.
        for use_cfg in [false, true] {
            let worker_factory = factory.clone();
            let worker_options = options.clone();
            let worker_config = config.clone();
            let path = std::path::PathBuf::from(&z3);
            let mut pool = ThreadVerificationPool::start(1, move |id| {
                let name = format!("foreign-sequence-{id}");
                let prover = z3_prover_std_io::new(
                    name.clone(),
                    z3_prover_std_io::settings(path.clone()),
                    worker_factory.clone(),
                    |_| {},
                );
                let identifiers = prover.identifier_factory();
                Ok(native_method_worker(
                    name,
                    prover,
                    identifiers,
                    worker_factory.clone(),
                    worker_options.clone(),
                    &worker_config,
                ))
            })
            .unwrap();
            pool.broadcast(WorkerPreambleCommand::Declare(declaration.clone()))
                .unwrap();
            let remote = NativeWorkerTask {
                analysis: analysis.clone(),
                target: NativeWorkerTarget::Join(Box::new(NativeJoinJob {
                    source_worker_id: "source".into(),
                    snapshot: snapshot.clone(),
                    state: state.clone(),
                    mark,
                    condition: factory.boolean(true),
                    original: Exp::new(ExpKind::TrueLit, Default::default()),
                    rewritten: None,
                    action: crate::verifier::verification_pool_manager::NativeJoinAction::Cfg(
                        action.clone(),
                    ),
                    after_start: None,
                    replay_check: Some(requirement.clone()),
                })),
                reporter: None,
                warning_sink: None,
            };
            let result = pool.submit(remote).unwrap().wait().unwrap();
            assert!(matches!(result, NativeWorkerOutput::Join(_)));
            let target = if use_cfg {
                NativeWorkerTarget::Cfg(cfg.clone())
            } else {
                NativeWorkerTarget::Method(method.clone())
            };
            let result = pool
                .submit(NativeWorkerTask {
                    analysis: analysis.clone(),
                    target,
                    reporter: None,
                    warning_sink: None,
                })
                .unwrap()
                .wait()
                .unwrap();
            let NativeWorkerOutput::Member(results) = result else {
                panic!("unexpected result")
            };
            assert!(
                results.iter().any(|r| r.is_fatal()),
                "foreign branch contaminated subsequent task: cfg={use_cfg}"
            );
            pool.shutdown().unwrap();
        }
        // Hold a submitted CFG branch after it has installed its solver state,
        // then cancel while its parent is cooperatively awaiting its result.
        let cancellation =
            crate::verifier::verification_pool_manager::CancellationController::default();
        let worker_cancellation = cancellation.clone();
        let (entered_tx, entered_rx) = std::sync::mpsc::channel();
        let (resume_tx, resume_rx) = std::sync::mpsc::channel();
        let resume_rx = Arc::new(Mutex::new(resume_rx));
        let hook = Arc::new(move || {
            entered_tx.send(()).unwrap();
            resume_rx.lock().unwrap().recv().unwrap();
        });
        let remote = NativeWorkerTask {
            analysis: analysis.clone(),
            target: NativeWorkerTarget::Join(Box::new(NativeJoinJob {
                source_worker_id: "source".into(),
                snapshot: snapshot.clone(),
                state: state.clone(),
                mark,
                condition: factory.boolean(true),
                original: Exp::new(ExpKind::TrueLit, Default::default()),
                rewritten: None,
                action: crate::verifier::verification_pool_manager::NativeJoinAction::Cfg(
                    action.clone(),
                ),
                after_start: Some(hook),
                replay_check: Some(requirement.clone()),
            })),
            reporter: None,
            warning_sink: None,
        };
        let started = Arc::new((Mutex::new(false), Condvar::new()));
        let (ready_tx, _ready_rx) = std::sync::mpsc::channel();
        let (release_tx, release_rx) = std::sync::mpsc::channel();
        let release_rx = Arc::new(Mutex::new(release_rx));
        let worker_requirement = requirement.clone();
        let worker_factory = factory.clone();
        let worker_options = options.clone();
        let worker_config = config.clone();
        let path = std::path::PathBuf::from(&z3);
        let mut pool = ThreadVerificationPool::start(2, move |id| {
            let name = format!("cancel-cfg-{id}");
            let prover = z3_prover_std_io::new(
                name.clone(),
                z3_prover_std_io::settings(path.clone()),
                worker_factory.clone(),
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            let mut native = native_method_worker(
                name,
                prover,
                identifiers,
                worker_factory.clone(),
                worker_options.clone(),
                &worker_config,
            );
            native.set_cancellation(worker_cancellation.clone());
            Ok(TestWorker {
                native,
                started: started.clone(),
                parent_ready: ready_tx.clone(),
                release_tx: release_tx.clone(),
                release_rx: release_rx.clone(),
                requirement: worker_requirement.clone(),
            })
        })
        .unwrap();
        pool.broadcast(WorkerPreambleCommand::Declare(declaration.clone()))
            .unwrap();
        let parent = pool.submit(Job::CancelParent(remote)).unwrap();
        entered_rx.recv().unwrap();
        cancellation.cancel();
        resume_tx.send(()).unwrap();
        assert!(matches!(
            parent.wait(),
            Err(
                crate::verifier::verification_pool_manager::ThreadPoolError::Worker(
                    NativeError::Cancelled
                )
            )
        ));
        pool.shutdown().unwrap();
        source.context.base.decider.pop_scope().unwrap();
        source.stop().unwrap();
    }
}
