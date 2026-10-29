//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/FunctionVerificationUnit.scala
//!
//! Purpose:
//! Verify functions in phases and emit their usable axioms to prover workers.
//!
//! Planned Rust structure:
//! Port FunctionVerificationUnit and provider analysis, ordered function data, two-phase
//! verification, recording and preamble/lifecycle methods; select default or mask heap
//! FunctionEncoding.
//!
//! Behavior to preserve:
//! Order by dependency height and source order. Declare base/limited/stateless/precondition and
//! auxiliary functions. Phase 1 locally produces preconditions and fresh-snapshot postconditions
//! for well-definedness, records paths, then emits limited, trigger, auxiliary and
//! post/propagation axioms only on nonfatal result. Phase 2 restores each precondition path,
//! evaluates body, equates result and consumes posts; emit definition/body propagation only if
//! nonfatal. Respect permission and prover options, declare recorded macros last and replay
//! accumulated axioms. reset clears functionData, emitted axioms and fresh variables, but does
//! not clear postConditionAxioms; axiomsAfterVerification is an eagerly initialized val while
//! emitAxiomsAfterVerification reads the current vector. Record these reuse differences for
//! reconciliation rather than silently changing them.
//!
//! Integration:
//! functions::{function_data,function_encoding,mask_heap_function_encoding,function_recorder,heap_access_replacing_expression_translator};
//! rules::{producer,consumer,evaluator,execution_flow_controller}, state and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for continuations, solver ordering, branch-local state and
//! explicit encoding context.
//!
//! Open decisions:
//! Reconcile phase/cache reset, failure cleanup and prover option lifetime with verifier and
//! function data.
//!
//! Status: partial; source function analysis, ordering, declaration, axiom replay, reset and
//! both verification phases are implemented. The native context connects solver, evaluator,
//! producer, consumer, scopes and recursive predicate triggers.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::interfaces::decider::prover::ProverLike;
use crate::state::identifiers::IdentifierFactory;
use crate::state::symbol_converter::DefaultSymbolConverter;
use crate::state::terms::{
    ApplicationTarget, DeclarationKind, ResourceKey, Term, TermFactory, TermKind,
};
use crate::supporters::functions::function_data::{FunctionData, FunctionDataError};
use ferrum_silver::ast::program::{Function, Member, Program};

#[derive(Debug)]
pub enum FunctionAnalysisError<E> {
    CallGraph(ferrum_silver::ast::utility::functions::FunctionAnalysisError),
    QuantifiedFields(
        ferrum_silver::ast::utility::quantified_permissions::QuantifiedPermissionError,
    ),
    Data(FunctionDataError),
    Encoding(E),
    MissingFunction(String),
    HeightOverflow,
}
/// Ordered function-unit data and source preamble/reuse state.
pub struct FunctionVerificationUnit<D> {
    pub program: Option<Program>,
    pub data: Vec<(String, std::sync::Arc<std::sync::Mutex<FunctionData<D>>>)>,
    pub emitted_axioms: Vec<Term>,
    pub fresh_variables: Vec<Term>,
    /// Source reset deliberately leaves this vector intact.
    pub postcondition_axioms: std::rc::Rc<std::cell::RefCell<Vec<Term>>>,
}
impl<D: Clone> Default for FunctionVerificationUnit<D> {
    fn default() -> Self {
        Self {
            program: None,
            data: vec![],
            emitted_axioms: vec![],
            fresh_variables: vec![],
            postcondition_axioms: Default::default(),
        }
    }
}
impl<D: Clone> FunctionVerificationUnit<D> {
    pub fn analyze<E>(
        &mut self,
        factory: &TermFactory,
        converter: &DefaultSymbolConverter,
        identifiers: &mut impl IdentifierFactory,
        program: &Program,
        alternative_order: bool,
        debugging: bool,
        mut encoding: impl FnMut(
            &Function,
            &Program,
        ) -> Result<(Vec<Term>, Option<Vec<ResourceKey>>), E>,
    ) -> Result<(), FunctionAnalysisError<E>> {
        let heights = ferrum_silver::ast::utility::functions::heights(program, alternative_order)
            .map_err(FunctionAnalysisError::CallGraph)?;
        let mut ordered: Vec<_> = program
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| {
                heights
                    .get(&f.name)
                    .copied()
                    .map(|height| (i, height, f.clone()))
                    .ok_or_else(|| FunctionAnalysisError::MissingFunction(f.name.clone()))
            })
            .collect::<Result<_, _>>()?;
        ordered.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        let mut data = Vec::new();
        for (_, height, function) in ordered {
            let fields = ferrum_silver::ast::utility::quantified_permissions::quantified_fields(
                &Member::Function(function.clone()),
                program,
            )
            .map_err(FunctionAnalysisError::QuantifiedFields)?;
            let (state_args, resources) =
                encoding(&function, program).map_err(FunctionAnalysisError::Encoding)?;
            let data_item = FunctionData::new(
                factory,
                converter,
                identifiers,
                function.clone(),
                program.clone(),
                i32::try_from(height).map_err(|_| FunctionAnalysisError::HeightOverflow)?,
                fields,
                state_args,
                resources.as_deref(),
                debugging,
            )
            .map_err(FunctionAnalysisError::Data)?;
            data.push((
                function.name.clone(),
                std::sync::Arc::new(std::sync::Mutex::new(data_item)),
            ));
        }
        self.program = Some(program.clone());
        self.data = data;
        Ok(())
    }
    pub fn units(&self) -> Vec<Function> {
        self.data
            .iter()
            .map(|(_, data)| {
                data.lock()
                    .expect("poisoned function data")
                    .program_function
                    .clone()
            })
            .collect()
    }
    pub fn data_mut(&self, name: &str) -> Option<std::sync::MutexGuard<'_, FunctionData<D>>> {
        self.data
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, data)| data.lock().expect("poisoned function data"))
    }
    pub fn declare_analysis_symbols<E>(
        &self,
        factory: &TermFactory,
        sink: &mut impl ProverLike<Error = E>,
        mut auxiliary: impl FnMut(&FunctionData<D>) -> Vec<crate::state::terms::Applicable>,
    ) -> Result<(), E> {
        sink.comment(&mut || {
            "Declaring symbols related to program functions (from program analysis)".into()
        })?;
        for (_, data) in &self.data {
            let data = data.lock().expect("poisoned function data");
            for function in [
                &data.function,
                &data.limited_function,
                &data.stateless_function,
                &data.precondition_function,
            ] {
                sink.declare(&factory.function_decl(function.clone()))?;
            }
            for function in auxiliary(&data) {
                sink.declare(&factory.function_decl(function))?;
            }
        }
        sink.comment(&mut || "Snapshot variable to be used during function verification".into())?;
        sink.declare(
            &factory
                .function_decl_target(ApplicationTarget::Variable(factory.predef_snapshot_var())),
        )?;
        assert!(
            self.fresh_variables.is_empty(),
            "analysis introduced fresh prover variables"
        );
        Ok(())
    }
    pub fn declare_verification_symbols<E>(
        &self,
        factory: &TermFactory,
        sink: &mut impl ProverLike<Error = E>,
    ) -> Result<(), E> {
        let mut normal = Vec::new();
        let mut macros = Vec::new();
        for (_, data) in &self.data {
            let data = data.lock().expect("poisoned function data");
            for decl in data.recorder_handler.fresh_symbols_across_phases.iter() {
                if matches!(decl.kind(), DeclarationKind::Macro { .. }) {
                    macros.push(decl.clone());
                } else {
                    normal.push(decl.clone());
                }
            }
        }
        sink.comment(&mut || {
            "Declaring symbols related to program functions (from verification)".into()
        })?;
        for decl in normal.iter().chain(&macros) {
            sink.declare(decl)?;
        }
        for variable in &self.fresh_variables {
            sink.declare(
                &factory.function_decl_target(ApplicationTarget::Variable(variable.clone())),
            )?;
        }
        Ok(())
    }
    pub fn emit_recorded_axioms<E>(&self, sink: &mut impl ProverLike<Error = E>) -> Result<(), E> {
        sink.assume_axioms(
            &self
                .emitted_axioms
                .iter()
                .cloned()
                .collect::<InsertionOrderedSet<_>>(),
            "Function axioms",
        )
    }
    pub fn reset(&mut self) {
        self.program = None;
        self.data.clear();
        self.emitted_axioms.clear();
        self.fresh_variables.clear();
    }
}

pub struct FunctionPhaseOne<P, D, J, V> {
    pub result: crate::interfaces::verification::VerificationResult<V>,
    pub paths: Vec<FunctionPhasePath<P, D, J>>,
    pub recorders: Vec<crate::supporters::functions::function_recorder::FunctionRecorder<D>>,
}
pub struct FunctionPhasePath<P, D, J> {
    pub state: crate::state::state::State<P, D, J>,
    pub branch_conditions: Vec<Term>,
    pub branch_condition_exps: Vec<(
        ferrum_silver::ast::expression::Exp,
        Option<ferrum_silver::ast::expression::Exp>,
    )>,
    pub assumptions: InsertionOrderedSet<Term>,
    pub assumption_exps: Option<Vec<crate::debugger::debug_exp::DebugExp>>,
}
pub struct FunctionPhaseTwo<D, V> {
    pub result: crate::interfaces::verification::VerificationResult<V>,
    pub recorders: Vec<crate::supporters::functions::function_recorder::FunctionRecorder<D>>,
}
pub struct FunctionPhaseOneAxioms {
    pub auxiliary_declarations: Vec<crate::state::terms::Declaration>,
    pub auxiliary_axioms: Vec<Term>,
    pub post_axiom: Option<Term>,
    pub post_precondition_axioms: Vec<Term>,
}
pub trait FunctionVerificationServices<P, D, J, V> {
    type Error;
    fn begin_function(
        &mut self,
        function: &Function,
        data: &FunctionData<D>,
    ) -> Result<(), Self::Error>;
    fn end_function(&mut self) -> Result<(), Self::Error>;
    /// Close the source member scope only when verification and option cleanup succeed.
    fn complete_function_log(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    /// Produce preconditions with ?s, capture every path, then produce postconditions
    /// using fresh snapshots; return every resulting function recorder.
    fn check_function_specifications(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        data: &FunctionData<D>,
    ) -> Result<FunctionPhaseOne<P, D, J, V>, Self::Error>;
    /// Encoding-specific declarations become recorded during phase transition.
    fn well_definedness_declarations(
        &mut self,
        data: &FunctionData<D>,
    ) -> Result<Vec<crate::state::terms::Declaration>, Self::Error>;
    fn build_phase_one_auxiliary_axioms(
        &mut self,
        data: &FunctionData<D>,
    ) -> Result<Vec<Term>, Self::Error>;
    fn build_phase_one_post_axiom(
        &mut self,
        data: &FunctionData<D>,
    ) -> Result<(Option<Term>, Vec<Term>), Self::Error>;
    fn build_phase_one_post_precondition_axioms(
        &mut self,
        data: &FunctionData<D>,
        posts: &[Term],
    ) -> Result<Vec<Term>, Self::Error>;
    fn declare_function_axiom_symbol(
        &mut self,
        decl: &crate::state::terms::Declaration,
    ) -> Result<(), Self::Error>;
    fn assume_function_axioms(&mut self, axioms: &[Term]) -> Result<(), Self::Error>;
    /// For each phase-one path, restore its branch and assumptions, evaluate the
    /// body, equate the formal result and consume posts in a local scope.
    fn check_function_body(
        &mut self,
        data: &FunctionData<D>,
        paths: Vec<FunctionPhasePath<P, D, J>>,
    ) -> Result<FunctionPhaseTwo<D, V>, Self::Error>;
    fn build_phase_two_definition(
        &mut self,
        data: &FunctionData<D>,
    ) -> Result<(Option<Term>, Option<Term>), Self::Error>;
    fn build_phase_two_precondition_axioms(
        &mut self,
        data: &FunctionData<D>,
        body: Option<&Term>,
    ) -> Result<Vec<Term>, Self::Error>;
    fn record_function_failure(
        &mut self,
        function: &Function,
        result: &crate::interfaces::verification::VerificationResult<V>,
    );
    fn actual_function_recorder(
        &mut self,
        data: &FunctionData<D>,
    ) -> Result<crate::supporters::functions::function_recorder::FunctionRecorder<D>, Self::Error>;
    fn respect_function_pre_permissions(&self) -> bool;
}
#[derive(Debug)]
pub enum FunctionVerificationError<E> {
    MissingFunction,
    PostconditionAxiomsBorrowed,
    Data(FunctionDataError),
    Service(E),
    Cleanup {
        primary: Box<FunctionVerificationError<E>>,
        cleanup: E,
    },
}
impl<D: Clone> FunctionVerificationUnit<D> {
    /// Run the source two-phase function protocol, emitting only axioms justified
    /// by nonfatal phases and retaining phase failures for later translation.
    pub fn verify<P, J: Clone, V, C: FunctionVerificationServices<P, D, J, V>>(
        &mut self,
        factory: &TermFactory,
        context: &mut C,
        mut state: crate::state::state::State<P, D, J>,
        function: &Function,
    ) -> Result<
        Vec<crate::interfaces::verification::VerificationResult<V>>,
        FunctionVerificationError<C::Error>,
    > {
        use crate::interfaces::verification::VerificationResult;
        let (_, data) = self
            .data
            .iter_mut()
            .find(|(name, _)| name == &function.name)
            .ok_or(FunctionVerificationError::MissingFunction)?;
        let mut data = data.lock().expect("poisoned function data");
        context
            .begin_function(function, &data)
            .map_err(FunctionVerificationError::Service)?;
        let verification =
            (|| {
                for (_, var) in &data.formal_args {
                    context
                        .declare_function_axiom_symbol(
                            &factory.function_decl_target(ApplicationTarget::Variable(var.clone())),
                        )
                        .map_err(FunctionVerificationError::Service)?;
                }
                context
                    .declare_function_axiom_symbol(&factory.function_decl_target(
                        ApplicationTarget::Variable(data.formal_result.clone()),
                    ))
                    .map_err(FunctionVerificationError::Service)?;
                state.function_recorder = context
                    .actual_function_recorder(&data)
                    .map_err(FunctionVerificationError::Service)?;
                state.conserving_snapshot_generation = true;
                state.assert_read_access_only = !context.respect_function_pre_permissions();
                let phase_one = context
                    .check_function_specifications(state, &data)
                    .map_err(FunctionVerificationError::Service)?;
                data.advance_phase(factory, &phase_one.recorders, &[])
                    .map_err(FunctionVerificationError::Data)?;
                let result = if phase_one.result.is_fatal() {
                    context.record_function_failure(function, &phase_one.result);
                    phase_one.result
                } else {
                    for group in [
                        vec![data.limited_axiom.clone()],
                        vec![data.trigger_axiom.clone()],
                    ] {
                        context
                            .assume_function_axioms(&group)
                            .map_err(FunctionVerificationError::Service)?;
                        self.emitted_axioms.extend(group);
                    }
                    let declarations = context
                        .well_definedness_declarations(&data)
                        .map_err(FunctionVerificationError::Service)?;
                    for decl in &declarations {
                        context
                            .declare_function_axiom_symbol(decl)
                            .map_err(FunctionVerificationError::Service)?;
                        data.recorder_handler.fresh_symbols_across_phases = data
                            .recorder_handler
                            .fresh_symbols_across_phases
                            .incl(decl.clone());
                    }
                    let auxiliary_axioms = context
                        .build_phase_one_auxiliary_axioms(&data)
                        .map_err(FunctionVerificationError::Service)?;
                    context
                        .assume_function_axioms(&auxiliary_axioms)
                        .map_err(FunctionVerificationError::Service)?;
                    self.emitted_axioms.extend(auxiliary_axioms);
                    let (post, translated_posts) = context
                        .build_phase_one_post_axiom(&data)
                        .map_err(FunctionVerificationError::Service)?;
                    let post = post.into_iter().collect::<Vec<_>>();
                    context
                        .assume_function_axioms(&post)
                        .map_err(FunctionVerificationError::Service)?;
                    self.emitted_axioms.extend(post.clone());
                    let propagation = context
                        .build_phase_one_post_precondition_axioms(&data, &translated_posts)
                        .map_err(FunctionVerificationError::Service)?;
                    context
                        .assume_function_axioms(&propagation)
                        .map_err(FunctionVerificationError::Service)?;
                    self.emitted_axioms.extend(propagation);
                    self.postcondition_axioms
                        .try_borrow_mut()
                        .map_err(|_| FunctionVerificationError::PostconditionAxiomsBorrowed)?
                        .extend(post);
                    if function.body.is_none() {
                        phase_one.result
                    } else {
                        let phase_two = context
                            .check_function_body(&data, phase_one.paths)
                            .map_err(FunctionVerificationError::Service)?;
                        data.advance_phase(factory, &phase_two.recorders, &[])
                            .map_err(FunctionVerificationError::Data)?;
                        if phase_two.result.is_fatal() {
                            context.record_function_failure(function, &phase_two.result);
                        } else {
                            let (definition, body) = context
                                .build_phase_two_definition(&data)
                                .map_err(FunctionVerificationError::Service)?;
                            let definition = definition.into_iter().collect::<Vec<_>>();
                            context
                                .assume_function_axioms(&definition)
                                .map_err(FunctionVerificationError::Service)?;
                            self.emitted_axioms.extend(definition);
                            let body_preconditions = context
                                .build_phase_two_precondition_axioms(&data, body.as_ref())
                                .map_err(FunctionVerificationError::Service)?;
                            context
                                .assume_function_axioms(&body_preconditions)
                                .map_err(FunctionVerificationError::Service)?;
                            self.emitted_axioms.extend(body_preconditions);
                        }
                        phase_one.result.and_then(|| phase_two.result)
                    }
                };
                let _: &VerificationResult<V> = &result;
                Ok(vec![result])
            })();
        match (verification, context.end_function()) {
            (Ok(results), Ok(())) => {
                context
                    .complete_function_log()
                    .map_err(FunctionVerificationError::Service)?;
                Ok(results)
            }
            (Err(primary), Ok(())) => Err(primary),
            (Ok(_), Err(cleanup)) => Err(FunctionVerificationError::Service(cleanup)),
            (Err(primary), Err(cleanup)) => Err(FunctionVerificationError::Cleanup {
                primary: Box::new(primary),
                cleanup,
            }),
        }
    }
}

pub enum ContractSnapshot<'a> {
    Fixed(&'a Term),
    Fresh,
}
pub enum FunctionDebugPhase<'a> {
    Pre,
    Body(&'a ferrum_silver::ast::expression::Exp),
    Post,
}
pub trait FunctionPhaseServices<P, D, J, V>: Sized {
    type Error;
    fn function_debugging(&self) -> bool;
    fn empty_function_heap(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
    ) -> Result<std::sync::Arc<crate::state::heap::ListBackedHeap>, Self::Error>;
    fn function_debug_begin(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        phase: FunctionDebugPhase<'_>,
    ) -> Result<crate::state::state::State<P, D, J>, Self::Error>;
    fn function_debug_finish(
        &mut self,
        state: crate::state::state::State<P, D, J>,
    ) -> Result<crate::state::state::State<P, D, J>, Self::Error>;
    fn function_local(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        action: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            FunctionPhaseError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        FunctionPhaseError<Self::Error>,
    >;
    fn function_mark(&mut self) -> Result<crate::decider::path_conditions::Mark, Self::Error>;
    fn function_paths_after(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<crate::decider::path_conditions::RecordedPathConditions, Self::Error>;
    fn produce_function_contract(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        snapshot: ContractSnapshot<'_>,
        assertions: &[ferrum_silver::ast::expression::Exp],
        function: &Function,
        continuation: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            FunctionPhaseError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        FunctionPhaseError<Self::Error>,
    >;
    fn restore_function_preconditions(
        &mut self,
        path: &FunctionPhasePath<P, D, J>,
        function: &Function,
    ) -> Result<(), Self::Error>;
    fn saturate_function_contract(&mut self) -> Result<(), Self::Error>;
    fn evaluate_function_body(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        body: &ferrum_silver::ast::expression::Exp,
        function: &Function,
        continuation: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
            Term,
            Option<ferrum_silver::ast::expression::Exp>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            FunctionPhaseError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        FunctionPhaseError<Self::Error>,
    >;
    fn assume_function_result(
        &mut self,
        data: &FunctionData<D>,
        body: &ferrum_silver::ast::expression::Exp,
        term: &Term,
        debug: Option<&ferrum_silver::ast::expression::Exp>,
    ) -> Result<(), Self::Error>;
    fn consume_function_posts(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        posts: &[ferrum_silver::ast::expression::Exp],
        function: &Function,
        continuation: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            FunctionPhaseError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        FunctionPhaseError<Self::Error>,
    >;
}
#[derive(Debug)]
pub enum FunctionPhaseError<E> {
    MissingBody,
    MissingDebugVersionSeparator,
    InvalidBranchExpressions,
    Service(E),
}
/// Source phase one: bind the formal/result store, produce preconditions using
/// the shared snapshot, save each path, then produce postconditions with fresh snapshots.
pub fn check_specification_well_definedness<
    P,
    D: Clone,
    J: Clone,
    V,
    C: FunctionPhaseServices<P, D, J, V>,
>(
    factory: &TermFactory,
    context: &mut C,
    mut state: crate::state::state::State<P, D, J>,
    data: &FunctionData<D>,
) -> Result<FunctionPhaseOne<P, D, J, V>, FunctionPhaseError<C::Error>> {
    use crate::state::store::{AbstractLocalVar, MapBackedStore};
    use ferrum_silver::ast::expression::{Exp, ExpKind};
    use std::sync::Arc;
    let mut bindings = Vec::new();
    for (local, term) in &data.formal_args {
        let debug = if context.function_debugging() {
            let TermKind::Var(variable) = term.kind() else {
                return Err(FunctionPhaseError::MissingDebugVersionSeparator);
            };
            let name = variable.id.name();
            let end = name
                .rfind('@')
                .ok_or(FunctionPhaseError::MissingDebugVersionSeparator)?;
            let typ = local
                .expression()
                .typ()
                .map_err(|_| FunctionPhaseError::MissingDebugVersionSeparator)?;
            Some(Exp::new(
                ExpKind::LocalVarWithVersion(name[..end].into(), typ),
                local.expression().metadata().clone(),
            ))
        } else {
            None
        };
        bindings.push((local.clone(), (term.clone(), debug)));
    }
    bindings.push((
        AbstractLocalVar::new(data.program_function.result()),
        (data.formal_result.clone(), data.formal_result_exp.clone()),
    ));
    state.g = Arc::new(MapBackedStore::from_bindings(bindings));
    state.h = context
        .empty_function_heap(&state)
        .map_err(FunctionPhaseError::Service)?;
    state.old_heaps = Default::default();
    if context.function_debugging() {
        state = context
            .function_debug_begin(state, FunctionDebugPhase::Pre)
            .map_err(FunctionPhaseError::Service)?;
    }
    let mut paths = Vec::new();
    let mut recorders = Vec::new();
    let pre_snapshot = factory.predef_snapshot_var();
    let result = context.function_local(state, &mut |context, state| {
        let mark = context
            .function_mark()
            .map_err(FunctionPhaseError::Service)?;
        context.produce_function_contract(
            state,
            ContractSnapshot::Fixed(&pre_snapshot),
            &data.program_function.pres,
            &data.program_function,
            &mut |context, state| {
                let state = if context.function_debugging() {
                    context
                        .function_debug_finish(state)
                        .map_err(FunctionPhaseError::Service)?
                } else {
                    state
                };
                let recorded = context
                    .function_paths_after(mark)
                    .map_err(FunctionPhaseError::Service)?;
                let mut conditions = recorded.branch_conditions();
                conditions.reverse();
                let mut condition_exps = recorded.branch_condition_exps();
                condition_exps.reverse();
                if conditions.len() != condition_exps.len() {
                    return Err(FunctionPhaseError::InvalidBranchExpressions);
                }
                paths.push(FunctionPhasePath {
                    state: state.clone(),
                    branch_conditions: conditions,
                    branch_condition_exps: condition_exps,
                    assumptions: recorded.assumptions(),
                    assumption_exps: context
                        .function_debugging()
                        .then(|| recorded.assumption_exps().into_iter().collect()),
                });
                context.produce_function_contract(
                    state,
                    ContractSnapshot::Fresh,
                    &data.program_function.posts,
                    &data.program_function,
                    &mut |_, state| {
                        recorders.push(state.function_recorder);
                        Ok(crate::interfaces::verification::VerificationResult::success())
                    },
                )
            },
        )
    })?;
    Ok(FunctionPhaseOne {
        result,
        paths,
        recorders,
    })
}
/// Source phase two: revisit each live precondition path, evaluate the body,
/// bind `result` to its value and consume postconditions; stop after fatal failure.
pub fn check_function_body<P, D: Clone, J: Clone, V, C: FunctionPhaseServices<P, D, J, V>>(
    context: &mut C,
    data: &FunctionData<D>,
    paths: Vec<FunctionPhasePath<P, D, J>>,
) -> Result<FunctionPhaseTwo<D, V>, FunctionPhaseError<C::Error>> {
    let body = data
        .program_function
        .body
        .as_ref()
        .ok_or(FunctionPhaseError::MissingBody)?;
    let mut recorders = Vec::new();
    let mut result = crate::interfaces::verification::VerificationResult::success();
    for path in paths {
        if result.is_fatal() {
            break;
        }
        let state = path.state.clone();
        let next = context.function_local(state, &mut |context, mut state| {
            context
                .restore_function_preconditions(&path, &data.program_function)
                .map_err(FunctionPhaseError::Service)?;
            context
                .saturate_function_contract()
                .map_err(FunctionPhaseError::Service)?;
            if context.function_debugging() {
                state = context
                    .function_debug_begin(state, FunctionDebugPhase::Body(body))
                    .map_err(FunctionPhaseError::Service)?;
            }
            context.evaluate_function_body(
                state,
                body,
                &data.program_function,
                &mut |context, mut state, term, debug| {
                    context
                        .assume_function_result(data, body, &term, debug.as_ref())
                        .map_err(FunctionPhaseError::Service)?;
                    if context.function_debugging() {
                        state = context
                            .function_debug_finish(state)
                            .map_err(FunctionPhaseError::Service)?;
                        state = context
                            .function_debug_begin(state, FunctionDebugPhase::Post)
                            .map_err(FunctionPhaseError::Service)?;
                    }
                    context.consume_function_posts(
                        state,
                        &data.program_function.posts,
                        &data.program_function,
                        &mut |_, state| {
                            recorders.push(state.function_recorder);
                            Ok(crate::interfaces::verification::VerificationResult::success())
                        },
                    )
                },
            )
        })?;
        result = result.and_then(|| next);
    }
    Ok(FunctionPhaseTwo { result, recorders })
}
