//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Evaluator.scala
//!
//! Purpose:
//! Evaluate Silver expressions to symbolic terms with well-definedness checks.
//!
//! Planned Rust structure:
//! EvaluationRules and evaluator expose eval/evals/evalQuantified; eval3 wraps heap switching and
//! trigger recording, eval2 dispatches literals, locals, field/current-permission/forperm, old and
//! labelled old, let, boolean/conditional, integer and permission arithmetic,
//! domain/backend/function applications, quantified expressions, unfolding/applying/asserting,
//! sequences, sets/multisets and maps. Helpers cover sequence bounds, implication and short-circuit
//! joins, old-state evaluation, resource access, division, trigger evaluation, heap triggers and
//! value joins.
//!
//! Behavior to preserve:
//! Evaluate sequences left to right, retaining source debug expressions. Temporarily use wand
//! evaluation heap and clear reserve/exhale context, then restore; current permission reads
//! partially consumed heap. Missing old label fails; old evaluation restores heap and trigger
//! context. Wildcard uses full permission in read-only mode, otherwise fresh constrained ARP. Honor
//! strict versus short-circuit config, branch feasibility and join results. Check zero divisors,
//! sequence bounds and map membership unless trigger evaluation bypasses checks; final retry can
//! assume failed checks while combining errors. Quantified evaluation enters local solver scope,
//! binds fresh variables, evaluates guards before body/triggers, captures auxiliary assumptions,
//! restores selected state, and represents infeasible guard by absent body. Existential function
//! preconditions are universally assumed; invalid weights warn. Function applications consume
//! preconditions in a temporary store/heap, record snapshot, select limited opaque or revealed
//! function and restore state. Unfolding respects recursion limit, permissions and snapshot
//! restoration; applying uses wand rules. Trigger evaluation rolls back path conditions and error
//! count, restores successful deltas or warns and retains cached terms; heap trigger alternatives
//! form Cartesian products.
//!
//! Integration:
//! rules::consumer, producer, brancher, joiner, execution_flow_controller, heap_supporter,
//! predicate_supporter, magic_wand_supporter, state::terms/triggers and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Continuation and verifier ownership, quantified auxiliary scopes, snapshot and error
//! propagation.
//!
//! Status: partial; CPS heap restoration, literals, locals and basic binary dispatch implemented.
//! Control-flow, division checks, heap/function/quantifier/collection families require collaborators.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::verification::VerificationResult;
use crate::state::terms::{Term, TermFactory};
use crate::state::{
    heap::ListBackedHeap,
    state::State,
    store::{AbstractLocalVar, Store},
};
use ferrum_silver::ast::expression::{Exp, ExpKind};
use std::sync::Arc;

#[derive(Debug)]
pub enum EvaluationError<E> {
    Context(E),
    MissingStoreValue,
    OwnedSchedulerUnavailable,
    MissingDebugExpression,
    ExpressionType(ferrum_silver::ast::expression::ExpressionTypeError),
    ExpectedSetType,
    EmptyExplicitCollection,
    InvalidMapLiteral,
    MissingOldState(String),
    MissingDomainFunction(String),
    MissingFunction(String),
    MissingFunctionSnapshot,
    PreconditionRewrite(
        ferrum_silver::ast::utility::rewriter::strategy::ExpressionRewriteError<&'static str>,
    ),
    MissingPredicate(String),
    Wand(ferrum_silver::ast::utility::expressions::MagicWandError),
    InvalidResourceAccess,
    InvalidJoinEntries,
    TriggerCleanup {
        evaluation: Box<EvaluationError<E>>,
        cleanup: E,
    },
    QuantifierTransform(crate::state::terms::UnsupportedTriggerTransform),
    Path(crate::decider::path_conditions::PathError),
    Precondition(crate::state::function_precondition_transformer::PreconditionTransformError<E>),
    Rewrite(ferrum_silver::ast::utility::rewriter::strategy::ExpressionReplacementError),
}
#[derive(Clone, Debug)]
pub struct QuantifiedExpressionData {
    pub variables: Vec<Term>,
    pub variable_expressions: Option<Vec<ferrum_silver::ast::program::LocalVarDecl>>,
    pub body: Term,
    pub body_expression: Option<Exp>,
    pub triggers: Vec<crate::state::terms::Trigger>,
    pub auxiliary_globals: Vec<Term>,
    pub auxiliary_non_globals: Vec<Term>,
    pub auxiliary_debug: Option<(
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::debugger::debug_exp::DebugExp,
        >,
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::debugger::debug_exp::DebugExp,
        >,
    )>,
}
#[derive(Clone, Debug)]
pub struct ForPermCondition {
    pub condition: Term,
    pub original: Exp,
    pub rewritten: Option<Exp>,
    pub variables: Vec<Term>,
    pub definitions: crate::state::store::MapBackedStore,
    pub triggers: Vec<crate::state::terms::Trigger>,
}
/// Verifier services for heap switching, symbolic execution logging and specialized cases.
/// Implementations handle the still-unported families explicitly and must not return success
/// for an expression they cannot evaluate.
/// Owned branch work for evaluation joins. The post-join continuation stays with
/// the caller; these values contain everything needed to explore one branch.
#[derive(Clone)]
pub enum EvaluationBranchAction<E> {
    Evaluate {
        expression: Exp,
        error: E,
    },
    Value {
        term: Term,
        debug: Option<Exp>,
    },
    True,
    ShortCircuit {
        expressions: Vec<Exp>,
        disjunction: bool,
        error: E,
    },
}

/// The exact old-expression return actions surrounding an owned inner value.
#[derive(Clone)]
pub struct OwnedOldValueFrame {
    pub expression: Exp,
    pub label: String,
    pub kind: u8,
    pub heap: Arc<crate::state::heap::ListBackedHeap>,
    pub partial_heap: Option<Arc<crate::state::heap::ListBackedHeap>>,
    pub possible_triggers: crate::state::package::OrderedMap<Exp, Term>,
    pub record_possible_triggers: bool,
    pub is_eval_in_old: bool,
    pub program: ferrum_silver::ast::program::Program,
    pub evaluation_heap: Arc<crate::state::heap::ListBackedHeap>,
    pub evaluation_reserve: Vec<Arc<crate::state::heap::ListBackedHeap>>,
    pub evaluation_exhale: bool,
}
/// Return operations are stored outermost first and resumed from the end.
#[derive(Clone)]
pub enum OwnedEvaluationReturnFrame {
    Old(OwnedOldValueFrame),
    Asserting(OwnedValueWrapper),
    IndexedCollectionArg {
        wrapper: OwnedValueWrapper,
        args: Vec<Exp>,
        index: usize,
        terms: Vec<Term>,
        debug_args: Vec<Option<Exp>>,
    },
    ExplicitCollectionArg {
        wrapper: OwnedValueWrapper,
        index: usize,
        terms: Vec<Term>,
        debug_args: Vec<Option<Exp>>,
    },
    FunctionArg {
        wrapper: OwnedValueWrapper,
        function: ferrum_silver::ast::program::Function,
        record_heap: bool,
        index: usize,
        terms: Vec<Term>,
        debug_args: Vec<Option<Exp>>,
    },
    DomainArg {
        wrapper: OwnedValueWrapper,
        function: ferrum_silver::ast::program::DomainFunc,
        index: usize,
        terms: Vec<Term>,
        debug_args: Vec<Option<Exp>>,
    },
    FieldReceiver {
        wrapper: OwnedValueWrapper,
        record_heap: bool,
    },
    CurrentPermArg {
        wrapper: OwnedValueWrapper,
        access: Exp,
        resource: crate::state::terms::ResourceKey,
        heap: Arc<ListBackedHeap>,
        args: Vec<Exp>,
        index: usize,
        terms: Vec<Term>,
        debug_args: Vec<Option<Exp>>,
    },
    LetValue(OwnedValueWrapper),
    LetBody {
        wrapper: OwnedValueWrapper,
        before: crate::state::package::OrderedMap<Exp, Term>,
        local: Exp,
        value_debug: Option<Exp>,
    },
    Minus(OwnedValueWrapper),
    PermMinus(OwnedValueWrapper),
    Not(OwnedValueWrapper),
    StrictLeft {
        wrapper: OwnedValueWrapper,
        right: Exp,
    },
    StrictRight {
        wrapper: OwnedValueWrapper,
        left: Term,
        left_debug: Option<Exp>,
    },
    AddLeft {
        wrapper: OwnedValueWrapper,
        right: Exp,
    },
    AddRight {
        wrapper: OwnedValueWrapper,
        left: Term,
        left_debug: Option<Exp>,
    },
}

/// The evaluator restores these fields after each expression independently.
#[derive(Clone)]
pub struct OwnedValueWrapper {
    expression: Exp,
    heap: Arc<crate::state::heap::ListBackedHeap>,
    reserve: Vec<Arc<crate::state::heap::ListBackedHeap>>,
    exhale: bool,
}

/// State and value receiver for a direct assignment of an asserting expression.
#[derive(Clone)]
pub struct OwnedAsserting<E> {
    pub original_store: Arc<crate::state::store::MapBackedStore>,
    pub evaluation_heap: Arc<crate::state::heap::ListBackedHeap>,
    pub outer_heap: Arc<crate::state::heap::ListBackedHeap>,
    pub outer_reserve: Vec<Arc<crate::state::heap::ListBackedHeap>>,
    pub outer_exhale: bool,
    pub expression: Exp,
    pub body: Exp,
    pub error: E,
    pub receiver: crate::rules::executor::OwnedAssignmentValue,
    pub return_frames: Vec<OwnedEvaluationReturnFrame>,
}

/// Explicit ownership token for a value-producing outer join.
pub struct OwnedEvaluationJoin<P, D, J> {
    pub initial: State<P, D, J>,
    pub mark: crate::decider::path_conditions::Mark,
    pub collector_id: Arc<()>,
}
impl<P, D, J: Clone> Clone for OwnedEvaluationJoin<P, D, J> {
    fn clone(&self) -> Self {
        Self {
            initial: self.initial.clone(),
            mark: self.mark,
            collector_id: self.collector_id.clone(),
        }
    }
}
/// Function application Q after precondition consumption returns a snapshot.
pub struct OwnedFunctionPre<P, D, J> {
    pub join: OwnedEvaluationJoin<P, D, J>,
    pub base: State<P, D, J>,
    pub pre_state: State<P, D, J>,
    pub function: ferrum_silver::ast::program::Function,
    pub expression: Exp,
    pub argument_expressions: Vec<Exp>,
    pub arguments: Vec<Term>,
    pub debug_arguments: Option<Vec<Exp>>,
    pub application_debug: Option<Exp>,
    pub label: String,
    pub preconditions: Vec<Exp>,
}
impl<P, D, J: Clone> Clone for OwnedFunctionPre<P, D, J> {
    fn clone(&self) -> Self {
        Self {
            join: self.join.clone(),
            base: self.base.clone(),
            pre_state: self.pre_state.clone(),
            function: self.function.clone(),
            expression: self.expression.clone(),
            argument_expressions: self.argument_expressions.clone(),
            arguments: self.arguments.clone(),
            debug_arguments: self.debug_arguments.clone(),
            application_debug: self.application_debug.clone(),
            label: self.label.clone(),
            preconditions: self.preconditions.clone(),
        }
    }
}

pub trait EvaluationContext<P, D, J, V>: Sized {
    type Error;
    type PartialError: Clone;
    /// Optional source debug logging before switching to the evaluation heap.
    fn log_evaluation(
        &mut self,
        _state: &State<P, D, J>,
        _expression: &Exp,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn factory(&self) -> &TermFactory;
    fn debugging(&self) -> bool;
    fn verifier_unique_id(&self) -> &str;
    fn to_sort(
        &mut self,
        typ: &ferrum_silver::ast::r#type::Type,
    ) -> Result<crate::state::terms::Sort, Self::Error>;
    fn disable_short_circuiting(&self) -> bool;
    fn is_short_circuit_implies(&self, expression: &Exp) -> bool;
    fn open_evaluation(
        &mut self,
        state: &State<P, D, J>,
        expression: &Exp,
    ) -> Result<(), Self::Error>;
    fn close_evaluation(&mut self) -> Result<(), Self::Error>;
    /// Return the source scope ID; legacy/no-op contexts delegate to their existing hook.
    fn open_evaluation_scope(
        &mut self,
        state: &State<P, D, J>,
        expression: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        self.open_evaluation(state, expression)?;
        Ok(None)
    }
    fn close_evaluation_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        self.close_evaluation()
    }

    /// Scopes for source implication, conditional-expression, and ForPerm records.
    fn open_implies_scope(
        &mut self,
        _state: &State<P, D, J>,
        _expression: Option<&Exp>,
        _environment: &str,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn open_conditional_scope(
        &mut self,
        _state: &State<P, D, J>,
        _expression: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn close_expression_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn eval_heap(&mut self, state: &State<P, D, J>) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn record_possible_trigger(
        &mut self,
        state: &mut State<P, D, J>,
        expression: &Exp,
        term: &Term,
    ) -> Result<(), Self::Error>;
    fn assert_goal(&mut self, goal: &Term) -> Result<bool, Self::Error>;
    fn report_further_errors(&self) -> bool;
    fn assume_generated(
        &mut self,
        term: &Term,
        original: Option<&Exp>,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn assume_nonzero(
        &mut self,
        term: &Term,
        original: Option<&Exp>,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn division_failure(
        &mut self,
        state: &State<P, D, J>,
        partial: &Self::PartialError,
        divisor: &Exp,
        assertion: &Term,
        rewritten_assertion: Option<&Exp>,
    ) -> Result<VerificationResult<V>, Self::Error>;
    fn sequence_bounds_failure(
        &mut self,
        state: &State<P, D, J>,
        partial: &Self::PartialError,
        sequence: &Exp,
        index: &Exp,
        negative: bool,
        goal: &Term,
        rewritten: Option<&Exp>,
    ) -> Result<VerificationResult<V>, Self::Error>;
    fn map_key_failure(
        &mut self,
        state: &State<P, D, J>,
        partial: &Self::PartialError,
        base: &Exp,
        key: &Exp,
        assertion: &Term,
        rewritten_assertion: Option<&Exp>,
    ) -> Result<VerificationResult<V>, Self::Error>;
    fn fresh_arp(&mut self) -> Result<(Term, Term, Option<Exp>), Self::Error>;
    fn assume_arp_definition(
        &mut self,
        constraint: &Term,
        debug_variable: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn consolidate_old(&mut self, state: State<P, D, J>) -> Result<State<P, D, J>, Self::Error>;
    fn is_heap_dependent(
        &mut self,
        expression: &Exp,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<bool, Self::Error>;
    fn missing_label_failure(
        &mut self,
        state: &State<P, D, J>,
        partial: &Self::PartialError,
        original: &Exp,
        label: &str,
    ) -> Result<VerificationResult<V>, Self::Error>;
    fn fresh_let_application(
        &mut self,
        typ: &ferrum_silver::ast::r#type::Type,
        variables: &[Term],
    ) -> Result<(Term, crate::state::terms::ApplicationTarget), Self::Error>;
    fn assume_let_definition(
        &mut self,
        equality: &Term,
        variable: &ferrum_silver::ast::expression::LocalVar,
        original: &Exp,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn merge_evaluation_states(
        &mut self,
        first: State<P, D, J>,
        second: &State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
    /// Branches run in local solver scopes, collect joined entries in source order, and
    /// restore the caller state fields using join(resetState=true).
    fn branch_join_evaluation(
        &mut self,
        state: State<P, D, J>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        from_short_circuit_and: bool,
        yes: EvaluationBranchAction<Self::PartialError>,
        no: EvaluationBranchAction<Self::PartialError>,
        merge: &mut dyn FnMut(
            &mut Self,
            Vec<(State<P, D, J>, Term, Option<Exp>)>,
        ) -> Result<
            (State<P, D, J>, Term, Option<Exp>),
            EvaluationError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Term,
            Option<Exp>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
    fn domain_function(
        &mut self,
        function: &ferrum_silver::ast::program::DomainFunc,
        program: &ferrum_silver::ast::program::Program,
        argument_sorts: &[crate::state::terms::Sort],
        result_sort: &crate::state::terms::Sort,
        backend: bool,
    ) -> Result<crate::state::terms::Applicable, Self::Error>;
    #[cfg(test)]
    fn test_owned_right_resume(&mut self, _frame: &OwnedAsserting<Self::PartialError>) {}
    /// Whether a continuation can transfer another assertion in this state.
    fn can_transfer_owned_asserting(&self, _state: &State<P, D, J>) -> bool {
        false
    }
    fn try_consume_owned_asserting(
        &mut self,
        _state: &State<P, D, J>,
        _assertion: &Exp,
        _frame: &OwnedAsserting<Self::PartialError>,
    ) -> Option<Result<VerificationResult<V>, EvaluationError<Self::Error>>> {
        None
    }
    fn finish_owned_assignment_value(
        &mut self,
        _state: State<P, D, J>,
        _term: Term,
        _debug: Option<Exp>,
        _receiver: &crate::rules::executor::OwnedAssignmentValue,
    ) -> Option<Result<VerificationResult<V>, EvaluationError<Self::Error>>> {
        None
    }
    fn consume_assertion(
        &mut self,
        state: State<P, D, J>,
        assertion: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
    fn eval_field_access(
        &mut self,
        state: State<P, D, J>,
        access: &ferrum_silver::ast::expression::FieldAccess,
        receiver: &Term,
        receiver_exp: Option<&Exp>,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Term,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
    fn record_intermediate_heap(
        &mut self,
        state: State<P, D, J>,
        expression: &Exp,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn debug_old_label(
        &mut self,
        state: &State<P, D, J>,
        position: &ferrum_silver::ast::position::Position,
    ) -> Result<String, Self::Error>;
    fn eval_current_permission(
        &mut self,
        state: State<P, D, J>,
        heap: Arc<ListBackedHeap>,
        access: &Exp,
        resource: &crate::state::terms::ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Term,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
    fn annotation_warning(&mut self, message: String) -> Result<(), Self::Error>;
    /// Executes source scoped quantified evaluation, returning None when the inner path dies.
    fn evaluate_quantifier(
        &mut self,
        state: State<P, D, J>,
        expression: &Exp,
        name: &str,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Option<QuantifiedExpressionData>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
    fn heap_independent_auxiliaries(&mut self, terms: &[Term]) -> Result<Vec<Term>, Self::Error>;
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
    ) -> Result<(), Self::Error>;
    fn precondition_function(
        &mut self,
        function: &crate::state::terms::Applicable,
    ) -> Result<crate::state::terms::Applicable, Self::Error>;
    fn assume_existential_preconditions(
        &mut self,
        term: &Term,
        original: &Exp,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn check_smoke(&mut self) -> Result<bool, Self::Error>;
    fn quantifier_failure(
        &mut self,
        state: &State<P, D, J>,
        expression: &Exp,
        error: &Self::PartialError,
    ) -> Result<VerificationResult<V>, Self::Error>;
    fn join_off(&self) -> J;
    fn respect_function_pre_permission_amounts(&self) -> bool;
    fn join_function_application(
        &mut self,
        state: State<P, D, J>,
        function: &ferrum_silver::ast::program::Function,
        args: &[Term],
        debug_exp: Option<&Exp>,
        block: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                State<P, D, J>,
                Term,
                Option<Exp>,
            )
                -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Term,
            Option<Exp>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
    fn join_function_application_with_owned(
        &mut self,
        state: State<P, D, J>,
        function: &ferrum_silver::ast::program::Function,
        args: &[Term],
        debug: Option<&Exp>,
        block: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                State<P, D, J>,
                Term,
                Option<Exp>,
            )
                -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
            Option<&OwnedEvaluationJoin<P, D, J>>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Term,
            Option<Exp>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>> {
        self.join_function_application(
            state,
            function,
            args,
            debug,
            &mut |context, state, done| block(context, state, done, None),
            continuation,
        )
    }
    fn try_consume_owned_function_preconditions(
        &mut self,
        _state: &State<P, D, J>,
        _frame: &OwnedFunctionPre<P, D, J>,
    ) -> Option<Result<VerificationResult<V>, EvaluationError<Self::Error>>> {
        None
    }
    fn consume_function_preconditions(
        &mut self,
        state: State<P, D, J>,
        caller_store: &Arc<crate::state::store::MapBackedStore>,
        function: &ferrum_silver::ast::program::Function,
        application: &Exp,
        arguments: &[Exp],
        preconditions: &[Exp],
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Option<Term>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
    fn function_snapshot_args(
        &mut self,
        state: &State<P, D, J>,
        function: &ferrum_silver::ast::program::Function,
        arguments: &[Term],
        snapshot: &Term,
    ) -> Result<(Vec<Term>, Term), Self::Error>;
    fn heap_function(
        &mut self,
        function: &ferrum_silver::ast::program::Function,
        program: &ferrum_silver::ast::program::Program,
    ) -> Result<crate::state::terms::Applicable, Self::Error>;
    fn assume_function_precondition(
        &mut self,
        term: &Term,
        function: &ferrum_silver::ast::program::Function,
        debug_args: Option<&[Exp]>,
    ) -> Result<(), Self::Error>;
    fn branch_conditions(&self) -> Vec<Term>;
    fn fresh_for_perm(
        &mut self,
        declaration: &ferrum_silver::ast::program::LocalVarDecl,
    ) -> Result<(Term, Option<Exp>), Self::Error>;
    fn for_perm_conditions(
        &mut self,
        state: &State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
        variables: &[(Term, Option<Exp>)],
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<Vec<ForPermCondition>, Self::Error>;
    fn evaluate_special(
        &mut self,
        state: State<P, D, J>,
        expression: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Term,
            Option<Exp>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
}
#[derive(Clone, Copy)]
enum Binary {
    Eq,
    Ne,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Fraction,
    PermDiv,
    PermPermDiv,
    Le,
    Lt,
    Ge,
    Gt,
    PermAdd,
    PermSub,
    PermMul,
    PermMin,
    IntPermMul,
    PermLe,
    PermLt,
    PermGe,
    PermGt,
    And,
    Or,
    SeqAppend,
    SeqDrop,
    SeqTake,
    SeqRange,
    SetUnion(bool),
    SetIntersection(bool),
    SetSubset(bool),
    SetMinus(bool),
    SetContains(bool),
    MapContains,
}
impl Binary {
    fn build(self, f: &TermFactory, a: Term, b: Term) -> Term {
        match self {
            Self::Eq => f.equals(a, b),
            Self::Ne => f.not(f.equals(a, b)),
            Self::Add => f.plus(a, b),
            Self::Sub => f.minus(a, b),
            Self::Mul => f.times(a, b),
            Self::Div => f.div(a, b),
            Self::Mod => f.modulo(a, b),
            Self::Fraction => f.fraction_perm(a, b),
            Self::PermDiv => f.perm_int_div(a, b),
            Self::PermPermDiv => f.perm_perm_div(a, b),
            Self::Le | Self::PermLe => f.at_most(a, b),
            Self::Lt | Self::PermLt => f.less(a, b),
            Self::Ge | Self::PermGe => f.at_least(a, b),
            Self::Gt | Self::PermGt => f.greater(a, b),
            Self::PermAdd => f.perm_plus(a, b),
            Self::PermSub => f.perm_minus(a, b),
            Self::PermMul => f.perm_times(a, b),
            Self::PermMin => f.perm_min(a, b),
            Self::IntPermMul => f.int_perm_times(a, b),
            Self::SeqAppend => f.seq_append(a, b),
            Self::SeqDrop => f.seq_drop(a, b),
            Self::SeqTake => f.seq_take(a, b),
            Self::SeqRange => f.seq_ranged(a, b),
            Self::SetUnion(false) => f.set_union(a, b),
            Self::SetUnion(true) => f.multiset_union(a, b),
            Self::SetIntersection(false) => f.set_intersection(a, b),
            Self::SetIntersection(true) => f.multiset_intersection(a, b),
            Self::SetSubset(false) => f.set_subset(a, b),
            Self::SetSubset(true) => f.multiset_subset(a, b),
            Self::SetMinus(false) => f.set_difference(a, b),
            Self::SetMinus(true) => f.multiset_difference(a, b),
            Self::SetContains(false) => f.set_in(a, b),
            Self::SetContains(true) => f.multiset_count(b, a),
            Self::MapContains => f.set_in(a, f.map_domain(b)),
            Self::And => f.and([a, b]),
            Self::Or => f.or([a, b]),
        }
    }
    fn expression(self, a: Exp, b: Exp) -> ExpKind {
        match self {
            Self::Eq => ExpKind::EqCmp(a, b),
            Self::Ne => ExpKind::NeCmp(a, b),
            Self::Add => ExpKind::Add(a, b),
            Self::Sub => ExpKind::Sub(a, b),
            Self::Mul => ExpKind::Mul(a, b),
            Self::Div => ExpKind::Div(a, b),
            Self::Mod => ExpKind::Mod(a, b),
            Self::Fraction => ExpKind::FractionalPerm(a, b),
            Self::PermDiv => ExpKind::PermDiv(a, b),
            Self::PermPermDiv => ExpKind::PermPermDiv(a, b),
            Self::Le => ExpKind::LeCmp(a, b),
            Self::Lt => ExpKind::LtCmp(a, b),
            Self::Ge => ExpKind::GeCmp(a, b),
            Self::Gt => ExpKind::GtCmp(a, b),
            Self::PermAdd => ExpKind::PermAdd(a, b),
            Self::PermSub => ExpKind::PermSub(a, b),
            Self::PermMul => ExpKind::PermMul(a, b),
            Self::PermMin => ExpKind::DebugPermMin(a, b),
            Self::IntPermMul => ExpKind::IntPermMul(a, b),
            Self::PermLe => ExpKind::PermLeCmp(a, b),
            Self::PermLt => ExpKind::PermLtCmp(a, b),
            Self::PermGe => ExpKind::PermGeCmp(a, b),
            Self::PermGt => ExpKind::PermGtCmp(a, b),
            Self::SeqAppend => ExpKind::SeqAppend(a, b),
            Self::SeqDrop => ExpKind::SeqDrop(a, b),
            Self::SeqTake => ExpKind::SeqTake(a, b),
            Self::SeqRange => ExpKind::RangeSeq(a, b),
            Self::SetUnion(_) => ExpKind::AnySetUnion(a, b),
            Self::SetIntersection(_) => ExpKind::AnySetIntersection(a, b),
            Self::SetSubset(_) => ExpKind::AnySetSubset(a, b),
            Self::SetMinus(_) => ExpKind::AnySetMinus(a, b),
            Self::SetContains(_) => ExpKind::AnySetContains(a, b),
            Self::MapContains => ExpKind::MapContains(a, b),
            Self::And => ExpKind::And(a, b),
            Self::Or => ExpKind::Or(a, b),
        }
    }
}
/// Evaluate a source expression with continuation-driven state and heap restoration.
/// Complete a function application from a snapshot into an explicit value receiver.
pub(crate) fn complete_owned_function_pre<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    snapshot: Option<Term>,
    frame: &OwnedFunctionPre<P, D, J>,
    done: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let snapshot = snapshot.ok_or(EvaluationError::MissingFunctionSnapshot)?;
    let (state_args, snapshot_to_record) = context
        .function_snapshot_args(
            &frame.pre_state,
            &frame.function,
            &frame.arguments,
            &snapshot,
        )
        .map_err(EvaluationError::Context)?;
    let symbol = context
        .heap_function(&frame.function, &frame.base.program)
        .map_err(EvaluationError::Context)?;
    let factory = context.factory().clone();
    let pre = crate::rules::function_supporter::precondition_version(&factory, &symbol);
    let mut all_args = state_args;
    all_args.extend(frame.arguments.iter().cloned());
    context
        .assume_function_precondition(
            &factory.app(pre, all_args.clone()),
            &frame.function,
            frame.debug_arguments.as_deref(),
        )
        .map_err(EvaluationError::Context)?;
    let opaque = matches!(frame.function.meta.info.find(&|info| matches!(info,ferrum_silver::ast::ast::Info::Annotation(_))),Some(ferrum_silver::ast::ast::Info::Annotation(a)) if a.contains_key("opaque"));
    let revealed = matches!(frame.expression.metadata().info.find(&|info| matches!(info,ferrum_silver::ast::ast::Info::Annotation(_))),Some(ferrum_silver::ast::ast::Info::Annotation(a)) if a.contains_key("reveal"));
    let symbol = if opaque && !revealed {
        crate::rules::function_supporter::limited_version(&factory, &symbol)
    } else {
        symbol
    };
    let term = factory.app(symbol, all_args);
    state.function_recorder = state
        .function_recorder
        .change_depth_by(-1)
        .record_function_snapshot(
            frame.expression.clone(),
            context.branch_conditions(),
            snapshot_to_record,
        );
    state.g = frame.base.g.clone();
    state.h = frame.base.h.clone();
    state.record_visited = frame.base.record_visited;
    state.sm_domain_needed = frame.base.sm_domain_needed;
    state.more_joins = frame.base.more_joins.clone();
    state.assert_read_access_only = frame.base.assert_read_access_only;
    let debug = if context.debugging() {
        let app = frame
            .application_debug
            .clone()
            .ok_or(EvaluationError::MissingDebugExpression)?;
        if state.is_eval_in_old || frame.preconditions.iter().all(Exp::is_pure) {
            Some(app)
        } else {
            Some(Exp::new(
                ExpKind::DebugLabelledOld(app, frame.label.clone()),
                frame.expression.metadata().clone(),
            ))
        }
    } else {
        None
    };
    done(context, state, term, debug)
}

/// Evaluate a direct asserting RHS whose statement continuation is explicitly owned.
pub(crate) fn evaluate_owned_asserting<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    receiver: &crate::rules::executor::OwnedAssignmentValue,
    return_frames: Vec<OwnedEvaluationReturnFrame>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let ExpKind::Asserting(assertion, body) = expression.kind() else {
        return Err(EvaluationError::OwnedSchedulerUnavailable);
    };
    let scope = context
        .open_evaluation_scope(&state, expression)
        .map_err(EvaluationError::Context)?;
    if scope.is_some() {
        return Err(EvaluationError::OwnedSchedulerUnavailable);
    }
    context
        .log_evaluation(&state, expression)
        .map_err(EvaluationError::Context)?;
    let outer_heap = state.h.clone();
    let outer_reserve = state.reserve_heaps.clone();
    let outer_exhale = state.exhale_ext;
    let mut state = state;
    state.h = context
        .eval_heap(&state)
        .map_err(EvaluationError::Context)?;
    state.reserve_heaps.clear();
    state.exhale_ext = false;
    let frame = OwnedAsserting {
        original_store: state.g.clone(),
        evaluation_heap: state.h.clone(),
        outer_heap,
        outer_reserve,
        outer_exhale,
        expression: expression.clone(),
        body: body.clone(),
        error: error.clone(),
        receiver: receiver.clone(),
        return_frames,
    };
    context
        .try_consume_owned_asserting(&state, assertion, &frame)
        .ok_or(EvaluationError::OwnedSchedulerUnavailable)?
}

/// Only transfer paths for which every intervening return action is represented.
fn owned_strict_binary(expression: &Exp) -> Option<(Binary, &Exp, &Exp)> {
    match expression.kind() {
        ExpKind::Sub(a, b) => Some((Binary::Sub, a, b)),
        ExpKind::Mul(a, b) => Some((Binary::Mul, a, b)),
        ExpKind::Div(a, b) => Some((Binary::Div, a, b)),
        ExpKind::Mod(a, b) => Some((Binary::Mod, a, b)),
        ExpKind::EqCmp(a, b) => Some((Binary::Eq, a, b)),
        ExpKind::NeCmp(a, b) => Some((Binary::Ne, a, b)),
        ExpKind::FractionalPerm(a, b) => Some((Binary::Fraction, a, b)),
        ExpKind::PermDiv(a, b) => Some((Binary::PermDiv, a, b)),
        ExpKind::PermPermDiv(a, b) => Some((Binary::PermPermDiv, a, b)),
        ExpKind::PermAdd(a, b) => Some((Binary::PermAdd, a, b)),
        ExpKind::PermSub(a, b) => Some((Binary::PermSub, a, b)),
        ExpKind::PermMul(a, b) => Some((Binary::PermMul, a, b)),
        ExpKind::DebugPermMin(a, b) => Some((Binary::PermMin, a, b)),
        ExpKind::IntPermMul(a, b) => Some((Binary::IntPermMul, a, b)),
        ExpKind::PermLeCmp(a, b) => Some((Binary::PermLe, a, b)),
        ExpKind::PermLtCmp(a, b) => Some((Binary::PermLt, a, b)),
        ExpKind::PermGeCmp(a, b) => Some((Binary::PermGe, a, b)),
        ExpKind::PermGtCmp(a, b) => Some((Binary::PermGt, a, b)),
        ExpKind::LeCmp(a, b) => Some((Binary::Le, a, b)),
        ExpKind::LtCmp(a, b) => Some((Binary::Lt, a, b)),
        ExpKind::GeCmp(a, b) => Some((Binary::Ge, a, b)),
        ExpKind::GtCmp(a, b) => Some((Binary::Gt, a, b)),
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum OwnedPathStep {
    Old,
    Minus,
    PermMinus,
    Not,
    FieldReceiver,
    LetValue,
    LetBody,
    DomainArg(usize),
    FunctionArg(usize),
    ExplicitCollectionArg(usize),
    IndexedCollectionArg(usize),
    CurrentPermArg(usize),
    AddLeft,
    AddRight,
    StrictLeft,
    StrictRight,
}

#[cfg(test)]
thread_local! { static OWNED_PATH_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) }; }
/// Select one leftmost supported path in a single traversal.
fn owned_asserting_path(expression: &Exp) -> Option<Vec<OwnedPathStep>> {
    enum Work<'a> {
        Visit(&'a Exp, Option<OwnedPathStep>),
        Leave,
    }
    let mut work = vec![Work::Visit(expression, None)];
    let mut path = Vec::new();
    while let Some(item) = work.pop() {
        match item {
            Work::Leave => {
                path.pop();
            }
            Work::Visit(exp, step) => {
                #[cfg(test)]
                OWNED_PATH_VISITS.with(|count| count.set(count.get() + 1));
                if let Some(step) = step {
                    path.push(step);
                    work.push(Work::Leave);
                }
                match exp.kind() {
                    ExpKind::Asserting(..) => return Some(path),
                    ExpKind::Old(body)
                    | ExpKind::LabelledOld(body, _)
                    | ExpKind::DebugLabelledOld(body, _) => {
                        work.push(Work::Visit(body, Some(OwnedPathStep::Old)))
                    }
                    ExpKind::Minus(body) => {
                        work.push(Work::Visit(body, Some(OwnedPathStep::Minus)))
                    }
                    ExpKind::PermMinus(body) => {
                        work.push(Work::Visit(body, Some(OwnedPathStep::PermMinus)))
                    }
                    ExpKind::Not(body) => work.push(Work::Visit(body, Some(OwnedPathStep::Not))),
                    ExpKind::FieldAccess(access) => work.push(Work::Visit(
                        &access.receiver,
                        Some(OwnedPathStep::FieldReceiver),
                    )),
                    ExpKind::CurrentPerm(access) => match access.kind() {
                        ExpKind::FieldAccess(field) => work.push(Work::Visit(
                            &field.receiver,
                            Some(OwnedPathStep::CurrentPermArg(0)),
                        )),
                        ExpKind::PredicateAccess(predicate) => {
                            for (index, arg) in predicate.args.iter().enumerate().rev() {
                                work.push(Work::Visit(
                                    arg,
                                    Some(OwnedPathStep::CurrentPermArg(index)),
                                ));
                            }
                        }
                        _ => (),
                    },
                    ExpKind::SeqIndex(a, b) | ExpKind::MapLookup(a, b) => {
                        work.push(Work::Visit(b, Some(OwnedPathStep::IndexedCollectionArg(1))));
                        work.push(Work::Visit(a, Some(OwnedPathStep::IndexedCollectionArg(0))));
                    }
                    ExpKind::SeqUpdate(a, b, c) | ExpKind::MapUpdate(a, b, c) => {
                        work.push(Work::Visit(c, Some(OwnedPathStep::IndexedCollectionArg(2))));
                        work.push(Work::Visit(b, Some(OwnedPathStep::IndexedCollectionArg(1))));
                        work.push(Work::Visit(a, Some(OwnedPathStep::IndexedCollectionArg(0))));
                    }
                    ExpKind::ExplicitSeq(args)
                    | ExpKind::ExplicitSet(args)
                    | ExpKind::ExplicitMultiset(args) => {
                        for (index, arg) in args.iter().enumerate().rev() {
                            work.push(Work::Visit(
                                arg,
                                Some(OwnedPathStep::ExplicitCollectionArg(index)),
                            ));
                        }
                    }
                    ExpKind::FuncApp(_, args) => {
                        for (index, arg) in args.iter().enumerate().rev() {
                            work.push(Work::Visit(arg, Some(OwnedPathStep::FunctionArg(index))));
                        }
                    }
                    ExpKind::DomainFuncApp(_, args, _) | ExpKind::BackendFuncApp(_, args) => {
                        for (index, arg) in args.iter().enumerate().rev() {
                            work.push(Work::Visit(arg, Some(OwnedPathStep::DomainArg(index))));
                        }
                    }
                    ExpKind::Let(_, value, body) => {
                        work.push(Work::Visit(body, Some(OwnedPathStep::LetBody)));
                        work.push(Work::Visit(value, Some(OwnedPathStep::LetValue)));
                    }
                    ExpKind::Add(left, right) => {
                        work.push(Work::Visit(right, Some(OwnedPathStep::AddRight)));
                        work.push(Work::Visit(left, Some(OwnedPathStep::AddLeft)));
                    }
                    _ => {
                        if let Some((_, left, right)) = owned_strict_binary(exp) {
                            work.push(Work::Visit(right, Some(OwnedPathStep::StrictRight)));
                            work.push(Work::Visit(left, Some(OwnedPathStep::StrictLeft)));
                        }
                    }
                }
            }
        }
    }
    None
}
pub(crate) fn has_owned_asserting_path(expression: &Exp) -> bool {
    match expression.kind() {
        ExpKind::Asserting(..) => true,
        ExpKind::Old(body)
        | ExpKind::LabelledOld(body, _)
        | ExpKind::DebugLabelledOld(body, _)
        | ExpKind::Minus(body)
        | ExpKind::PermMinus(body)
        | ExpKind::Not(body) => has_owned_asserting_path(body),
        ExpKind::FieldAccess(access) => has_owned_asserting_path(&access.receiver),
        ExpKind::CurrentPerm(access) => match access.kind() {
            ExpKind::FieldAccess(field) => has_owned_asserting_path(&field.receiver),
            ExpKind::PredicateAccess(predicate) => {
                predicate.args.iter().any(has_owned_asserting_path)
            }
            _ => false,
        },
        ExpKind::SeqIndex(a, b) | ExpKind::MapLookup(a, b) => {
            has_owned_asserting_path(a) || has_owned_asserting_path(b)
        }
        ExpKind::SeqUpdate(a, b, c) | ExpKind::MapUpdate(a, b, c) => {
            has_owned_asserting_path(a)
                || has_owned_asserting_path(b)
                || has_owned_asserting_path(c)
        }
        ExpKind::ExplicitSeq(args)
        | ExpKind::ExplicitSet(args)
        | ExpKind::ExplicitMultiset(args) => args.iter().any(has_owned_asserting_path),
        ExpKind::FuncApp(_, args) => args.iter().any(has_owned_asserting_path),
        ExpKind::DomainFuncApp(_, args, _) | ExpKind::BackendFuncApp(_, args) => {
            args.iter().any(has_owned_asserting_path)
        }
        ExpKind::Let(_, value, body) => {
            has_owned_asserting_path(value) || has_owned_asserting_path(body)
        }
        ExpKind::Add(left, right) => {
            has_owned_asserting_path(left) || has_owned_asserting_path(right)
        }
        _ => owned_strict_binary(expression).is_some_and(|(_, left, right)| {
            has_owned_asserting_path(left) || has_owned_asserting_path(right)
        }),
    }
}

/// Kept for the direct-old service tests; all wrappers use the same owned stack.
#[cfg(test)]
pub(crate) fn evaluate_owned_old_asserting<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    receiver: &crate::rules::executor::OwnedAssignmentValue,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    evaluate_owned_nested(context, state, expression, error, receiver, Vec::new())
}

#[cfg(test)]
thread_local! {
    static FORCE_OWNED_FALLBACK_AFTER_LEFT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static FALLBACK_RECEIVER_VALUES: std::cell::RefCell<Option<Vec<Term>>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
pub(crate) fn test_force_owned_fallback_after_left() {
    FORCE_OWNED_FALLBACK_AFTER_LEFT.with(|flag| flag.set(true));
}
#[cfg(test)]
pub(crate) fn test_capture_fallback_values(enabled: bool) -> Vec<Term> {
    FALLBACK_RECEIVER_VALUES.with(|slot| slot.replace(enabled.then(Vec::new)).unwrap_or_default())
}
#[cfg(test)]
fn test_change_guard_after_left<P, D, J>(mut state: State<P, D, J>) -> State<P, D, J> {
    if FORCE_OWNED_FALLBACK_AFTER_LEFT.with(|flag| flag.replace(false)) {
        state.under_join = true;
    }
    state
}

/// Select the leftmost supported path and save each surrounding evaluator
/// return action outermost first. Binary operators evaluate their left operand first.
pub(crate) fn evaluate_owned_nested<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    receiver: &crate::rules::executor::OwnedAssignmentValue,
    frames: Vec<OwnedEvaluationReturnFrame>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    if !context.can_transfer_owned_asserting(&state) {
        return evaluate(
            context,
            state,
            expression,
            error,
            &mut |context, state, term, debug| {
                resume_owned_return_frames(context, state, term, debug, &frames, error, receiver)
            },
        );
    }
    let path =
        owned_asserting_path(expression).ok_or(EvaluationError::OwnedSchedulerUnavailable)?;
    evaluate_owned_planned(context, state, expression, error, receiver, &path, frames)
}

fn evaluate_owned_planned<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    receiver: &crate::rules::executor::OwnedAssignmentValue,
    path: &[OwnedPathStep],
    mut frames: Vec<OwnedEvaluationReturnFrame>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    if !context.can_transfer_owned_asserting(&state) {
        return evaluate(
            context,
            state,
            expression,
            error,
            &mut |context, state, term, debug| {
                resume_owned_return_frames(context, state, term, debug, &frames, error, receiver)
            },
        );
    }
    let Some((step, rest)) = path.split_first() else {
        return evaluate_owned_asserting(context, state, expression, error, receiver, frames);
    };
    let scope = context
        .open_evaluation_scope(&state, expression)
        .map_err(EvaluationError::Context)?;
    if scope.is_some() {
        return Err(EvaluationError::OwnedSchedulerUnavailable);
    }
    context
        .log_evaluation(&state, expression)
        .map_err(EvaluationError::Context)?;
    let wrapper = OwnedValueWrapper {
        expression: expression.clone(),
        heap: state.h.clone(),
        reserve: state.reserve_heaps.clone(),
        exhale: state.exhale_ext,
    };
    let mut state = state;
    state.h = context
        .eval_heap(&state)
        .map_err(EvaluationError::Context)?;
    state.reserve_heaps.clear();
    state.exhale_ext = false;
    match (expression.kind(), step) {
        (
            ExpKind::Old(body) | ExpKind::LabelledOld(body, _) | ExpKind::DebugLabelledOld(body, _),
            OwnedPathStep::Old,
        ) => {
            let (label, kind) = match expression.kind() {
                ExpKind::Old(_) => ("old".to_string(), 0),
                ExpKind::LabelledOld(_, label) => (label.clone(), 1),
                ExpKind::DebugLabelledOld(_, label) => {
                    (label.split('#').next().unwrap_or(label).to_string(), 2)
                }
                _ => unreachable!(),
            };
            let Some(old_heap) = state.old_heaps.get(&label).cloned() else {
                if kind == 0 {
                    return Err(EvaluationError::MissingOldState(label));
                }
                let labelled = if kind == 2 {
                    Exp::new(
                        ExpKind::LabelledOld(body.clone(), label.clone()),
                        expression.metadata().clone(),
                    )
                } else {
                    expression.clone()
                };
                return context
                    .missing_label_failure(&state, error, &labelled, &label)
                    .map_err(EvaluationError::Context);
            };
            let old = OwnedOldValueFrame {
                expression: expression.clone(),
                label,
                kind,
                heap: state.h.clone(),
                partial_heap: state.partially_consumed_heap.clone(),
                possible_triggers: state.possible_triggers.clone(),
                record_possible_triggers: state.record_possible_triggers,
                is_eval_in_old: state.is_eval_in_old,
                program: state.program.clone(),
                evaluation_heap: wrapper.heap,
                evaluation_reserve: wrapper.reserve,
                evaluation_exhale: wrapper.exhale,
            };
            state.h = old_heap;
            state.partially_consumed_heap = None;
            state.is_eval_in_old = true;
            state.possible_triggers = Default::default();
            let state = context
                .consolidate_old(state)
                .map_err(EvaluationError::Context)?;
            frames.push(OwnedEvaluationReturnFrame::Old(old));
            evaluate_owned_planned(context, state, body, error, receiver, rest, frames)
        }
        (ExpKind::Minus(body), OwnedPathStep::Minus) => {
            frames.push(OwnedEvaluationReturnFrame::Minus(wrapper));
            evaluate_owned_planned(context, state, body, error, receiver, rest, frames)
        }
        (ExpKind::PermMinus(body), OwnedPathStep::PermMinus) => {
            frames.push(OwnedEvaluationReturnFrame::PermMinus(wrapper));
            evaluate_owned_planned(context, state, body, error, receiver, rest, frames)
        }
        (ExpKind::Not(body), OwnedPathStep::Not) => {
            frames.push(OwnedEvaluationReturnFrame::Not(wrapper));
            evaluate_owned_planned(context, state, body, error, receiver, rest, frames)
        }
        (ExpKind::FieldAccess(access), OwnedPathStep::FieldReceiver) => {
            let record_heap = context.debugging() && state.temporary_heap_record.is_some();
            frames.push(OwnedEvaluationReturnFrame::FieldReceiver {
                wrapper,
                record_heap,
            });
            evaluate_owned_planned(
                context,
                state,
                &access.receiver,
                error,
                receiver,
                rest,
                frames,
            )
        }
        (
            ExpKind::SeqIndex(..)
            | ExpKind::SeqUpdate(..)
            | ExpKind::MapLookup(..)
            | ExpKind::MapUpdate(..),
            OwnedPathStep::IndexedCollectionArg(index),
        ) => {
            let (_, args) =
                indexed_collection_arguments(expression).expect("indexed collection frame");
            evaluate_owned_arguments(
                context,
                state,
                &wrapper,
                &OwnedArgumentsTerminal::IndexedCollection(args),
                0,
                Vec::new(),
                Vec::new(),
                &frames,
                error,
                receiver,
                Some((*index, rest)),
            )
        }
        (
            ExpKind::ExplicitSeq(_) | ExpKind::ExplicitSet(_) | ExpKind::ExplicitMultiset(_),
            OwnedPathStep::ExplicitCollectionArg(index),
        ) => evaluate_owned_arguments(
            context,
            state,
            &wrapper,
            &OwnedArgumentsTerminal::ExplicitCollection,
            0,
            Vec::new(),
            Vec::new(),
            &frames,
            error,
            receiver,
            Some((*index, rest)),
        ),
        (ExpKind::FuncApp(name, _), OwnedPathStep::FunctionArg(index)) => {
            let function = state
                .program
                .functions
                .iter()
                .find(|function| &function.name == name)
                .cloned()
                .ok_or_else(|| EvaluationError::MissingFunction(name.clone()))?;
            let record_heap = context.debugging() && state.temporary_heap_record.is_some();
            evaluate_owned_arguments(
                context,
                state,
                &wrapper,
                &OwnedArgumentsTerminal::Function {
                    function,
                    record_heap,
                },
                0,
                Vec::new(),
                Vec::new(),
                &frames,
                error,
                receiver,
                Some((*index, rest)),
            )
        }
        (
            ExpKind::DomainFuncApp(name, _, _) | ExpKind::BackendFuncApp(name, _),
            OwnedPathStep::DomainArg(index),
        ) => {
            let function = state
                .program
                .find_domain_function_optionally(name)
                .cloned()
                .ok_or_else(|| EvaluationError::MissingDomainFunction(name.clone()))?;
            evaluate_owned_arguments(
                context,
                state,
                &wrapper,
                &OwnedArgumentsTerminal::Domain(function),
                0,
                Vec::new(),
                Vec::new(),
                &frames,
                error,
                receiver,
                Some((*index, rest)),
            )
        }
        (ExpKind::CurrentPerm(access), OwnedPathStep::CurrentPermArg(index)) => {
            let heap = state
                .partially_consumed_heap
                .clone()
                .unwrap_or_else(|| state.h.clone());
            let (resource, args) = current_permission_resource(&state, access)?;
            let terminal = OwnedArgumentsTerminal::CurrentPerm {
                access: access.clone(),
                resource,
                heap,
                args,
            };
            evaluate_owned_arguments(
                context,
                state,
                &wrapper,
                &terminal,
                0,
                Vec::new(),
                Vec::new(),
                &frames,
                error,
                receiver,
                Some((*index, rest)),
            )
        }
        (ExpKind::Let(_, value, _), OwnedPathStep::LetValue) => {
            frames.push(OwnedEvaluationReturnFrame::LetValue(wrapper));
            evaluate_owned_planned(context, state, value, error, receiver, rest, frames)
        }
        (ExpKind::Let(_, value, _), OwnedPathStep::LetBody) => evaluate(
            context,
            state,
            value,
            error,
            &mut |context, state, term, debug| {
                resume_owned_let_value(
                    context,
                    state,
                    term,
                    debug,
                    &wrapper,
                    &frames,
                    error,
                    receiver,
                    Some(rest),
                )
            },
        ),
        (_, OwnedPathStep::StrictLeft) => {
            let (_, left, right) =
                owned_strict_binary(expression).expect("planned strict operator");
            frames.push(OwnedEvaluationReturnFrame::StrictLeft {
                wrapper,
                right: right.clone(),
            });
            evaluate_owned_planned(context, state, left, error, receiver, rest, frames)
        }
        (_, OwnedPathStep::StrictRight) => {
            let (_, left, right) =
                owned_strict_binary(expression).expect("planned strict operator");
            evaluate(
                context,
                state,
                left,
                error,
                &mut |context, state, term, debug| {
                    #[cfg(test)]
                    let state = test_change_guard_after_left(state);
                    let mut next = frames.clone();
                    next.push(OwnedEvaluationReturnFrame::StrictRight {
                        wrapper: wrapper.clone(),
                        left: term,
                        left_debug: debug,
                    });
                    evaluate_owned_planned(context, state, right, error, receiver, rest, next)
                },
            )
        }
        (ExpKind::Add(left, right), OwnedPathStep::AddLeft) => {
            frames.push(OwnedEvaluationReturnFrame::AddLeft {
                wrapper,
                right: right.clone(),
            });
            evaluate_owned_planned(context, state, left, error, receiver, rest, frames)
        }
        (ExpKind::Add(left, right), OwnedPathStep::AddRight) => evaluate(
            context,
            state,
            left,
            error,
            &mut |context, state, term, debug| {
                #[cfg(test)]
                let state = test_change_guard_after_left(state);
                let mut next = frames.clone();
                next.push(OwnedEvaluationReturnFrame::AddRight {
                    wrapper: wrapper.clone(),
                    left: term,
                    left_debug: debug,
                });
                evaluate_owned_planned(context, state, right, error, receiver, rest, next)
            },
        ),
        _ => Err(EvaluationError::OwnedSchedulerUnavailable),
    }
}
#[cfg(test)]
thread_local! {
    static OWNED_ASSERTING_RESUME_HOOK: std::cell::RefCell<Option<Box<dyn FnOnce()>>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
pub(crate) fn set_owned_asserting_resume_hook(hook: impl FnOnce() + 'static) {
    OWNED_ASSERTING_RESUME_HOOK.with(|slot| *slot.borrow_mut() = Some(Box::new(hook)));
}

/// Resume an asserting RHS after consuming its assertion.
pub(crate) fn complete_owned_asserting<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    frame: &OwnedAsserting<C::PartialError>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    #[cfg(test)]
    context.test_owned_right_resume(frame);
    #[cfg(test)]
    let hook = OWNED_ASSERTING_RESUME_HOOK.with(|slot| slot.borrow_mut().take());
    #[cfg(test)]
    if let Some(hook) = hook {
        hook();
    }
    state.g = frame.original_store.clone();
    state.h = frame.evaluation_heap.clone();
    let mut frames = frame.return_frames.clone();
    frames.push(OwnedEvaluationReturnFrame::Asserting(OwnedValueWrapper {
        expression: frame.expression.clone(),
        heap: frame.outer_heap.clone(),
        reserve: frame.outer_reserve.clone(),
        exhale: frame.outer_exhale,
    }));
    if has_owned_asserting_path(&frame.body) && context.can_transfer_owned_asserting(&state) {
        evaluate_owned_nested(
            context,
            state,
            &frame.body,
            &frame.error,
            &frame.receiver,
            frames,
        )
    } else {
        evaluate(
            context,
            state,
            &frame.body,
            &frame.error,
            &mut |context, state, term, debug| {
                resume_owned_return_frames(
                    context,
                    state,
                    term,
                    debug,
                    &frames,
                    &frame.error,
                    &frame.receiver,
                )
            },
        )
    }
}

#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct OldReturnSnapshot {
    pub heap: Arc<ListBackedHeap>,
    pub partial: Option<Arc<ListBackedHeap>>,
    pub triggers: crate::state::package::OrderedMap<Exp, Term>,
    pub in_old: bool,
}
#[cfg(test)]
pub(crate) fn test_old_return_snapshot<P, D, J>(state: &State<P, D, J>) -> OldReturnSnapshot {
    OldReturnSnapshot {
        heap: state.h.clone(),
        partial: state.partially_consumed_heap.clone(),
        triggers: state.possible_triggers.clone(),
        in_old: state.is_eval_in_old,
    }
}
#[cfg(test)]
thread_local! {
    static OLD_RETURN_SNAPSHOTS: std::cell::RefCell<Option<Vec<OldReturnSnapshot>>> = const { std::cell::RefCell::new(None) };
    static LET_DEBUG_VALUES: std::cell::RefCell<Option<Vec<Option<Exp>>>> = const { std::cell::RefCell::new(None) };
}
#[cfg(test)]
pub(crate) fn test_capture_let_debug(enabled: bool) -> Vec<Option<Exp>> {
    LET_DEBUG_VALUES.with(|slot| slot.replace(enabled.then(Vec::new)).unwrap_or_default())
}
#[cfg(test)]
pub(crate) fn test_capture_old_returns(enabled: bool) -> Vec<OldReturnSnapshot> {
    OLD_RETURN_SNAPSHOTS.with(|slot| slot.replace(enabled.then(Vec::new)).unwrap_or_default())
}

fn current_permission_resource<P, D, J, E>(
    state: &State<P, D, J>,
    access: &Exp,
) -> Result<(crate::state::terms::ResourceKey, Vec<Exp>), EvaluationError<E>> {
    use crate::state::{chunks::MagicWandIdentifier, terms::ResourceKey};
    match access.kind() {
        ExpKind::FieldAccess(field) => Ok((
            ResourceKey::Field(Arc::new(field.field.clone())),
            vec![field.receiver.clone()],
        )),
        ExpKind::PredicateAccess(predicate) => {
            let name = &predicate.predicate_name;
            let decl = state
                .program
                .predicates
                .iter()
                .find(|p| &p.name == name)
                .ok_or_else(|| EvaluationError::MissingPredicate(name.clone()))?;
            Ok((
                ResourceKey::Predicate(Arc::new(decl.clone())),
                predicate.args.clone(),
            ))
        }
        ExpKind::MagicWand(..) => {
            let wand = MagicWandIdentifier::new(access.clone(), &state.program)
                .map_err(EvaluationError::Wand)?;
            let args = access
                .magic_wand_subexpressions(&state.program)
                .map_err(EvaluationError::Wand)?;
            Ok((ResourceKey::Wand(wand), args))
        }
        _ => Err(EvaluationError::InvalidResourceAccess),
    }
}

fn complete_current_permission<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    heap: Arc<ListBackedHeap>,
    access: &Exp,
    resource: &crate::state::terms::ResourceKey,
    terms: Vec<Term>,
    debug_args: Option<Vec<Exp>>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let record = context.debugging() && state.temporary_heap_record.is_some();
    let state = if record {
        context
            .record_intermediate_heap(state, expression)
            .map_err(EvaluationError::Context)?
    } else {
        state
    };
    context.eval_current_permission(
        state,
        heap,
        access,
        resource,
        &terms,
        debug_args.as_deref(),
        &mut |context, state, term| {
            let debug = context.debugging().then(|| expression.clone());
            continuation(context, state, term, debug)
        },
    )
}

/// Complete a function application after all arguments have been evaluated.
fn complete_function_application<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    function: &ferrum_silver::ast::program::Function,
    record_heap: bool,
    terms: Vec<Term>,
    debug_args: Option<Vec<Exp>>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let ExpKind::FuncApp(name, args) = expression.kind() else {
        unreachable!("function application frame")
    };
    let factory = context.factory().clone();
    let state = if record_heap {
        context
            .record_intermediate_heap(state, expression)
            .map_err(EvaluationError::Context)?
    } else {
        state
    };
    let label = context
        .debug_old_label(&state, &expression.metadata().position)
        .map_err(EvaluationError::Context)?;
    let application_debug = debug_args.as_ref().map(|args| {
        Exp::with_extra(
            ExpKind::FuncApp(name.clone(), args.clone()),
            expression.metadata().clone(),
            expression.0.extra.clone(),
        )
    });
    let join_debug = if context.debugging() {
        let app = application_debug
            .clone()
            .ok_or(EvaluationError::MissingDebugExpression)?;
        if state.is_eval_in_old || function.pres.iter().all(Exp::is_pure) {
            Some(app)
        } else {
            Some(Exp::new(
                ExpKind::DebugLabelledOld(app, label.clone()),
                expression.metadata().clone(),
            ))
        }
    } else {
        None
    };
    context.join_function_application_with_owned(state,&function,&terms,join_debug.as_ref(),&mut |context,base,done,owned_join| {
                let mut pres = Vec::new();
                for pre in &function.pres {
                    let transformed = ferrum_silver::ast::utility::rewriter::strategy::rewrite_expression_bottom_up(pre,&mut |e| Ok::<_, &'static str>(match e.kind() { ExpKind::Forall(vars,_,body) => Exp::new(ExpKind::Forall(vars.clone(),vec![],body.clone()),e.metadata().clone()), _ => e.clone() }),&|_,_| Err(ferrum_silver::ast::utility::rewriter::strategy::ExpressionRewriteError::Callback("extension reconstruction unsupported"))).map_err(EvaluationError::PreconditionRewrite)?;
                    pres.push(transformed);
                }
                let mut bindings = Vec::new();
                for (index,(decl,term)) in function.formal_args.iter().zip(&terms).enumerate() {
                    let debug = if context.debugging() { Some(debug_args.as_ref().and_then(|es| es.get(index)).cloned().ok_or(EvaluationError::MissingDebugExpression)?) } else { None };
                    bindings.push((AbstractLocalVar::new(Exp::new(ExpKind::LocalVar(decl.local_var()),decl.meta.clone())),(term.clone(),debug)));
                }
                let mut pre_state = base.clone();
                pre_state.g = Arc::new(crate::state::store::MapBackedStore::from_bindings(bindings));
                pre_state.record_visited = true; pre_state.function_recorder = pre_state.function_recorder.change_depth_by(1);
                pre_state.sm_domain_needed = true; pre_state.more_joins = context.join_off();
                if !context.respect_function_pre_permission_amounts() { pre_state.assert_read_access_only = true; }
                let pre_state_for_snapshot = pre_state.clone();
                if let Some(join) = owned_join {
                    let frame = OwnedFunctionPre { join: join.clone(), base: base.clone(), pre_state: pre_state.clone(), function: function.clone(), expression: expression.clone(), argument_expressions: args.to_vec(), arguments: terms.clone(), debug_arguments: debug_args.clone(), application_debug: application_debug.clone(), label: label.clone(), preconditions: pres.clone() };
                    if let Some(result) = context.try_consume_owned_function_preconditions(&pre_state, &frame) { return result; }
                }
                context.consume_function_preconditions(pre_state,&base.g,&function,expression,args,&pres,&mut |context,mut state,snapshot| {
                    let snapshot = snapshot.ok_or(EvaluationError::MissingFunctionSnapshot)?;
                    let (state_args,snapshot_to_record) = context.function_snapshot_args(&pre_state_for_snapshot,&function,&terms,&snapshot).map_err(EvaluationError::Context)?;
                    let symbol = context.heap_function(&function,&base.program).map_err(EvaluationError::Context)?;
                    let pre = crate::rules::function_supporter::precondition_version(&factory,&symbol);
                    let mut all_args = state_args; all_args.extend(terms.iter().cloned());
                    context.assume_function_precondition(&factory.app(pre,all_args.clone()),&function,debug_args.as_deref()).map_err(EvaluationError::Context)?;
                    let opaque = matches!(function.meta.info.find(&|info| matches!(info,ferrum_silver::ast::ast::Info::Annotation(_))),Some(ferrum_silver::ast::ast::Info::Annotation(a)) if a.contains_key("opaque"));
                    let revealed = matches!(expression.metadata().info.find(&|info| matches!(info,ferrum_silver::ast::ast::Info::Annotation(_))),Some(ferrum_silver::ast::ast::Info::Annotation(a)) if a.contains_key("reveal"));
                    let symbol = if opaque && !revealed { crate::rules::function_supporter::limited_version(&factory,&symbol) } else { symbol };
                    let term = factory.app(symbol,all_args);
                    state.function_recorder = state.function_recorder.change_depth_by(-1).record_function_snapshot(expression.clone(),context.branch_conditions(),snapshot_to_record);
                    state.g = base.g.clone(); state.h = base.h.clone(); state.record_visited = base.record_visited; state.sm_domain_needed = base.sm_domain_needed; state.more_joins = base.more_joins.clone(); state.assert_read_access_only = base.assert_read_access_only;
                    let debug = if context.debugging() { let app = application_debug.clone().ok_or(EvaluationError::MissingDebugExpression)?; if state.is_eval_in_old || pres.iter().all(Exp::is_pure) { Some(app) } else { Some(Exp::new(ExpKind::DebugLabelledOld(app,label.clone()),expression.metadata().clone())) } } else { None };
                    done(context,state,term,debug)
                })
            },continuation)
}

fn indexed_collection_arguments(expression: &Exp) -> Option<(u8, Vec<Exp>)> {
    match expression.kind() {
        ExpKind::SeqIndex(seq, index) => Some((0, vec![seq.clone(), index.clone()])),
        ExpKind::SeqUpdate(seq, index, value) => {
            Some((1, vec![seq.clone(), index.clone(), value.clone()]))
        }
        ExpKind::MapLookup(base, key) => Some((2, vec![base.clone(), key.clone()])),
        ExpKind::MapUpdate(base, key, value) => {
            Some((3, vec![base.clone(), key.clone(), value.clone()]))
        }
        _ => None,
    }
}

/// Finish an indexed collection after all operands, including source checks.
fn complete_indexed_collection<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    args: &[Exp],
    terms: Vec<Term>,
    debug_args: Option<Vec<Exp>>,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let (kind, _) = indexed_collection_arguments(expression).expect("indexed collection frame");
    let factory = context.factory().clone();
    let result = match kind {
        0 => factory.seq_at(terms[0].clone(), terms[1].clone()),
        1 => factory.seq_update(terms[0].clone(), terms[1].clone(), terms[2].clone()),
        2 => factory.map_lookup(terms[0].clone(), terms[1].clone()),
        _ => factory.map_update(terms[0].clone(), terms[1].clone(), terms[2].clone()),
    };
    let rebuilt = debug_args.as_ref().map(|es| {
        Exp::new(
            match kind {
                0 => ExpKind::SeqIndex(es[0].clone(), es[1].clone()),
                1 => ExpKind::SeqUpdate(es[0].clone(), es[1].clone(), es[2].clone()),
                2 => ExpKind::MapLookup(es[0].clone(), es[1].clone()),
                _ => ExpKind::MapUpdate(es[0].clone(), es[1].clone(), es[2].clone()),
            },
            expression.metadata().clone(),
        )
    });
    if kind == 3 || state.trigger_exp {
        return continuation(context, state, result, rebuilt);
    }
    if kind <= 1 {
        let checked = sequence_bounds(
            context,
            &state,
            &terms[0],
            &terms[1],
            &args[0],
            &args[1],
            debug_args.as_deref(),
            error,
        )?;
        if checked
            .with_kind(|kind| matches!(kind, crate::interfaces::verification::ResultKind::Success))
        {
            return continuation(context, state, result, rebuilt);
        }
        if state.retry_level == 0
            && context.report_further_errors()
            && checked.continue_verification()
        {
            let next = continuation(context, state, result, rebuilt)?;
            return Ok(checked.combine(|| next, false));
        }
        return Ok(checked);
    }
    let assertion = factory.set_in(terms[1].clone(), factory.map_domain(terms[0].clone()));
    if context
        .assert_goal(&assertion)
        .map_err(EvaluationError::Context)?
    {
        return continuation(context, state, result, rebuilt);
    }
    let original_test = context.debugging().then(|| {
        Exp::new(
            ExpKind::MapContains(args[1].clone(), args[0].clone()),
            expression.metadata().clone(),
        )
    });
    let rewritten_test = if context.debugging() {
        let es = debug_args
            .as_ref()
            .ok_or(EvaluationError::MissingDebugExpression)?;
        Some(Exp::new(
            ExpKind::MapContains(es[1].clone(), es[0].clone()),
            expression.metadata().clone(),
        ))
    } else {
        None
    };
    let failure = context
        .map_key_failure(
            &state,
            error,
            &args[0],
            &args[1],
            &assertion,
            rewritten_test.as_ref(),
        )
        .map_err(EvaluationError::Context)?;
    if state.retry_level == 0 && context.report_further_errors() {
        context
            .assume_generated(&assertion, original_test.as_ref(), rewritten_test.as_ref())
            .map_err(EvaluationError::Context)?;
        if failure.continue_verification() {
            let next = continuation(context, state, result, rebuilt)?;
            return Ok(failure.combine(|| next, false));
        }
    }
    Ok(failure)
}

/// Complete an explicit sequence, set or multiset after evaluating elements.
fn complete_explicit_collection<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    terms: Vec<Term>,
    debug_elements: Option<Vec<Exp>>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let (kind, elements) = match expression.kind() {
        ExpKind::ExplicitSeq(es) => (0, es),
        ExpKind::ExplicitSet(es) => (1, es),
        ExpKind::ExplicitMultiset(es) => (2, es),
        _ => unreachable!("explicit collection frame"),
    };
    let factory = context.factory().clone();
    let Some((first, rest)) = terms.split_first() else {
        return Err(EvaluationError::EmptyExplicitCollection);
    };
    let mut result = match kind {
        0 => factory.seq_singleton(first.clone()),
        1 => factory.singleton_set(first.clone()),
        _ => factory.singleton_multiset(first.clone()),
    };
    for term in rest {
        result = match kind {
            0 => factory.seq_append(result, factory.seq_singleton(term.clone())),
            1 => factory.set_add(result, term.clone()),
            _ => factory.multiset_add(result, term.clone()),
        };
    }
    let reconstructed = debug_elements.map(|es| {
        Exp::new(
            match kind {
                0 => ExpKind::ExplicitSeq(es),
                1 => ExpKind::ExplicitSet(es),
                _ => ExpKind::ExplicitMultiset(es),
            },
            expression.metadata().clone(),
        )
    });
    if kind == 0 {
        let equality = factory.equals(
            factory.seq_length(result.clone()),
            factory.int_literal(elements.len()),
        );
        let make_equality = |seq: Exp| {
            Exp::new(
                ExpKind::EqCmp(
                    Exp::new(ExpKind::SeqLength(seq), Default::default()),
                    Exp::new(ExpKind::IntLit(elements.len().into()), Default::default()),
                ),
                expression.metadata().clone(),
            )
        };
        let original = context
            .debugging()
            .then(|| make_equality(expression.clone()));
        let rewritten = if context.debugging() {
            Some(make_equality(
                reconstructed
                    .clone()
                    .ok_or(EvaluationError::MissingDebugExpression)?,
            ))
        } else {
            None
        };
        context
            .assume_generated(&equality, original.as_ref(), rewritten.as_ref())
            .map_err(EvaluationError::Context)?;
    }
    continuation(context, state, result, reconstructed)
}

/// Complete a resolved domain/backend application after its arguments.
fn complete_domain_application<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    function: &ferrum_silver::ast::program::DomainFunc,
    terms: Vec<Term>,
    debug_args: Option<Vec<Exp>>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let (name, substitutions, backend) = match expression.kind() {
        ExpKind::DomainFuncApp(name, _, substitutions) => (name, Some(substitutions), false),
        ExpKind::BackendFuncApp(name, _) => (name, None, true),
        _ => unreachable!("domain application frame"),
    };
    let argument_sorts: Vec<_> = terms.iter().map(|term| term.sort().clone()).collect();
    let result_type = expression.typ().map_err(EvaluationError::ExpressionType)?;
    let result_sort = context
        .to_sort(&result_type)
        .map_err(EvaluationError::Context)?;
    let function = context
        .domain_function(
            function,
            &state.program,
            &argument_sorts,
            &result_sort,
            backend,
        )
        .map_err(EvaluationError::Context)?;
    let term = context.factory().app(function, terms);
    let debug = if context.debugging() {
        let args = debug_args.ok_or(EvaluationError::MissingDebugExpression)?;
        let kind = if backend {
            ExpKind::BackendFuncApp(name.clone(), args)
        } else {
            ExpKind::DomainFuncApp(
                name.clone(),
                args,
                substitutions.expect("domain substitutions").clone(),
            )
        };
        Some(Exp::with_extra(
            kind,
            expression.metadata().clone(),
            expression.0.extra.clone(),
        ))
    } else {
        None
    };
    continuation(context, state, term, debug)
}

fn rebuild_domain_debug_arguments<E>(
    debugging: bool,
    values: Vec<Option<Exp>>,
) -> Result<Option<Vec<Exp>>, EvaluationError<E>> {
    let mut debug = debugging.then(Vec::new);
    for value in values.into_iter().rev() {
        debug = if let Some(value) = value {
            let mut tail = debug.ok_or(EvaluationError::MissingDebugExpression)?;
            tail.insert(0, value);
            Some(tail)
        } else {
            None
        };
    }
    Ok(debug)
}

#[derive(Clone)]
enum OwnedArgumentsTerminal {
    IndexedCollection(Vec<Exp>),
    ExplicitCollection,
    Function {
        function: ferrum_silver::ast::program::Function,
        record_heap: bool,
    },
    Domain(ferrum_silver::ast::program::DomainFunc),
    CurrentPerm {
        access: Exp,
        resource: crate::state::terms::ResourceKey,
        heap: Arc<ListBackedHeap>,
        args: Vec<Exp>,
    },
}

/// Evaluate owned argument lists left-to-right while retaining their complete prefix.
fn evaluate_owned_arguments<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    wrapper: &OwnedValueWrapper,
    terminal: &OwnedArgumentsTerminal,
    index: usize,
    terms: Vec<Term>,
    debug_args: Vec<Option<Exp>>,
    frames: &[OwnedEvaluationReturnFrame],
    error: &C::PartialError,
    receiver: &crate::rules::executor::OwnedAssignmentValue,
    selected: Option<(usize, &[OwnedPathStep])>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let args = match terminal {
        OwnedArgumentsTerminal::IndexedCollection(args) => args,
        OwnedArgumentsTerminal::ExplicitCollection => match wrapper.expression.kind() {
            ExpKind::ExplicitSeq(args)
            | ExpKind::ExplicitSet(args)
            | ExpKind::ExplicitMultiset(args) => args,
            _ => unreachable!("explicit collection frame"),
        },
        OwnedArgumentsTerminal::Function { .. } => match wrapper.expression.kind() {
            ExpKind::FuncApp(_, args) => args,
            _ => unreachable!("function argument frame"),
        },
        OwnedArgumentsTerminal::Domain(_) => match wrapper.expression.kind() {
            ExpKind::DomainFuncApp(_, args, _) | ExpKind::BackendFuncApp(_, args) => args,
            _ => unreachable!("domain argument frame"),
        },
        OwnedArgumentsTerminal::CurrentPerm { args, .. } => args,
    };
    if index == args.len() {
        let debug = rebuild_domain_debug_arguments(context.debugging(), debug_args)?;
        let mut done = |context: &mut C, mut state, term, debug| {
            finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &term)?;
            resume_owned_return_frames(context, state, term, debug, frames, error, receiver)
        };
        return match terminal {
            OwnedArgumentsTerminal::IndexedCollection(args) => complete_indexed_collection(
                context,
                state,
                &wrapper.expression,
                args,
                terms,
                debug,
                error,
                &mut done,
            ),
            OwnedArgumentsTerminal::ExplicitCollection => complete_explicit_collection(
                context,
                state,
                &wrapper.expression,
                terms,
                debug,
                &mut done,
            ),
            OwnedArgumentsTerminal::Function {
                function,
                record_heap,
            } => complete_function_application(
                context,
                state,
                &wrapper.expression,
                function,
                *record_heap,
                terms,
                debug,
                &mut done,
            ),
            OwnedArgumentsTerminal::Domain(function) => complete_domain_application(
                context,
                state,
                &wrapper.expression,
                function,
                terms,
                debug,
                &mut done,
            ),
            OwnedArgumentsTerminal::CurrentPerm {
                access,
                resource,
                heap,
                ..
            } => complete_current_permission(
                context,
                state,
                &wrapper.expression,
                heap.clone(),
                access,
                resource,
                terms,
                debug,
                &mut done,
            ),
        };
    }
    let argument = &args[index];
    let planned = match selected {
        Some((target, path)) if target == index => Some(path.to_vec()),
        Some(_) => None,
        None if context.can_transfer_owned_asserting(&state) => owned_asserting_path(argument),
        None => None,
    };
    if let Some(path) = planned {
        let mut next = frames.to_vec();
        next.push(match terminal {
            OwnedArgumentsTerminal::IndexedCollection(args) => {
                OwnedEvaluationReturnFrame::IndexedCollectionArg {
                    wrapper: wrapper.clone(),
                    args: args.clone(),
                    index,
                    terms,
                    debug_args,
                }
            }
            OwnedArgumentsTerminal::ExplicitCollection => {
                OwnedEvaluationReturnFrame::ExplicitCollectionArg {
                    wrapper: wrapper.clone(),
                    index,
                    terms,
                    debug_args,
                }
            }
            OwnedArgumentsTerminal::Function {
                function,
                record_heap,
            } => OwnedEvaluationReturnFrame::FunctionArg {
                wrapper: wrapper.clone(),
                function: function.clone(),
                record_heap: *record_heap,
                index,
                terms,
                debug_args,
            },
            OwnedArgumentsTerminal::Domain(function) => OwnedEvaluationReturnFrame::DomainArg {
                wrapper: wrapper.clone(),
                function: function.clone(),
                index,
                terms,
                debug_args,
            },
            OwnedArgumentsTerminal::CurrentPerm {
                access,
                resource,
                heap,
                args,
            } => OwnedEvaluationReturnFrame::CurrentPermArg {
                wrapper: wrapper.clone(),
                access: access.clone(),
                resource: resource.clone(),
                heap: heap.clone(),
                args: args.clone(),
                index,
                terms,
                debug_args,
            },
        });
        return evaluate_owned_planned(context, state, argument, error, receiver, &path, next);
    }
    evaluate(
        context,
        state,
        argument,
        error,
        &mut |context, state, term, debug| {
            let mut next_terms = terms.clone();
            next_terms.push(term);
            let mut next_debug = debug_args.clone();
            next_debug.push(debug);
            evaluate_owned_arguments(
                context,
                state,
                wrapper,
                terminal,
                index + 1,
                next_terms,
                next_debug,
                frames,
                error,
                receiver,
                selected,
            )
        },
    )
}

/// Bind a completed Let value, then evaluate its body with an owned return frame.
fn resume_owned_let_value<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    value_term: Term,
    value_debug: Option<Exp>,
    wrapper: &OwnedValueWrapper,
    frames: &[OwnedEvaluationReturnFrame],
    error: &C::PartialError,
    receiver: &crate::rules::executor::OwnedAssignmentValue,
    body_path: Option<&[OwnedPathStep]>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let ExpKind::Let(declaration, value, body) = wrapper.expression.kind() else {
        unreachable!("let frame")
    };
    let mut variables = state.function_recorder.arguments().unwrap_or_default();
    variables.extend(state.packaging_wand_snapshots.clone());
    variables.extend(state.quantified_variables.clone());
    let variables: Vec<_> = variables.into_iter().map(|(term, _)| term).collect();
    let (fresh, applicable) = context
        .fresh_let_application(&declaration.typ, &variables)
        .map_err(EvaluationError::Context)?;
    let equality = context.factory().builtin_equals(fresh, value_term.clone());
    let variable = declaration.local_var();
    if context.debugging() && value_debug.is_none() {
        return Err(EvaluationError::MissingDebugExpression);
    }
    context
        .assume_let_definition(&equality, &variable, value, value_debug.as_ref())
        .map_err(EvaluationError::Context)?;
    state.function_recorder = state
        .function_recorder
        .record_fresh_snapshot(applicable)
        .enter_let(wrapper.expression.clone());
    let before = state.possible_triggers.clone();
    let local = Exp::new(ExpKind::LocalVar(variable), declaration.meta.clone());
    let key = AbstractLocalVar::new(local.clone());
    state.g = Arc::new(state.g.with_binding(key, (value_term, value_debug.clone())));
    let mut next = frames.to_vec();
    next.push(OwnedEvaluationReturnFrame::LetBody {
        wrapper: wrapper.clone(),
        before,
        local,
        value_debug,
    });
    if let Some(path) = body_path {
        return evaluate_owned_planned(context, state, body, error, receiver, path, next);
    }
    if context.can_transfer_owned_asserting(&state) {
        if let Some(path) = owned_asserting_path(body) {
            return evaluate_owned_planned(context, state, body, error, receiver, &path, next);
        }
    }
    evaluate(
        context,
        state,
        body,
        error,
        &mut |context, state, term, debug| {
            resume_owned_return_frames(context, state, term, debug, &next, error, receiver)
        },
    )
}

fn resume_owned_return_frames<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    mut term: Term,
    mut debug: Option<Exp>,
    frames: &[OwnedEvaluationReturnFrame],
    error: &C::PartialError,
    receiver: &crate::rules::executor::OwnedAssignmentValue,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    for (index, frame) in frames.iter().enumerate().rev() {
        match frame {
            OwnedEvaluationReturnFrame::Old(old) => {
                let mut triggers = old.possible_triggers.clone();
                if old.record_possible_triggers {
                    for (exp, value) in state.possible_triggers.iter() {
                        let wrapped = if old.label == "old" {
                            ExpKind::Old(exp.clone())
                        } else {
                            ExpKind::LabelledOld(exp.clone(), old.label.clone())
                        };
                        triggers.insert(Exp::new(wrapped, exp.metadata().clone()), value.clone());
                    }
                    for (exp, value) in state.possible_triggers.iter() {
                        if !context
                            .is_heap_dependent(exp, &old.program)
                            .map_err(EvaluationError::Context)?
                        {
                            triggers.insert(exp.clone(), value.clone());
                        }
                    }
                }
                state.h = old.heap.clone();
                state.partially_consumed_heap = old.partial_heap.clone();
                state.possible_triggers = triggers;
                state.is_eval_in_old = old.is_eval_in_old;
                debug = if old.kind == 2 {
                    Some(old.expression.clone())
                } else {
                    debug.map(|e| {
                        Exp::new(
                            if old.kind == 0 {
                                ExpKind::Old(e)
                            } else {
                                ExpKind::LabelledOld(e, old.label.clone())
                            },
                            old.expression.metadata().clone(),
                        )
                    })
                };
                if state.record_possible_triggers {
                    context
                        .record_possible_trigger(&mut state, &old.expression, &term)
                        .map_err(EvaluationError::Context)?;
                }
                state.h = old.evaluation_heap.clone();
                state.reserve_heaps = old.evaluation_reserve.clone();
                state.exhale_ext = old.evaluation_exhale;
                context
                    .close_evaluation_scope(None)
                    .map_err(EvaluationError::Context)?;
            }
            OwnedEvaluationReturnFrame::FieldReceiver {
                wrapper,
                record_heap,
            } => {
                return finish_field_receiver(
                    context,
                    state,
                    &wrapper.expression,
                    error,
                    &term,
                    debug.as_ref(),
                    *record_heap,
                    &mut |context, mut state, value, rebuilt| {
                        finish_owned_wrapper::<C, P, D, J, V>(
                            context, &mut state, wrapper, &value,
                        )?;
                        resume_owned_return_frames(
                            context,
                            state,
                            value,
                            rebuilt,
                            &frames[..index],
                            error,
                            receiver,
                        )
                    },
                );
            }
            OwnedEvaluationReturnFrame::IndexedCollectionArg {
                wrapper,
                args,
                index: argument_index,
                terms,
                debug_args,
            } => {
                let mut terms = terms.clone();
                terms.push(term);
                let mut debug_args = debug_args.clone();
                debug_args.push(debug);
                return evaluate_owned_arguments(
                    context,
                    state,
                    wrapper,
                    &OwnedArgumentsTerminal::IndexedCollection(args.clone()),
                    argument_index + 1,
                    terms,
                    debug_args,
                    &frames[..index],
                    error,
                    receiver,
                    None,
                );
            }
            OwnedEvaluationReturnFrame::ExplicitCollectionArg {
                wrapper,
                index: argument_index,
                terms,
                debug_args,
            } => {
                let mut terms = terms.clone();
                terms.push(term);
                let mut debug_args = debug_args.clone();
                debug_args.push(debug);
                return evaluate_owned_arguments(
                    context,
                    state,
                    wrapper,
                    &OwnedArgumentsTerminal::ExplicitCollection,
                    argument_index + 1,
                    terms,
                    debug_args,
                    &frames[..index],
                    error,
                    receiver,
                    None,
                );
            }
            OwnedEvaluationReturnFrame::FunctionArg {
                wrapper,
                function,
                record_heap,
                index: argument_index,
                terms,
                debug_args,
            } => {
                let mut terms = terms.clone();
                terms.push(term);
                let mut debug_args = debug_args.clone();
                debug_args.push(debug);
                let terminal = OwnedArgumentsTerminal::Function {
                    function: function.clone(),
                    record_heap: *record_heap,
                };
                return evaluate_owned_arguments(
                    context,
                    state,
                    wrapper,
                    &terminal,
                    argument_index + 1,
                    terms,
                    debug_args,
                    &frames[..index],
                    error,
                    receiver,
                    None,
                );
            }
            OwnedEvaluationReturnFrame::DomainArg {
                wrapper,
                function,
                index: argument_index,
                terms,
                debug_args,
            } => {
                let mut terms = terms.clone();
                terms.push(term);
                let mut debug_args = debug_args.clone();
                debug_args.push(debug);
                return evaluate_owned_arguments(
                    context,
                    state,
                    wrapper,
                    &OwnedArgumentsTerminal::Domain(function.clone()),
                    argument_index + 1,
                    terms,
                    debug_args,
                    &frames[..index],
                    error,
                    receiver,
                    None,
                );
            }
            OwnedEvaluationReturnFrame::CurrentPermArg {
                wrapper,
                access,
                resource,
                heap,
                args,
                index: argument_index,
                terms,
                debug_args,
            } => {
                let mut terms = terms.clone();
                terms.push(term);
                let mut debug_args = debug_args.clone();
                debug_args.push(debug);
                let terminal = OwnedArgumentsTerminal::CurrentPerm {
                    access: access.clone(),
                    resource: resource.clone(),
                    heap: heap.clone(),
                    args: args.clone(),
                };
                return evaluate_owned_arguments(
                    context,
                    state,
                    wrapper,
                    &terminal,
                    argument_index + 1,
                    terms,
                    debug_args,
                    &frames[..index],
                    error,
                    receiver,
                    None,
                );
            }
            OwnedEvaluationReturnFrame::LetValue(wrapper) => {
                return resume_owned_let_value(
                    context,
                    state,
                    term,
                    debug,
                    wrapper,
                    &frames[..index],
                    error,
                    receiver,
                    None,
                );
            }
            OwnedEvaluationReturnFrame::LetBody {
                wrapper,
                before,
                local,
                value_debug,
            } => {
                let ExpKind::Let(declaration, value, _) = wrapper.expression.kind() else {
                    unreachable!("let body frame")
                };
                if state.record_possible_triggers {
                    let added: Vec<_> = state
                        .possible_triggers
                        .iter()
                        .filter(|(exp, _)| before.get(exp).is_none())
                        .cloned()
                        .collect();
                    for (trigger, value_term) in added {
                        let replaced =
                            ferrum_silver::ast::utility::rewriter::strategy::replace_expressions(
                                &trigger,
                                &[(local.clone(), value.clone())],
                            )
                            .map_err(EvaluationError::Rewrite)?;
                        state.possible_triggers.insert(replaced, value_term);
                    }
                }
                state.function_recorder = state.function_recorder.leave_let(&wrapper.expression);
                debug = if let Some(value) = value_debug {
                    let body = debug.ok_or(EvaluationError::MissingDebugExpression)?;
                    Some(Exp::new(
                        ExpKind::Let(declaration.clone(), value.clone(), body),
                        wrapper.expression.metadata().clone(),
                    ))
                } else {
                    None
                };
                finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &term)?;
            }
            OwnedEvaluationReturnFrame::Asserting(wrapper) => {
                finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &term)?;
            }
            OwnedEvaluationReturnFrame::Minus(wrapper) => {
                let factory = context.factory().clone();
                term = factory.minus(factory.int_literal(0), term);
                debug = debug.map(|value| {
                    Exp::new(ExpKind::Minus(value), wrapper.expression.metadata().clone())
                });
                finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &term)?;
            }
            OwnedEvaluationReturnFrame::PermMinus(wrapper) => {
                let factory = context.factory().clone();
                term = factory.perm_minus(factory.no_perm(), term);
                debug = debug.map(|value| {
                    Exp::new(
                        ExpKind::PermMinus(value),
                        wrapper.expression.metadata().clone(),
                    )
                });
                finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &term)?;
            }
            OwnedEvaluationReturnFrame::Not(wrapper) => {
                term = context.factory().not(term);
                debug = debug.map(|value| {
                    Exp::new(ExpKind::Not(value), wrapper.expression.metadata().clone())
                });
                finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &term)?;
            }
            OwnedEvaluationReturnFrame::StrictRight {
                wrapper,
                left,
                left_debug,
            } => {
                let operator = owned_strict_binary(&wrapper.expression)
                    .expect("strict operator frame")
                    .0;
                if matches!(
                    operator,
                    Binary::Div
                        | Binary::Mod
                        | Binary::Fraction
                        | Binary::PermDiv
                        | Binary::PermPermDiv
                ) {
                    return finish_owned_checked_division(
                        context,
                        state,
                        operator,
                        wrapper,
                        left.clone(),
                        left_debug.clone(),
                        term,
                        debug,
                        &frames[..index],
                        error,
                        receiver,
                    );
                }
                term = operator.build(context.factory(), left.clone(), term);
                debug = match (left_debug, debug) {
                    (Some(left), Some(right)) => Some(Exp::new(
                        operator.expression(left.clone(), right),
                        wrapper.expression.metadata().clone(),
                    )),
                    (None, _) => None,
                    (Some(_), None) => return Err(EvaluationError::MissingDebugExpression),
                };
                finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &term)?;
            }
            OwnedEvaluationReturnFrame::StrictLeft { wrapper, right } => {
                let operator = owned_strict_binary(&wrapper.expression)
                    .expect("strict operator frame")
                    .0;
                if has_owned_asserting_path(right) && context.can_transfer_owned_asserting(&state) {
                    let mut next = frames[..index].to_vec();
                    next.push(OwnedEvaluationReturnFrame::StrictRight {
                        wrapper: wrapper.clone(),
                        left: term,
                        left_debug: debug,
                    });
                    return evaluate_owned_nested(context, state, right, error, receiver, next);
                }
                return evaluate(
                    context,
                    state,
                    right,
                    error,
                    &mut |context, mut state, right_term, right_debug| {
                        if matches!(
                            operator,
                            Binary::Div
                                | Binary::Mod
                                | Binary::Fraction
                                | Binary::PermDiv
                                | Binary::PermPermDiv
                        ) {
                            return finish_owned_checked_division(
                                context,
                                state,
                                operator,
                                wrapper,
                                term.clone(),
                                debug.clone(),
                                right_term,
                                right_debug,
                                &frames[..index],
                                error,
                                receiver,
                            );
                        }
                        let value = operator.build(context.factory(), term.clone(), right_term);
                        let rebuilt = match (&debug, right_debug) {
                            (Some(left), Some(right)) => Some(Exp::new(
                                operator.expression(left.clone(), right),
                                wrapper.expression.metadata().clone(),
                            )),
                            (None, _) => None,
                            (Some(_), None) => return Err(EvaluationError::MissingDebugExpression),
                        };
                        finish_owned_wrapper::<C, P, D, J, V>(
                            context, &mut state, wrapper, &value,
                        )?;
                        resume_owned_return_frames(
                            context,
                            state,
                            value,
                            rebuilt,
                            &frames[..index],
                            error,
                            receiver,
                        )
                    },
                );
            }
            OwnedEvaluationReturnFrame::AddRight {
                wrapper,
                left,
                left_debug,
            } => {
                term = context.factory().plus(left.clone(), term);
                debug = match (left_debug, debug) {
                    (Some(left), Some(right)) => Some(Exp::new(
                        ExpKind::Add(left.clone(), right),
                        wrapper.expression.metadata().clone(),
                    )),
                    (None, _) => None,
                    (Some(_), None) => return Err(EvaluationError::MissingDebugExpression),
                };
                finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &term)?;
            }
            OwnedEvaluationReturnFrame::AddLeft { wrapper, right } => {
                if has_owned_asserting_path(right) && context.can_transfer_owned_asserting(&state) {
                    let mut next = frames[..index].to_vec();
                    next.push(OwnedEvaluationReturnFrame::AddRight {
                        wrapper: wrapper.clone(),
                        left: term,
                        left_debug: debug,
                    });
                    return evaluate_owned_nested(context, state, right, error, receiver, next);
                }
                return evaluate(
                    context,
                    state,
                    right,
                    error,
                    &mut |context, mut state, right_term, right_debug| {
                        let value = context.factory().plus(term.clone(), right_term);
                        let rebuilt = match (&debug, right_debug) {
                            (Some(left), Some(right)) => Some(Exp::new(
                                ExpKind::Add(left.clone(), right),
                                wrapper.expression.metadata().clone(),
                            )),
                            (None, _) => None,
                            (Some(_), None) => return Err(EvaluationError::MissingDebugExpression),
                        };
                        finish_owned_wrapper::<C, P, D, J, V>(
                            context, &mut state, wrapper, &value,
                        )?;
                        resume_owned_return_frames(
                            context,
                            state,
                            value,
                            rebuilt,
                            &frames[..index],
                            error,
                            receiver,
                        )
                    },
                );
            }
        }
    }
    #[cfg(test)]
    OLD_RETURN_SNAPSHOTS.with(|slot| {
        if let Some(snapshots) = slot.borrow_mut().as_mut() {
            snapshots.push(test_old_return_snapshot(&state));
        }
    });
    #[cfg(test)]
    LET_DEBUG_VALUES.with(|slot| {
        if let Some(values) = slot.borrow_mut().as_mut() {
            values.push(debug.clone());
        }
    });
    #[cfg(test)]
    FALLBACK_RECEIVER_VALUES.with(|slot| {
        if let Some(values) = slot.borrow_mut().as_mut() {
            values.push(term.clone());
        }
    });
    context
        .finish_owned_assignment_value(state, term, debug, receiver)
        .ok_or(EvaluationError::OwnedSchedulerUnavailable)?
}

fn finish_owned_checked_division<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    operator: Binary,
    wrapper: &OwnedValueWrapper,
    left: Term,
    left_debug: Option<Exp>,
    right: Term,
    right_debug: Option<Exp>,
    frames: &[OwnedEvaluationReturnFrame],
    error: &C::PartialError,
    receiver: &crate::rules::executor::OwnedAssignmentValue,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let factory = context.factory().clone();
    let result = operator.build(&factory, left, right.clone());
    let right_for_check = right_debug.clone();
    let rebuilt = match (&left_debug, right_debug) {
        (Some(left), Some(right)) => Some(Exp::new(
            operator.expression(left.clone(), right),
            wrapper.expression.metadata().clone(),
        )),
        (None, _) => None,
        (Some(_), None) => return Err(EvaluationError::MissingDebugExpression),
    };
    let (_, _, original_right) = owned_strict_binary(&wrapper.expression).expect("divisor frame");
    let zero = if matches!(operator, Binary::PermPermDiv) {
        factory.no_perm()
    } else {
        factory.int_literal(0)
    };
    let nonzero = factory.not(factory.equals(right, zero));
    if !context
        .assert_goal(&nonzero)
        .map_err(EvaluationError::Context)?
    {
        let zero = Exp::new(ExpKind::IntLit(0.into()), Default::default());
        let original_test = context.debugging().then(|| {
            Exp::new(
                ExpKind::NeCmp(original_right.clone(), zero.clone()),
                original_right.metadata().clone(),
            )
        });
        let rewritten_test = if context.debugging() {
            let divisor = right_for_check.ok_or(EvaluationError::MissingDebugExpression)?;
            Some(Exp::new(
                ExpKind::NeCmp(divisor, zero),
                original_right.metadata().clone(),
            ))
        } else {
            None
        };
        let failure = context
            .division_failure(
                &state,
                error,
                original_right,
                &nonzero,
                rewritten_test.as_ref(),
            )
            .map_err(EvaluationError::Context)?;
        if state.retry_level == 0 && context.report_further_errors() {
            context
                .assume_nonzero(&nonzero, original_test.as_ref(), rewritten_test.as_ref())
                .map_err(EvaluationError::Context)?;
            if failure.continue_verification() {
                finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &result)?;
                let next = resume_owned_return_frames(
                    context, state, result, rebuilt, frames, error, receiver,
                )?;
                return Ok(failure.combine(|| next, false));
            }
        }
        return Ok(failure);
    }
    finish_owned_wrapper::<C, P, D, J, V>(context, &mut state, wrapper, &result)?;
    resume_owned_return_frames(context, state, result, rebuilt, frames, error, receiver)
}

fn finish_owned_wrapper<C, P, D, J: Clone, V>(
    context: &mut C,
    state: &mut State<P, D, J>,
    wrapper: &OwnedValueWrapper,
    term: &Term,
) -> Result<(), EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    if state.record_possible_triggers {
        context
            .record_possible_trigger(state, &wrapper.expression, term)
            .map_err(EvaluationError::Context)?;
    }
    state.h = wrapper.heap.clone();
    state.reserve_heaps = wrapper.reserve.clone();
    state.exhale_ext = wrapper.exhale;
    context
        .close_evaluation_scope(None)
        .map_err(EvaluationError::Context)
}

pub fn evaluate<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let scope = context
        .open_evaluation_scope(&state, expression)
        .map_err(EvaluationError::Context)?;
    context
        .log_evaluation(&state, expression)
        .map_err(EvaluationError::Context)?;
    let old_heap = state.h.clone();
    let old_reserve = state.reserve_heaps.clone();
    let old_exhale = state.exhale_ext;
    let mut evaluation_state = state;
    evaluation_state.h = context
        .eval_heap(&evaluation_state)
        .map_err(EvaluationError::Context)?;
    evaluation_state.reserve_heaps.clear();
    evaluation_state.exhale_ext = false;
    evaluate_inner(
        context,
        evaluation_state,
        expression,
        error,
        &mut |context, mut state, term, debug| {
            if state.record_possible_triggers {
                context
                    .record_possible_trigger(&mut state, expression, &term)
                    .map_err(EvaluationError::Context)?;
            }
            state.h = old_heap.clone();
            state.reserve_heaps = old_reserve.clone();
            state.exhale_ext = old_exhale;
            context
                .close_evaluation_scope(scope)
                .map_err(EvaluationError::Context)?;
            continuation(context, state, term, debug)
        },
    )
}
fn evaluate_inner<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let factory = context.factory().clone();
    let debug = context.debugging().then(|| expression.clone());
    // Dispatch to one non-inlined family to keep nested CPS frames bounded.
    // Factory and debug state are computed once, before choosing the family.
    let stage: fn(
        &mut C,
        State<P, D, J>,
        &Exp,
        &C::PartialError,
        &mut dyn FnMut(
            &mut C,
            State<P, D, J>,
            Term,
            Option<Exp>,
        ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
        crate::state::terms::TermFactory,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>> = match expression.kind() {
        ExpKind::TrueLit
        | ExpKind::FalseLit
        | ExpKind::NullLit
        | ExpKind::IntLit(_)
        | ExpKind::FullPerm
        | ExpKind::NoPerm
        | ExpKind::LocalVarWithVersion(..)
        | ExpKind::LocalVar(_)
        | ExpKind::Result(_) => evaluate_atomic_family,
        ExpKind::WildcardPerm => evaluate_wildcard_family,
        ExpKind::EmptySeq(_)
        | ExpKind::EmptySet(_)
        | ExpKind::EmptyMultiset(_)
        | ExpKind::EmptyMap(..) => evaluate_empty_collection_family,
        ExpKind::And(..) | ExpKind::Or(..) | ExpKind::CondExp(..) | ExpKind::Implies(..) => {
            evaluate_boolean_branch_family
        }
        ExpKind::FieldAccess(_) | ExpKind::CurrentPerm(_) => evaluate_heap_access_family,
        ExpKind::ForPerm(..) | ExpKind::Forall(..) | ExpKind::Exists(..) => {
            evaluate_quantifier_family
        }
        ExpKind::FuncApp(..)
        | ExpKind::DomainFuncApp(..)
        | ExpKind::BackendFuncApp(..)
        | ExpKind::Asserting(..)
        | ExpKind::Old(_)
        | ExpKind::LabelledOld(..)
        | ExpKind::DebugLabelledOld(..)
        | ExpKind::Let(..) => evaluate_calls_and_old_family,
        ExpKind::ExplicitMap(_)
        | ExpKind::ExplicitSeq(_)
        | ExpKind::ExplicitSet(_)
        | ExpKind::ExplicitMultiset(_)
        | ExpKind::SeqIndex(..)
        | ExpKind::SeqUpdate(..)
        | ExpKind::MapLookup(..)
        | ExpKind::MapUpdate(..) => evaluate_collection_family,
        _ => evaluate_operator_family,
    };
    stage(
        context,
        state,
        expression,
        error,
        continuation,
        factory,
        debug,
    )
}

#[inline(never)]
fn evaluate_atomic_family<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    factory: crate::state::terms::TermFactory,
    debug: Option<Exp>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let literal = match expression.kind() {
        ExpKind::TrueLit => Some(factory.boolean(true)),
        ExpKind::FalseLit => Some(factory.boolean(false)),
        ExpKind::NullLit => Some(factory.null()),
        ExpKind::IntLit(n) => Some(factory.int_literal(n.clone())),
        ExpKind::FullPerm => Some(factory.full_perm()),
        ExpKind::NoPerm => Some(factory.no_perm()),
        _ => None,
    };
    if let Some(term) = literal {
        return continuation(context, state, term, debug);
    }
    if let ExpKind::LocalVarWithVersion(name, typ) = expression.kind() {
        let sort = context.to_sort(typ).map_err(EvaluationError::Context)?;
        let id = crate::state::identifiers::Identifier::new(format!(
            "{name}@{}",
            context.verifier_unique_id()
        ));
        return continuation(context, state, factory.var(id, sort, false), debug);
    }
    if matches!(expression.kind(), ExpKind::LocalVar(_) | ExpKind::Result(_)) {
        let key = AbstractLocalVar::new(expression.clone());
        let term = state
            .g
            .get(&key)
            .cloned()
            .ok_or(EvaluationError::MissingStoreValue)?;
        let debug = state.g.get_exp(&key).cloned();
        return continuation(context, state, term, debug);
    }
    context.evaluate_special(state, expression, error, continuation)
}

#[inline(never)]
fn evaluate_wildcard_family<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    factory: crate::state::terms::TermFactory,
    debug: Option<Exp>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    if state.assert_read_access_only {
        return continuation(context, state, factory.full_perm(), debug);
    }
    if matches!(expression.kind(), ExpKind::WildcardPerm) {
        let (variable, constraint, debug_variable) =
            context.fresh_arp().map_err(EvaluationError::Context)?;
        if context.debugging() && debug_variable.is_none() {
            return Err(EvaluationError::MissingDebugExpression);
        }
        context
            .assume_arp_definition(&constraint, debug_variable.as_ref())
            .map_err(EvaluationError::Context)?;
        let mut state = state;
        state.function_recorder = state
            .function_recorder
            .record_constrained_var(variable.clone(), constraint);
        state.constrainable_arps = state.constrainable_arps.incl(variable.clone());
        return continuation(context, state, variable, debug_variable);
    }
    context.evaluate_special(state, expression, error, continuation)
}

#[inline(never)]
fn evaluate_empty_collection_family<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    factory: crate::state::terms::TermFactory,
    debug: Option<Exp>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    match expression.kind() {
        ExpKind::EmptySeq(typ) | ExpKind::EmptySet(typ) | ExpKind::EmptyMultiset(typ) => {
            let sort = context.to_sort(typ).map_err(EvaluationError::Context)?;
            let term = match expression.kind() {
                ExpKind::EmptySeq(_) => factory.seq_nil(sort),
                ExpKind::EmptySet(_) => factory.empty_set(sort),
                _ => factory.empty_multiset(sort),
            };
            return continuation(context, state, term, debug);
        }
        ExpKind::EmptyMap(key, value) => {
            let key = context.to_sort(key).map_err(EvaluationError::Context)?;
            let value = context.to_sort(value).map_err(EvaluationError::Context)?;
            return continuation(context, state, factory.empty_map(key, value), debug);
        }
        _ => {}
    }
    context.evaluate_special(state, expression, error, continuation)
}

#[inline(never)]
fn evaluate_boolean_branch_family<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    factory: crate::state::terms::TermFactory,
    debug: Option<Exp>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    if !context.disable_short_circuiting()
        && matches!(expression.kind(), ExpKind::And(..) | ExpKind::Or(..))
    {
        fn flatten(expression: &Exp, disjunction: bool, out: &mut Vec<Exp>) {
            match expression.kind() {
                ExpKind::And(a, b) if !disjunction => {
                    flatten(a, disjunction, out);
                    flatten(b, disjunction, out);
                }
                ExpKind::Or(a, b) if disjunction => {
                    flatten(a, disjunction, out);
                    flatten(b, disjunction, out);
                }
                _ => out.push(expression.clone()),
            }
        }
        let disjunction = matches!(expression.kind(), ExpKind::Or(..));
        let mut expressions = Vec::new();
        flatten(expression, disjunction, &mut expressions);
        return evaluate_short_circuit(
            context,
            state,
            &expressions,
            disjunction,
            error,
            continuation,
        );
    }
    if let ExpKind::CondExp(condition, yes, no) = expression.kind() {
        let scope = context
            .open_conditional_scope(&state, expression)
            .map_err(EvaluationError::Context)?;
        return evaluate(
            context,
            state,
            condition,
            error,
            &mut |context, state, cond, cond_exp| {
                context.branch_join_evaluation(
                    state,
                    cond.clone(),
                    condition,
                    cond_exp.as_ref(),
                    false,
                    EvaluationBranchAction::Evaluate {
                        expression: yes.clone(),
                        error: error.clone(),
                    },
                    EvaluationBranchAction::Evaluate {
                        expression: no.clone(),
                        error: error.clone(),
                    },
                    &mut |context, entries| {
                        let mut entries = entries.into_iter();
                        let (state, a, a_exp) =
                            entries.next().ok_or(EvaluationError::InvalidJoinEntries)?;
                        if let Some((other, b, b_exp)) = entries.next() {
                            if entries.next().is_some() {
                                return Err(EvaluationError::InvalidJoinEntries);
                            }
                            let state = context
                                .merge_evaluation_states(state, &other)
                                .map_err(EvaluationError::Context)?;
                            let debug = match (&cond_exp, a_exp, b_exp) {
                                (Some(c), Some(a), Some(b)) => Some(Exp::new(
                                    ExpKind::CondExp(c.clone(), a, b),
                                    condition.metadata().clone(),
                                )),
                                (None, _, _) => None,
                                _ => return Err(EvaluationError::MissingDebugExpression),
                            };
                            Ok((state, factory.ite(cond.clone(), a, b), debug))
                        } else {
                            Ok((state, a, a_exp))
                        }
                    },
                    &mut |context, state, term, debug| {
                        context
                            .close_expression_scope(scope)
                            .map_err(EvaluationError::Context)?;
                        continuation(context, state, term, debug)
                    },
                )
            },
        );
    }
    if let ExpKind::Implies(left, right) = expression.kind() {
        let scope = context
            .open_implies_scope(&state, Some(expression), "Implies")
            .map_err(EvaluationError::Context)?;
        return evaluate(
            context,
            state,
            left,
            error,
            &mut |context, state, lhs, lhs_exp| {
                let from_short_circuit = context.is_short_circuit_implies(expression);
                context.branch_join_evaluation(
                    state,
                    lhs.clone(),
                    left,
                    lhs_exp.as_ref(),
                    from_short_circuit,
                    EvaluationBranchAction::Evaluate {
                        expression: right.clone(),
                        error: error.clone(),
                    },
                    EvaluationBranchAction::True,
                    &mut |context, entries| {
                        let mut entries = entries.into_iter();
                        let (mut state, first, first_exp) =
                            entries.next().ok_or(EvaluationError::InvalidJoinEntries)?;
                        if let Some((other, _, _)) = entries.next() {
                            state = context
                                .merge_evaluation_states(state, &other)
                                .map_err(EvaluationError::Context)?;
                        }
                        if entries.next().is_some() {
                            return Err(EvaluationError::InvalidJoinEntries);
                        }
                        let debug = if let Some(lhs) = &lhs_exp {
                            let rhs = first_exp.ok_or(EvaluationError::MissingDebugExpression)?;
                            let inner =
                                Exp::new(ExpKind::Implies(lhs.clone(), rhs), Default::default());
                            Some(Exp::new(
                                ExpKind::Implies(lhs.clone(), inner),
                                expression.metadata().clone(),
                            ))
                        } else {
                            None
                        };
                        Ok((state, factory.implies(lhs.clone(), first), debug))
                    },
                    &mut |context, state, term, debug| {
                        context
                            .close_expression_scope(scope)
                            .map_err(EvaluationError::Context)?;
                        continuation(context, state, term, debug)
                    },
                )
            },
        );
    }
    evaluate_operator_family(
        context,
        state,
        expression,
        error,
        continuation,
        factory,
        debug,
    )
}

/// Finish a field read after its receiver has been evaluated, shared by borrowed
/// and owned return paths so heap recording and debug labels stay identical.
fn finish_field_receiver<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    receiver: &Term,
    receiver_exp: Option<&Exp>,
    record_heap: bool,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let ExpKind::FieldAccess(access) = expression.kind() else {
        unreachable!("field receiver")
    };
    let is_old = state.is_eval_in_old;
    context.eval_field_access(
        state,
        access,
        receiver,
        receiver_exp,
        error,
        &mut |context, state, snapshot| {
            let state = if record_heap {
                context
                    .record_intermediate_heap(state, expression)
                    .map_err(EvaluationError::Context)?
            } else {
                state
            };
            let debug = if context.debugging() {
                let label = context
                    .debug_old_label(&state, &expression.metadata().position)
                    .map_err(EvaluationError::Context)?;
                let receiver = receiver_exp
                    .cloned()
                    .ok_or(EvaluationError::MissingDebugExpression)?;
                let field_meta = if is_old {
                    expression.metadata().clone()
                } else {
                    Default::default()
                };
                let field = ferrum_silver::ast::expression::FieldAccess::new(
                    receiver,
                    access.field.clone(),
                    field_meta.clone(),
                );
                let field = Exp::new(ExpKind::FieldAccess(field), field_meta);
                if is_old {
                    Some(field)
                } else {
                    Some(Exp::new(
                        ExpKind::DebugLabelledOld(field, label),
                        expression.metadata().clone(),
                    ))
                }
            } else {
                None
            };
            continuation(context, state, snapshot, debug)
        },
    )
}

#[inline(never)]
fn evaluate_heap_access_family<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    _factory: crate::state::terms::TermFactory,
    _debug: Option<Exp>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    if let ExpKind::FieldAccess(access) = expression.kind() {
        let record_heap = context.debugging() && state.temporary_heap_record.is_some();
        return evaluate(
            context,
            state,
            &access.receiver,
            error,
            &mut |context, state, receiver, receiver_exp| {
                finish_field_receiver(
                    context,
                    state,
                    expression,
                    error,
                    &receiver,
                    receiver_exp.as_ref(),
                    record_heap,
                    continuation,
                )
            },
        );
    }
    if let ExpKind::CurrentPerm(access) = expression.kind() {
        let heap = state
            .partially_consumed_heap
            .clone()
            .unwrap_or_else(|| state.h.clone());
        let (resource, args) = current_permission_resource(&state, access)?;
        return evaluate_all(
            context,
            state,
            &args,
            &|_| error.clone(),
            &mut |context, state, terms, debug_args| {
                complete_current_permission(
                    context,
                    state,
                    expression,
                    heap.clone(),
                    access,
                    &resource,
                    terms,
                    debug_args,
                    continuation,
                )
            },
        );
    }

    context.evaluate_special(state, expression, error, continuation)
}

#[inline(never)]
fn evaluate_quantifier_family<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    factory: crate::state::terms::TermFactory,
    _debug: Option<Exp>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    if let ExpKind::ForPerm(declarations, access, body) = expression.kind() {
        use crate::state::{chunks::MagicWandIdentifier, terms::ResourceKey};
        let (resource, args) = match access.kind() {
            ExpKind::FieldAccess(field) => (
                ResourceKey::Field(Arc::new(field.field.clone())),
                vec![field.receiver.clone()],
            ),
            ExpKind::PredicateAccess(predicate) => {
                let name = &predicate.predicate_name;
                let decl = state
                    .program
                    .predicates
                    .iter()
                    .find(|p| &p.name == name)
                    .ok_or_else(|| EvaluationError::MissingPredicate(name.clone()))?;
                (
                    ResourceKey::Predicate(Arc::new(decl.clone())),
                    predicate.args.clone(),
                )
            }
            ExpKind::MagicWand(..) => {
                let wand = MagicWandIdentifier::new(access.clone(), &state.program)
                    .map_err(EvaluationError::Wand)?;
                let args = access
                    .magic_wand_subexpressions(&state.program)
                    .map_err(EvaluationError::Wand)?;
                (ResourceKey::Wand(wand), args)
            }
            _ => return Err(EvaluationError::InvalidResourceAccess),
        };
        let original = state.clone();
        let mut state = state;
        state.h = state
            .partially_consumed_heap
            .clone()
            .unwrap_or_else(|| state.h.clone());
        let mut vars = Vec::new();
        let mut declarations_new = Vec::new();
        let mut bindings = Vec::new();
        let mut quantified = Vec::new();
        for decl in declarations {
            let (term, debug) = context
                .fresh_for_perm(decl)
                .map_err(EvaluationError::Context)?;
            if context.debugging() && debug.is_none() {
                return Err(EvaluationError::MissingDebugExpression);
            }
            let local = Exp::new(ExpKind::LocalVar(decl.local_var()), decl.meta.clone());
            bindings.push((
                AbstractLocalVar::new(local.clone()),
                (term.clone(), debug.clone()),
            ));
            quantified.push((
                term.clone(),
                context.debugging().then(|| AbstractLocalVar::new(local)),
            ));
            if context.debugging() {
                let crate::state::terms::TermKind::Var(var) = term.kind() else {
                    return Err(EvaluationError::InvalidResourceAccess);
                };
                declarations_new.push(ferrum_silver::ast::program::LocalVarDecl::new(
                    var.id.name(),
                    decl.typ.clone(),
                    decl.meta.clone(),
                ));
            }
            vars.push((term, debug));
        }
        state.g = Arc::new(state.g.with_store(
            &crate::state::store::MapBackedStore::from_bindings(bindings),
        ));
        quantified.extend(state.quantified_variables.clone());
        state.quantified_variables = quantified;
        return evaluate_all(
            context,
            state,
            &args,
            &|_| error.clone(),
            &mut |context, state, terms, debug_args| {
                let options = context
                    .for_perm_conditions(&state, &resource, &vars, &terms, debug_args.as_deref())
                    .map_err(EvaluationError::Context)?;
                let bound_store = state.g.clone();
                evaluate_for_perm_options(
                    context,
                    state,
                    &options,
                    body,
                    error,
                    &declarations_new,
                    bound_store,
                    &mut |context, mut state, terms, exps| {
                        state.h = original.h.clone();
                        state.g = original.g.clone();
                        state.quantified_variables = original.quantified_variables.clone();
                        let term = factory.and(terms);
                        let debug = if context.debugging() {
                            let mut it = exps
                                .ok_or(EvaluationError::MissingDebugExpression)?
                                .into_iter();
                            let mut e = it
                                .next()
                                .unwrap_or_else(|| Exp::new(ExpKind::TrueLit, Default::default()));
                            for next in it {
                                e = Exp::new(ExpKind::And(e, next), Default::default());
                            }
                            Some(e)
                        } else {
                            None
                        };
                        continuation(context, state, term, debug)
                    },
                )
            },
        );
    }
    let quantified = match expression.kind() {
        ExpKind::Forall(vars, triggers, body) => Some((
            crate::state::terms::Quantifier::Forall,
            vars,
            triggers,
            body,
        )),
        ExpKind::Exists(vars, triggers, body) => Some((
            crate::state::terms::Quantifier::Exists,
            vars,
            triggers,
            body,
        )),
        _ => None,
    };
    if let Some((quantifier, source_vars, source_triggers, source_body)) = quantified {
        let (name, weight) = quantifier_name_and_weight(expression, &mut |message| {
            context.annotation_warning(message)
        })
        .map_err(EvaluationError::Context)?;
        let mut state = state;
        state.function_recorder = state.function_recorder.enter_quantified(expression.clone());
        return context.evaluate_quantifier(
            state,
            expression,
            &name,
            error,
            &mut |context, mut state, data| {
                let Some(data) = data else {
                    return if context.check_smoke().map_err(EvaluationError::Context)? {
                        Ok(VerificationResult::unreachable())
                    } else {
                        context
                            .quantifier_failure(&state, expression, error)
                            .map_err(EvaluationError::Context)
                    };
                };
                let auxiliary = context
                    .heap_independent_auxiliaries(&data.auxiliary_non_globals)
                    .map_err(EvaluationError::Context)?;
                context
                    .assume_quantifier_auxiliaries(
                        &data.auxiliary_globals,
                        &auxiliary,
                        data.auxiliary_debug.as_ref(),
                    )
                    .map_err(EvaluationError::Context)?;
                if quantifier == crate::state::terms::Quantifier::Exists {
                    let preconditions = crate::state::function_precondition_transformer::transform(
                        &factory,
                        &data.body,
                        &mut |function| context.precondition_function(function),
                    )
                    .map_err(EvaluationError::Precondition)?;
                    let universal = factory
                        .quantification(
                            crate::state::terms::Quantifier::Forall,
                            data.variables.clone(),
                            preconditions,
                            data.triggers.clone(),
                            name.clone(),
                            false,
                            weight,
                        )
                        .map_err(EvaluationError::QuantifierTransform)?;
                    let original = Exp::new(
                        ExpKind::Forall(
                            source_vars.clone(),
                            source_triggers.clone(),
                            source_body.clone(),
                        ),
                        expression.metadata().clone(),
                    );
                    let rewritten = if context.debugging() {
                        let body = data
                            .body_expression
                            .clone()
                            .ok_or(EvaluationError::MissingDebugExpression)?;
                        Some(Exp::new(
                            ExpKind::Forall(source_vars.clone(), source_triggers.clone(), body),
                            expression.metadata().clone(),
                        ))
                    } else {
                        None
                    };
                    context
                        .assume_existential_preconditions(&universal, &original, rewritten.as_ref())
                        .map_err(EvaluationError::Context)?;
                }
                let term = factory
                    .quantification(
                        quantifier,
                        data.variables,
                        data.body,
                        data.triggers,
                        name.clone(),
                        false,
                        weight,
                    )
                    .map_err(EvaluationError::QuantifierTransform)?;
                let debug = if context.debugging() {
                    let vars = data
                        .variable_expressions
                        .ok_or(EvaluationError::MissingDebugExpression)?;
                    let body = data
                        .body_expression
                        .ok_or(EvaluationError::MissingDebugExpression)?;
                    let meta = body.metadata().clone();
                    Some(Exp::new(
                        if quantifier == crate::state::terms::Quantifier::Forall {
                            ExpKind::Forall(vars, vec![], body)
                        } else {
                            ExpKind::Exists(vars, vec![], body)
                        },
                        meta,
                    ))
                } else {
                    None
                };
                state.function_recorder = state.function_recorder.leave_quantified(expression);
                continuation(context, state, term, debug)
            },
        );
    }
    context.evaluate_special(state, expression, error, continuation)
}

#[inline(never)]
fn evaluate_calls_and_old_family<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    factory: crate::state::terms::TermFactory,
    _debug: Option<Exp>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    if let ExpKind::FuncApp(name, args) = expression.kind() {
        let function = state
            .program
            .functions
            .iter()
            .find(|f| &f.name == name)
            .cloned()
            .ok_or_else(|| EvaluationError::MissingFunction(name.clone()))?;
        let record_heap = context.debugging() && state.temporary_heap_record.is_some();
        return evaluate_all(
            context,
            state,
            args,
            &|_| error.clone(),
            &mut |context, state, terms, debug_args| {
                complete_function_application(
                    context,
                    state,
                    expression,
                    &function,
                    record_heap,
                    terms,
                    debug_args,
                    continuation,
                )
            },
        );
    }
    let domain_application = match expression.kind() {
        ExpKind::DomainFuncApp(name, args, substitutions) => {
            Some((name, args, Some(substitutions), false))
        }
        ExpKind::BackendFuncApp(name, args) => Some((name, args, None, true)),
        _ => None,
    };
    if let Some((name, args, _, _)) = domain_application {
        let function = state
            .program
            .find_domain_function_optionally(name)
            .cloned()
            .ok_or_else(|| EvaluationError::MissingDomainFunction(name.clone()))?;
        return evaluate_all(
            context,
            state,
            args,
            &|_| error.clone(),
            &mut |context, state, terms, debug_args| {
                complete_domain_application(
                    context,
                    state,
                    expression,
                    &function,
                    terms,
                    debug_args,
                    continuation,
                )
            },
        );
    }

    if let ExpKind::Asserting(assertion, body) = expression.kind() {
        let original_store = state.g.clone();
        let original_heap = state.h.clone();
        return context.consume_assertion(state, assertion, error, &mut |context, mut state| {
            state.g = original_store.clone();
            state.h = original_heap.clone();
            evaluate(context, state, body, error, continuation)
        });
    }
    let old = match expression.kind() {
        ExpKind::Old(body) => Some((body, "old".to_string(), 0)),
        ExpKind::LabelledOld(body, label) => Some((body, label.clone(), 1)),
        ExpKind::DebugLabelledOld(body, label) => Some((
            body,
            label.split('#').next().unwrap_or(label).to_string(),
            2,
        )),
        _ => None,
    };
    if let Some((body, label, kind)) = old {
        let Some(old_heap) = state.old_heaps.get(&label).cloned() else {
            if kind == 0 {
                return Err(EvaluationError::MissingOldState(label));
            }
            let source_labelled = if kind == 2 {
                Exp::new(
                    ExpKind::LabelledOld(body.clone(), label.clone()),
                    expression.metadata().clone(),
                )
            } else {
                expression.clone()
            };
            return context
                .missing_label_failure(&state, error, &source_labelled, &label)
                .map_err(EvaluationError::Context);
        };
        let original = state.clone();
        let mut old_state = state;
        old_state.h = old_heap;
        old_state.partially_consumed_heap = None;
        old_state.is_eval_in_old = true;
        old_state.possible_triggers = Default::default();
        let old_state = context
            .consolidate_old(old_state)
            .map_err(EvaluationError::Context)?;
        return evaluate(
            context,
            old_state,
            body,
            error,
            &mut |context, mut state, term, rewritten| {
                let mut triggers = original.possible_triggers.clone();
                if original.record_possible_triggers {
                    for (exp, value) in state.possible_triggers.iter() {
                        let wrapped = if label == "old" {
                            ExpKind::Old(exp.clone())
                        } else {
                            ExpKind::LabelledOld(exp.clone(), label.clone())
                        };
                        triggers.insert(Exp::new(wrapped, exp.metadata().clone()), value.clone());
                    }
                    for (exp, value) in state.possible_triggers.iter() {
                        if !context
                            .is_heap_dependent(exp, &original.program)
                            .map_err(EvaluationError::Context)?
                        {
                            triggers.insert(exp.clone(), value.clone());
                        }
                    }
                }
                state.h = original.h.clone();
                state.partially_consumed_heap = original.partially_consumed_heap.clone();
                state.possible_triggers = triggers;
                state.is_eval_in_old = original.is_eval_in_old;
                let debug = if kind == 2 {
                    Some(expression.clone())
                } else {
                    rewritten.map(|e| {
                        Exp::new(
                            if kind == 0 {
                                ExpKind::Old(e)
                            } else {
                                ExpKind::LabelledOld(e, label.clone())
                            },
                            expression.metadata().clone(),
                        )
                    })
                };
                continuation(context, state, term, debug)
            },
        );
    }
    if let ExpKind::Let(declaration, value, body) = expression.kind() {
        return evaluate(
            context,
            state,
            value,
            error,
            &mut |context, mut state, value_term, value_exp| {
                let mut variables = state.function_recorder.arguments().unwrap_or_default();
                variables.extend(state.packaging_wand_snapshots.clone());
                variables.extend(state.quantified_variables.clone());
                let variables: Vec<_> = variables.into_iter().map(|(term, _)| term).collect();
                let (fresh, applicable) = context
                    .fresh_let_application(&declaration.typ, &variables)
                    .map_err(EvaluationError::Context)?;
                let equality = factory.builtin_equals(fresh, value_term.clone());
                let variable = declaration.local_var();
                if context.debugging() && value_exp.is_none() {
                    return Err(EvaluationError::MissingDebugExpression);
                }
                context
                    .assume_let_definition(&equality, &variable, value, value_exp.as_ref())
                    .map_err(EvaluationError::Context)?;
                state.function_recorder = state
                    .function_recorder
                    .record_fresh_snapshot(applicable)
                    .enter_let(expression.clone());
                let before = state.possible_triggers.clone();
                let local = Exp::new(ExpKind::LocalVar(variable), declaration.meta.clone());
                let key = AbstractLocalVar::new(local.clone());
                state.g = Arc::new(state.g.with_binding(key, (value_term, value_exp.clone())));
                evaluate(
                    context,
                    state,
                    body,
                    error,
                    &mut |context, mut state, term, body_exp| {
                        if state.record_possible_triggers {
                            let added: Vec<_> = state
                                .possible_triggers
                                .iter()
                                .filter(|(exp, _)| before.get(exp).is_none())
                                .cloned()
                                .collect();
                            for (trigger, term) in added {
                                let replaced = ferrum_silver::ast::utility::rewriter::strategy::replace_expressions(&trigger,&[(local.clone(),value.clone())]).map_err(EvaluationError::Rewrite)?;
                                state.possible_triggers.insert(replaced, term);
                            }
                        }
                        state.function_recorder = state.function_recorder.leave_let(expression);
                        let rebuilt = if let Some(value) = &value_exp {
                            let body = body_exp.ok_or(EvaluationError::MissingDebugExpression)?;
                            Some(Exp::new(
                                ExpKind::Let(declaration.clone(), value.clone(), body),
                                expression.metadata().clone(),
                            ))
                        } else {
                            None
                        };
                        continuation(context, state, term, rebuilt)
                    },
                )
            },
        );
    }
    context.evaluate_special(state, expression, error, continuation)
}

#[inline(never)]
fn evaluate_collection_family<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    _factory: crate::state::terms::TermFactory,
    _debug: Option<Exp>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    if let ExpKind::ExplicitMap(entries) = expression.kind() {
        let Some(first) = entries.first() else {
            return Err(EvaluationError::EmptyExplicitCollection);
        };
        let ExpKind::Maplet(first_key, first_value) = first.kind() else {
            return Err(EvaluationError::InvalidMapLiteral);
        };
        let key_type = first_key.typ().map_err(EvaluationError::ExpressionType)?;
        let value_type = first_value.typ().map_err(EvaluationError::ExpressionType)?;
        let mut desugared = Exp::new(
            ExpKind::EmptyMap(key_type, value_type),
            expression.metadata().clone(),
        );
        for entry in entries {
            let ExpKind::Maplet(key, value) = entry.kind() else {
                return Err(EvaluationError::InvalidMapLiteral);
            };
            desugared = Exp::new(
                ExpKind::MapUpdate(desugared, key.clone(), value.clone()),
                expression.metadata().clone(),
            );
        }
        return evaluate(
            context,
            state,
            &desugared,
            error,
            &mut |context, state, term, _| {
                continuation(
                    context,
                    state,
                    term,
                    context.debugging().then(|| expression.clone()),
                )
            },
        );
    }
    let explicit = match expression.kind() {
        ExpKind::ExplicitSeq(es) | ExpKind::ExplicitSet(es) | ExpKind::ExplicitMultiset(es) => {
            Some(es)
        }
        _ => None,
    };
    if let Some(elements) = explicit {
        return evaluate_all(
            context,
            state,
            elements,
            &|_| error.clone(),
            &mut |context, state, terms, debug_elements| {
                complete_explicit_collection(
                    context,
                    state,
                    expression,
                    terms,
                    debug_elements,
                    continuation,
                )
            },
        );
    }
    if let Some((_, args)) = indexed_collection_arguments(expression) {
        return evaluate_all(
            context,
            state,
            &args,
            &|_| error.clone(),
            &mut |context, state, terms, debug_args| {
                complete_indexed_collection(
                    context,
                    state,
                    expression,
                    &args,
                    terms,
                    debug_args,
                    error,
                    continuation,
                )
            },
        );
    }

    context.evaluate_special(state, expression, error, continuation)
}

#[inline(never)]
fn evaluate_operator_family<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expression: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    factory: crate::state::terms::TermFactory,
    _debug: Option<Exp>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let unary = match expression.kind() {
        ExpKind::Not(arg) => Some((0, arg)),
        ExpKind::Minus(arg) => Some((1, arg)),
        ExpKind::PermMinus(arg) => Some((2, arg)),
        ExpKind::SeqLength(arg) => Some((3, arg)),
        ExpKind::MapCardinality(arg) => Some((4, arg)),
        ExpKind::MapDomain(arg) => Some((5, arg)),
        ExpKind::MapRange(arg) => Some((6, arg)),
        _ => None,
    };
    if let Some((operator, arg)) = unary {
        return evaluate(
            context,
            state,
            arg,
            error,
            &mut |context, state, term, debug| {
                let result = match operator {
                    0 => factory.not(term),
                    1 => factory.minus(factory.int_literal(0), term),
                    2 => factory.perm_minus(factory.no_perm(), term),
                    3 => factory.seq_length(term),
                    4 => factory.map_cardinality(term),
                    5 => factory.map_domain(term),
                    _ => factory.map_range(term),
                };
                let debug = debug.map(|arg| {
                    Exp::new(
                        match operator {
                            0 => ExpKind::Not(arg),
                            1 => ExpKind::Minus(arg),
                            2 => ExpKind::PermMinus(arg),
                            3 => ExpKind::SeqLength(arg),
                            4 => ExpKind::MapCardinality(arg),
                            5 => ExpKind::MapDomain(arg),
                            _ => ExpKind::MapRange(arg),
                        },
                        expression.metadata().clone(),
                    )
                });
                continuation(context, state, result, debug)
            },
        );
    }
    if let ExpKind::SeqContains(element, sequence) = expression.kind() {
        return evaluate(
            context,
            state,
            sequence,
            error,
            &mut |context, state, seq, seq_exp| {
                evaluate(
                    context,
                    state,
                    element,
                    error,
                    &mut |context, state, element_term, element_exp| {
                        let debug = match (&element_exp, &seq_exp) {
                            (Some(e), Some(s)) => Some(Exp::new(
                                ExpKind::SeqContains(e.clone(), s.clone()),
                                expression.metadata().clone(),
                            )),
                            (None, _) => None,
                            (Some(_), None) => return Err(EvaluationError::MissingDebugExpression),
                        };
                        continuation(
                            context,
                            state,
                            factory.seq_in(seq.clone(), element_term),
                            debug,
                        )
                    },
                )
            },
        );
    }
    if let ExpKind::AnySetCardinality(arg) = expression.kind() {
        let typ = arg.typ().map_err(EvaluationError::ExpressionType)?;
        let multi = match typ {
            ferrum_silver::ast::r#type::Type::Set(_) => false,
            ferrum_silver::ast::r#type::Type::Multiset(_) => true,
            _ => return Err(EvaluationError::ExpectedSetType),
        };
        return evaluate(
            context,
            state,
            arg,
            error,
            &mut |context, state, term, debug| {
                let term = if multi {
                    factory.multiset_cardinality(term)
                } else {
                    factory.set_cardinality(term)
                };
                let debug = debug.map(|arg| {
                    Exp::new(
                        ExpKind::AnySetCardinality(arg),
                        expression.metadata().clone(),
                    )
                });
                continuation(context, state, term, debug)
            },
        );
    }
    let collection_kind = match expression.kind() {
        ExpKind::AnySetUnion(a, b) => Some((0, a, b)),
        ExpKind::AnySetIntersection(a, b) => Some((1, a, b)),
        ExpKind::AnySetSubset(a, b) => Some((2, a, b)),
        ExpKind::AnySetMinus(a, b) => Some((3, a, b)),
        ExpKind::AnySetContains(a, b) => Some((4, a, b)),
        _ => None,
    };
    let collection = if let Some((kind, a, b)) = collection_kind {
        let typ = if kind == 4 {
            b.typ()
        } else if kind == 2 {
            a.typ()
        } else {
            expression.typ()
        }
        .map_err(EvaluationError::ExpressionType)?;
        let multi = match typ {
            ferrum_silver::ast::r#type::Type::Set(_) => false,
            ferrum_silver::ast::r#type::Type::Multiset(_) => true,
            _ => return Err(EvaluationError::ExpectedSetType),
        };
        let op = match kind {
            0 => Binary::SetUnion(multi),
            1 => Binary::SetIntersection(multi),
            2 => Binary::SetSubset(multi),
            3 => Binary::SetMinus(multi),
            _ => Binary::SetContains(multi),
        };
        Some((op, a, b))
    } else {
        None
    };
    let binary = match expression.kind() {
        ExpKind::EqCmp(a, b) => Some((Binary::Eq, a, b)),
        ExpKind::NeCmp(a, b) => Some((Binary::Ne, a, b)),
        ExpKind::Add(a, b) => Some((Binary::Add, a, b)),
        ExpKind::Sub(a, b) => Some((Binary::Sub, a, b)),
        ExpKind::Mul(a, b) => Some((Binary::Mul, a, b)),
        ExpKind::Div(a, b) => Some((Binary::Div, a, b)),
        ExpKind::Mod(a, b) => Some((Binary::Mod, a, b)),
        ExpKind::FractionalPerm(a, b) => Some((Binary::Fraction, a, b)),
        ExpKind::PermDiv(a, b) => Some((Binary::PermDiv, a, b)),
        ExpKind::PermPermDiv(a, b) => Some((Binary::PermPermDiv, a, b)),
        ExpKind::LeCmp(a, b) => Some((Binary::Le, a, b)),
        ExpKind::LtCmp(a, b) => Some((Binary::Lt, a, b)),
        ExpKind::GeCmp(a, b) => Some((Binary::Ge, a, b)),
        ExpKind::GtCmp(a, b) => Some((Binary::Gt, a, b)),
        ExpKind::MapContains(a, b) => Some((Binary::MapContains, a, b)),
        ExpKind::SeqAppend(a, b) => Some((Binary::SeqAppend, a, b)),
        ExpKind::SeqDrop(a, b) => Some((Binary::SeqDrop, a, b)),
        ExpKind::SeqTake(a, b) => Some((Binary::SeqTake, a, b)),
        ExpKind::RangeSeq(a, b) => Some((Binary::SeqRange, a, b)),
        ExpKind::PermAdd(a, b) => Some((Binary::PermAdd, a, b)),
        ExpKind::PermSub(a, b) => Some((Binary::PermSub, a, b)),
        ExpKind::PermMul(a, b) => Some((Binary::PermMul, a, b)),
        ExpKind::DebugPermMin(a, b) => Some((Binary::PermMin, a, b)),
        ExpKind::IntPermMul(a, b) => Some((Binary::IntPermMul, a, b)),
        ExpKind::PermLeCmp(a, b) => Some((Binary::PermLe, a, b)),
        ExpKind::PermLtCmp(a, b) => Some((Binary::PermLt, a, b)),
        ExpKind::PermGeCmp(a, b) => Some((Binary::PermGe, a, b)),
        ExpKind::PermGtCmp(a, b) => Some((Binary::PermGt, a, b)),
        ExpKind::And(a, b) if context.disable_short_circuiting() => Some((Binary::And, a, b)),
        ExpKind::Or(a, b) if context.disable_short_circuiting() => Some((Binary::Or, a, b)),
        _ => None,
    };
    if let Some((operator, left, right)) = collection.or(binary) {
        return evaluate(
            context,
            state,
            left,
            error,
            &mut |context, state, left_term, left_exp| {
                evaluate(
                    context,
                    state,
                    right,
                    error,
                    &mut |context, state, right_term, right_exp| {
                        let result =
                            operator.build(&factory, left_term.clone(), right_term.clone());
                        let right_exp_for_check = right_exp.clone();
                        let reconstructed = match (&left_exp, right_exp) {
                            (Some(left), Some(right)) => Some(Exp::new(
                                operator.expression(left.clone(), right),
                                expression.metadata().clone(),
                            )),
                            (None, _) => None,
                            (Some(_), None) => return Err(EvaluationError::MissingDebugExpression),
                        };
                        if matches!(
                            operator,
                            Binary::Div
                                | Binary::Mod
                                | Binary::Fraction
                                | Binary::PermDiv
                                | Binary::PermPermDiv
                        ) {
                            let zero = if matches!(operator, Binary::PermPermDiv) {
                                factory.no_perm()
                            } else {
                                factory.int_literal(0)
                            };
                            let nonzero = factory.not(factory.equals(right_term.clone(), zero));
                            if !context
                                .assert_goal(&nonzero)
                                .map_err(EvaluationError::Context)?
                            {
                                let debug_zero =
                                    Exp::new(ExpKind::IntLit(0.into()), Default::default());
                                let original_test = context.debugging().then(|| {
                                    Exp::new(
                                        ExpKind::NeCmp(right.clone(), debug_zero.clone()),
                                        right.metadata().clone(),
                                    )
                                });
                                let rewritten_test = if context.debugging() {
                                    let divisor = right_exp_for_check
                                        .clone()
                                        .ok_or(EvaluationError::MissingDebugExpression)?;
                                    Some(Exp::new(
                                        ExpKind::NeCmp(divisor, debug_zero),
                                        right.metadata().clone(),
                                    ))
                                } else {
                                    None
                                };
                                let failure = context
                                    .division_failure(
                                        &state,
                                        error,
                                        right,
                                        &nonzero,
                                        rewritten_test.as_ref(),
                                    )
                                    .map_err(EvaluationError::Context)?;
                                if state.retry_level == 0 && context.report_further_errors() {
                                    context
                                        .assume_nonzero(
                                            &nonzero,
                                            original_test.as_ref(),
                                            rewritten_test.as_ref(),
                                        )
                                        .map_err(EvaluationError::Context)?;
                                    if failure.continue_verification() {
                                        let next =
                                            continuation(context, state, result, reconstructed)?;
                                        return Ok(failure.combine(|| next, false));
                                    }
                                }
                                return Ok(failure);
                            }
                        }
                        continuation(context, state, result, reconstructed)
                    },
                )
            },
        );
    }
    context.evaluate_special(state, expression, error, continuation)
}

/// Evaluate a sequence left-to-right, retaining source order and debug option semantics.
pub fn evaluate_all<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expressions: &[Exp],
    error_for: &impl Fn(&Exp) -> C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Vec<Term>,
        Option<Vec<Exp>>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let Some((first, rest)) = expressions.split_first() else {
        return continuation(
            context,
            state,
            Vec::new(),
            context.debugging().then(Vec::new),
        );
    };
    let error = error_for(first);
    evaluate(
        context,
        state,
        first,
        &error,
        &mut |context, state, term, expression| {
            evaluate_all(
                context,
                state,
                rest,
                error_for,
                &mut |context, state, mut terms, debug| {
                    terms.insert(0, term.clone());
                    let debug = if let Some(first) = &expression {
                        let mut tail = debug.ok_or(EvaluationError::MissingDebugExpression)?;
                        tail.insert(0, first.clone());
                        Some(tail)
                    } else {
                        None
                    };
                    continuation(context, state, terms, debug)
                },
            )
        },
    )
}

/// Source flattens adjacent conjunctions/disjunctions, then joins the stop and continue paths.
fn evaluate_short_circuit<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expressions: &[Exp],
    disjunction: bool,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let (head, tail) = expressions
        .split_first()
        .expect("flattened expression is nonempty");
    let factory = context.factory().clone();
    evaluate(
        context,
        state,
        head,
        error,
        &mut |context, state, term, debug| {
            if tail.is_empty()
                || matches!(
                    (disjunction, term.kind()),
                    (true, crate::state::terms::TermKind::True)
                        | (false, crate::state::terms::TermKind::False)
                )
            {
                return continuation(context, state, term, debug);
            }
            let (condition, original, rewritten) = if disjunction {
                (term.clone(), head.clone(), debug.clone())
            } else {
                (
                    factory.not(term.clone()),
                    Exp::new(ExpKind::Not(head.clone()), Default::default()),
                    debug
                        .clone()
                        .map(|e| Exp::new(ExpKind::Not(e), Default::default())),
                )
            };
            context.branch_join_evaluation(
                state,
                condition,
                &original,
                rewritten.as_ref(),
                true,
                EvaluationBranchAction::Value {
                    term: term.clone(),
                    debug: debug.clone(),
                },
                EvaluationBranchAction::ShortCircuit {
                    expressions: tail.to_vec(),
                    disjunction,
                    error: error.clone(),
                },
                &mut |context, entries| {
                    let mut entries = entries.into_iter();
                    let (state, a, a_exp) =
                        entries.next().ok_or(EvaluationError::InvalidJoinEntries)?;
                    if let Some((other, b, b_exp)) = entries.next() {
                        if entries.next().is_some() {
                            return Err(EvaluationError::InvalidJoinEntries);
                        }
                        let state = context
                            .merge_evaluation_states(state, &other)
                            .map_err(EvaluationError::Context)?;
                        let result = if disjunction {
                            factory.or([a, b])
                        } else {
                            factory.and([a, b])
                        };
                        let debug = if context.debugging() {
                            let (a, b) = (
                                a_exp.ok_or(EvaluationError::MissingDebugExpression)?,
                                b_exp.ok_or(EvaluationError::MissingDebugExpression)?,
                            );
                            Some(Exp::new(
                                if disjunction {
                                    ExpKind::Or(a, b)
                                } else {
                                    ExpKind::And(a, b)
                                },
                                Default::default(),
                            ))
                        } else {
                            None
                        };
                        Ok((state, result, debug))
                    } else {
                        Ok((state, a, a_exp))
                    }
                },
                continuation,
            )
        },
    )
}

/// Execute an owned join action using the worker's local context.
pub fn execute_branch_action<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    action: EvaluationBranchAction<C::PartialError>,
    done: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    match action {
        EvaluationBranchAction::Evaluate { expression, error } => {
            evaluate(context, state, &expression, &error, done)
        }
        EvaluationBranchAction::Value { term, debug } => done(context, state, term, debug),
        EvaluationBranchAction::True => {
            let debug = context
                .debugging()
                .then(|| Exp::new(ExpKind::TrueLit, Default::default()));
            let term = context.factory().boolean(true);
            done(context, state, term, debug)
        }
        EvaluationBranchAction::ShortCircuit {
            expressions,
            disjunction,
            error,
        } => evaluate_short_circuit(context, state, &expressions, disjunction, &error, done),
    }
}

/// Result of the general `evalQuantified` operation; a missing second result represents
/// an infeasible inner path, not a successful proof.
#[derive(Clone, Debug)]
pub struct ScopedQuantifiedResult {
    pub variables: Vec<Term>,
    pub variable_expressions: Option<Vec<ferrum_silver::ast::program::LocalVarDecl>>,
    pub first_terms: Vec<Term>,
    pub first_expressions: Option<Vec<Exp>>,
    pub second: Option<ScopedQuantifiedBody>,
}
#[derive(Clone, Debug)]
pub struct ScopedQuantifiedBody {
    pub terms: Vec<Term>,
    pub expressions: Option<Vec<Exp>>,
    pub triggers: Vec<crate::state::terms::Trigger>,
    pub auxiliary_globals: Vec<Term>,
    pub auxiliary_non_globals: Vec<Term>,
    pub auxiliary_debug: Option<(
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::debugger::debug_exp::DebugExp,
        >,
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::debugger::debug_exp::DebugExp,
        >,
    )>,
    pub possible_triggers: crate::state::package::OrderedMap<Exp, Term>,
}
#[derive(Clone, Debug)]
pub struct ScopedQuantifiedState<P, D, J> {
    pub state: State<P, D, J>,
    pub first_terms: Vec<Term>,
    pub first_expressions: Option<Vec<Exp>>,
    pub second: Option<ScopedQuantifiedBody>,
}
/// Local solver scopes and fresh-variable/trigger facilities for source quantified evaluation.
pub trait QuantifiedScopeContext<P, D, J, V>: EvaluationContext<P, D, J, V> {
    fn fresh_quantified_variable(
        &mut self,
        decl: &ferrum_silver::ast::program::LocalVarDecl,
    ) -> Result<(Term, Option<Exp>), Self::Error>;
    fn locally_quantified(
        &mut self,
        state: State<P, D, J>,
        block: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                ScopedQuantifiedState<P, D, J>,
            )
                -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
        continuation: &mut dyn FnMut(
            &mut Self,
            ScopedQuantifiedState<P, D, J>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
    fn path_mark(&mut self) -> crate::decider::path_conditions::Mark;
    fn set_quantified_branch(
        &mut self,
        condition: Term,
        original: Exp,
        rewritten: Option<Exp>,
    ) -> Result<(), Self::Error>;
    fn path_after(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<crate::decider::path_conditions::RecordedPathConditions, Self::Error>;
    fn evaluate_triggers(
        &mut self,
        state: State<P, D, J>,
        triggers: &[ferrum_silver::ast::expression::Trigger],
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Vec<crate::state::terms::Trigger>,
        )
            -> Result<VerificationResult<V>, EvaluationError<Self::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<Self::Error>>;
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
    >;
}
/// Source quantified evaluation: bind variables, evaluate guards in a local solver scope,
/// then evaluate bodies/triggers and export quantified auxiliary assumptions.
pub fn evaluate_quantified<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    quantifier: crate::state::terms::Quantifier,
    declarations: &[ferrum_silver::ast::program::LocalVarDecl],
    first: &[Exp],
    second: &[Exp],
    ast_triggers: Option<&[ferrum_silver::ast::expression::Trigger]>,
    name: &str,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        ScopedQuantifiedResult,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: QuantifiedScopeContext<P, D, J, V>,
{
    use crate::state::store::MapBackedStore;
    let original = state.clone();
    let mut state = state;
    let mut vars = Vec::new();
    let mut var_exps = Vec::new();
    let mut bindings = Vec::new();
    for decl in declarations {
        let (term, debug) = context
            .fresh_quantified_variable(decl)
            .map_err(EvaluationError::Context)?;
        if context.debugging() && debug.is_none() {
            return Err(EvaluationError::MissingDebugExpression);
        }
        let local = Exp::new(ExpKind::LocalVar(decl.local_var()), decl.meta.clone());
        bindings.push((AbstractLocalVar::new(local), (term.clone(), debug.clone())));
        vars.push(term);
        if let Some(debug) = debug {
            var_exps.push(debug);
        }
    }
    state.g = Arc::new(state.g.with_store(&MapBackedStore::from_bindings(bindings)));
    let mut quantified = Vec::new();
    for (index, term) in vars.iter().enumerate() {
        let debug = if context.debugging() {
            Some(AbstractLocalVar::new(var_exps[index].clone()))
        } else {
            None
        };
        quantified.push((term.clone(), debug));
    }
    quantified.extend(state.quantified_variables.clone());
    state.quantified_variables = quantified;
    state.record_possible_triggers = true;
    state.possible_triggers = Default::default();
    let factory = context.factory().clone();
    let triggers = ast_triggers.unwrap_or_default();
    context.locally_quantified(
        state,
        &mut |context, state, done| {
            let mark = context.path_mark();
            evaluate_all(
                context,
                state,
                first,
                &|_| error.clone(),
                &mut |context, state, first_terms, first_expressions| {
                    let condition = factory.and(first_terms.clone());
                    fn big_and(expressions: &[Exp]) -> Exp {
                        let mut iter = expressions.iter();
                        let Some(first) = iter.next() else {
                            return Exp::new(ExpKind::TrueLit, Default::default());
                        };
                        iter.fold(first.clone(), |a, b| {
                            Exp::new(ExpKind::And(a, b.clone()), Default::default())
                        })
                    }
                    let rewritten = first_expressions.as_ref().map(|es| big_and(es));
                    context
                        .set_quantified_branch(condition.clone(), big_and(first), rewritten)
                        .map_err(EvaluationError::Context)?;
                    let mut final_state = state.clone();
                    let mut body = None;
                    let result = evaluate_all(
                        context,
                        state,
                        second,
                        &|_| error.clone(),
                        &mut |context, state, terms, expressions| {
                            context.evaluate_triggers(
                                state,
                                triggers,
                                error,
                                &mut |context, state, term_triggers| {
                                    let paths = context
                                        .path_after(mark)
                                        .map_err(EvaluationError::Context)?;
                                    let (globals, non_globals) = paths
                                        .quantified(
                                            &factory,
                                            quantifier,
                                            &vars,
                                            &term_triggers,
                                            &format!("{name}-aux"),
                                            false,
                                            &condition,
                                        )
                                        .map_err(EvaluationError::Path)?;
                                    let debug = if context.debugging() {
                                        Some(
                                            context
                                                .quantified_debug(
                                                    &paths,
                                                    quantifier,
                                                    &vars,
                                                    &var_exps,
                                                    triggers,
                                                    &term_triggers,
                                                    &condition,
                                                )
                                                .map_err(EvaluationError::Context)?,
                                        )
                                    } else {
                                        None
                                    };
                                    let possible_triggers = if original.record_possible_triggers {
                                        state.possible_triggers.clone()
                                    } else {
                                        Default::default()
                                    };
                                    final_state = state;
                                    body = Some(ScopedQuantifiedBody {
                                        terms: terms.clone(),
                                        expressions: expressions.clone(),
                                        triggers: term_triggers,
                                        auxiliary_globals: globals,
                                        auxiliary_non_globals: non_globals,
                                        auxiliary_debug: debug,
                                        possible_triggers,
                                    });
                                    Ok(VerificationResult::success())
                                },
                            )
                        },
                    )?;
                    if !result.continue_verification() {
                        return Ok(result);
                    }
                    let next = done(
                        context,
                        ScopedQuantifiedState {
                            state: final_state,
                            first_terms,
                            first_expressions,
                            second: body,
                        },
                    )?;
                    Ok(result.combine(|| next, false))
                },
            )
        },
        &mut |context, local| {
            let mut state = original.clone();
            state.debug_old_heaps = local.state.debug_old_heaps.clone();
            state.temporary_heap_record = local.state.temporary_heap_record.clone();
            state.function_recorder = local.state.function_recorder.clone();
            state.sm_cache = local.state.sm_cache.clone();
            state.constrainable_arps = local.state.constrainable_arps.clone();
            state.possible_triggers = if let Some(body) = &local.second {
                original.possible_triggers.union(&body.possible_triggers)
            } else {
                original.possible_triggers.clone()
            };
            let variable_expressions = if context.debugging() {
                let mut result = Vec::new();
                for exp in &var_exps {
                    match exp.kind() {
                        ExpKind::LocalVarWithVersion(name, typ) => {
                            result.push(ferrum_silver::ast::program::LocalVarDecl::new(
                                name.clone(),
                                typ.clone(),
                                exp.metadata().clone(),
                            ))
                        }
                        _ => return Err(EvaluationError::MissingDebugExpression),
                    }
                }
                Some(result)
            } else {
                None
            };
            continuation(
                context,
                state,
                ScopedQuantifiedResult {
                    variables: vars.clone(),
                    variable_expressions,
                    first_terms: local.first_terms,
                    first_expressions: local.first_expressions,
                    second: local.second,
                },
            )
        },
    )
}

/// Check lower then upper bounds; on retry level zero the source may assume each failed
/// bound and retain both failures, in their original order.
fn sequence_bounds<C, P, D, J, V>(
    context: &mut C,
    state: &State<P, D, J>,
    sequence: &Term,
    index: &Term,
    original_sequence: &Exp,
    original_index: &Exp,
    rewritten: Option<&[Exp]>,
    error: &C::PartialError,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let f = context.factory().clone();
    let lower = f.at_least(index.clone(), f.int_literal(0));
    let upper = f.less(index.clone(), f.seq_length(sequence.clone()));
    let make_lower = |idx: Exp| {
        Exp::new(
            ExpKind::GeCmp(idx, Exp::new(ExpKind::IntLit(0.into()), Default::default())),
            original_index.metadata().clone(),
        )
    };
    let make_upper = |seq: Exp, idx: Exp| {
        Exp::new(
            ExpKind::LtCmp(idx, Exp::new(ExpKind::SeqLength(seq), Default::default())),
            original_index.metadata().clone(),
        )
    };
    let debug = if context.debugging() {
        let es = rewritten
            .filter(|e| e.len() >= 2)
            .ok_or(EvaluationError::MissingDebugExpression)?;
        Some((
            make_lower(original_index.clone()),
            make_lower(es[1].clone()),
            make_upper(original_sequence.clone(), original_index.clone()),
            make_upper(es[0].clone(), es[1].clone()),
        ))
    } else {
        None
    };
    let lower_ok = context
        .assert_goal(&lower)
        .map_err(EvaluationError::Context)?;
    if !lower_ok && !(state.retry_level == 0 && context.report_further_errors()) {
        return context
            .sequence_bounds_failure(
                state,
                error,
                original_sequence,
                original_index,
                true,
                &lower,
                debug.as_ref().map(|d| &d.1),
            )
            .map_err(EvaluationError::Context);
    }
    if !lower_ok {
        context
            .assume_generated(
                &lower,
                debug.as_ref().map(|d| &d.0),
                debug.as_ref().map(|d| &d.1),
            )
            .map_err(EvaluationError::Context)?;
    }
    let upper_ok = context
        .assert_goal(&upper)
        .map_err(EvaluationError::Context)?;
    let upper_result = if upper_ok {
        VerificationResult::success()
    } else {
        if state.retry_level == 0 && context.report_further_errors() {
            context
                .assume_generated(
                    &upper,
                    debug.as_ref().map(|d| &d.2),
                    debug.as_ref().map(|d| &d.3),
                )
                .map_err(EvaluationError::Context)?;
        }
        context
            .sequence_bounds_failure(
                state,
                error,
                original_sequence,
                original_index,
                false,
                &upper,
                debug.as_ref().map(|d| &d.3),
            )
            .map_err(EvaluationError::Context)?
    };
    if lower_ok {
        return Ok(upper_result);
    }
    let lower_failure = context
        .sequence_bounds_failure(
            state,
            error,
            original_sequence,
            original_index,
            true,
            &lower,
            debug.as_ref().map(|d| &d.1),
        )
        .map_err(EvaluationError::Context)?;
    if upper_result.with_kind(|k| matches!(k, crate::interfaces::verification::ResultKind::Success))
    {
        Ok(lower_failure)
    } else {
        Ok(lower_failure.combine(|| upper_result, false))
    }
}

/// Preserve source quantifier annotation precedence and position-derived qid.
pub fn quantifier_name_and_weight<E>(
    expression: &Exp,
    warn: &mut impl FnMut(String) -> Result<(), E>,
) -> Result<(String, Option<i32>), E> {
    use ferrum_silver::ast::{
        ast::Info,
        position::{LineColumn, Position},
    };
    let info = &expression.metadata().info;
    let weight = match info.find(&|i| matches!(i, Info::WeightedQuantifier(_))) {
        Some(Info::WeightedQuantifier(weight)) if *weight >= 0 => Some(*weight),
        Some(Info::WeightedQuantifier(weight)) => {
            warn(format!(
                "Invalid quantifier weight annotation: WeightedQuantifier({weight})"
            ))?;
            None
        }
        _ => match info.find(&|i| matches!(i, Info::Annotation(_))) {
            Some(Info::Annotation(annotations)) => {
                if let Some(values) = annotations.get("weight") {
                    match values.as_slice() {
                        [value] => match value.parse::<i32>() {
                            Ok(weight) if weight >= 0 => Some(weight),
                            _ => {
                                warn(format!(
                                    "Invalid quantifier weight annotation: List({})",
                                    values.join(", ")
                                ))?;
                                None
                            }
                        },
                        _ => {
                            warn(format!(
                                "Invalid quantifier weight annotation: List({})",
                                values.join(", ")
                            ))?;
                            None
                        }
                    }
                } else {
                    None
                }
            }
            _ => None,
        },
    };
    let position = &expression.metadata().position;
    let line = position
        .line_column()
        .map(|p| p.line().to_string())
        .unwrap_or_else(|| position.to_string());
    let fallback = format!("l{}", line.replace(' ', ""));
    let source = match position {
        Position::LineColumn(LineColumn::Source(p)) => {
            Some((p.file.as_deref(), p.start.as_ref(), p.end.as_deref()))
        }
        Position::LineColumn(LineColumn::Identifier(p)) => {
            Some((p.file.as_deref(), p.start.as_ref(), p.end.as_deref()))
        }
        Position::LineColumn(LineColumn::Translated(p)) => Some((p.file(), p.start(), p.end())),
        _ => None,
    };
    let name = match source {
        Some((file, start, Some(end))) => format!(
            "{}@{}@{}@{}@{}",
            file.map(|p| p.to_string_lossy().into_owned())
                .unwrap_or_else(|| "null".into()),
            start.line(),
            start.column(),
            end.line(),
            end.column()
        ),
        _ => fallback,
    };
    Ok((format!("prog.{name}"), weight))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ferrum_silver::ast::{
        ast::{Info, Metadata},
        position::{LineColumn, LineColumnPosition, Position, SourcePosition},
    };
    #[test]
    fn domain_debug_arguments_match_evaluate_all_option_order() {
        let a = Exp::new(ExpKind::IntLit(1.into()), Default::default());
        let b = Exp::new(ExpKind::IntLit(2.into()), Default::default());
        let rebuild = |values| rebuild_domain_debug_arguments::<()>(true, values);
        assert_eq!(
            rebuild(vec![Some(a.clone()), Some(b.clone())]).unwrap(),
            Some(vec![a.clone(), b.clone()])
        );
        assert_eq!(rebuild(vec![None, Some(b.clone())]).unwrap(), None);
        assert!(matches!(
            rebuild(vec![Some(a.clone()), None]),
            Err(EvaluationError::MissingDebugExpression)
        ));
        assert!(matches!(
            rebuild(vec![None, Some(a), None]),
            Err(EvaluationError::MissingDebugExpression)
        ));
        assert_eq!(
            rebuild_domain_debug_arguments::<()>(false, vec![]).unwrap(),
            None
        );
    }
    #[test]
    fn selected_path_visits_deep_wrappers_once() {
        let yes = Exp::new(ExpKind::TrueLit, Default::default());
        let mut exp = Exp::new(
            ExpKind::Asserting(yes, Exp::new(ExpKind::IntLit(1.into()), Default::default())),
            Default::default(),
        );
        let mut suffixes = Vec::new();
        for _ in 0..128 {
            exp = Exp::new(ExpKind::Minus(exp), Default::default());
            suffixes.push(exp.clone());
        }
        // Count the nodes scanned by the prior per-wrapper suffix selection.
        fn legacy_scan(exp: &Exp, visits: &mut usize) -> bool {
            *visits += 1;
            match exp.kind() {
                ExpKind::Asserting(..) => true,
                ExpKind::Minus(body) => legacy_scan(body, visits),
                _ => false,
            }
        }
        let mut legacy_visits = 0;
        for suffix in &suffixes {
            assert!(legacy_scan(suffix, &mut legacy_visits));
        }
        OWNED_PATH_VISITS.with(|count| count.set(0));
        let path = owned_asserting_path(&exp).unwrap();
        let visits = OWNED_PATH_VISITS.with(|count| count.get());
        assert_eq!(path.len(), 128);
        assert_eq!(visits, 129);
        assert_eq!(legacy_visits, 8384);
    }
    #[test]
    fn native_evaluation_branch_actions_are_send() {
        fn require_send<T: Send>() {}
        require_send::<
            EvaluationBranchAction<
                ferrum_silver::verifier::verification_error::PartialVerificationError,
            >,
        >();
    }
    #[test]
    fn quantifier_weight_precedence_and_full_source_qid() {
        let mut pos = SourcePosition::new("/tmp/example.vpr", 4, 2);
        pos.end = Some(Box::new(LineColumn::LineColumn(LineColumnPosition::new(
            5, 7,
        ))));
        let info = Info::pair(
            Info::WeightedQuantifier(-1),
            Info::Annotation([("weight".into(), vec!["3".into()])].into_iter().collect()),
        );
        let e = Exp::new(
            ExpKind::TrueLit,
            Metadata {
                position: Position::LineColumn(LineColumn::Source(Box::new(pos))),
                info,
                ..Default::default()
            },
        );
        let mut warnings = Vec::new();
        let (name, weight) = quantifier_name_and_weight(&e, &mut |message| {
            warnings.push(message);
            Ok::<_, ()>(())
        })
        .unwrap();
        assert_eq!(name, "prog./tmp/example.vpr@4@2@5@7");
        assert_eq!(weight, None);
        assert_eq!(warnings.len(), 1);
    }
}

fn evaluate_implication_term<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    lhs: Term,
    original: &Exp,
    rewritten: Option<&Exp>,
    rhs: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
        Option<Exp>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let factory = context.factory().clone();
    context.branch_join_evaluation(
        state,
        lhs.clone(),
        original,
        rewritten,
        false,
        EvaluationBranchAction::Evaluate {
            expression: rhs.clone(),
            error: error.clone(),
        },
        EvaluationBranchAction::True,
        &mut |context, entries| {
            let mut entries = entries.into_iter();
            let (mut state, first, first_exp) =
                entries.next().ok_or(EvaluationError::InvalidJoinEntries)?;
            if let Some((other, _, _)) = entries.next() {
                state = context
                    .merge_evaluation_states(state, &other)
                    .map_err(EvaluationError::Context)?;
            }
            if entries.next().is_some() {
                return Err(EvaluationError::InvalidJoinEntries);
            }
            let debug = if let Some(lhs) = rewritten {
                Some(Exp::new(
                    ExpKind::Implies(
                        lhs.clone(),
                        first_exp.ok_or(EvaluationError::MissingDebugExpression)?,
                    ),
                    Default::default(),
                ))
            } else {
                None
            };
            Ok((state, factory.implies(lhs.clone(), first), debug))
        },
        continuation,
    )
}
fn evaluate_for_perm_options<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    options: &[ForPermCondition],
    body: &Exp,
    error: &C::PartialError,
    declarations: &[ferrum_silver::ast::program::LocalVarDecl],
    store: Arc<crate::state::store::MapBackedStore>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Vec<Term>,
        Option<Vec<Exp>>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: EvaluationContext<P, D, J, V>,
{
    let Some((first, rest)) = options.split_first() else {
        let debug = context.debugging().then(Vec::new);
        return continuation(context, state, Vec::new(), debug);
    };
    let scope = context
        .open_implies_scope(&state, None, "ForPerm")
        .map_err(EvaluationError::Context)?;
    let mut state = state;
    state.g = Arc::new(state.g.with_store(&first.definitions));
    let factory = context.factory().clone();
    evaluate_implication_term(
        context,
        state,
        first.condition.clone(),
        &first.original,
        first.rewritten.as_ref(),
        body,
        error,
        &mut |context, mut state, implies, debug| {
            let term = factory
                .simplifying_forall(first.variables.clone(), implies, first.triggers.clone())
                .map_err(EvaluationError::QuantifierTransform)?;
            let exp = if context.debugging() {
                let body = debug.ok_or(EvaluationError::MissingDebugExpression)?;
                let implication = Exp::new(
                    ExpKind::Implies(first.original.clone(), body),
                    Default::default(),
                );
                Some(Exp::new(
                    ExpKind::Forall(declarations.to_vec(), vec![], implication),
                    Default::default(),
                ))
            } else {
                None
            };
            context
                .close_expression_scope(scope)
                .map_err(EvaluationError::Context)?;
            state.g = store.clone();
            evaluate_for_perm_options(
                context,
                state,
                rest,
                body,
                error,
                declarations,
                store.clone(),
                &mut |context, state, mut terms, debugs| {
                    // Source prepends each result during recursion, so final order is reversed.
                    terms.push(term.clone());
                    let debugs = if let Some(exp) = &exp {
                        let mut es = debugs.ok_or(EvaluationError::MissingDebugExpression)?;
                        es.push(exp.clone());
                        Some(es)
                    } else {
                        None
                    };
                    continuation(context, state, terms, debugs)
                },
            )
        },
    )
}

/// Trigger evaluation services preserve temporary solver paths, error counts and heap encoding.
pub trait TriggerEvaluationContext<P, D, J, V>: QuantifiedScopeContext<P, D, J, V> {
    fn cacheable_trigger(&self, expression: &Exp) -> bool;
    fn path_pop_until(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<(), Self::Error>;
    fn reported_errors(&self) -> usize;
    fn set_reported_errors(&mut self, count: usize);
    fn assume_trigger_delta(
        &mut self,
        paths: &crate::decider::path_conditions::RecordedPathConditions,
    ) -> Result<(), Self::Error>;
    fn adapt_trigger_terms(
        &mut self,
        state: &State<P, D, J>,
        terms: Vec<Term>,
    ) -> Result<Vec<Term>, Self::Error>;
    fn warn_trigger(&mut self, expression: &Exp) -> Result<(), Self::Error>;
    fn handles_resource_trigger(&self, state: &State<P, D, J>, expression: &Exp) -> bool;
    fn resource_trigger_variants(
        &mut self,
        state: State<P, D, J>,
        expression: &Exp,
        error: &Self::PartialError,
    ) -> Result<
        (
            State<P, D, J>,
            Vec<Term>,
            Vec<Vec<Term>>,
            Vec<crate::rules::quantified_chunk_support::SnapshotMapDefinition>,
        ),
        Self::Error,
    >;
    fn assume_heap_trigger_axioms(
        &mut self,
        expressions: &[Exp],
        axioms: &[Term],
    ) -> Result<(), Self::Error>;
}
/// Evaluate a non-heap trigger set, reusing recorded body terms before fresh evaluation.
pub fn evaluate_trigger<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expressions: &[Exp],
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Vec<Term>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: TriggerEvaluationContext<P, D, J, V>,
{
    use crate::state::terms::{ApplicableKind, ApplicationTarget, TermKind};
    let factory = context.factory().clone();
    let mut cached = Vec::new();
    let mut remaining = Vec::new();
    for expression in expressions {
        if context.cacheable_trigger(expression) {
            if let Some(term) = state.possible_triggers.get(expression) {
                let term = match term.kind() {
                    TermKind::App {
                        applicable: ApplicationTarget::Function(function),
                        args,
                    } if function.data().kind == ApplicableKind::HeapDepFun => factory.app(
                        crate::rules::function_supporter::limited_version(&factory, function),
                        args.clone(),
                    ),
                    _ => term.clone(),
                };
                cached.push(term);
                continue;
            }
        }
        remaining.push(expression.clone());
    }
    let mark = context.path_mark();
    let old_errors = context.reported_errors();
    let mut inner = state.clone();
    inner.trigger_exp = true;
    let mut evaluated = None;
    let mut delta = None;
    let mut recorder = state.function_recorder.clone();
    let result = evaluate_all(
        context,
        inner,
        &remaining,
        &|_| error.clone(),
        &mut |context, state, terms, _| {
            evaluated = Some(terms);
            delta = Some(context.path_after(mark).map_err(EvaluationError::Context)?);
            recorder = state.function_recorder;
            Ok(VerificationResult::success())
        },
    );
    let cleanup = context.path_pop_until(mark);
    context.set_reported_errors(old_errors);
    let result = match (result, cleanup) {
        (Ok(result), Ok(())) => result,
        (Err(evaluation), Err(cleanup)) => {
            return Err(EvaluationError::TriggerCleanup {
                evaluation: Box::new(evaluation),
                cleanup,
            });
        }
        (Err(error), Ok(())) => return Err(error),
        (Ok(_), Err(error)) => return Err(EvaluationError::Context(error)),
    };
    if result.with_kind(|kind| matches!(kind, crate::interfaces::verification::ResultKind::Success))
    {
        if let (Some(terms), Some(paths)) = (evaluated, delta) {
            context
                .assume_trigger_delta(&paths)
                .map_err(EvaluationError::Context)?;
            cached.extend(terms);
            let terms = context
                .adapt_trigger_terms(&state, cached)
                .map_err(EvaluationError::Context)?;
            let mut state = state;
            state.function_recorder = recorder;
            return continuation(context, state, terms);
        }
    }
    for expression in &remaining {
        context
            .warn_trigger(expression)
            .map_err(EvaluationError::Context)?;
    }
    let terms = context
        .adapt_trigger_terms(&state, cached)
        .map_err(EvaluationError::Context)?;
    continuation(context, state, terms)
}
/// Source heap triggers form the Cartesian product of resource-trigger alternatives.
pub fn evaluate_heap_trigger<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    expressions: &[Exp],
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Vec<Vec<Term>>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: TriggerEvaluationContext<P, D, J, V>,
{
    let mut alternatives = vec![Vec::new()];
    let mut axioms = Vec::new();
    let mut definitions = Vec::new();
    let mut current = state.clone();
    for expression in expressions {
        if context.handles_resource_trigger(&state, expression) {
            let (next, new_axioms, variants, new_definitions) = context
                .resource_trigger_variants(current, expression, error)
                .map_err(EvaluationError::Context)?;
            let mut product = Vec::new();
            for prefix in &alternatives {
                for variant in &variants {
                    let mut item = prefix.clone();
                    item.extend(variant.clone());
                    product.push(item);
                }
            }
            alternatives = product;
            axioms.extend(new_axioms);
            definitions.extend(new_definitions);
            current = next;
        } else {
            let mut trigger_state = state.clone();
            trigger_state.trigger_exp = true;
            let _ = evaluate_trigger(
                context,
                trigger_state,
                std::slice::from_ref(expression),
                error,
                &mut |_, _, terms| {
                    for alternative in &mut alternatives {
                        alternative.extend(terms.clone());
                    }
                    Ok(VerificationResult::success())
                },
            )?;
        }
    }
    context
        .assume_heap_trigger_axioms(expressions, &axioms)
        .map_err(EvaluationError::Context)?;
    for definition in definitions {
        current.function_recorder = current.function_recorder.record_fvf_and_domain(definition);
    }
    continuation(context, current, alternatives)
}
/// Evaluate trigger groups in order, expanding heap alternatives before later groups.
pub fn evaluate_triggers<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    triggers: &[ferrum_silver::ast::expression::Trigger],
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Vec<crate::state::terms::Trigger>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
where
    C: TriggerEvaluationContext<P, D, J, V>,
{
    fn go<C, P, D, J: Clone, V>(
        context: &mut C,
        state: State<P, D, J>,
        triggers: &[ferrum_silver::ast::expression::Trigger],
        collected: Vec<crate::state::terms::Trigger>,
        error: &C::PartialError,
        continuation: &mut dyn FnMut(
            &mut C,
            State<P, D, J>,
            Vec<crate::state::terms::Trigger>,
        )
            -> Result<VerificationResult<V>, EvaluationError<C::Error>>,
    ) -> Result<VerificationResult<V>, EvaluationError<C::Error>>
    where
        C: TriggerEvaluationContext<P, D, J, V>,
    {
        let Some((head, tail)) = triggers.split_first() else {
            return continuation(context, state, collected);
        };
        let heap = head.exps.iter().any(|e| {
            matches!(
                e.kind(),
                ExpKind::FieldAccess(..) | ExpKind::PredicateAccess(..) | ExpKind::MagicWand(..)
            )
        });
        if heap {
            evaluate_heap_trigger(
                context,
                state,
                &head.exps,
                error,
                &mut |context, state, variants| {
                    let mut next = collected.clone();
                    next.extend(
                        variants
                            .into_iter()
                            .map(|terms| crate::state::terms::Trigger { terms }),
                    );
                    go(context, state, tail, next, error, continuation)
                },
            )
        } else {
            evaluate_trigger(
                context,
                state,
                &head.exps,
                error,
                &mut |context, state, terms| {
                    let mut next = collected.clone();
                    next.push(crate::state::terms::Trigger { terms });
                    go(context, state, tail, next, error, continuation)
                },
            )
        }
    }
    go(context, state, triggers, Vec::new(), error, continuation)
}
