//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Consumer.scala
//!
//! Purpose:
//! Consume assertions and permissions from a symbolic heap, optionally returning a snapshot.
//!
//! Planned Rust structure:
//! ConsumptionRules and consumer implement consume/consumes, ordered consumeTlcs, recursive
//! consumeR, wrappedConsumeTlc, consumeTlc, consumeConditionalTlcMoreJoins and evalAndAssert.
//! Dispatch impure implication/conditional with branch or more-joins, access predicates, quantified
//! permissions, impure lets, invalid inhale-exhale nodes, and pure expression assertion.
//!
//! Behavior to preserve:
//! Select whenExhaling, flatten conjuncts in order with original per-assertion error and combine
//! snapshots; finalize against original heap before Q and restore partiallyConsumedHeap. Wrapper
//! temporarily sets the consumed heap as main heap for failure-driven consolidation, then restores
//! evaluation heap. Access evaluates args/permission, checks nonnegative, applies scaling and
//! configured wildcard optimization, triggers resource and updates partial heap. Quantified path
//! records entry/exit and delegates errors including noninjectivity and insufficient permission.
//! Impure joins merge heaps and snapshots conditionally; pure checks switch to wand evaluation heap
//! and restore reserve/exhale state. Quantifier checks assume transformed preconditions;
//! final-retry failure may assume assertion and continue to report further errors.
//!
//! Integration:
//! rules::producer, evaluator, execution_flow_controller, brancher, joiner, heap_supporter,
//! permission_supporter, magic_wand_supporter and supporters::snapshot_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Snapshot lifecycle, continuation and retry state with producer and heap supporter.
//!
//! Status: partial; CPS exhale projection, heap threading, retry boundaries and snapshots implemented.
//! Ordinary/QP resource, pure proof, impure branches and let sequencing implemented.
//! Quantifier evaluation, heap mutation and concrete verifier services remain boundaries.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::verification::VerificationResult;
use crate::state::{heap::ListBackedHeap, state::State, terms::Term};
use ferrum_silver::ast::{
    expression::{Exp, ExpKind},
    utility::expressions::{UnsupportedExtensionProjection, when_exhaling},
};
use std::sync::Arc;

#[derive(Debug)]
pub enum ConsumptionError<E> {
    Context(E),
    Projection(UnsupportedExtensionProjection),
    UnexpectedSnapshot,
    MissingPredicate(String),
    Wand(ferrum_silver::ast::utility::expressions::MagicWandError),
    MissingDebugExpression,
    Precondition(crate::state::function_precondition_transformer::PreconditionTransformError<E>),
    Trigger(crate::state::terms::UnsupportedTriggerTransform),
}
/// Verifier services needed to consume each conjunct, including failure-driven retry.
pub trait ConsumptionContext<P, D, J, V>: Sized {
    type Error;
    type PartialError: Clone;
    /// Native contexts use this safe point for cancellation; other hosts may omit it.
    fn cancellation_checkpoint(&self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn unit_snapshot(&self) -> Term;
    fn combine_snapshots(
        &mut self,
        state: &State<P, D, J>,
        first: Term,
        second: Term,
        assertion: &Exp,
        rest: &[Exp],
    ) -> Result<Term, Self::Error>;
    fn finalize_snapshot(
        &mut self,
        state: &State<P, D, J>,
        original_heap: &Arc<ListBackedHeap>,
        snapshot: Term,
        assertions: &[Exp],
    ) -> Result<Term, Self::Error>;
    /// Runs source tryOrFail with the consumption heap temporarily as main heap,
    /// then invokes consume_one with the original main heap restored.
    fn consume_with_retry(
        &mut self,
        state: State<P, D, J>,
        heap: Arc<ListBackedHeap>,
        assertion: &Exp,
        return_snapshot: bool,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
    /// Scope hooks for the retry-local ConsumeRecord. Active logger contexts must
    /// override both hooks; None is the disabled-logging default.
    fn open_consumption_scope(
        &mut self,
        _state: &State<P, D, J>,
        _assertion: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn close_consumption_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        Ok(())
    }
    /// Source impure implication or conditional-expression scope.
    fn open_consumption_conditional_scope(
        &mut self,
        _state: &State<P, D, J>,
        _assertion: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn close_consumption_conditional_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn factory(&self) -> &crate::state::terms::TermFactory;
    fn debugging(&self) -> bool;
    fn unsafe_wildcard_optimization(&self) -> bool;
    fn evaluate(
        &mut self,
        state: State<P, D, J>,
        expression: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Term,
            Option<Exp>,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
    fn assert_not_negative(
        &mut self,
        state: State<P, D, J>,
        permission: &Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
    fn trigger_resource(
        &mut self,
        state: State<P, D, J>,
        assertion: &Exp,
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn consume_single(
        &mut self,
        state: State<P, D, J>,
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
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
    fn eval_heap(&mut self, state: &State<P, D, J>) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn retry_pure(
        &mut self,
        state: State<P, D, J>,
        action: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                State<P, D, J>,
            )
                -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>,
        )
            -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
    fn precondition_function(
        &mut self,
        function: &crate::state::terms::Applicable,
    ) -> Result<crate::state::terms::Applicable, Self::Error>;
    fn assume_quantifier_precondition(
        &mut self,
        term: &Term,
        expression: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn assert_goal(&mut self, term: &Term) -> Result<bool, Self::Error>;
    fn assume_assertion(
        &mut self,
        term: &Term,
        original: &Exp,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn assertion_failure(
        &mut self,
        state: &State<P, D, J>,
        error: &Self::PartialError,
        original: &Exp,
        goal: &Term,
        rewritten: Option<&Exp>,
    ) -> Result<VerificationResult<V>, Self::Error>;
    fn report_further_errors(&self) -> bool;
    fn join_impure(&self, state: &State<P, D, J>) -> bool;
    fn branch_consumption(
        &mut self,
        state: State<P, D, J>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        join: bool,
        return_snapshot: bool,
        when_true: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                State<P, D, J>,
                Arc<ListBackedHeap>,
                Option<Term>,
            )
                -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>,
        )
            -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>,
        when_false: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                State<P, D, J>,
                Arc<ListBackedHeap>,
                Option<Term>,
            )
                -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>,
        )
            -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
    fn handle_let(
        &mut self,
        state: State<P, D, J>,
        assertion: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            crate::state::store::MapBackedStore,
            Exp,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
    fn evaluate_quantified_permission(
        &mut self,
        state: State<P, D, J>,
        forall: &Exp,
        condition: &Exp,
        permission: &Exp,
        arguments: &[Exp],
        qid: &str,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Option<crate::rules::producer::QuantifiedProductionData>,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
    fn consume_quantified(
        &mut self,
        state: State<P, D, J>,
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
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
    /// Implements impure conditionals, let, ordinary/QP resources and unexpected syntax.
    fn consume_special(
        &mut self,
        state: State<P, D, J>,
        heap: Arc<ListBackedHeap>,
        assertion: &Exp,
        return_snapshot: bool,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<V>,
            ConsumptionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ConsumptionError<Self::Error>>;
}
/// Entry projects exhale clauses, threads heaps, and restores partially-consumed heap on success.
pub fn consume_all<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    assertions: &[Exp],
    return_snapshot: bool,
    error_for: &impl Fn(&Exp) -> C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Option<Term>,
    ) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>,
) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>
where
    C: ConsumptionContext<P, D, J, V>,
{
    let mut conjuncts = Vec::new();
    let mut errors = Vec::new();
    for assertion in assertions {
        let projected = when_exhaling(assertion).map_err(ConsumptionError::Projection)?;
        let parts = projected.top_level_conjuncts();
        errors.extend(std::iter::repeat_n(error_for(assertion), parts.len()));
        conjuncts.extend(parts);
    }
    let original_heap = state.h.clone();
    let old_partial = state.partially_consumed_heap.clone();
    consume_conjuncts(
        context,
        state,
        original_heap.clone(),
        &conjuncts,
        return_snapshot,
        &errors,
        &mut |context, mut state, heap, snapshot| {
            let result = if let Some(snapshot) = snapshot {
                Some(
                    context
                        .finalize_snapshot(&state, &original_heap, snapshot, &conjuncts)
                        .map_err(ConsumptionError::Context)?,
                )
            } else {
                None
            };
            state.h = heap;
            state.partially_consumed_heap = old_partial.clone();
            continuation(context, state, result)
        },
    )
}
/// Recursive consumption uses already-projected assertions and source per-conjunct retry.
pub fn consume_recursive<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    assertion: &Exp,
    return_snapshot: bool,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Option<Term>,
    ) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>,
) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>
where
    C: ConsumptionContext<P, D, J, V>,
{
    let conjuncts = assertion.top_level_conjuncts();
    let errors = vec![error.clone(); conjuncts.len()];
    consume_conjuncts(
        context,
        state,
        heap,
        &conjuncts,
        return_snapshot,
        &errors,
        continuation,
    )
}
fn consume_conjuncts<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    assertions: &[Exp],
    return_snapshot: bool,
    errors: &[C::PartialError],
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Option<Term>,
    ) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>,
) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>
where
    C: ConsumptionContext<P, D, J, V>,
{
    let Some((first, rest)) = assertions.split_first() else {
        let snapshot = return_snapshot.then(|| context.unit_snapshot());
        return continuation(context, state, heap, snapshot);
    };
    if rest.is_empty() {
        return context.consume_with_retry(
            state,
            heap,
            first,
            return_snapshot,
            &errors[0],
            continuation,
        );
    }
    context.consume_with_retry(
        state,
        heap,
        first,
        return_snapshot,
        &errors[0],
        &mut |context, state, heap, first_snapshot| {
            consume_conjuncts(
                context,
                state,
                heap,
                rest,
                return_snapshot,
                &errors[1..],
                &mut |context, state, heap, second_snapshot| {
                    let snapshot = match (&first_snapshot, second_snapshot) {
                        (Some(a), Some(b)) if return_snapshot => Some(
                            context
                                .combine_snapshots(&state, a.clone(), b, first, rest)
                                .map_err(ConsumptionError::Context)?,
                        ),
                        (None, None) if !return_snapshot => None,
                        _ => return Err(ConsumptionError::UnexpectedSnapshot),
                    };
                    continuation(context, state, heap, snapshot)
                },
            )
        },
    )
}
/// Source `wrappedConsumeTlc` logging boundary. Call once inside each retry
/// attempt, after restoring the caller's main heap; a failed path deliberately
/// retains its scope, while every successful continuation closes the captured ID.
pub fn consume_one_logged<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    assertion: &Exp,
    return_snapshot: bool,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Option<Term>,
    ) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>,
) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>
where
    C: ConsumptionContext<P, D, J, V>,
{
    let scope = context
        .open_consumption_scope(&state, assertion)
        .map_err(ConsumptionError::Context)?;
    consume_one(
        context,
        state,
        heap,
        assertion,
        return_snapshot,
        error,
        &mut |context, state, heap, snapshot| {
            context
                .close_consumption_scope(scope)
                .map_err(ConsumptionError::Context)?;
            continuation(context, state, heap, snapshot)
        },
    )
}

/// Dispatch a retry-wrapped conjunct without assuming unimplemented cases succeed.
pub fn consume_one<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    assertion: &Exp,
    return_snapshot: bool,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Option<Term>,
    ) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>,
) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>
where
    C: ConsumptionContext<P, D, J, V>,
{
    context
        .cancellation_checkpoint()
        .map_err(ConsumptionError::Context)?;
    let special = matches!(
        assertion.kind(),
        ExpKind::FieldAccessPredicate(..)
            | ExpKind::PredicateAccessPredicate(..)
            | ExpKind::MagicWand(..)
            | ExpKind::InhaleExhaleExp(..)
    )
        || ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(
            assertion,
        )
        .is_some()
        || (!assertion.is_pure()
            && matches!(
                assertion.kind(),
                ExpKind::Implies(..) | ExpKind::CondExp(..) | ExpKind::Let(..)
            ));
    if !assertion.is_pure() {
        let conditional = match assertion.kind() {
            ExpKind::Implies(condition, yes) => Some((condition, yes, None)),
            ExpKind::CondExp(condition, yes, no) => Some((condition, yes, Some(no))),
            _ => None,
        };
        if let Some((condition, yes, no)) = conditional {
            let conditional_scope = context
                .open_consumption_conditional_scope(&state, assertion)
                .map_err(ConsumptionError::Context)?;
            return context.evaluate(
                state,
                condition,
                error,
                &mut |context, state, term, rewritten| {
                    let join = context.join_impure(&state);
                    context.branch_consumption(
                        state,
                        term,
                        condition,
                        rewritten.as_ref(),
                        join,
                        return_snapshot,
                        &mut |context, state, done| {
                            consume_recursive(
                                context,
                                state,
                                heap.clone(),
                                yes,
                                return_snapshot,
                                error,
                                &mut |context, state, heap, snapshot| {
                                    context
                                        .close_consumption_conditional_scope(conditional_scope)
                                        .map_err(ConsumptionError::Context)?;
                                    done(context, state, heap, snapshot)
                                },
                            )
                        },
                        &mut |context, state, done| {
                            if let Some(no) = no {
                                consume_recursive(
                                    context,
                                    state,
                                    heap.clone(),
                                    no,
                                    return_snapshot,
                                    error,
                                    &mut |context, state, heap, snapshot| {
                                        context
                                            .close_consumption_conditional_scope(conditional_scope)
                                            .map_err(ConsumptionError::Context)?;
                                        done(context, state, heap, snapshot)
                                    },
                                )
                            } else {
                                context
                                    .close_consumption_conditional_scope(conditional_scope)
                                    .map_err(ConsumptionError::Context)?;
                                let snapshot = return_snapshot.then(|| context.unit_snapshot());
                                done(context, state, heap.clone(), snapshot)
                            }
                        },
                        continuation,
                    )
                },
            );
        }
        if matches!(assertion.kind(), ExpKind::Let(..)) {
            return context.handle_let(
                state,
                assertion,
                error,
                &mut |context, mut state, bindings, body| {
                    state.g = Arc::new(state.g.with_store(&bindings));
                    consume_recursive(
                        context,
                        state,
                        heap.clone(),
                        &body,
                        return_snapshot,
                        error,
                        continuation,
                    )
                },
            );
        }
    }
    if matches!(
        assertion.kind(),
        ExpKind::FieldAccessPredicate(..)
            | ExpKind::PredicateAccessPredicate(..)
            | ExpKind::MagicWand(..)
    ) {
        return consume_access(
            context,
            state,
            heap,
            assertion,
            return_snapshot,
            error,
            continuation,
        );
    }
    if ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(
        assertion,
    )
    .is_some()
    {
        return consume_quantified_assertion(
            context,
            state,
            heap,
            assertion,
            return_snapshot,
            error,
            continuation,
        );
    }
    if special {
        context.consume_special(state, heap, assertion, return_snapshot, error, continuation)
    } else {
        assert_pure(
            context,
            state,
            heap,
            assertion,
            return_snapshot,
            error,
            continuation,
        )
    }
}

fn consume_access<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    assertion: &Exp,
    return_snapshot: bool,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Option<Term>,
    ) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>,
) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>
where
    C: ConsumptionContext<P, D, J, V>,
{
    use crate::state::{chunks::MagicWandIdentifier, terms::ResourceKey};
    let (resource, args) = match assertion.kind() {
        ExpKind::FieldAccessPredicate(field, _) => (
            ResourceKey::Field(Arc::new(field.field.clone())),
            vec![field.receiver.clone()],
        ),
        ExpKind::PredicateAccessPredicate(predicate) => {
            let name = &predicate.location.predicate_name;
            let decl = state
                .program
                .predicates
                .iter()
                .find(|p| &p.name == name)
                .ok_or_else(|| ConsumptionError::MissingPredicate(name.clone()))?;
            (
                ResourceKey::Predicate(Arc::new(decl.clone())),
                predicate.location.args.clone(),
            )
        }
        ExpKind::MagicWand(..) => {
            let wand = MagicWandIdentifier::new(assertion.clone(), &state.program)
                .map_err(ConsumptionError::Wand)?;
            let args = assertion
                .magic_wand_subexpressions(&state.program)
                .map_err(ConsumptionError::Wand)?;
            (ResourceKey::Wand(wand), args)
        }
        _ => unreachable!(),
    };
    let permission = assertion.permission_or_full().expect("access predicate");
    let original_arps = state.constrainable_arps.clone();
    evaluate_arguments(
        context,
        state,
        &args,
        error,
        &mut |context, state, terms, debug_args| {
            context.evaluate(
                state,
                &permission,
                error,
                &mut |context, state, permission_term, permission_exp| {
                    context.assert_not_negative(
                        state,
                        &permission_term,
                        &permission,
                        permission_exp.as_ref(),
                        error,
                        &mut |context, state| {
                            let factory = context.factory();
                            let strict = !context.unsafe_wildcard_optimization()
                                || (!matches!(resource, ResourceKey::Wand(_))
                                    && state.perm_locations.contains(&resource));
                            let loss = if strict {
                                factory.perm_times(
                                    permission_term.clone(),
                                    state.permission_scaling_factor.clone(),
                                )
                            } else {
                                factory.wildcard_simplifying_perm_times(
                                    permission_term.clone(),
                                    state.permission_scaling_factor.clone(),
                                )
                            };
                            let loss_exp = if let Some(p) = &permission_exp {
                                let scale = state
                                    .permission_scaling_factor_exp
                                    .clone()
                                    .ok_or(ConsumptionError::MissingDebugExpression)?;
                                Some(Exp::new(
                                    ExpKind::PermMul(p.clone(), scale),
                                    p.metadata().clone(),
                                ))
                            } else {
                                None
                            };
                            let state = context
                                .trigger_resource(state, assertion, &terms, debug_args.as_deref())
                                .map_err(ConsumptionError::Context)?;
                            context.consume_single(
                                state,
                                heap.clone(),
                                &resource,
                                assertion,
                                &terms,
                                debug_args.as_deref(),
                                loss,
                                loss_exp,
                                return_snapshot,
                                error,
                                &mut |context, mut state, heap, snapshot| {
                                    state.constrainable_arps = original_arps.clone();
                                    state.partially_consumed_heap = Some(heap.clone());
                                    continuation(context, state, heap, snapshot)
                                },
                            )
                        },
                    )
                },
            )
        },
    )
}
fn evaluate_arguments<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    args: &[Exp],
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Vec<Term>,
        Option<Vec<Exp>>,
    ) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>,
) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>
where
    C: ConsumptionContext<P, D, J, V>,
{
    let Some((head, tail)) = args.split_first() else {
        return continuation(
            context,
            state,
            Vec::new(),
            if context.debugging() {
                Some(Vec::new())
            } else {
                None
            },
        );
    };
    context.evaluate(state, head, error, &mut |context, state, term, debug| {
        evaluate_arguments(
            context,
            state,
            tail,
            error,
            &mut |context, state, mut terms, tail_debug| {
                terms.insert(0, term.clone());
                let debug = if let Some(head) = &debug {
                    let mut tail = tail_debug.ok_or(ConsumptionError::MissingDebugExpression)?;
                    tail.insert(0, head.clone());
                    Some(tail)
                } else {
                    None
                };
                continuation(context, state, terms, debug)
            },
        )
    })
}

fn assert_pure<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    assertion: &Exp,
    return_snapshot: bool,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Option<Term>,
    ) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>,
) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>
where
    C: ConsumptionContext<P, D, J, V>,
{
    let old_heap = state.h.clone();
    let old_reserve = state.reserve_heaps.clone();
    let old_exhale = state.exhale_ext;
    let mut evaluation_state = state;
    evaluation_state.h = context
        .eval_heap(&evaluation_state)
        .map_err(ConsumptionError::Context)?;
    evaluation_state.reserve_heaps.clear();
    evaluation_state.exhale_ext = false;
    context.retry_pure(
        evaluation_state,
        &mut |context, state, done| {
            context.evaluate(
                state,
                assertion,
                error,
                &mut |context, state, term, rewritten| {
                    let factory = context.factory().clone();
                    let goal = if let crate::state::terms::TermKind::Quantification {
                        quantifier,
                        vars,
                        body,
                        triggers,
                        name,
                        is_global,
                        weight,
                    } = term.kind()
                    {
                        let transformed =
                            crate::state::function_precondition_transformer::transform(
                                &factory,
                                body,
                                &mut |function| context.precondition_function(function),
                            )
                            .map_err(ConsumptionError::Precondition)?;
                        let precondition = factory
                            .quantification(
                                *quantifier,
                                vars.clone(),
                                transformed.clone(),
                                triggers.clone(),
                                format!("{name}_precondition"),
                                *is_global,
                                *weight,
                            )
                            .map_err(ConsumptionError::Trigger)?;
                        context
                            .assume_quantifier_precondition(&precondition, rewritten.as_ref())
                            .map_err(ConsumptionError::Context)?;
                        factory
                            .quantification(
                                *quantifier,
                                vars.clone(),
                                factory.implies(transformed, body.clone()),
                                triggers.clone(),
                                name.clone(),
                                *is_global,
                                *weight,
                            )
                            .map_err(ConsumptionError::Trigger)?
                    } else {
                        term.clone()
                    };
                    if context
                        .assert_goal(&goal)
                        .map_err(ConsumptionError::Context)?
                    {
                        context
                            .assume_assertion(&term, assertion, rewritten.as_ref())
                            .map_err(ConsumptionError::Context)?;
                        return done(context, state);
                    }
                    let failure = context
                        .assertion_failure(&state, error, assertion, &goal, rewritten.as_ref())
                        .map_err(ConsumptionError::Context)?;
                    if state.retry_level == 0 && context.report_further_errors() {
                        context
                            .assume_assertion(&term, assertion, rewritten.as_ref())
                            .map_err(ConsumptionError::Context)?;
                        if failure.continue_verification() {
                            let next = done(context, state)?;
                            return Ok(failure.combine(|| next, false));
                        }
                    }
                    Ok(failure)
                },
            )
        },
        &mut |context, mut state| {
            state.h = old_heap.clone();
            state.reserve_heaps = old_reserve.clone();
            state.exhale_ext = old_exhale;
            let snapshot = return_snapshot.then(|| context.unit_snapshot());
            continuation(context, state, heap.clone(), snapshot)
        },
    )
}

#[derive(Debug)]
pub enum ConditionalMergeError {
    InvalidEntries,
    UnexpectedSnapshot,
    MissingDebugExpression,
    State(crate::state::state::StateMergeError),
}
/// Source more-joins merge of the consumed heaps, snapshots and symbolic states.
pub fn merge_conditional_entries<P, D, J: Clone + PartialEq>(
    entries: &[crate::rules::joiner::JoinDataEntry<P, D, J, (Arc<ListBackedHeap>, Option<Term>)>],
    factory: &crate::state::terms::TermFactory,
    return_snapshot: bool,
    debugging: bool,
    warn: &mut impl FnMut(String),
) -> Result<(State<P, D, J>, Arc<ListBackedHeap>, Option<Term>), ConditionalMergeError> {
    if let [entry] = entries {
        return Ok((
            entry.state.clone(),
            entry.data.0.clone(),
            entry.data.1.clone(),
        ));
    }
    let [first, second] = entries else {
        return Err(ConditionalMergeError::InvalidEntries);
    };
    let guard1 = factory.and(first.path_conditions.branch_conditions());
    let guard2 = factory.and(second.path_conditions.branch_conditions());
    fn debug_guard(
        path: &crate::decider::path_conditions::RecordedPathConditions,
    ) -> Result<Exp, ConditionalMergeError> {
        let mut expressions = path
            .branch_condition_exps()
            .into_iter()
            .map(|(_, e)| e.ok_or(ConditionalMergeError::MissingDebugExpression));
        let Some(first) = expressions.next() else {
            return Ok(Exp::new(ExpKind::TrueLit, Default::default()));
        };
        let mut result = first?;
        for next in expressions {
            result = Exp::new(ExpKind::And(result, next?), Default::default());
        }
        Ok(result)
    }
    let debug1 = if debugging {
        Some(debug_guard(&first.path_conditions)?)
    } else {
        None
    };
    let debug2 = if debugging {
        Some(debug_guard(&second.path_conditions)?)
    } else {
        None
    };
    let heap = crate::state::state::merge_heap(
        first.data.0.as_ref(),
        &guard1,
        &debug1,
        second.data.0.as_ref(),
        &guard2,
        &debug2,
        factory,
    )
    .map_err(ConditionalMergeError::State)?;
    let snapshot = match (&first.data.1, &second.data.1) {
        (Some(a), Some(b)) if return_snapshot => Some(factory.ite(guard1, a.clone(), b.clone())),
        (None, None) if !return_snapshot => None,
        _ => return Err(ConditionalMergeError::UnexpectedSnapshot),
    };
    let state = first
        .state
        .merge_recorded(
            &first.path_conditions,
            &second.state,
            &second.path_conditions,
            factory,
            debugging,
            warn,
        )
        .map_err(ConditionalMergeError::State)?;
    Ok((state, Arc::new(heap), snapshot))
}

fn consume_quantified_assertion<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    assertion: &Exp,
    return_snapshot: bool,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Option<Term>,
    ) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>,
) -> Result<VerificationResult<V>, ConsumptionError<C::Error>>
where
    C: ConsumptionContext<P, D, J, V>,
{
    use crate::state::{chunks::MagicWandIdentifier, terms::ResourceKey};
    let (forall, condition, access) =
        ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(
            assertion,
        )
        .expect("quantified assertion");
    let (resource, args, qid) = match access.kind() {
        ExpKind::FieldAccessPredicate(field, _) => (
            ResourceKey::Field(Arc::new(field.field.clone())),
            vec![field.receiver.clone()],
            field.field.name.clone(),
        ),
        ExpKind::PredicateAccessPredicate(predicate) => {
            let name = &predicate.location.predicate_name;
            let decl = state
                .program
                .predicates
                .iter()
                .find(|p| &p.name == name)
                .ok_or_else(|| ConsumptionError::MissingPredicate(name.clone()))?;
            (
                ResourceKey::Predicate(Arc::new(decl.clone())),
                predicate.location.args.clone(),
                name.clone(),
            )
        }
        ExpKind::MagicWand(..) => {
            let wand = MagicWandIdentifier::new(access.clone(), &state.program)
                .map_err(ConsumptionError::Wand)?;
            let id = wand.to_string();
            let args = access
                .magic_wand_subexpressions(&state.program)
                .map_err(ConsumptionError::Wand)?;
            (ResourceKey::Wand(wand), args, id)
        }
        _ => unreachable!(),
    };
    let permission = access.permission_or_full().expect("access predicate");
    let original_arps = state.constrainable_arps.clone();
    state.function_recorder = state.function_recorder.enter_quantified(assertion.clone());
    context.evaluate_quantified_permission(
        state,
        &forall,
        &condition,
        &permission,
        &args,
        &qid,
        error,
        &mut |context, state, data| {
            if let Some(data) = data {
                context.consume_quantified(
                    state,
                    heap.clone(),
                    &resource,
                    &access,
                    &forall,
                    &qid,
                    &data,
                    return_snapshot,
                    error,
                    &mut |context, mut state, heap, snapshot| {
                        state.constrainable_arps = original_arps.clone();
                        state.function_recorder =
                            state.function_recorder.leave_quantified(assertion);
                        continuation(context, state, heap, snapshot)
                    },
                )
            } else {
                let snapshot = return_snapshot.then(|| context.unit_snapshot());
                continuation(context, state, heap.clone(), snapshot)
            }
        },
    )
}
