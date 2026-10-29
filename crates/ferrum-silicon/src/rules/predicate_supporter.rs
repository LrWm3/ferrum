//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/PredicateSupporter.scala
//!
//! Purpose:
//! Fold and unfold predicate resources, including cached predicate contents.
//!
//! Planned Rust structure:
//! PredicateSupportRules and predicateSupporter implement fold, unfold and producePredicateContents
//! for leaf and branch trees.
//!
//! Behavior to preserve:
//! Fold binds formal arguments, scales permission, consumes body with snapshot, restores store and
//! scaling, produces predicate chunk, then optionally assumes unfold trigger and resource trigger.
//! Unfold consumes predicate chunk, chooses cached contents or produces body from its snapshot,
//! saturates, assumes configured trigger and restores store/scaling. Cached leaves substitute and
//! scale chunks, convert singleton resources to quantified chunks where needed, record maps and
//! consolidate; branches use optional impure join except while unfolding, otherwise branch
//! directly.
//!
//! Integration:
//! rules::consumer, producer, heap_supporter, brancher, joiner, quantified_chunk_support,
//! state_consolidator and supporters::predicate_verification_unit.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Snapshot and permission scaling, branch continuation and predicate-content ownership.
//!
//! Status: fold/unfold and cached-content replay are connected to the native solver, heap,
//! quantified conversion and branch/join services. Simplified unfolding is connected;
//! debugging retains separate unsupported paths and broader parity remains unproved.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::verification::VerificationResult;
use crate::state::heap::ListBackedHeap;
use crate::state::state::State;
use crate::state::terms::{Term, TermFactory};
use crate::supporters::predicate_verification_unit::PredicateContentsTree;
use ferrum_silver::ast::expression::Exp;
use ferrum_silver::ast::program::Predicate;
use std::sync::Arc;

/// Owned continuation after a fold body has produced its snapshot.
#[derive(Clone)]
pub struct OwnedFoldBody<E> {
    pub outer_store: Arc<crate::state::store::MapBackedStore>,
    pub outer_sm_domain_needed: bool,
    pub outer_scaling: Term,
    pub outer_scaling_exp: Option<Exp>,
    pub wildcards: Vec<Term>,
    pub predicate: Predicate,
    pub access: Exp,
    pub args: Vec<Term>,
    pub arg_exps: Option<Vec<Exp>>,
    pub permission: Term,
    pub permission_exp: Option<Exp>,
    pub error: E,
    pub tail: crate::rules::executor::CfgStatementTail,
}

/// Explicit continuation after cached predicate contents have been produced.
#[derive(Clone)]
pub struct OwnedUnfoldFinish {
    pub outer_store: Arc<crate::state::store::MapBackedStore>,
    pub outer_scaling: Term,
    pub outer_scaling_exp: Option<Exp>,
    pub predicate: Predicate,
    pub args: Vec<Term>,
    pub arg_exps: Option<Vec<Exp>>,
    pub snapshot: Term,
    pub pre_heap: Arc<ListBackedHeap>,
    pub tail: crate::rules::executor::CfgStatementTail,
}

/// Owned reference to the existing outer unfolding join collector.
pub struct OwnedUnfoldJoin<P, D> {
    pub initial: State<P, D, crate::config::JoinMode>,
    pub mark: crate::decider::path_conditions::Mark,
    pub collector_id: Arc<()>,
}

/// Exact value-producing continuation of a cached predicate unfolding join.
pub struct OwnedUnfoldEvaluation<P, D> {
    pub initial: State<P, D, crate::config::JoinMode>,
    pub outer_store: Arc<crate::state::store::MapBackedStore>,
    pub outer_record_visited: bool,
    pub outer_scaling: Term,
    pub outer_scaling_exp: Option<Exp>,
    pub old_arps:
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<Term>,
    pub predicate: Predicate,
    pub body: Exp,
    pub error: ferrum_silver::verifier::verification_error::PartialVerificationError,
    pub mark: crate::decider::path_conditions::Mark,
    pub collector_id: Arc<()>,
}
impl<P, D> Clone for OwnedUnfoldEvaluation<P, D> {
    fn clone(&self) -> Self {
        Self {
            initial: self.initial.clone(),
            outer_store: self.outer_store.clone(),
            outer_record_visited: self.outer_record_visited,
            outer_scaling: self.outer_scaling.clone(),
            outer_scaling_exp: self.outer_scaling_exp.clone(),
            old_arps: self.old_arps.clone(),
            predicate: self.predicate.clone(),
            body: self.body.clone(),
            error: self.error.clone(),
            mark: self.mark,
            collector_id: self.collector_id.clone(),
        }
    }
}

pub trait PredicateExecutionServices<P, D, J, V>: Sized {
    type Error;
    type VerificationError;
    fn try_consume_owned_fold_body(
        &mut self,
        _state: &State<P, D, J>,
        _body: &Exp,
        _frame: &OwnedFoldBody<Self::VerificationError>,
    ) -> Option<Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>> {
        None
    }
    fn finish_owned_fold(
        &mut self,
        _state: State<P, D, J>,
        _tail: &crate::rules::executor::CfgStatementTail,
    ) -> Option<Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>> {
        None
    }
    fn predicate_debugging(&self) -> bool;
    fn consume_predicate_body(
        &mut self,
        state: State<P, D, J>,
        body: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Option<Term>,
        ) -> Result<
            VerificationResult<V>,
            PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>;
    fn produce_predicate_chunk(
        &mut self,
        state: State<P, D, J>,
        predicate: &Predicate,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
        snapshot: Term,
        permission: Term,
        permission_exp: Option<Exp>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>;
    fn consume_predicate_chunk(
        &mut self,
        state: State<P, D, J>,
        access: &Exp,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
        permission: &Term,
        permission_exp: Option<&Exp>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<V>,
            PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>;
    fn folded_predicate_snapshot(
        &mut self,
        state: &State<P, D, J>,
        predicate: &Predicate,
        args: &[Term],
        snapshot: &Term,
    ) -> Result<Term, Self::Error>;
    fn cached_predicate_contents(
        &self,
        state: &State<P, D, J>,
        predicate: &Predicate,
    ) -> Result<Option<(PredicateContentsTree, Vec<Term>)>, Self::Error>;
    fn try_produce_owned_cached_predicate(
        &mut self,
        _state: &State<P, D, J>,
        _tree: &PredicateContentsTree,
        _replacements: &std::collections::HashMap<Term, Term>,
        _finish: &OwnedUnfoldFinish,
    ) -> Option<Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>> {
        None
    }
    fn finish_owned_unfold(
        &mut self,
        _state: State<P, D, J>,
        _finish: &OwnedUnfoldFinish,
    ) -> Option<Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>> {
        None
    }
    fn produce_cached_predicate(
        &mut self,
        state: State<P, D, J>,
        tree: &PredicateContentsTree,
        replacements: &std::collections::HashMap<Term, Term>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>;
    fn try_produce_owned_unfolded_body(
        &mut self,
        _state: &State<P, D, J>,
        _body: &Exp,
        _error: &Self::VerificationError,
        _finish: &OwnedUnfoldFinish,
    ) -> Option<Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>> {
        None
    }
    fn produce_unfolded_body(
        &mut self,
        state: State<P, D, J>,
        predicate: &Predicate,
        args: &[Term],
        snapshot: &Term,
        pre_heap: &ListBackedHeap,
        body: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>;
    fn saturate_after_unfold(&mut self) -> Result<(), Self::Error>;
    fn predicate_unfold_triggers_enabled(&self) -> bool;
    fn assume_unfold_trigger(
        &mut self,
        state: &State<P, D, J>,
        predicate: &Predicate,
        snapshot: &Term,
        heap: &ListBackedHeap,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
    ) -> Result<(), Self::Error>;
    fn trigger_predicate_resource(
        &mut self,
        state: State<P, D, J>,
        access: &Exp,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
    ) -> Result<State<P, D, J>, Self::Error>;
}
#[derive(Debug)]
pub enum PredicateExecutionError<E> {
    AbstractPredicate,
    MissingDebugArguments,
    MissingDebugPermission,
    MissingSnapshot,
    Transform(crate::state::terms::UnsupportedTriggerTransform),
    Chunk(crate::state::chunks::ChunkError),
    UnsupportedMaskChunk,
    ReentrantContinuation,
    OwnedSchedulerUnavailable,
    Service(E),
}
fn bind_formals<P, D, J>(
    state: &State<P, D, J>,
    predicate: &Predicate,
    args: &[Term],
    arg_exps: Option<&[Exp]>,
    debugging: bool,
) -> Result<
    Arc<crate::state::store::MapBackedStore>,
    PredicateExecutionError<std::convert::Infallible>,
> {
    use crate::state::store::AbstractLocalVar;
    use ferrum_silver::ast::expression::ExpKind;
    let debug = if debugging {
        Some(arg_exps.ok_or(PredicateExecutionError::MissingDebugArguments)?)
    } else {
        None
    };
    let mut store = state.g.as_ref().clone();
    for (index, (formal, term)) in predicate.formal_args.iter().zip(args).enumerate() {
        if debugging && index >= debug.expect("debug arguments").len() {
            break;
        }
        let key = AbstractLocalVar::new(Exp::new(
            ExpKind::LocalVar(formal.local_var()),
            formal.meta.clone(),
        ));
        store = store.with_binding(
            key,
            (term.clone(), debug.map(|values| values[index].clone())),
        );
    }
    Ok(Arc::new(store))
}
fn binding_error<E>(
    error: PredicateExecutionError<std::convert::Infallible>,
) -> PredicateExecutionError<E> {
    match error {
        PredicateExecutionError::MissingDebugArguments => {
            PredicateExecutionError::MissingDebugArguments
        }
        _ => unreachable!("formal binding only reports missing debug arguments"),
    }
}
/// Fold consumes the body under bound formals and a scaled permission, then produces
/// the predicate chunk before assuming its configured trigger and resource trigger.
pub fn fold_predicate<P, D, J: Clone + PartialEq, V, C: PredicateExecutionServices<P, D, J, V>>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, J>,
    predicate: &Predicate,
    access: &Exp,
    args: &[Term],
    arg_exps: Option<&[Exp]>,
    permission: &Term,
    permission_exp: Option<&Exp>,
    constrainable_wildcards: &[Term],
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<
        VerificationResult<V>,
        PredicateExecutionError<C::Error>,
    >,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>>
where
    C::VerificationError: Clone,
{
    fold_predicate_with_owned_tail(
        factory,
        context,
        state,
        predicate,
        access,
        args,
        arg_exps,
        permission,
        permission_exp,
        constrainable_wildcards,
        error,
        None,
        continuation,
    )
}
pub fn fold_predicate_with_owned_tail<
    P,
    D,
    J: Clone + PartialEq,
    V,
    C: PredicateExecutionServices<P, D, J, V>,
>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, J>,
    predicate: &Predicate,
    access: &Exp,
    args: &[Term],
    arg_exps: Option<&[Exp]>,
    permission: &Term,
    permission_exp: Option<&Exp>,
    constrainable_wildcards: &[Term],
    error: &C::VerificationError,
    owned_tail: Option<&crate::rules::executor::CfgStatementTail>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<
        VerificationResult<V>,
        PredicateExecutionError<C::Error>,
    >,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>>
where
    C::VerificationError: Clone,
{
    let body = predicate
        .body
        .as_ref()
        .ok_or(PredicateExecutionError::AbstractPredicate)?;
    let bindings = bind_formals(
        &state,
        predicate,
        args,
        arg_exps,
        context.predicate_debugging(),
    )
    .map_err(binding_error)?;
    if state.permission_scaling_factor_exp.is_some() && permission_exp.is_none() {
        return Err(PredicateExecutionError::MissingDebugPermission);
    }
    let outer = state.clone();
    let mut inner =
        state.scale_permission_factor(permission.clone(), permission_exp.cloned(), factory);
    inner.g = bindings;
    inner.sm_domain_needed = true;
    if let Some(tail) = owned_tail {
        let frame = OwnedFoldBody {
            outer_store: outer.g.clone(),
            outer_sm_domain_needed: outer.sm_domain_needed,
            outer_scaling: outer.permission_scaling_factor.clone(),
            outer_scaling_exp: outer.permission_scaling_factor_exp.clone(),
            wildcards: constrainable_wildcards.to_vec(),
            predicate: predicate.clone(),
            access: access.clone(),
            args: args.to_vec(),
            arg_exps: arg_exps.map(|values| values.to_vec()),
            permission: permission.clone(),
            permission_exp: permission_exp.cloned(),
            error: error.clone(),
            tail: tail.clone(),
        };
        if let Some(result) = context.try_consume_owned_fold_body(&inner, body, &frame) {
            return result;
        }
    }
    context.consume_predicate_body(inner, body, error, &mut |context, mut state, snapshot| {
        let snapshot = snapshot.ok_or(PredicateExecutionError::MissingSnapshot)?;
        state.g = outer.g.clone();
        state.sm_domain_needed = outer.sm_domain_needed;
        state.permission_scaling_factor = outer.permission_scaling_factor.clone();
        state.permission_scaling_factor_exp = outer.permission_scaling_factor_exp.clone();
        state = state.set_constrainable(constrainable_wildcards.iter().cloned(), false);
        let folded = context
            .folded_predicate_snapshot(&state, predicate, args, &snapshot)
            .map_err(PredicateExecutionError::Service)?;
        context.produce_predicate_chunk(
            state,
            predicate,
            args,
            arg_exps,
            folded,
            permission.clone(),
            permission_exp.cloned(),
            error,
            &mut |context, state| {
                if context.predicate_unfold_triggers_enabled() {
                    context
                        .assume_unfold_trigger(
                            &state, predicate, &snapshot, &state.h, args, arg_exps,
                        )
                        .map_err(PredicateExecutionError::Service)?;
                }
                let state = context
                    .trigger_predicate_resource(state, access, args, arg_exps)
                    .map_err(PredicateExecutionError::Service)?;
                continuation(context, state)
            },
        )
    })
}
pub(crate) fn execute_owned_fold_body<
    P,
    D,
    J: Clone + PartialEq,
    V,
    C: PredicateExecutionServices<P, D, J, V>,
>(
    context: &mut C,
    mut state: State<P, D, J>,
    snapshot: Option<Term>,
    frame: &OwnedFoldBody<C::VerificationError>,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>> {
    let snapshot = snapshot.ok_or(PredicateExecutionError::MissingSnapshot)?;
    state.g = frame.outer_store.clone();
    state.sm_domain_needed = frame.outer_sm_domain_needed;
    state.permission_scaling_factor = frame.outer_scaling.clone();
    state.permission_scaling_factor_exp = frame.outer_scaling_exp.clone();
    state = state.set_constrainable(frame.wildcards.iter().cloned(), false);
    let folded = context
        .folded_predicate_snapshot(&state, &frame.predicate, &frame.args, &snapshot)
        .map_err(PredicateExecutionError::Service)?;
    context.produce_predicate_chunk(
        state,
        &frame.predicate,
        &frame.args,
        frame.arg_exps.as_deref(),
        folded,
        frame.permission.clone(),
        frame.permission_exp.clone(),
        &frame.error,
        &mut |context, state| {
            if context.predicate_unfold_triggers_enabled() {
                context
                    .assume_unfold_trigger(
                        &state,
                        &frame.predicate,
                        &snapshot,
                        &state.h,
                        &frame.args,
                        frame.arg_exps.as_deref(),
                    )
                    .map_err(PredicateExecutionError::Service)?;
            }
            let state = context
                .trigger_predicate_resource(
                    state,
                    &frame.access,
                    &frame.args,
                    frame.arg_exps.as_deref(),
                )
                .map_err(PredicateExecutionError::Service)?;
            context
                .finish_owned_fold(state, &frame.tail)
                .ok_or(PredicateExecutionError::OwnedSchedulerUnavailable)?
        },
    )
}

/// Unfold consumes the predicate before producing either cached contents or its body,
/// and restores the outer store and permission scaling after saturation and trigger emission.
pub fn unfold_predicate<
    P,
    D,
    J: Clone + PartialEq,
    V,
    C: PredicateExecutionServices<P, D, J, V>,
>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, J>,
    predicate: &Predicate,
    access: &Exp,
    args: &[Term],
    arg_exps: Option<&[Exp]>,
    permission: &Term,
    permission_exp: Option<&Exp>,
    constrainable_wildcards: &[Term],
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<
        VerificationResult<V>,
        PredicateExecutionError<C::Error>,
    >,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>> {
    unfold_predicate_with_owned_tail(
        factory,
        context,
        state,
        predicate,
        access,
        args,
        arg_exps,
        permission,
        permission_exp,
        constrainable_wildcards,
        error,
        None,
        continuation,
    )
}
pub fn unfold_predicate_with_owned_tail<
    P,
    D,
    J: Clone + PartialEq,
    V,
    C: PredicateExecutionServices<P, D, J, V>,
>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, J>,
    predicate: &Predicate,
    access: &Exp,
    args: &[Term],
    arg_exps: Option<&[Exp]>,
    permission: &Term,
    permission_exp: Option<&Exp>,
    constrainable_wildcards: &[Term],
    error: &C::VerificationError,
    owned_tail: Option<&crate::rules::executor::CfgStatementTail>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<
        VerificationResult<V>,
        PredicateExecutionError<C::Error>,
    >,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>> {
    let body = predicate
        .body
        .as_ref()
        .ok_or(PredicateExecutionError::AbstractPredicate)?;
    let bindings = bind_formals(
        &state,
        predicate,
        args,
        arg_exps,
        context.predicate_debugging(),
    )
    .map_err(binding_error)?;
    if state.permission_scaling_factor_exp.is_some() && permission_exp.is_none() {
        return Err(PredicateExecutionError::MissingDebugPermission);
    }
    let outer = state.clone();
    let inner = state.scale_permission_factor(permission.clone(), permission_exp.cloned(), factory);
    let pre_heap = inner.h.clone();
    context.consume_predicate_chunk(
        inner,
        access,
        args,
        arg_exps,
        permission,
        permission_exp,
        error,
        &mut |context, mut state, heap, snapshot| {
            let snapshot = snapshot.ok_or(PredicateExecutionError::MissingSnapshot)?;
            state.g = bindings.clone();
            state.h = heap;
            state = state.set_constrainable(constrainable_wildcards.iter().cloned(), false);
            let mut finish = |context: &mut C, mut state: State<P, D, J>| {
                context
                    .saturate_after_unfold()
                    .map_err(PredicateExecutionError::Service)?;
                if context.predicate_unfold_triggers_enabled() {
                    context
                        .assume_unfold_trigger(
                            &state, predicate, &snapshot, &pre_heap, args, arg_exps,
                        )
                        .map_err(PredicateExecutionError::Service)?;
                }
                state.g = outer.g.clone();
                state.permission_scaling_factor = outer.permission_scaling_factor.clone();
                state.permission_scaling_factor_exp = outer.permission_scaling_factor_exp.clone();
                continuation(context, state)
            };
            match context
                .cached_predicate_contents(&state, predicate)
                .map_err(PredicateExecutionError::Service)?
            {
                Some((tree, params)) => {
                    let replacements = params
                        .into_iter()
                        .zip(std::iter::once(snapshot.clone()).chain(args.iter().cloned()))
                        .collect();
                    if let Some(tail) = owned_tail {
                        let owned_finish = OwnedUnfoldFinish {
                            outer_store: outer.g.clone(),
                            outer_scaling: outer.permission_scaling_factor.clone(),
                            outer_scaling_exp: outer.permission_scaling_factor_exp.clone(),
                            predicate: predicate.clone(),
                            args: args.to_vec(),
                            arg_exps: arg_exps.map(|values| values.to_vec()),
                            snapshot: snapshot.clone(),
                            pre_heap: pre_heap.clone(),
                            tail: tail.clone(),
                        };
                        if let Some(result) = context.try_produce_owned_cached_predicate(
                            &state,
                            &tree,
                            &replacements,
                            &owned_finish,
                        ) {
                            return result;
                        }
                    }
                    context.produce_cached_predicate(
                        state,
                        &tree,
                        &replacements,
                        error,
                        &mut finish,
                    )
                }
                None => {
                    if let Some(tail) = owned_tail {
                        let owned_finish = OwnedUnfoldFinish {
                            outer_store: outer.g.clone(),
                            outer_scaling: outer.permission_scaling_factor.clone(),
                            outer_scaling_exp: outer.permission_scaling_factor_exp.clone(),
                            predicate: predicate.clone(),
                            args: args.to_vec(),
                            arg_exps: arg_exps.map(|values| values.to_vec()),
                            snapshot: snapshot.clone(),
                            pre_heap: pre_heap.clone(),
                            tail: tail.clone(),
                        };
                        if let Some(result) = context.try_produce_owned_unfolded_body(
                            &state,
                            body,
                            error,
                            &owned_finish,
                        ) {
                            return result;
                        }
                    }
                    context.produce_unfolded_body(
                        state,
                        predicate,
                        args,
                        &snapshot,
                        &pre_heap,
                        body,
                        error,
                        &mut finish,
                    )
                }
            }
        },
    )
}

pub trait PredicateTreeServices<P, D, V>:
    PredicateExecutionServices<P, D, crate::config::JoinMode, V>
{
    fn assume_predicate_contents(&mut self, assumptions: &[Term]) -> Result<(), Self::Error>;
    /// Convert an ordinary chunk to its singleton quantified representation if the
    /// state designates that resource as quantified, emitting and recording its map definition.
    fn quantify_predicate_leaf_chunk(
        &mut self,
        state: &State<P, D, crate::config::JoinMode>,
        recorder: crate::supporters::functions::function_recorder::FunctionRecorder<D>,
        chunk: crate::state::chunks::Chunk,
    ) -> Result<
        (
            crate::supporters::functions::function_recorder::FunctionRecorder<D>,
            crate::state::chunks::Chunk,
        ),
        Self::Error,
    >;
    fn merge_predicate_contents(
        &mut self,
        state: &State<P, D, crate::config::JoinMode>,
        recorder: crate::supporters::functions::function_recorder::FunctionRecorder<D>,
        heap: &ListBackedHeap,
    ) -> Result<
        (
            crate::supporters::functions::function_recorder::FunctionRecorder<D>,
            ListBackedHeap,
        ),
        Self::Error,
    >;
    fn try_branch_owned_predicate_evaluation(
        &mut self,
        _state: &State<P, D, crate::config::JoinMode>,
        _condition: &Term,
        _condition_exp: &(Exp, Option<Exp>),
        _yes: PredicateContentsAction,
        _no: PredicateContentsAction,
        _frame: &OwnedUnfoldEvaluation<P, D>,
    ) -> Option<Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>> {
        None
    }
    fn finish_owned_predicate_evaluation(
        &mut self,
        _state: State<P, D, crate::config::JoinMode>,
        _frame: &OwnedUnfoldEvaluation<P, D>,
    ) -> Option<Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>> {
        None
    }
    fn try_branch_owned_predicate_contents(
        &mut self,
        _state: &State<P, D, crate::config::JoinMode>,
        _condition: &Term,
        _condition_exp: &(Exp, Option<Exp>),
        _yes: PredicateContentsAction,
        _no: PredicateContentsAction,
        _finish: &OwnedUnfoldFinish,
    ) -> Option<Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>> {
        None
    }
    /// Branch subtrees call `done` at leaves; joining collects these states before
    /// invoking the outer continuation, preserving source continuation order.
    fn branch_predicate_contents(
        &mut self,
        state: State<P, D, crate::config::JoinMode>,
        condition: Term,
        condition_exp: &(Exp, Option<Exp>),
        join: bool,
        left: PredicateContentsAction,
        right: PredicateContentsAction,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, crate::config::JoinMode>,
        ) -> Result<
            VerificationResult<V>,
            PredicateExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, PredicateExecutionError<Self::Error>>;
}
/// Owned predicate subtree work for a branch; the caller supplies its leaf continuation.
#[derive(Clone)]
pub struct PredicateContentsAction {
    factory: TermFactory,
    tree: PredicateContentsTree,
    replacements: std::collections::HashMap<Term, Term>,
    is_unfolding: bool,
}
pub(crate) fn execute_predicate_contents_action<
    P,
    D: Clone,
    V,
    C: PredicateTreeServices<P, D, V>,
>(
    context: &mut C,
    state: State<P, D, crate::config::JoinMode>,
    action: &PredicateContentsAction,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, crate::config::JoinMode>,
    ) -> Result<
        VerificationResult<V>,
        PredicateExecutionError<C::Error>,
    >,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>> {
    produce_predicate_contents(
        &action.factory,
        context,
        state,
        &action.tree,
        &action.replacements,
        action.is_unfolding,
        continuation,
    )
}

pub(crate) fn execute_owned_predicate_contents_action<
    P,
    D: Clone,
    V,
    C: PredicateTreeServices<P, D, V>,
>(
    context: &mut C,
    state: State<P, D, crate::config::JoinMode>,
    action: &PredicateContentsAction,
    finish: &OwnedUnfoldFinish,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>> {
    produce_predicate_contents_with_owned_finish(
        &action.factory,
        context,
        state,
        &action.tree,
        &action.replacements,
        action.is_unfolding,
        Some(finish),
        None,
        &mut |context, state| {
            context
                .finish_owned_unfold(state, finish)
                .ok_or(PredicateExecutionError::OwnedSchedulerUnavailable)?
        },
    )
}

pub(crate) fn execute_owned_predicate_evaluation_action<
    P,
    D: Clone,
    V,
    C: PredicateTreeServices<P, D, V>,
>(
    context: &mut C,
    state: State<P, D, crate::config::JoinMode>,
    action: &PredicateContentsAction,
    frame: &OwnedUnfoldEvaluation<P, D>,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>> {
    produce_predicate_contents_with_owned_finish(
        &action.factory,
        context,
        state,
        &action.tree,
        &action.replacements,
        action.is_unfolding,
        None,
        Some(frame),
        &mut |context, state| {
            context
                .finish_owned_predicate_evaluation(state, frame)
                .ok_or(PredicateExecutionError::OwnedSchedulerUnavailable)?
        },
    )
}

/// Produce a cached predicate tree, substituting assumptions and chunks, scaling
/// each chunk's permission, converting quantified singleton resources and merging leaves.
pub fn produce_predicate_contents<P, D: Clone, V, C: PredicateTreeServices<P, D, V>>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, crate::config::JoinMode>,
    tree: &PredicateContentsTree,
    replacements: &std::collections::HashMap<Term, Term>,
    is_unfolding: bool,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, crate::config::JoinMode>,
    ) -> Result<
        VerificationResult<V>,
        PredicateExecutionError<C::Error>,
    >,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>> {
    produce_predicate_contents_with_owned_finish(
        factory,
        context,
        state,
        tree,
        replacements,
        is_unfolding,
        None,
        None,
        continuation,
    )
}
pub fn produce_predicate_contents_with_owned_finish<
    P,
    D: Clone,
    V,
    C: PredicateTreeServices<P, D, V>,
>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, crate::config::JoinMode>,
    tree: &PredicateContentsTree,
    replacements: &std::collections::HashMap<Term, Term>,
    is_unfolding: bool,
    owned_finish: Option<&OwnedUnfoldFinish>,
    owned_evaluation: Option<&OwnedUnfoldEvaluation<P, D>>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, crate::config::JoinMode>,
    ) -> Result<
        VerificationResult<V>,
        PredicateExecutionError<C::Error>,
    >,
) -> Result<VerificationResult<V>, PredicateExecutionError<C::Error>> {
    use crate::interfaces::state::chunks::{Chunk as ChunkContract, GeneralChunk};
    use crate::state::chunks::Chunk;
    use crate::state::heap::Heap;
    match tree {
        PredicateContentsTree::Leaf { heap, assumptions } => {
            let assumptions = assumptions
                .iter()
                .map(|term| {
                    factory
                        .replace(term, replacements)
                        .map_err(PredicateExecutionError::Transform)
                })
                .collect::<Result<Vec<_>, _>>()?;
            context
                .assume_predicate_contents(&assumptions)
                .map_err(PredicateExecutionError::Service)?;
            let mut recorder = state.function_recorder.clone();
            let mut chunks = Vec::new();
            for chunk in heap.values() {
                let chunk = chunk
                    .substitute(factory, replacements)
                    .map_err(PredicateExecutionError::Chunk)?;
                let permission = state.permission_scaling_factor.clone();
                let exp = state.permission_scaling_factor_exp.clone();
                let chunk = match chunk {
                    Chunk::Basic(c) => Chunk::Basic(c.perm_scale(factory, permission, exp)),
                    Chunk::MagicWand(c) => Chunk::MagicWand(c.perm_scale(factory, permission, exp)),
                    Chunk::QuantifiedField(c) => {
                        Chunk::QuantifiedField(c.perm_scale(factory, permission, exp))
                    }
                    Chunk::QuantifiedPredicate(c) => {
                        Chunk::QuantifiedPredicate(c.perm_scale(factory, permission, exp))
                    }
                    Chunk::QuantifiedMagicWand(c) => {
                        Chunk::QuantifiedMagicWand(c.perm_scale(factory, permission, exp))
                    }
                    Chunk::MaskHeap(_) => {
                        return Err(PredicateExecutionError::UnsupportedMaskChunk);
                    }
                };
                let (new_recorder, chunk) = context
                    .quantify_predicate_leaf_chunk(&state, recorder, chunk)
                    .map_err(PredicateExecutionError::Service)?;
                recorder = new_recorder;
                chunks.push(chunk);
            }
            let heap = ListBackedHeap::from_chunks(chunks);
            let (recorder, heap) = context
                .merge_predicate_contents(&state, recorder, &heap)
                .map_err(PredicateExecutionError::Service)?;
            let mut state = state;
            state.h = Arc::new(heap);
            state.function_recorder = recorder;
            continuation(context, state)
        }
        PredicateContentsTree::Branch {
            condition,
            condition_exp,
            left,
            right,
        } => {
            let condition = factory
                .replace(condition, replacements)
                .map_err(PredicateExecutionError::Transform)?;
            let join = !is_unfolding && state.more_joins != crate::config::JoinMode::Off;
            if !join {
                if let Some(frame) = owned_evaluation {
                    let yes = PredicateContentsAction {
                        factory: factory.clone(),
                        tree: (**left).clone(),
                        replacements: replacements.clone(),
                        is_unfolding,
                    };
                    let no = PredicateContentsAction {
                        factory: factory.clone(),
                        tree: (**right).clone(),
                        replacements: replacements.clone(),
                        is_unfolding,
                    };
                    if let Some(result) = context.try_branch_owned_predicate_evaluation(
                        &state,
                        &condition,
                        condition_exp,
                        yes,
                        no,
                        frame,
                    ) {
                        return result;
                    }
                }
                if let Some(finish) = owned_finish {
                    let yes = PredicateContentsAction {
                        factory: factory.clone(),
                        tree: (**left).clone(),
                        replacements: replacements.clone(),
                        is_unfolding,
                    };
                    let no = PredicateContentsAction {
                        factory: factory.clone(),
                        tree: (**right).clone(),
                        replacements: replacements.clone(),
                        is_unfolding,
                    };
                    if let Some(result) = context.try_branch_owned_predicate_contents(
                        &state,
                        &condition,
                        condition_exp,
                        yes,
                        no,
                        finish,
                    ) {
                        return result;
                    }
                }
            }
            context.branch_predicate_contents(
                state,
                condition,
                condition_exp,
                join,
                PredicateContentsAction {
                    factory: factory.clone(),
                    tree: (**left).clone(),
                    replacements: replacements.clone(),
                    is_unfolding,
                },
                PredicateContentsAction {
                    factory: factory.clone(),
                    tree: (**right).clone(),
                    replacements: replacements.clone(),
                    is_unfolding,
                },
                continuation,
            )
        }
    }
}

pub trait PredicateLeafQuantification<P, D, J>:
    crate::rules::quantified_chunk_support::SnapshotMapFreshener<P, D, J>
{
    fn predicate_leaf_debugging(&self) -> bool;
    fn formal_resource_variables(
        &mut self,
        state: &State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
    ) -> Result<Vec<Term>, Self::Error>;
    fn assume_leaf_snapshot_definition(&mut self, definition: &Term) -> Result<(), Self::Error>;
}
#[derive(Debug)]
pub enum PredicateLeafQuantificationError<E> {
    MissingResource,
    Map(crate::rules::quantified_chunk_support::SingletonMapError<E>),
    Chunk(crate::rules::quantified_chunk_support::SingletonChunkError),
    Service(E),
}
/// Convert ordinary cached chunks of quantified resources to singleton quantified
/// chunks, defining and recording the fresh snapshot map; all other chunks pass through.
pub fn quantify_predicate_leaf_chunk<
    P,
    D: Clone,
    J: Clone + PartialEq,
    C: PredicateLeafQuantification<P, D, J>,
>(
    factory: &TermFactory,
    context: &mut C,
    state: &State<P, D, J>,
    recorder: crate::supporters::functions::function_recorder::FunctionRecorder<D>,
    chunk: crate::state::chunks::Chunk,
) -> Result<
    (
        crate::supporters::functions::function_recorder::FunctionRecorder<D>,
        crate::state::chunks::Chunk,
    ),
    PredicateLeafQuantificationError<C::Error>,
> {
    use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk};
    use crate::resources::resources::ResourceId;
    use crate::rules::quantified_chunk_support::{
        SnapshotMapDefinition, SnapshotResource, singleton_quantified_chunk, singleton_snapshot_map,
    };
    use crate::state::chunks::Chunk;
    use crate::state::terms::ResourceKey;
    let (resource, source_resource, args, snapshot, permission, tag) = match &chunk {
        Chunk::Basic(c) => {
            let quantified = state.qp_fields.iter().any(|f| f.name == c.id_ref().0)
                || state.qp_predicates.iter().any(|p| p.name == c.id_ref().0);
            if !quantified {
                return Ok((recorder, chunk));
            }
            let (resource, source) = match c.resource_id() {
                ResourceId::Field => {
                    let field = state
                        .program
                        .find_field_optionally(&c.id_ref().0)
                        .cloned()
                        .ok_or(PredicateLeafQuantificationError::MissingResource)?;
                    let field = Arc::new(field);
                    (
                        ResourceKey::Field(field.clone()),
                        SnapshotResource::Field(field),
                    )
                }
                ResourceId::Predicate => {
                    let predicate = state
                        .program
                        .find_predicate_optionally(&c.id_ref().0)
                        .cloned()
                        .ok_or(PredicateLeafQuantificationError::MissingResource)?;
                    let predicate = Arc::new(predicate);
                    (
                        ResourceKey::Predicate(predicate.clone()),
                        SnapshotResource::Predicate(predicate),
                    )
                }
                _ => return Err(PredicateLeafQuantificationError::MissingResource),
            };
            (
                resource,
                source,
                c.args().to_vec(),
                c.snapshot().clone(),
                c.permission(factory),
                c.tag(),
            )
        }
        Chunk::MagicWand(c) => {
            if !state.qp_magic_wands.contains(c.id_ref()) {
                return Ok((recorder, chunk));
            }
            (
                ResourceKey::Wand(c.id_ref().clone()),
                SnapshotResource::Wand(c.id_ref().ghost_free_wand.clone()),
                c.args().to_vec(),
                c.snapshot().clone(),
                c.permission(factory),
                c.tag(),
            )
        }
        _ => return Ok((recorder, chunk)),
    };
    let (map, definition) =
        singleton_snapshot_map(factory, context, state, &resource, &args, snapshot)
            .map_err(PredicateLeafQuantificationError::Map)?;
    context
        .assume_leaf_snapshot_definition(&definition)
        .map_err(PredicateLeafQuantificationError::Service)?;
    let formal = context
        .formal_resource_variables(state, &resource)
        .map_err(PredicateLeafQuantificationError::Service)?;
    let map_definition = SnapshotMapDefinition {
        resource: source_resource,
        snapshot_map: map.clone(),
        value_definitions: vec![definition],
        domain_definitions: vec![],
    };
    let new_chunk = singleton_quantified_chunk(
        factory, &resource, formal, None, args, None, permission, None, map, tag, false,
    )
    .map_err(PredicateLeafQuantificationError::Chunk)?;
    Ok((recorder.record_fvf_and_domain(map_definition), new_chunk))
}

#[cfg(test)]
mod owned_predicate_action_tests {
    #[test]
    fn predicate_contents_action_is_send() {
        fn require_send<T: Send>() {}
        require_send::<super::PredicateContentsAction>();
    }
}
