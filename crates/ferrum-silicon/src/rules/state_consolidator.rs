//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/StateConsolidator.scala
//!
//! Purpose:
//! Merge heap chunks and derive permission and snapshot facts.
//!
//! Planned Rust structure:
//! StateConsolidationRules plus MinimalStateConsolidator, DefaultStateConsolidator,
//! RetryingStateConsolidator, RetryingFailOnlyStateConsolidator, LastRetryStateConsolidator,
//! LastRetryFailOnlyStateConsolidator, MinimalRetryingStateConsolidator,
//! MoreComplexExhaleStateConsolidator and MaskHeapStateConsolidator. Default implements
//! singleMerge, alias matching, chunk merging, combineSnapshots and quantified field bounds.
//!
//! Behavior to preserve:
//! Default saturates then repeatedly merges each main/reserve heap until no snapshot equalities
//! arise, assuming instance and delayed resource properties. During wand packaging retain only
//! first three newly consolidated reserve heaps; later outer heaps remain original. Basic aliases
//! combine permission and guard snapshot equalities; uncertain positivity creates fresh constrained
//! snapshot. Quantified merge behavior depends on exhaleModeQP: more-complete combines only
//! matching field/predicate maps; all other modes summarise, retaining both inverse-function lists
//! and singleton only for identical tuples. Bounds use field triggers or inverse-function/pointwise
//! singleton triggers; no untriggered bound for chunks without either. Retry and last-retry variants
//! control when consolidation runs; fail-only variants suppress optional consolidation. Minimal
//! retrying keeps simple merge and no quantified bounds. MoreComplexExhaleStateConsolidator only
//! assumes nonquantified field bounds on the main heap when retrying, without consolidating it.
//! MaskHeapStateConsolidator delegates heap merge to mask heap rules; its single-chunk merge is
//! upstream unimplemented.
//!
//! Integration:
//! rules::chunk_supporter, quantified_chunk_support, more_complete_exhale_supporter,
//! mask_heap_supporter, resources and state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Heap and snapshot equality, quantifier identity and consolidator selection.
//!
//! Status: partial; ordinary snapshot merging, fixed-point heap consolidation and strategy
//! dispatch and quantified pair merge implemented. Property/bound and concrete solver services remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk};
use crate::state::chunks::Chunk;
use crate::state::heap::{Heap, ListBackedHeap};
use crate::state::state::State;
use crate::state::terms::{ApplicationTarget, Sort, Term, TermFactory, TermKind};
use crate::supporters::functions::function_recorder::FunctionRecorder;
use crate::verifier::base_verifier::ConsolidatorChoice;
use std::sync::Arc;

pub trait ConsolidationServices<P, D, J> {
    type Error;
    fn open_consolidation_comment(
        &mut self,
        _comment: &str,
        _state: Option<&State<P, D, J>>,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn open_single_merge_scope(
        &mut self,
        _destination: &[Chunk],
        _incoming: &[Chunk],
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn close_consolidation_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        Ok(())
    }
    /// Match only source-compatible chunk kinds using the configured alias algorithm.
    fn find_merge_candidate(
        &mut self,
        state: &State<P, D, J>,
        chunks: &[Chunk],
        incoming: &Chunk,
    ) -> Result<Option<usize>, Self::Error>;
    /// Quantified merging uses the selected exhale mode and emits snapshot-map definitions.
    fn merge_quantified_chunks(
        &mut self,
        state: &State<P, D, J>,
        recorder: FunctionRecorder<D>,
        first: &Chunk,
        second: &Chunk,
        qvars: &[Term],
    ) -> Result<Option<(FunctionRecorder<D>, Chunk, Vec<Term>)>, Self::Error>;
    fn fresh_merged_snapshot(
        &mut self,
        sort: &Sort,
        qvars: &[Term],
    ) -> Result<(Term, ApplicationTarget), Self::Error>;
    fn assume_merge_equations(
        &mut self,
        equations: &[Term],
        definitions: bool,
        label: &str,
    ) -> Result<(), Self::Error>;
    fn assume_chunk_properties(
        &mut self,
        state: &State<P, D, J>,
        heap: &ListBackedHeap,
        chunk: &Chunk,
    ) -> Result<(), Self::Error>;
    fn assume_delayed_properties(
        &mut self,
        state: &State<P, D, J>,
        heap: &ListBackedHeap,
    ) -> Result<(), Self::Error>;
    fn saturate_before_consolidation(&mut self) -> Result<(), Self::Error>;
    fn assume_quantified_field_bounds(
        &mut self,
        state: State<P, D, J>,
        heaps: &[Arc<ListBackedHeap>],
    ) -> Result<State<P, D, J>, Self::Error>;
    fn assume_more_complete_field_bounds(
        &mut self,
        state: &State<P, D, J>,
    ) -> Result<(), Self::Error>;
    fn merge_mask_heaps(
        &mut self,
        state: &State<P, D, J>,
        first: &ListBackedHeap,
        second: &ListBackedHeap,
    ) -> Result<ListBackedHeap, Self::Error>;
    fn consolidation_debugging(&self) -> bool;
    fn begin_consolidation_record(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn finish_consolidation_record(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
}
#[derive(Debug)]
pub enum ConsolidationError<E> {
    Service(E),
    InvalidCandidate,
    MissingDebugPermission,
    UnsupportedMaskSingleChunk,
}
/// Combine same-location ordinary snapshots without constraining a possibly empty chunk.
pub fn combine_snapshots<D: Clone, P, J, C: ConsolidationServices<P, D, J>>(
    factory: &TermFactory,
    context: &mut C,
    recorder: FunctionRecorder<D>,
    first: Term,
    second: Term,
    first_permission: Term,
    second_permission: Term,
    qvars: &[Term],
) -> Result<(FunctionRecorder<D>, Term, Term), ConsolidationError<C::Error>> {
    let positive1 = factory.is_positive_perm(first_permission);
    let positive2 = factory.is_positive_perm(second_permission);
    if matches!(positive1.kind(), TermKind::True) {
        let equation = factory.implies(positive2, factory.equals(first.clone(), second));
        return Ok((recorder, first, equation));
    }
    if matches!(positive2.kind(), TermKind::True) {
        let equation = factory.implies(positive1, factory.equals(second.clone(), first));
        return Ok((recorder, second, equation));
    }
    let (fresh, symbol) = context
        .fresh_merged_snapshot(first.sort(), qvars)
        .map_err(ConsolidationError::Service)?;
    let equation = factory.and([
        factory.implies(positive1, factory.equals(fresh.clone(), first)),
        factory.implies(positive2, factory.equals(fresh.clone(), second)),
    ]);
    Ok((
        recorder
            .record_path_symbol(symbol)
            .record_constraint(equation.clone()),
        fresh,
        equation,
    ))
}
/// One source merge round prepends new/merged chunks and removes every chunk equal
/// to a selected alias; snapshot equations retain insertion order and deduplicate.
pub fn single_merge<P, D: Clone, J, C: ConsolidationServices<P, D, J>>(
    factory: &TermFactory,
    context: &mut C,
    state: &State<P, D, J>,
    mut recorder: FunctionRecorder<D>,
    destination: &[Chunk],
    incoming: &[Chunk],
    qvars: &[Term],
) -> Result<
    (
        FunctionRecorder<D>,
        Vec<Chunk>,
        Vec<Chunk>,
        InsertionOrderedSet<Term>,
    ),
    ConsolidationError<C::Error>,
> {
    let scope = context
        .open_single_merge_scope(destination, incoming)
        .map_err(ConsolidationError::Service)?;
    let mut merged = destination.to_vec();
    let mut added = Vec::new();
    let mut equations = InsertionOrderedSet::new();
    for next in incoming {
        let match_index = context
            .find_merge_candidate(state, &merged, next)
            .map_err(ConsolidationError::Service)?;
        let combined = if let Some(index) = match_index {
            let existing = merged
                .get(index)
                .ok_or(ConsolidationError::InvalidCandidate)?;
            match (existing, next) {
                (Chunk::Basic(a), Chunk::Basic(b)) => {
                    if a.permission_exp().is_some() && b.permission_exp().is_none() {
                        return Err(ConsolidationError::MissingDebugPermission);
                    }
                    let (new_recorder, snapshot, equation) = combine_snapshots(
                        factory,
                        context,
                        recorder.clone(),
                        a.snapshot().clone(),
                        b.snapshot().clone(),
                        a.permission(factory),
                        b.permission(factory),
                        qvars,
                    )?;
                    let combined = a
                        .perm_plus(factory, b.permission(factory), b.permission_exp())
                        .with_snapshot(snapshot, a.snap_exp_ref().clone());
                    Some((new_recorder, Chunk::Basic(combined), vec![equation]))
                }
                _ => context
                    .merge_quantified_chunks(state, recorder.clone(), existing, next, qvars)
                    .map_err(ConsolidationError::Service)?,
            }
        } else {
            None
        };
        if let Some((new_recorder, chunk, new_equations)) = combined {
            let existing = merged[match_index.expect("combined implies candidate")].clone();
            merged.retain(|chunk| chunk != &existing);
            merged.insert(0, chunk.clone());
            added.insert(0, chunk);
            recorder = new_recorder;
            for term in new_equations {
                equations = equations.incl(term);
            }
        } else {
            merged.insert(0, next.clone());
            added.insert(0, next.clone());
        }
    }
    context
        .close_consolidation_scope(scope)
        .map_err(ConsolidationError::Service)?;
    Ok((recorder, merged, added, equations))
}
/// Merge one heap into another, emitting snapshot equalities before chunk properties.
pub fn merge_heaps<P, D: Clone, J, C: ConsolidationServices<P, D, J>>(
    factory: &TermFactory,
    context: &mut C,
    state: &State<P, D, J>,
    recorder: FunctionRecorder<D>,
    first: &ListBackedHeap,
    second: &ListBackedHeap,
    choice: ConsolidatorChoice,
) -> Result<(FunctionRecorder<D>, ListBackedHeap), ConsolidationError<C::Error>> {
    if matches!(
        choice,
        ConsolidatorChoice::Minimal | ConsolidatorChoice::MinimalRetrying
    ) {
        return Ok((recorder, first.with_heap(second)));
    }
    if choice == ConsolidatorChoice::Mask {
        return Ok((
            recorder,
            context
                .merge_mask_heaps(state, first, second)
                .map_err(ConsolidationError::Service)?,
        ));
    }
    let scope = context
        .open_consolidation_comment("Merge", None)
        .map_err(ConsolidationError::Service)?;
    let mut qvars: Vec<_> = state
        .function_recorder
        .arguments()
        .unwrap_or_default()
        .into_iter()
        .map(|(t, _)| t)
        .collect();
    qvars.extend(
        state
            .packaging_wand_snapshots
            .iter()
            .map(|(t, _)| t.clone()),
    );
    let (recorder, chunks, added, equations) = single_merge(
        factory,
        context,
        state,
        recorder,
        first.values(),
        second.values(),
        &qvars,
    )?;
    context
        .assume_merge_equations(
            &equations.iter().cloned().collect::<Vec<_>>(),
            false,
            "Snapshot",
        )
        .map_err(ConsolidationError::Service)?;
    let heap = ListBackedHeap::from_chunks(chunks);
    for chunk in added.iter().filter(|c| matches!(c, Chunk::Basic(_))) {
        context
            .assume_chunk_properties(state, &heap, chunk)
            .map_err(ConsolidationError::Service)?;
    }
    context
        .close_consolidation_scope(scope)
        .map_err(ConsolidationError::Service)?;
    Ok((recorder, heap))
}
/// Source consolidation strategy dispatch and fixed-point merging of the main and reserve heaps.
pub fn consolidate<P, D: Clone, J: Clone + PartialEq, C: ConsolidationServices<P, D, J>>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, J>,
    choice: ConsolidatorChoice,
    optional: bool,
) -> Result<State<P, D, J>, ConsolidationError<C::Error>> {
    let enabled = match choice {
        ConsolidatorChoice::Minimal | ConsolidatorChoice::Mask => false,
        ConsolidatorChoice::Default => !optional || state.retrying,
        ConsolidatorChoice::Retrying | ConsolidatorChoice::MinimalRetrying => state.retrying,
        ConsolidatorChoice::RetryingFailOnly => !optional && state.retrying,
        ConsolidatorChoice::LastRetry => state.is_last_retry(),
        ConsolidatorChoice::LastRetryFailOnly => !optional && state.is_last_retry(),
        ConsolidatorChoice::MoreCompleteExhale => {
            if state.retrying {
                context
                    .assume_more_complete_field_bounds(&state)
                    .map_err(ConsolidationError::Service)?;
            }
            false
        }
    };
    if !enabled {
        return Ok(state);
    }
    let scope = context
        .open_consolidation_comment("state consolidation", Some(&state))
        .map_err(ConsolidationError::Service)?;
    context
        .saturate_before_consolidation()
        .map_err(ConsolidationError::Service)?;
    let mut heaps = vec![state.h.clone()];
    heaps.extend(state.reserve_heaps.iter().cloned());
    let mut recorder = state.function_recorder.clone();
    let mut merged_heaps = Vec::new();
    let mut qvars: Vec<_> = state
        .function_recorder
        .arguments()
        .unwrap_or_default()
        .into_iter()
        .map(|(t, _)| t)
        .collect();
    qvars.extend(
        state
            .packaging_wand_snapshots
            .iter()
            .map(|(t, _)| t.clone()),
    );
    for heap in heaps {
        let mut current = heap.values().to_vec();
        let mut round = 0;
        loop {
            let round_scope = context
                .open_consolidation_comment(&format!("Round {round}"), Some(&state))
                .map_err(ConsolidationError::Service)?;
            let (next_recorder, chunks, _, equations) =
                single_merge(factory, context, &state, recorder, &[], &current, &qvars)?;
            let changed = !equations.is_empty();
            context
                .assume_merge_equations(
                    &equations.iter().cloned().collect::<Vec<_>>(),
                    false,
                    "Snapshot Equations",
                )
                .map_err(ConsolidationError::Service)?;
            recorder = next_recorder;
            current = chunks;
            context
                .close_consolidation_scope(round_scope)
                .map_err(ConsolidationError::Service)?;
            round += 1;
            if !changed {
                break;
            }
        }
        let heap = ListBackedHeap::from_chunks(current);
        for chunk in heap
            .values()
            .iter()
            .filter(|c| matches!(c, Chunk::Basic(_)))
        {
            context
                .assume_chunk_properties(&state, &heap, chunk)
                .map_err(ConsolidationError::Service)?;
        }
        context
            .assume_delayed_properties(&state, &heap)
            .map_err(ConsolidationError::Service)?;
        context
            .close_consolidation_scope(scope)
            .map_err(ConsolidationError::Service)?;
        merged_heaps.push(Arc::new(heap));
    }
    let record = context.consolidation_debugging() && !state.is_recording_heaps();
    let mut next = if record {
        context
            .begin_consolidation_record(state.clone())
            .map_err(ConsolidationError::Service)?
    } else {
        state.clone()
    };
    next.function_recorder = recorder;
    next.h = merged_heaps[0].clone();
    next.reserve_heaps = if state.exhale_ext {
        merged_heaps
            .iter()
            .skip(1)
            .take(3)
            .cloned()
            .chain(state.reserve_heaps.iter().skip(3).cloned())
            .collect()
    } else {
        merged_heaps.iter().skip(1).cloned().collect()
    };
    if choice != ConsolidatorChoice::MinimalRetrying {
        next = context
            .assume_quantified_field_bounds(next, &merged_heaps)
            .map_err(ConsolidationError::Service)?;
    }
    if record {
        next = context
            .finish_consolidation_record(next)
            .map_err(ConsolidationError::Service)?;
    }
    Ok(next)
}

pub trait QuantifiedMergeServices<P, D, J>:
    ConsolidationServices<P, D, J>
    + crate::rules::quantified_chunk_support::SnapshotCombinationFreshener<
        Error = <Self as ConsolidationServices<P, D, J>>::Error,
    >
{
    fn complete_quantified_exhale(&self) -> bool;
    fn replace_quantified_debug(
        &mut self,
        expression: &ferrum_silver::ast::expression::Exp,
        from: &[ferrum_silver::ast::program::LocalVarDecl],
        to: &[ferrum_silver::ast::program::LocalVarDecl],
    ) -> Result<ferrum_silver::ast::expression::Exp, <Self as ConsolidationServices<P, D, J>>::Error>;
    fn summarise_quantified_pair(
        &mut self,
        state: &State<P, D, J>,
        first: &Chunk,
        second: &Chunk,
    ) -> Result<
        (
            crate::rules::quantified_chunk_support::SnapshotMapDefinition,
            Vec<Term>,
        ),
        <Self as ConsolidationServices<P, D, J>>::Error,
    >;
}
#[derive(Debug)]
pub enum QuantifiedMergeError<E> {
    MissingDebugExpression,
    MissingResource,
    Transform(crate::state::terms::UnsupportedTriggerTransform),
    Combination(crate::rules::quantified_chunk_support::SnapshotCombinationError<E>),
    Service(E),
}
/// Combine a matched quantified pair using the source complete-mode fast path or
/// greedy summary path. Magic-wand chunks do not merge in complete mode.
pub fn merge_quantified_pair<P, D: Clone, J, C: QuantifiedMergeServices<P, D, J>>(
    factory: &TermFactory,
    context: &mut C,
    state: &State<P, D, J>,
    recorder: FunctionRecorder<D>,
    first: &Chunk,
    second: &Chunk,
    qvars: &[Term],
) -> Result<
    Option<(FunctionRecorder<D>, Chunk, Vec<Term>)>,
    QuantifiedMergeError<<C as ConsolidationServices<P, D, J>>::Error>,
> {
    use crate::interfaces::state::chunks::QuantifiedChunk;
    use crate::rules::quantified_chunk_support::combine_snapshot_maps;
    use crate::state::chunks::{
        QuantifiedFieldChunk, QuantifiedMagicWandChunk, QuantifiedPredicateChunk,
    };
    use crate::state::terms::ResourceKey;
    use ferrum_silver::ast::expression::{Exp, ExpKind};
    use std::collections::HashMap;
    let sum_exp = |a: &Option<Exp>,
                   b: &Option<Exp>|
     -> Result<
        Option<Exp>,
        QuantifiedMergeError<<C as ConsolidationServices<P, D, J>>::Error>,
    > {
        match a {
            None => Ok(None),
            Some(a) => Ok(Some(Exp::new(
                ExpKind::PermAdd(
                    a.clone(),
                    b.clone()
                        .ok_or(QuantifiedMergeError::MissingDebugExpression)?,
                ),
                Default::default(),
            ))),
        }
    };
    if context.complete_quantified_exhale() {
        match (first, second) {
            (Chunk::QuantifiedField(a), Chunk::QuantifiedField(b)) => {
                let field = state
                    .program
                    .find_field_optionally(&a.id_ref().0)
                    .ok_or(QuantifiedMergeError::MissingResource)?;
                let resource = ResourceKey::Field(Arc::new(field.clone()));
                let vars = a.quantified_vars(factory);
                let (recorder, map, equation) = combine_snapshot_maps(
                    factory,
                    context,
                    recorder,
                    &resource,
                    &vars,
                    qvars,
                    a.fvf_ref().clone(),
                    b.fvf_ref().clone(),
                    a.permission(factory),
                    b.permission(factory),
                )
                .map_err(QuantifiedMergeError::Combination)?;
                let hints = if a.hints_ref().is_empty() {
                    b.hints_ref().clone()
                } else {
                    a.hints_ref().clone()
                };
                let chunk = QuantifiedFieldChunk::new(
                    factory,
                    a.id_ref().clone(),
                    map,
                    a.org_condition_ref().clone(),
                    a.condition_ref().clone(),
                    a.condition_exp_ref().clone(),
                    factory.perm_plus(a.perm_value_ref().clone(), b.perm_value_ref().clone()),
                    sum_exp(a.perm_value_exp_ref(), b.perm_value_exp_ref())?,
                    a.invs_ref().clone(),
                    a.singleton_rcvr_ref().clone(),
                    a.singleton_rcvr_exp_ref().clone(),
                    *a.tag_ref(),
                    hints,
                    *a.debugging_ref(),
                );
                return Ok(Some((
                    recorder,
                    Chunk::QuantifiedField(chunk),
                    vec![equation],
                )));
            }
            (Chunk::QuantifiedPredicate(a), Chunk::QuantifiedPredicate(b)) => {
                let predicate = state
                    .program
                    .find_predicate_optionally(&a.id_ref().0)
                    .ok_or(QuantifiedMergeError::MissingResource)?;
                let resource = ResourceKey::Predicate(Arc::new(predicate.clone()));
                let substitutions: HashMap<_, _> = a
                    .quantified_vars_ref()
                    .iter()
                    .cloned()
                    .zip(b.quantified_vars_ref().iter().cloned())
                    .collect();
                let first_permission = factory
                    .replace(&a.permission(factory), &substitutions)
                    .map_err(QuantifiedMergeError::Transform)?;
                let first_value = factory
                    .replace(a.perm_value_ref(), &substitutions)
                    .map_err(QuantifiedMergeError::Transform)?;
                let (recorder, map, equation) = combine_snapshot_maps(
                    factory,
                    context,
                    recorder,
                    &resource,
                    b.quantified_vars_ref(),
                    qvars,
                    a.psf_ref().clone(),
                    b.psf_ref().clone(),
                    first_permission,
                    b.permission(factory),
                )
                .map_err(QuantifiedMergeError::Combination)?;
                let first_exp = match a.perm_value_exp_ref() {
                    Some(exp) => Some(
                        context
                            .replace_quantified_debug(
                                exp,
                                a.quantified_var_exps_ref()
                                    .as_deref()
                                    .ok_or(QuantifiedMergeError::MissingDebugExpression)?,
                                b.quantified_var_exps_ref()
                                    .as_deref()
                                    .ok_or(QuantifiedMergeError::MissingDebugExpression)?,
                            )
                            .map_err(QuantifiedMergeError::Service)?,
                    ),
                    None => None,
                };
                let chunk = QuantifiedPredicateChunk::new(
                    factory,
                    a.id_ref().clone(),
                    b.quantified_vars_ref().clone(),
                    b.quantified_var_exps_ref().clone(),
                    map,
                    b.org_condition_ref().clone(),
                    b.condition_ref().clone(),
                    b.condition_exp_ref().clone(),
                    factory.perm_plus(first_value, b.perm_value_ref().clone()),
                    sum_exp(&first_exp, b.perm_value_exp_ref())?,
                    b.invs_ref().clone(),
                    b.singleton_args_ref().clone(),
                    b.singleton_arg_exps_ref().clone(),
                    *b.tag_ref(),
                    b.hints_ref().clone(),
                );
                return Ok(Some((
                    recorder,
                    Chunk::QuantifiedPredicate(chunk),
                    vec![equation],
                )));
            }
            _ => return Ok(None),
        }
    }
    let info = |chunk: &Chunk| match chunk {
        Chunk::QuantifiedField(c) => Some((
            c.quantified_vars(factory),
            c.quantified_var_exps(),
            c.permission(factory),
            c.permission_exp(),
            c.invs_ref().clone(),
            c.singleton_rcvr_ref().clone().map(|x| vec![x]),
            c.singleton_rcvr_exp_ref().clone().map(|x| vec![x]),
            c.hints_ref().clone(),
        )),
        Chunk::QuantifiedPredicate(c) => Some((
            c.quantified_vars(factory),
            c.quantified_var_exps(),
            c.permission(factory),
            c.permission_exp(),
            c.invs_ref().clone(),
            c.singleton_args_ref().clone(),
            c.singleton_arg_exps_ref().clone(),
            c.hints_ref().clone(),
        )),
        Chunk::QuantifiedMagicWand(c) => Some((
            c.quantified_vars(factory),
            c.quantified_var_exps(),
            c.permission(factory),
            c.permission_exp(),
            c.invs_ref().clone(),
            c.singleton_args_ref().clone(),
            c.singleton_arg_exps_ref().clone(),
            c.hints_ref().clone(),
        )),
        _ => None,
    };
    let Some((
        vars,
        vars_exp,
        permission,
        permission_exp,
        mut inverses,
        singleton,
        singleton_exp,
        mut hints,
    )) = info(first)
    else {
        return Ok(None);
    };
    let Some((
        other_vars,
        other_var_exps,
        other_permission,
        other_exp,
        other_inverses,
        other_singleton,
        other_singleton_exp,
        other_hints,
    )) = info(second)
    else {
        return Ok(None);
    };
    let substitutions: HashMap<_, _> = other_vars.into_iter().zip(vars.iter().cloned()).collect();
    let other_permission = factory
        .replace(&other_permission, &substitutions)
        .map_err(QuantifiedMergeError::Transform)?;
    let other_exp = match other_exp {
        Some(exp) => Some(
            context
                .replace_quantified_debug(
                    &exp,
                    other_var_exps
                        .as_deref()
                        .ok_or(QuantifiedMergeError::MissingDebugExpression)?,
                    vars_exp
                        .as_deref()
                        .ok_or(QuantifiedMergeError::MissingDebugExpression)?,
                )
                .map_err(QuantifiedMergeError::Service)?,
        ),
        None => None,
    };
    let permission = factory.perm_plus(permission, other_permission);
    let permission_exp = sum_exp(&permission_exp, &other_exp)?;
    let condition_exp = permission_exp
        .as_ref()
        .map(|_| Exp::new(ExpKind::TrueLit, Default::default()));
    inverses.extend(other_inverses);
    hints.extend(other_hints);
    let singleton = singleton.filter(|s| other_singleton.as_ref() == Some(s));
    let singleton_exp = if singleton.is_some() && other_singleton_exp.is_some() {
        singleton_exp
    } else {
        None
    };
    let (definition, equations) = context
        .summarise_quantified_pair(state, first, second)
        .map_err(QuantifiedMergeError::Service)?;
    // The upstream greedy case deliberately starts from the state's recorder.
    let recorder = state
        .function_recorder
        .record_fvf_and_domain(definition.clone());
    let chunk = match first {
        Chunk::QuantifiedField(a) => Chunk::QuantifiedField(QuantifiedFieldChunk::new(
            factory,
            a.id_ref().clone(),
            definition.snapshot_map,
            a.org_condition_ref().clone(),
            factory.boolean(true),
            condition_exp,
            permission,
            permission_exp,
            inverses,
            singleton.map(|v| v[0].clone()),
            singleton_exp.map(|v| v[0].clone()),
            *a.tag_ref(),
            hints,
            *a.debugging_ref(),
        )),
        Chunk::QuantifiedPredicate(a) => Chunk::QuantifiedPredicate(QuantifiedPredicateChunk::new(
            factory,
            a.id_ref().clone(),
            vars,
            vars_exp,
            definition.snapshot_map,
            a.org_condition_ref().clone(),
            factory.boolean(true),
            condition_exp,
            permission,
            permission_exp,
            inverses,
            singleton,
            singleton_exp,
            *a.tag_ref(),
            hints,
        )),
        Chunk::QuantifiedMagicWand(a) => Chunk::QuantifiedMagicWand(QuantifiedMagicWandChunk::new(
            a.id_ref().clone(),
            vars,
            vars_exp,
            definition.snapshot_map,
            a.org_condition_ref().clone(),
            permission,
            permission_exp,
            inverses,
            singleton,
            singleton_exp,
            *a.tag_ref(),
            hints,
        )),
        _ => unreachable!(),
    };
    Ok(Some((recorder, chunk, equations)))
}

pub trait QuantifiedFieldBoundServices<P, D, J> {
    type Error;
    fn summarise_bound_maps(
        &mut self,
        state: State<P, D, J>,
        field: &ferrum_silver::ast::program::Field,
        receiver: &Term,
        chunks: &[crate::state::chunks::QuantifiedFieldChunk],
    ) -> Result<
        (
            State<P, D, J>,
            crate::rules::quantified_chunk_support::SnapshotMapDefinition,
            crate::rules::quantified_chunk_support::PermMapDefinition,
        ),
        Self::Error,
    >;
    /// Records any debug heap and emits the bound with its source diagnostic expression.
    fn assume_quantified_field_bound(
        &mut self,
        state: State<P, D, J>,
        field: &ferrum_silver::ast::program::Field,
        chunk: Option<&crate::state::chunks::QuantifiedFieldChunk>,
        receiver: &Term,
        goal: &Term,
    ) -> Result<State<P, D, J>, Self::Error>;
}
#[derive(Debug)]
pub enum QuantifiedFieldBoundError<E> {
    MissingField,
    Transform(crate::state::terms::UnsupportedTriggerTransform),
    Service(E),
}
/// Summarize each quantified field in each heap, then assume a trigger-guarded
/// universal bound or inverse-triggered and singleton pointwise bounds.
pub fn assume_quantified_field_bounds<P, D, J, C: QuantifiedFieldBoundServices<P, D, J>>(
    factory: &TermFactory,
    context: &mut C,
    mut state: State<P, D, J>,
    heaps: &[Arc<ListBackedHeap>],
    receiver: &Term,
) -> Result<State<P, D, J>, QuantifiedFieldBoundError<C::Error>> {
    use crate::interfaces::state::chunks::QuantifiedChunk;
    use crate::state::terms::{Quantifier, ResourceKey, Trigger};
    for heap in heaps {
        let mut groups: Vec<(String, Vec<crate::state::chunks::QuantifiedFieldChunk>)> = Vec::new();
        for chunk in heap.values() {
            if let Chunk::QuantifiedField(chunk) = chunk {
                let name = chunk.id_ref().0.clone();
                if let Some((_, chunks)) = groups.iter_mut().find(|(field, _)| *field == name) {
                    chunks.push(chunk.clone());
                } else {
                    groups.push((name, vec![chunk.clone()]));
                }
            }
        }
        // Scala groupBy map iteration is unspecified; native iteration retains first field occurrence.
        for (name, chunks) in groups {
            let field = state
                .program
                .find_field_optionally(&name)
                .cloned()
                .ok_or(QuantifiedFieldBoundError::MissingField)?;
            let (next, snapshot, permission) = context
                .summarise_bound_maps(state, &field, receiver, &chunks)
                .map_err(QuantifiedFieldBoundError::Service)?;
            state = next;
            let heap_trigger = state
                .heap_dependent_triggers
                .iter()
                .any(|r| matches!(r,ResourceKey::Field(f) if f.name == name));
            if heap_trigger {
                let trigger = factory.field_trigger(
                    name.clone(),
                    snapshot.snapshot_map.clone(),
                    receiver.clone(),
                );
                let lookup = factory.perm_lookup(
                    name.clone(),
                    permission.permission_map.clone(),
                    receiver.clone(),
                );
                let goal = factory
                    .quantification(
                        Quantifier::Forall,
                        vec![receiver.clone()],
                        factory.perm_at_most(lookup, factory.full_perm()),
                        vec![Trigger {
                            terms: vec![trigger],
                        }],
                        "qp-fld-prm-bnd".into(),
                        false,
                        None,
                    )
                    .map_err(QuantifiedFieldBoundError::Transform)?;
                state = context
                    .assume_quantified_field_bound(state, &field, None, receiver, &goal)
                    .map_err(QuantifiedFieldBoundError::Service)?;
            } else {
                for chunk in &chunks {
                    if !chunk.invs_ref().is_empty() {
                        let vars = chunk.quantified_vars(factory);
                        let triggers = chunk
                            .invs_ref()
                            .iter()
                            .flat_map(|inverse| inverse.qvars_to_inverses_of(factory, &vars))
                            .map(|(_, term)| Trigger { terms: vec![term] })
                            .collect();
                        let lookup = factory.perm_lookup(
                            name.clone(),
                            permission.permission_map.clone(),
                            vars[0].clone(),
                        );
                        let goal = factory
                            .quantification(
                                Quantifier::Forall,
                                vars.clone(),
                                factory.perm_at_most(lookup, factory.full_perm()),
                                triggers,
                                "qp-fld-prm-bnd".into(),
                                false,
                                None,
                            )
                            .map_err(QuantifiedFieldBoundError::Transform)?;
                        state = context
                            .assume_quantified_field_bound(
                                state,
                                &field,
                                Some(chunk),
                                &vars[0],
                                &goal,
                            )
                            .map_err(QuantifiedFieldBoundError::Service)?;
                    }
                    if let Some(at) = chunk.singleton_rcvr_ref() {
                        let lookup = factory.perm_lookup(
                            name.clone(),
                            permission.permission_map.clone(),
                            at.clone(),
                        );
                        let goal = factory.perm_at_most(lookup, factory.full_perm());
                        state = context
                            .assume_quantified_field_bound(state, &field, Some(chunk), at, &goal)
                            .map_err(QuantifiedFieldBoundError::Service)?;
                    }
                }
            }
        }
    }
    Ok(state)
}
