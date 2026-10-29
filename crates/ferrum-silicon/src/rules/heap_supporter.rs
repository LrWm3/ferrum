//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/HeapSupporter.scala
//!
//! Purpose:
//! Define heap encoding contract and implement the default chunk-based heap rules.
//!
//! Planned Rust structure:
//! HeapSupportRules specifies single/quantified consumption and production, field
//! access/assignment, current permission, havoc, forperm, triggers, snapshots, wand reserve
//! operations and empty heap. DefaultHeapSupportRules/defaultHeapSupporter route to chunkSupporter
//! and quantifiedChunkSupporter; helper groups construct wand chunks, trigger variants and
//! conditional havoc.
//!
//! Behavior to preserve:
//! Field assignment consumes full permission before producing new value; greedy quantified modes
//! retry and continuation must leave retry action before executing later work. Current permission
//! sums alias-guarded chunks or uses summarised quantified maps and assumes field upper bounds.
//! Field access uses cached summary with re-emitted definitions or singleton/summarised map, checks
//! positive permission except in trigger mode, records snapshot and possible triggers.
//! Produce/consume dispatch by quantified resource, preserving distinct insufficient-permission and
//! missing-wand errors and configured predicate inhale triggers. Havoc replaces snapshots
//! conditionally; quantified havoc assumes agreement of old/new maps outside condition, with
//! inverse-based havocall conditions. Forperm builds per-chunk matching/positive conditions.
//! Preserve resource snapshot conversions, fresh quantified wand maps, trigger generation and
//! reserve heap merges.
//!
//! Integration:
//! rules::chunk_supporter, quantified_chunk_support, mask_heap_supporter, evaluator, consumer,
//! producer, havoc_supporter, predicate_supporter and magic_wand_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Encoding interface, snapshot/trigger alternatives and continuation/context ownership.
//!
//! Status: partial; ordinary/quantified single-location routing, current permission and chunk production implemented.
//! Quantified field access and assignment, quantified rules and verifier encoding services remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk, QuantifiedChunk};
use crate::interfaces::verification::VerificationResult;
use crate::resources::resources::BaseId;
use crate::rules::chunk_supporter::{self, ChunkExecutionContext, ChunkExecutionError};
use crate::state::{
    chunks::{BasicChunk, BasicChunkIdentifier, Chunk, ChunkIdentifier},
    heap::{Heap, ListBackedHeap},
    state::State,
    terms::{ResourceKey, Sort, Term},
};
use ferrum_silver::ast::expression::Exp;
use std::sync::Arc;

/// Concrete heap encodings supply quantified chunks, wand creation and trigger assumptions.
pub trait HeapExecutionContext<P, D, J, V>: ChunkExecutionContext<P, D, J, V> {
    fn produce_quantified_single(
        &mut self,
        state: State<P, D, J>,
        resource: &ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
        snapshot: Term,
        permission: Term,
        debug_permission: Option<Exp>,
        merge_and_trigger: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ChunkExecutionError<Self::Error>>;
    fn consume_quantified_single(
        &mut self,
        state: State<P, D, J>,
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
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ChunkExecutionError<Self::Error>>;
    fn create_wand_chunk(
        &mut self,
        state: State<P, D, J>,
        resource: &ResourceKey,
        snapshot: Term,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Chunk,
        ) -> Result<
            VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ChunkExecutionError<Self::Error>>;
    /// Build quantified summary maps, assume any resource trigger and the field upper bound,
    /// and return the permission lookup. These effects belong to the quantified encoding.
    fn quantified_current_permission(
        &mut self,
        state: State<P, D, J>,
        heap: &ListBackedHeap,
        resource: &ResourceKey,
        access: &Exp,
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<(State<P, D, J>, Term), Self::Error>;
    /// Quantified field lookup owns summary-cache, trigger and positivity handling.
    fn quantified_field_access(
        &mut self,
        state: State<P, D, J>,
        field_access: &Exp,
        resource: &ResourceKey,
        receiver: &Term,
        debug_receiver: Option<&Exp>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Term,
        ) -> Result<
            VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ChunkExecutionError<Self::Error>>;
    /// Quantified assignment must retain its source retry boundary and singleton-map axioms.
    fn assign_quantified_field(
        &mut self,
        state: State<P, D, J>,
        resource: &ResourceKey,
        debug_access: Option<&Exp>,
        receiver: &Term,
        debug_receiver: Option<&Exp>,
        value: &Term,
        debug_value: Option<&Exp>,
        debug_full_permission: Option<&Exp>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, ChunkExecutionError<Self::Error>>;
    fn record_assignment_heap(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
    /// Create a fresh havoc value; wand map functions use the source `mwsf` name.
    fn fresh_havoc_snapshot(&mut self, sort: &Sort, wand_map: bool) -> Result<Term, Self::Error>;
    /// Formal resource arguments and aggregate binder used by quantified snapshot maps.
    fn havoc_codomain(
        &mut self,
        state: &State<P, D, J>,
        resource: &ResourceKey,
    ) -> Result<(Vec<Term>, Term), Self::Error>;
    fn fresh_havoc_map(
        &mut self,
        state: &State<P, D, J>,
        resource: &ResourceKey,
    ) -> Result<Term, Self::Error>;
    fn assume_havoc_axiom(&mut self, axiom: &Term) -> Result<(), Self::Error>;
    fn next_havoc_axiom_id(&mut self) -> u64;
    fn heap_branch_conditions(&self) -> Vec<Term>;
    fn enable_predicate_triggers_on_inhale(&self) -> bool;
    fn disable_function_unfold_trigger(&self) -> bool;
    fn assume_predicate_trigger(
        &mut self,
        state: &State<P, D, J>,
        predicate: &ferrum_silver::ast::program::Predicate,
        snapshot: &Term,
        args: &[Term],
        debug_args: Option<&[Exp]>,
    ) -> Result<(), Self::Error>;
}
fn is_quantified<P, D, J>(state: &State<P, D, J>, resource: &ResourceKey) -> bool {
    match resource {
        ResourceKey::Field(f) => state.qp_fields.contains(f.as_ref()),
        ResourceKey::Predicate(p) => state.qp_predicates.contains(p.as_ref()),
        ResourceKey::Wand(w) => state.qp_magic_wands.contains(w),
    }
}
fn identifier(resource: &ResourceKey) -> ChunkIdentifier {
    match resource {
        ResourceKey::Field(f) => ChunkIdentifier::Basic(BasicChunkIdentifier(f.name.clone())),
        ResourceKey::Predicate(p) => ChunkIdentifier::Basic(BasicChunkIdentifier(p.name.clone())),
        ResourceKey::Wand(w) => ChunkIdentifier::Wand(w.clone()),
    }
}
/// Produce a single location, retaining source quantified/nonquantified and trigger branches.
pub fn produce_single<P, D, J: Clone, V, C: HeapExecutionContext<P, D, J, V>>(
    context: &mut C,
    state: State<P, D, J>,
    resource: &ResourceKey,
    args: &[Term],
    debug_args: Option<&[Exp]>,
    snapshot: Term,
    debug_snapshot: Option<Exp>,
    permission: Term,
    debug_permission: Option<Exp>,
    error: &C::VerificationError,
    merge_and_trigger: bool,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    )
        -> Result<VerificationResult<V>, ChunkExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ChunkExecutionError<C::Error>> {
    if is_quantified(&state, resource) {
        return context.produce_quantified_single(
            state,
            resource,
            args,
            debug_args,
            snapshot,
            permission,
            debug_permission,
            merge_and_trigger,
            continuation,
        );
    }
    if matches!(resource, ResourceKey::Wand(_)) {
        let wand_snapshot = context.factory().magic_wand_snapshot(snapshot);
        return context.create_wand_chunk(
            state,
            resource,
            wand_snapshot,
            error,
            &mut |context, state, chunk| {
                let heap = state.h.clone();
                chunk_supporter::produce(
                    context,
                    state,
                    heap.as_ref(),
                    &chunk,
                    &mut |context, mut state, heap| {
                        state.h = heap;
                        continuation(context, state)
                    },
                )
            },
        );
    }
    let factory = context.factory().clone();
    let (resource_id, id, snapshot) = match resource {
        ResourceKey::Field(field) => (
            BaseId::Field,
            BasicChunkIdentifier(field.name.clone()),
            snapshot,
        ),
        ResourceKey::Predicate(predicate) => (
            BaseId::Predicate,
            BasicChunkIdentifier(predicate.name.clone()),
            factory.sort_wrapper(snapshot, Sort::Snap),
        ),
        ResourceKey::Wand(_) => unreachable!(),
    };
    let chunk = Chunk::Basic(BasicChunk::new(
        resource_id,
        id,
        args.to_vec(),
        debug_args.map(<[Exp]>::to_vec),
        snapshot.clone(),
        debug_snapshot,
        permission,
        debug_permission,
        state.qp_tag,
    ));
    if !merge_and_trigger {
        let mut state = state;
        state.h = Arc::new(state.h.with_chunk(chunk));
        return continuation(context, state);
    }
    let heap = state.h.clone();
    chunk_supporter::produce(
        context,
        state,
        heap.as_ref(),
        &chunk,
        &mut |context, mut state, heap| {
            if let ResourceKey::Predicate(predicate) = resource {
                if context.enable_predicate_triggers_on_inhale()
                    && matches!(
                        state.function_recorder,
                        crate::supporters::functions::function_recorder::FunctionRecorder::Noop
                    )
                    && !context.disable_function_unfold_trigger()
                {
                    context
                        .assume_predicate_trigger(&state, predicate, &snapshot, args, debug_args)
                        .map_err(ChunkExecutionError::Context)?;
                }
            }
            state.h = heap;
            continuation(context, state)
        },
    )
}
/// Dispatch single-location consumption to quantified or ordinary chunk algorithms.
pub fn consume_single<P, D, J: Clone, V, C: HeapExecutionContext<P, D, J, V>>(
    context: &mut C,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    resource: &ResourceKey,
    args: &[Term],
    debug_args: Option<&[Exp]>,
    permission: &Term,
    debug_permission: Option<&Exp>,
    return_snapshot: bool,
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Option<Term>,
    )
        -> Result<VerificationResult<V>, ChunkExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ChunkExecutionError<C::Error>> {
    if is_quantified(&state, resource) {
        context.consume_quantified_single(
            state,
            heap,
            resource,
            args,
            debug_args,
            permission,
            debug_permission,
            return_snapshot,
            error,
            continuation,
        )
    } else {
        chunk_supporter::consume(
            context,
            state,
            heap,
            resource,
            &identifier(resource),
            args,
            debug_args,
            permission,
            debug_permission,
            return_snapshot,
            error,
            continuation,
        )
    }
}

/// Sum permissions of ordinary chunks guarded by pairwise argument equality; quantified
/// resources use the encoding's summary maps and field permission upper-bound assumption.
pub fn current_permission<P, D, J, V, C: HeapExecutionContext<P, D, J, V>>(
    context: &mut C,
    state: State<P, D, J>,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    access: &Exp,
    args: &[Term],
    debug_args: Option<&[Exp]>,
) -> Result<(State<P, D, J>, Term), C::Error> {
    if is_quantified(&state, resource) {
        return context
            .quantified_current_permission(state, heap, resource, access, args, debug_args);
    }
    let factory = context.factory().clone();
    let id = identifier(resource);
    let mut total = factory.no_perm();
    for chunk in heap.values() {
        let (chunk_id, chunk_args, permission) = match chunk {
            Chunk::Basic(c) => (c.identifier(), c.args(), c.perm_ref()),
            Chunk::MagicWand(c) => (c.identifier(), c.args(), c.perm_ref()),
            _ => continue,
        };
        if chunk_id == id {
            let equal = factory.and(
                args.iter()
                    .zip(chunk_args)
                    .map(|(a, b)| factory.equals(a.clone(), b.clone())),
            );
            let amount = factory.ite(equal, permission.clone(), factory.no_perm());
            total = factory.perm_plus(total, amount);
        }
    }
    Ok((state, total))
}

/// Evaluate a field location through the ordinary chunk lookup or quantified field encoding.
/// Ordinary lookup can update the heap during retry and records the resulting snapshot under
/// the current branch guards, exactly as the source continuation does.
pub fn field_access<P, D: Clone, J: Clone, V, C: HeapExecutionContext<P, D, J, V>>(
    context: &mut C,
    state: State<P, D, J>,
    field_access: &Exp,
    resource: &ResourceKey,
    receiver: &Term,
    debug_receiver: Option<&Exp>,
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Term,
    )
        -> Result<VerificationResult<V>, ChunkExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ChunkExecutionError<C::Error>> {
    if is_quantified(&state, resource) {
        return context.quantified_field_access(
            state,
            field_access,
            resource,
            receiver,
            debug_receiver,
            error,
            continuation,
        );
    }
    let heap = state.h.clone();
    let args = [receiver.clone()];
    let debug_args = debug_receiver.cloned().map(|e| vec![e]);
    chunk_supporter::lookup(
        context,
        state,
        heap,
        resource,
        &identifier(resource),
        &args,
        debug_args.as_deref(),
        error,
        &mut |context, mut state, heap, snapshot| {
            state.function_recorder = state.function_recorder.record_location_snapshot(
                field_access.clone(),
                context.heap_branch_conditions(),
                snapshot.clone(),
            );
            state.h = heap;
            continuation(context, state, snapshot)
        },
    )
}

/// A field write consumes full permission before merging the new value into the resulting heap.
pub fn assign_field<P, D, J: Clone, V, C: HeapExecutionContext<P, D, J, V>>(
    context: &mut C,
    state: State<P, D, J>,
    field: &ferrum_silver::ast::program::Field,
    debug_access: Option<&Exp>,
    receiver: &Term,
    debug_receiver: Option<&Exp>,
    value: &Term,
    debug_value: Option<&Exp>,
    debug_full_permission: Option<&Exp>,
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    )
        -> Result<VerificationResult<V>, ChunkExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ChunkExecutionError<C::Error>> {
    let resource = ResourceKey::Field(Arc::new(field.clone()));
    if is_quantified(&state, &resource) {
        return context.assign_quantified_field(
            state,
            &resource,
            debug_access,
            receiver,
            debug_receiver,
            value,
            debug_value,
            debug_full_permission,
            error,
            continuation,
        );
    }
    let heap = state.h.clone();
    let permission = context.factory().full_perm();
    let args = [receiver.clone()];
    let debug_args = debug_receiver.cloned().map(|e| vec![e]);
    chunk_supporter::consume(
        context,
        state,
        heap,
        &resource,
        &identifier(&resource),
        &args,
        debug_args.as_deref(),
        &permission,
        debug_full_permission,
        false,
        error,
        &mut |context, state, heap, _| {
            let chunk = Chunk::Basic(BasicChunk::new(
                BaseId::Field,
                BasicChunkIdentifier(field.name.clone()),
                args.to_vec(),
                debug_args.clone(),
                value.clone(),
                debug_value.cloned(),
                permission.clone(),
                debug_full_permission.cloned(),
                state.qp_tag,
            ));
            chunk_supporter::produce(
                context,
                state,
                &heap,
                &chunk,
                &mut |context, mut state, heap| {
                    state.h = heap;
                    let state = context
                        .record_assignment_heap(state)
                        .map_err(ChunkExecutionError::Context)?;
                    continuation(context, state)
                },
            )
        },
    )
}

#[derive(Debug)]
pub enum HavocError<E> {
    Context(E),
    UnexpectedQuantifiedChunk,
    UnexpectedNonQuantifiedChunk,
    Transform(crate::state::terms::UnsupportedTriggerTransform),
}

/// Replace matching ordinary snapshots conditionally; splitHeap's reversal and the source's
/// other-then-replaced ordering are preserved. Quantified resources use snapshot-map axioms.
pub fn havoc_resource<P, D, J, V, C: HeapExecutionContext<P, D, J, V>>(
    context: &mut C,
    state: &State<P, D, J>,
    lhs: &Term,
    resource: &ResourceKey,
    info: &crate::rules::havoc_supporter::HavocHelperData,
) -> Result<ListBackedHeap, HavocError<C::Error>> {
    if is_quantified(state, resource) {
        return havoc_quantified(context, state, lhs, resource, info);
    }
    let (relevant, mut others) = chunk_supporter::split_heap(&state.h, &identifier(resource))
        .map_err(|_| HavocError::UnexpectedQuantifiedChunk)?;
    let factory = context.factory().clone();
    for chunk in relevant {
        let updated = match chunk {
            Chunk::Basic(chunk) => {
                let fresh = context
                    .fresh_havoc_snapshot(chunk.snapshot().sort(), false)
                    .map_err(HavocError::Context)?;
                let condition = crate::rules::havoc_supporter::replacement_condition(
                    &factory,
                    lhs,
                    chunk.args(),
                    info,
                )
                .map_err(HavocError::Transform)?;
                Chunk::Basic(chunk.with_snapshot(
                    factory.ite(condition, fresh, chunk.snapshot().clone()),
                    None,
                ))
            }
            Chunk::MagicWand(chunk) => {
                let fresh = context
                    .fresh_havoc_snapshot(&Sort::MagicWandSnapFunction, true)
                    .map_err(HavocError::Context)?;
                let condition = crate::rules::havoc_supporter::replacement_condition(
                    &factory,
                    lhs,
                    chunk.args(),
                    info,
                )
                .map_err(HavocError::Transform)?;
                let crate::state::terms::TermKind::MagicWandSnapshot(old) = chunk.snapshot().kind()
                else {
                    unreachable!("validated wand chunk snapshot")
                };
                let snapshot =
                    factory.magic_wand_snapshot(factory.ite(condition, fresh, old.clone()));
                Chunk::MagicWand(chunk.with_snapshot(snapshot, None))
            }
            _ => unreachable!("split_heap returns ordinary chunks"),
        };
        others.push(updated);
    }
    Ok(ListBackedHeap::from_chunks(others))
}

/// A fresh map agrees with each previous map whenever the replacement condition is false.
fn havoc_quantified<P, D, J, V, C: HeapExecutionContext<P, D, J, V>>(
    context: &mut C,
    state: &State<P, D, J>,
    lhs: &Term,
    resource: &ResourceKey,
    info: &crate::rules::havoc_supporter::HavocHelperData,
) -> Result<ListBackedHeap, HavocError<C::Error>> {
    use crate::state::terms::{Quantifier, Trigger};
    use std::collections::HashMap;
    let factory = context.factory().clone();
    let (codomain, aggregate) = context
        .havoc_codomain(state, resource)
        .map_err(HavocError::Context)?;
    let condition =
        crate::rules::havoc_supporter::replacement_condition(&factory, lhs, &codomain, info)
            .map_err(HavocError::Transform)?;
    let destructors = factory.from_snap_tree_targets(aggregate.clone(), &codomain);
    let substitutions: HashMap<_, _> = codomain.into_iter().zip(destructors).collect();
    let condition = factory
        .replace(&condition, &substitutions)
        .map_err(HavocError::Transform)?;
    let (relevant, others) = crate::rules::quantified_chunk_support::split_quantified_heap(
        &state.h,
        &identifier(resource),
    )
    .map_err(|_| HavocError::UnexpectedNonQuantifiedChunk)?;
    let mut updated = Vec::new();
    for chunk in relevant {
        let old = match &chunk {
            Chunk::QuantifiedField(c) => c.snapshot_map(),
            Chunk::QuantifiedPredicate(c) => c.snapshot_map(),
            Chunk::QuantifiedMagicWand(c) => c.snapshot_map(),
            _ => unreachable!(),
        };
        let fresh = context
            .fresh_havoc_map(state, resource)
            .map_err(HavocError::Context)?;
        let new_lookup = factory.resource_lookup(resource, fresh.clone(), vec![aggregate.clone()]);
        let old_lookup = factory.resource_lookup(resource, old.clone(), vec![aggregate.clone()]);
        let equality = factory.equals(old_lookup.clone(), new_lookup.clone());
        let body = factory.implies(factory.not(condition.clone()), equality);
        let name = format!("qp.smValDef{}", context.next_havoc_axiom_id());
        let axiom = factory
            .quantification(
                Quantifier::Forall,
                vec![aggregate.clone()],
                body,
                vec![
                    Trigger {
                        terms: vec![new_lookup],
                    },
                    Trigger {
                        terms: vec![old_lookup],
                    },
                ],
                name,
                true,
                None,
            )
            .map_err(HavocError::Transform)?;
        context
            .assume_havoc_axiom(&axiom)
            .map_err(HavocError::Context)?;
        updated.push(match chunk {
            Chunk::QuantifiedField(c) => Chunk::QuantifiedField(c.with_snapshot_map(fresh)),
            Chunk::QuantifiedPredicate(c) => Chunk::QuantifiedPredicate(c.with_snapshot_map(fresh)),
            Chunk::QuantifiedMagicWand(c) => Chunk::QuantifiedMagicWand(c.with_snapshot_map(fresh)),
            _ => unreachable!(),
        });
    }
    updated.extend(others);
    Ok(ListBackedHeap::from_chunks(updated))
}

/// Apply a concrete or quantified wand snapshot to its consumed left snapshot.
pub fn applied_wand_snapshot(
    factory: &crate::state::terms::TermFactory,
    wand: &Term,
    lhs: Term,
) -> Term {
    use crate::state::terms::TermKind;
    match wand.kind() {
        TermKind::MagicWandSnapshot(_) => factory.apply_wand_snapshot(wand, lhs),
        TermKind::SortWrapper(inner, _)
            if matches!(inner.kind(), TermKind::MagicWandSnapshot(_)) =>
        {
            factory.apply_wand_snapshot(inner, lhs)
        }
        _ if wand.sort() == &Sort::MagicWandSnapFunction => factory.mwsf_lookup(wand.clone(), lhs),
        _ => wand.clone(),
    }
}
