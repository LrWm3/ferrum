//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/MagicWandSupporter.scala
//!
//! Purpose:
//! Package, apply and transfer resources for magic wands.
//!
//! Planned Rust structure:
//! magicWandSupporter implements createChunk/evaluateWandArguments, consumeFromMultipleHeaps,
//! packageWand/packageWandWithArguments, applyWand, transfer, getEvalHeap/getExecutionHeap,
//! moveToReserveHeap and getOutEdges. The earlier self-framing check is commented out.
//!
//! Behavior to preserve:
//! Evaluate wand arguments with extended exhale disabled, restoring it. Transfer consumes reserve
//! heaps in order with retry and preserves stack order. For ordinary chunks, equate snapshots
//! under same-location and positive-permission guards; quantified basic chunks instead equate
//! snapshot maps directly. Do not equate wand snapshots. Packaging consolidates outer state first,
//! disables branch parallelism, creates abstract LHS root and wand snapshot function, produces LHS,
//! runs proof CFG with used/ops/LHS reserve heaps, then consumes RHS. Record per-branch conditions
//! and snapshot definitions; substitute a fresh unknown LHS for each merged branch, guard recorded
//! conditions with universally quantified wand token, retain LHS-independent definitions,
//! consolidate multiple branches and create wand chunk. If no branch records a result construct an
//! unconstrained wand snapshot. Application consumes wand and LHS, labels old LHS heap, applies
//! snapshot function and assumes token, produces RHS, consolidates and restores old heaps/store.
//! Preserve failure combination, reserves and nested package CFG.
//!
//! Integration:
//! rules::consumer, producer, executor, execution_flow_controller, heap_supporter,
//! state_consolidator; state::chunks and decider::path_conditions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! LHS snapshot/token representation and solver scope/continuation ownership.
//!
//! Status: partial; reserve-heap consumption, snapshot agreement and execution-heap selection
//! retryable transfer, package and apply orchestration implemented. Concrete verifier,
//! solver, heap and CFG services remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2025 ETH Zurich.
use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk, QuantifiedChunk};
use crate::rules::consumption_result::ConsumptionResult;
use crate::state::chunks::Chunk;
use crate::state::heap::ListBackedHeap;
use crate::state::state::State;
use crate::state::terms::{Term, TermFactory};
use ferrum_silver::ast::expression::Exp;
use std::sync::Arc;

pub trait WandHeapServices {
    type Error;
    fn check_wand_permissions(
        &mut self,
        assertion: &Term,
        timeout_ms: i32,
    ) -> Result<bool, Self::Error>;
    fn wand_check_timeout(&self) -> i32;
    fn assume_wand_snapshot_definition(&mut self, definition: &Term) -> Result<(), Self::Error>;
    fn wand_smoke_check(&mut self) -> Result<bool, Self::Error>;
}
#[derive(Debug)]
pub enum MultipleHeapsError<E> {
    Solver(E),
    Consume(E),
}
pub enum MultipleHeapsOutcome<P, D, J> {
    Complete {
        state: State<P, D, J>,
        heaps: Vec<Arc<ListBackedHeap>>,
        chunks: Vec<Option<Chunk>>,
    },
    Incomplete {
        state: State<P, D, J>,
        result: ConsumptionResult,
    },
}
/// Consume permissions from reserve heaps in order. Corresponding ordinary snapshot values
/// are equated only under same-location and positive-permission guards; wand snapshots
/// are intentionally never equated. Smoke checks can complete an infeasible path.
pub fn consume_from_multiple_heaps<P, D, J: Clone, S: WandHeapServices>(
    factory: &TermFactory,
    services: &mut S,
    mut state: State<P, D, J>,
    heaps: &[Arc<ListBackedHeap>],
    loss: Term,
    loss_exp: Option<Exp>,
    quantified_vars: &[Term],
    consume: &mut impl FnMut(
        &mut S,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Term,
        Option<Exp>,
    ) -> Result<
        (
            ConsumptionResult,
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Chunk>,
        ),
        S::Error,
    >,
) -> Result<MultipleHeapsOutcome<P, D, J>, MultipleHeapsError<S::Error>> {
    let timeout = services.wand_check_timeout();
    let mut result = ConsumptionResult::check(
        factory,
        loss,
        loss_exp,
        quantified_vars,
        timeout,
        |goal, timeout| services.check_wand_permissions(goal, timeout),
    )
    .map_err(MultipleHeapsError::Solver)?;
    let mut output_heaps = Vec::new();
    let mut chunks: Vec<Option<Chunk>> = Vec::new();
    for heap in heaps {
        if result.is_complete() {
            output_heaps.push(heap.clone());
            chunks.push(None);
            continue;
        }
        let ConsumptionResult::Incomplete {
            perms_needed,
            perms_needed_exp,
        } = result
        else {
            unreachable!()
        };
        let (next, next_state, next_heap, consumed) = consume(
            services,
            state,
            heap.clone(),
            perms_needed,
            perms_needed_exp,
        )
        .map_err(MultipleHeapsError::Consume)?;
        state = next_state;
        let previous = chunks.iter().find_map(Option::as_ref);
        let equality = match (previous, consumed.as_ref()) {
            (
                Some(Chunk::MagicWand(_) | Chunk::QuantifiedMagicWand(_)),
                Some(Chunk::MagicWand(_) | Chunk::QuantifiedMagicWand(_)),
            ) => factory.boolean(true),
            (Some(Chunk::Basic(a)), Some(Chunk::Basic(b))) => {
                let same = factory.and(
                    a.args()
                        .iter()
                        .zip(b.args())
                        .map(|(x, y)| factory.equals(x.clone(), y.clone())),
                );
                let guard = factory.and([
                    same,
                    factory.is_positive_perm(a.permission(factory)),
                    factory.is_positive_perm(b.permission(factory)),
                ]);
                factory.implies(
                    guard,
                    factory.equals(a.snapshot().clone(), b.snapshot().clone()),
                )
            }
            (Some(a), Some(b)) => {
                let map = |chunk: &Chunk| match chunk {
                    Chunk::QuantifiedField(c) => Some(c.snapshot_map().clone()),
                    Chunk::QuantifiedPredicate(c) => Some(c.snapshot_map().clone()),
                    Chunk::QuantifiedMagicWand(c) => Some(c.snapshot_map().clone()),
                    _ => None,
                };
                match (map(a), map(b)) {
                    (Some(a), Some(b)) => factory.equals(a, b),
                    _ => factory.boolean(true),
                }
            }
            _ => factory.boolean(true),
        };
        services
            .assume_wand_snapshot_definition(&equality)
            .map_err(MultipleHeapsError::Solver)?;
        result = if services
            .wand_smoke_check()
            .map_err(MultipleHeapsError::Solver)?
        {
            ConsumptionResult::Complete
        } else {
            next
        };
        output_heaps.push(next_heap);
        chunks.push(consumed);
    }
    if result.is_complete() {
        Ok(MultipleHeapsOutcome::Complete {
            state,
            heaps: output_heaps,
            chunks,
        })
    } else {
        Ok(MultipleHeapsOutcome::Incomplete { state, result })
    }
}

/// The execution heap is the current used reserve during extended exhale.
pub fn execution_heap<P, D, J>(state: &State<P, D, J>) -> Option<Arc<ListBackedHeap>> {
    if state.exhale_ext {
        state.reserve_heaps.first().cloned()
    } else {
        Some(state.h.clone())
    }
}

pub trait WandTransferServices<P, D, J, V>: WandHeapServices + Sized {
    fn retry_wand_transfer(
        &mut self,
        state: State<P, D, J>,
        action: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                State<P, D, J>,
                Vec<Arc<ListBackedHeap>>,
                Vec<Option<Chunk>>,
            ) -> Result<
                crate::interfaces::verification::VerificationResult<V>,
                WandTransferError<Self::Error>,
            >,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            WandTransferError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Vec<Arc<ListBackedHeap>>,
            Vec<Option<Chunk>>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            WandTransferError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        WandTransferError<Self::Error>,
    >;
    fn merge_transferred_chunks(
        &mut self,
        state: &State<P, D, J>,
        heap: &ListBackedHeap,
        chunks: &[Chunk],
    ) -> Result<
        (
            crate::supporters::functions::function_recorder::FunctionRecorder<D>,
            ListBackedHeap,
        ),
        Self::Error,
    >;
}
#[derive(Debug)]
pub enum WandTransferError<E> {
    MissingReserveHeap,
    MultipleHeaps(MultipleHeapsError<E>),
    Service(E),
}
/// Retry transfer from reserve heaps other than the used heap, then merge all consumed
/// chunks into the used heap and continue outside the retryable action.
pub fn transfer<P, D, J: Clone, V, C: WandTransferServices<P, D, J, V>>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, J>,
    permission: Term,
    permission_exp: Option<Exp>,
    failure: crate::interfaces::verification::VerificationResult<V>,
    quantified_vars: &[Term],
    consume: &mut impl FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Term,
        Option<Exp>,
    ) -> Result<
        (
            ConsumptionResult,
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Chunk>,
        ),
        C::Error,
    >,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Vec<Chunk>,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        WandTransferError<C::Error>,
    >,
) -> Result<crate::interfaces::verification::VerificationResult<V>, WandTransferError<C::Error>> {
    let original_used = state
        .reserve_heaps
        .first()
        .cloned()
        .ok_or(WandTransferError::MissingReserveHeap)?;
    context.retry_wand_transfer(
        state,
        &mut |context, state, done| {
            if state.reserve_heaps.is_empty() {
                return Err(WandTransferError::MissingReserveHeap);
            }
            let heaps = state.reserve_heaps[1..].to_vec();
            match consume_from_multiple_heaps(
                factory,
                context,
                state,
                &heaps,
                permission.clone(),
                permission_exp.clone(),
                quantified_vars,
                consume,
            )
            .map_err(WandTransferError::MultipleHeaps)?
            {
                MultipleHeapsOutcome::Complete {
                    state,
                    heaps,
                    chunks,
                } => done(context, state, heaps, chunks),
                MultipleHeapsOutcome::Incomplete { .. } => Ok(failure.clone()),
            }
        },
        &mut |context, mut state, heaps, chunks| {
            let prior_used = state
                .reserve_heaps
                .first()
                .cloned()
                .ok_or(WandTransferError::MissingReserveHeap)?;
            let prior_state = state.clone();
            let mut reserve = vec![original_used.clone()];
            reserve.extend(heaps);
            state.reserve_heaps = reserve;
            let used: Vec<_> = chunks.into_iter().flatten().collect();
            let (recorder, merged) = context
                .merge_transferred_chunks(&prior_state, &prior_used, &used)
                .map_err(WandTransferError::Service)?;
            state.function_recorder = recorder;
            state.reserve_heaps[0] = Arc::new(merged);
            continuation(context, state, used)
        },
    )
}

pub trait WandReserveHeapServices<P, D, J> {
    type Error;
    fn merge_evaluation_reserves(
        &mut self,
        state: &State<P, D, J>,
        used: &ListBackedHeap,
        operations: &ListBackedHeap,
        lhs: &ListBackedHeap,
    ) -> Result<ListBackedHeap, Self::Error>;
    fn empty_wand_heap(&mut self, state: &State<P, D, J>) -> Result<ListBackedHeap, Self::Error>;
    fn merge_wand_operations(
        &mut self,
        state: &State<P, D, J>,
        operations: &ListBackedHeap,
        new_heap: &ListBackedHeap,
    ) -> Result<
        (
            crate::supporters::functions::function_recorder::FunctionRecorder<D>,
            ListBackedHeap,
        ),
        Self::Error,
    >;
}
#[derive(Debug)]
pub enum WandReserveHeapError<E> {
    MissingReserveHeap,
    Service(E),
}
/// Extended-exhale expression evaluation combines used, operation and LHS reserve heaps.
pub fn evaluation_heap<P, D, J, C: WandReserveHeapServices<P, D, J>>(
    context: &mut C,
    state: &State<P, D, J>,
) -> Result<Arc<ListBackedHeap>, WandReserveHeapError<C::Error>> {
    if !state.exhale_ext {
        return Ok(state.h.clone());
    }
    let [used, operations, lhs, ..] = state.reserve_heaps.as_slice() else {
        return Err(WandReserveHeapError::MissingReserveHeap);
    };
    context
        .merge_evaluation_reserves(state, used, operations, lhs)
        .map(Arc::new)
        .map_err(WandReserveHeapError::Service)
}
/// After a proof-script statement, move its produced heap into the operations reserve.
pub fn move_to_reserve_heap<P, D, J, C: WandReserveHeapServices<P, D, J>>(
    context: &mut C,
    mut state: State<P, D, J>,
) -> Result<State<P, D, J>, WandReserveHeapError<C::Error>> {
    if !state.exhale_ext {
        return Ok(state);
    }
    let operations = state
        .reserve_heaps
        .get(1)
        .cloned()
        .ok_or(WandReserveHeapError::MissingReserveHeap)?;
    let empty = Arc::new(
        context
            .empty_wand_heap(&state)
            .map_err(WandReserveHeapError::Service)?,
    );
    let (recorder, merged) = context
        .merge_wand_operations(&state, &operations, &state.h)
        .map_err(WandReserveHeapError::Service)?;
    state.function_recorder = recorder;
    state.h = empty.clone();
    state.reserve_heaps[0] = empty;
    state.reserve_heaps[1] = Arc::new(merged);
    Ok(state)
}

/// Evaluate wand holes in source order with extended exhale temporarily disabled.
pub fn evaluate_wand_arguments<
    P,
    D,
    J: Clone,
    V,
    C: crate::rules::evaluator::EvaluationContext<P, D, J, V>,
>(
    context: &mut C,
    mut state: State<P, D, J>,
    wand: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Vec<Term>,
        Option<Vec<Exp>>,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        crate::rules::evaluator::EvaluationError<C::Error>,
    >,
) -> Result<
    crate::interfaces::verification::VerificationResult<V>,
    crate::rules::evaluator::EvaluationError<C::Error>,
> {
    let old_exhale = state.exhale_ext;
    state.exhale_ext = false;
    let expressions = wand
        .magic_wand_subexpressions(&state.program)
        .map_err(crate::rules::evaluator::EvaluationError::Wand)?;
    crate::rules::evaluator::evaluate_all(
        context,
        state,
        &expressions,
        &|_| error.clone(),
        &mut |context, mut state, terms, debug| {
            state.exhale_ext = old_exhale;
            continuation(context, state, terms, debug)
        },
    )
}
/// Capture the current store and evaluated wand arguments in a full-permission chunk.
pub fn create_wand_chunk<
    P,
    D,
    J: Clone,
    V,
    C: crate::rules::evaluator::EvaluationContext<P, D, J, V>,
>(
    context: &mut C,
    state: State<P, D, J>,
    wand: &Exp,
    snapshot: Term,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        crate::state::chunks::MagicWandChunk,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        crate::rules::evaluator::EvaluationError<C::Error>,
    >,
) -> Result<
    crate::interfaces::verification::VerificationResult<V>,
    crate::rules::evaluator::EvaluationError<C::Error>,
> {
    use crate::state::chunks::{ChunkBindings, MagicWandChunk, MagicWandIdentifier};
    use crate::state::store::Store;
    use ferrum_silver::ast::expression::ExpKind;
    evaluate_wand_arguments(
        context,
        state,
        wand,
        error,
        &mut |context, state, args, arg_exps| {
            let identifier = MagicWandIdentifier::new(wand.clone(), &state.program)
                .map_err(crate::rules::evaluator::EvaluationError::Wand)?;
            let bindings = ChunkBindings::new(state.g.values().iter().cloned());
            let permission = context.factory().full_perm();
            let permission_exp = context
                .debugging()
                .then(|| Exp::new(ExpKind::FullPerm, wand.metadata().clone()));
            let chunk = MagicWandChunk::new(
                identifier,
                bindings,
                args,
                arg_exps,
                snapshot.clone(),
                permission,
                permission_exp,
                None,
            );
            continuation(context, state, chunk)
        },
    )
}

pub trait WandApplicationServices<P, D, J, V>: Sized {
    type Error;
    type VerificationError;
    fn consume_wand_assertion(
        &mut self,
        state: State<P, D, J>,
        assertion: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            WandApplicationError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        WandApplicationError<Self::Error>,
    >;
    fn wand_evaluation_heap(
        &mut self,
        state: &State<P, D, J>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn assume_wand_token(&mut self, token: &Term) -> Result<(), Self::Error>;
    /// Produce the RHS using the snapshot-to-sort conversion of the given term.
    fn produce_wand_rhs(
        &mut self,
        state: State<P, D, J>,
        rhs: &Exp,
        snapshot: &Term,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            WandApplicationError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        WandApplicationError<Self::Error>,
    >;
    fn consolidate_wand_state(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
}
#[derive(Debug)]
pub enum WandApplicationError<E> {
    InvalidWand,
    MissingSnapshot,
    InvalidLhsSort,
    Service(E),
}
/// Apply a wand by consuming it and its LHS, yielding the token, producing the RHS,
/// then restoring the original store and labelled-old heaps after consolidation.
pub fn apply_wand<P, D, J: Clone, V, C: WandApplicationServices<P, D, J, V>>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, J>,
    wand: &Exp,
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        WandApplicationError<C::Error>,
    >,
) -> Result<crate::interfaces::verification::VerificationResult<V>, WandApplicationError<C::Error>>
{
    use crate::state::terms::{Sort, TermKind};
    use ferrum_silver::ast::expression::ExpKind;
    let ExpKind::MagicWand(lhs, rhs) = wand.kind() else {
        return Err(WandApplicationError::InvalidWand);
    };
    context.consume_wand_assertion(
        state,
        wand,
        error,
        &mut |context, state_after_wand, wand_snapshot| {
            let wand_snapshot = wand_snapshot.ok_or(WandApplicationError::MissingSnapshot)?;
            let original_store = state_after_wand.g.clone();
            let original_old = state_after_wand.old_heaps.clone();
            let reference_state = state_after_wand.clone();
            context.consume_wand_assertion(
                state_after_wand,
                lhs,
                error,
                &mut |context, mut state, lhs_snapshot| {
                    let lhs_snapshot = lhs_snapshot.ok_or(WandApplicationError::MissingSnapshot)?;
                    if lhs_snapshot.sort() != &Sort::Snap {
                        return Err(WandApplicationError::InvalidLhsSort);
                    }
                    let old_heap = context
                        .wand_evaluation_heap(&reference_state)
                        .map_err(WandApplicationError::Service)?;
                    state.old_heaps = original_old.clone();
                    state.old_heaps.insert("lhs".into(), old_heap);
                    let old_conserving = state.conserving_snapshot_generation;
                    let snapshot = crate::rules::heap_supporter::applied_wand_snapshot(
                        factory,
                        &wand_snapshot,
                        lhs_snapshot.clone(),
                    );
                    if let TermKind::MwsfLookup(mwsf, _) = snapshot.kind() {
                        context
                            .assume_wand_token(
                                &factory.magic_wand_token(mwsf.clone(), lhs_snapshot),
                            )
                            .map_err(WandApplicationError::Service)?;
                    }
                    state.conserving_snapshot_generation = true;
                    context.produce_wand_rhs(
                        state,
                        rhs,
                        &snapshot,
                        error,
                        &mut |context, mut state| {
                            state.g = original_store.clone();
                            state.conserving_snapshot_generation = old_conserving;
                            let mut state = context
                                .consolidate_wand_state(state)
                                .map_err(WandApplicationError::Service)?;
                            state.old_heaps = original_old.clone();
                            continuation(context, state)
                        },
                    )
                },
            )
        },
    )
}

pub trait WandPackagingFinalization<P, D, J> {
    type Error;
    fn fresh_unknown_lhs(&mut self) -> Result<Term, Self::Error>;
    fn empty_package_heap(
        &mut self,
        state: &State<P, D, J>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn assume_package_token_axiom(&mut self, axiom: &Term) -> Result<(), Self::Error>;
    fn assume_package_definitions(&mut self, definitions: &[Term]) -> Result<(), Self::Error>;
    fn consolidate_package_branches(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn create_packaged_wand(
        &mut self,
        state: &State<P, D, J>,
        wand: &Exp,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
        snapshot: &Term,
    ) -> Result<Chunk, Self::Error>;
    fn package_merge_warning(&mut self, warning: String);
    fn debug_package_branches(&self) -> bool;
}
#[derive(Debug)]
pub enum WandPackagingError<E> {
    MissingReserveHeap,
    MissingDebugCondition,
    Transform(crate::state::terms::UnsupportedTriggerTransform),
    Traversal(crate::state::terms::UnsupportedSubterms),
    Chunk(crate::state::chunks::ChunkError),
    State(crate::state::state::StateMergeError),
    Service(E),
}
/// Join locally recorded package branches. Each branch receives a fresh unknown LHS
/// in its heap and branch condition; original branch path conditions are retained
/// only behind the wand token, while LHS-independent definitions are re-assumed.
pub fn finalize_wand_package<
    P,
    D: Clone,
    J: Clone + PartialEq,
    C: WandPackagingFinalization<P, D, J>,
>(
    factory: &TermFactory,
    context: &mut C,
    outer: &State<P, D, J>,
    empty_state: State<P, D, J>,
    wand: &Exp,
    args: &[Term],
    arg_exps: Option<&[Exp]>,
    root: &Term,
    wand_snapshot: &Term,
    branches: Vec<(
        State<P, D, J>,
        crate::decider::path_conditions::RecordedPathConditions,
    )>,
) -> Result<(State<P, D, J>, Chunk), WandPackagingError<C::Error>> {
    use crate::interfaces::state::chunks::Chunk as ChunkContract;
    use crate::state::heap::Heap;
    use crate::state::terms::{Quantifier, Trigger};
    use ferrum_silver::ast::expression::ExpKind;
    use std::collections::HashMap;
    if outer.reserve_heaps.is_empty() {
        return Err(WandPackagingError::MissingReserveHeap);
    }
    let mut joined = if branches.is_empty() {
        let empty = context
            .empty_package_heap(&empty_state)
            .map_err(WandPackagingError::Service)?;
        let mut state = empty_state;
        state.reserve_heaps = vec![empty.clone(), empty.clone(), empty];
        state
            .reserve_heaps
            .extend_from_slice(&outer.reserve_heaps[1..]);
        state.parallelize_branches = outer.parallelize_branches;
        state
    } else {
        let mut transformed = Vec::new();
        for (branch, paths) in &branches {
            let unknown = context
                .fresh_unknown_lhs()
                .map_err(WandPackagingError::Service)?;
            let replacements: HashMap<_, _> = [(root.clone(), unknown)].into_iter().collect();
            let substitute_heap = |heap: &ListBackedHeap| -> Result<Arc<ListBackedHeap>,WandPackagingError<C::Error>> {
                let chunks = heap.values().iter().map(|c| c.substitute(factory,&replacements).map_err(WandPackagingError::Chunk)).collect::<Result<Vec<_>,_>>()?;
                Ok(Arc::new(ListBackedHeap::from_chunks(chunks)))
            };
            let mut state = branch.clone();
            state.h = substitute_heap(&branch.h)?;
            state.reserve_heaps = branch
                .reserve_heaps
                .iter()
                .map(|h| substitute_heap(h))
                .collect::<Result<Vec<_>, _>>()?;
            let condition = factory
                .replace(&factory.and(paths.branch_conditions()), &replacements)
                .map_err(WandPackagingError::Transform)?;
            let condition_exp = if context.debug_package_branches() {
                let mut expressions = Vec::new();
                for (_, exp) in paths.branch_condition_exps() {
                    expressions.push(exp.ok_or(WandPackagingError::MissingDebugCondition)?);
                }
                let mut iter = expressions.into_iter();
                Some(match iter.next() {
                    Some(first) => iter.fold(first, |a, b| {
                        Exp::new(ExpKind::And(a, b), Default::default())
                    }),
                    None => Exp::new(ExpKind::TrueLit, Default::default()),
                })
            } else {
                None
            };
            transformed.push((state, condition, condition_exp));
        }
        let mut iter = transformed.into_iter();
        let (mut state, mut condition, mut condition_exp) = iter.next().expect("nonempty branches");
        for (other, other_condition, other_exp) in iter {
            state = state
                .merge_conditional(
                    &condition,
                    &condition_exp,
                    &other,
                    &other_condition,
                    &other_exp,
                    factory,
                    &mut |warning| context.package_merge_warning(warning),
                )
                .map_err(WandPackagingError::State)?;
            condition = factory.or([condition, other_condition]);
            condition_exp = match (condition_exp, other_exp) {
                (Some(a), Some(b)) => Some(Exp::new(ExpKind::Or(a, b), Default::default())),
                (None, _) => None,
                _ => return Err(WandPackagingError::MissingDebugCondition),
            };
        }
        let token = factory.yield_wand_token(wand_snapshot, root.clone());
        let branch_conditions = branches.iter().map(|(_, paths)| {
            factory.and(
                paths
                    .branch_conditions()
                    .into_iter()
                    .chain(paths.conditionalized(factory)),
            )
        });
        let body = factory.implies(token.clone(), factory.or(branch_conditions));
        let axiom = factory
            .quantification(
                Quantifier::Forall,
                vec![root.clone()],
                body,
                vec![Trigger { terms: vec![token] }],
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(WandPackagingError::Transform)?;
        context
            .assume_package_token_axiom(&axiom)
            .map_err(WandPackagingError::Service)?;
        let mut definitions = Vec::new();
        for (_, paths) in &branches {
            for definition in paths.defining_assumptions() {
                if !definitions.contains(&definition)
                    && !definition
                        .contains(root)
                        .map_err(WandPackagingError::Traversal)?
                {
                    definitions.push(definition);
                }
            }
        }
        context
            .assume_package_definitions(&definitions)
            .map_err(WandPackagingError::Service)?;
        if branches.len() > 1 {
            state = context
                .consolidate_package_branches(state)
                .map_err(WandPackagingError::Service)?;
        }
        state
    };
    if joined.reserve_heaps.len() < 3 {
        return Err(WandPackagingError::MissingReserveHeap);
    }
    joined.reserve_heaps.drain(..3);
    let chunk = context
        .create_packaged_wand(&joined, wand, args, arg_exps, wand_snapshot)
        .map_err(WandPackagingError::Service)?;
    Ok((joined, chunk))
}

pub trait WandPackageServices<P, D, J, V>: WandPackagingFinalization<P, D, J> + Sized {
    type VerificationError;
    fn consolidate_before_package(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn fresh_package_root(&mut self) -> Result<Term, Self::Error>;
    fn fresh_wand_snapshot_function(&mut self) -> Result<Term, Self::Error>;
    fn package_root_debug_variable(
        &mut self,
    ) -> Result<Option<crate::state::store::AbstractLocalVar>, Self::Error>;
    fn evaluate_package_arguments(
        &mut self,
        state: State<P, D, J>,
        wand: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Vec<Term>,
            Option<Vec<Exp>>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            PackageExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        PackageExecutionError<Self::Error>,
    >;
    fn locally_package(
        &mut self,
        state: State<P, D, J>,
        action: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            PackageExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        PackageExecutionError<Self::Error>,
    >;
    fn package_path_mark(&mut self) -> Result<crate::decider::path_conditions::Mark, Self::Error>;
    fn package_paths_after(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<crate::decider::path_conditions::RecordedPathConditions, Self::Error>;
    fn produce_package_lhs(
        &mut self,
        state: State<P, D, J>,
        lhs: &Exp,
        root: &Term,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            PackageExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        PackageExecutionError<Self::Error>,
    >;
    fn package_proof_cfg(
        &mut self,
        proof: &ferrum_silver::ast::statement::Stmt,
    ) -> Result<Arc<ferrum_silver::cfg::silver::silver_cfg::SilverCfg>, Self::Error>;
    fn execute_package_proof(
        &mut self,
        state: State<P, D, J>,
        cfg: Arc<ferrum_silver::cfg::silver::silver_cfg::SilverCfg>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            PackageExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        PackageExecutionError<Self::Error>,
    >;
    fn consume_package_rhs(
        &mut self,
        state: State<P, D, J>,
        rhs: &Exp,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            PackageExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        PackageExecutionError<Self::Error>,
    >;
    fn assume_package_snapshot_definition(&mut self, definition: &Term) -> Result<(), Self::Error>;
}
#[derive(Debug)]
pub enum PackageExecutionError<E> {
    InvalidWand,
    MissingReserveHeap,
    MissingSnapshot,
    Finalization(WandPackagingError<E>),
    Service(E),
}
/// Package the wand in a local scope, executing its proof and recording each RHS
/// branch before joining those branches outside the scope.
pub fn package_wand<P, D: Clone, J: Clone + PartialEq, V, C: WandPackageServices<P, D, J, V>>(
    factory: &TermFactory,
    context: &mut C,
    state: State<P, D, J>,
    wand: &Exp,
    proof: &ferrum_silver::ast::statement::Stmt,
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Chunk,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        PackageExecutionError<C::Error>,
    >,
) -> Result<crate::interfaces::verification::VerificationResult<V>, PackageExecutionError<C::Error>>
{
    use ferrum_silver::ast::expression::ExpKind;
    let ExpKind::MagicWand(lhs, rhs) = wand.kind() else {
        return Err(PackageExecutionError::InvalidWand);
    };
    let mut state = context
        .consolidate_before_package(state)
        .map_err(PackageExecutionError::Service)?;
    if !state.exhale_ext {
        let empty = context
            .empty_package_heap(&state)
            .map_err(PackageExecutionError::Service)?;
        state.reserve_heaps = vec![empty, state.h.clone()];
    }
    context.evaluate_package_arguments(state, wand, error, &mut |context, outer, args, arg_exps| {
        if outer.reserve_heaps.is_empty() {
            return Err(PackageExecutionError::MissingReserveHeap);
        }
        let root = context
            .fresh_package_root()
            .map_err(PackageExecutionError::Service)?;
        let mwsf = context
            .fresh_wand_snapshot_function()
            .map_err(PackageExecutionError::Service)?;
        let wand_snapshot = factory.magic_wand_snapshot(mwsf);
        let mut empty_state = outer.clone();
        empty_state.h = context
            .empty_package_heap(&outer)
            .map_err(PackageExecutionError::Service)?;
        empty_state.reserve_heaps.clear();
        empty_state.exhale_ext = false;
        empty_state.parallelize_branches = false;
        let mut branches = Vec::new();
        let result = context.locally_package(empty_state.clone(), &mut |context, mut state| {
            let mark = context
                .package_path_mark()
                .map_err(PackageExecutionError::Service)?;
            let debug_root = context
                .package_root_debug_variable()
                .map_err(PackageExecutionError::Service)?;
            state
                .packaging_wand_snapshots
                .insert(0, (root.clone(), debug_root));
            state.conserving_snapshot_generation = true;
            context.produce_package_lhs(state, lhs, &root, error, &mut |context, mut lhs_state| {
                let cfg = context
                    .package_proof_cfg(proof)
                    .map_err(PackageExecutionError::Service)?;
                let empty = context
                    .empty_package_heap(&lhs_state)
                    .map_err(PackageExecutionError::Service)?;
                let lhs_heap = lhs_state.h.clone();
                lhs_state.g = outer.g.clone();
                lhs_state.h = empty.clone();
                lhs_state.reserve_heaps = vec![empty.clone(), empty, lhs_heap.clone()];
                lhs_state
                    .reserve_heaps
                    .extend_from_slice(&outer.reserve_heaps[1..]);
                lhs_state.reserve_cfgs.insert(0, cfg.clone());
                lhs_state.exhale_ext = true;
                lhs_state.old_heaps = outer.old_heaps.clone();
                lhs_state.old_heaps.insert("lhs".into(), lhs_heap);
                lhs_state.conserving_snapshot_generation = outer.conserving_snapshot_generation;
                let lhs_old = lhs_state.old_heaps.clone();
                context.execute_package_proof(
                    lhs_state,
                    cfg,
                    error,
                    &mut |context, mut proof_state| {
                        proof_state.old_heaps = lhs_old.clone();
                        if proof_state.reserve_cfgs.is_empty() {
                            return Err(PackageExecutionError::MissingReserveHeap);
                        }
                        proof_state.reserve_cfgs.remove(0);
                        context.consume_package_rhs(
                            proof_state,
                            rhs,
                            error,
                            &mut |context, mut state, snapshot| {
                                let snapshot =
                                    snapshot.ok_or(PackageExecutionError::MissingSnapshot)?;
                                let lookup =
                                    factory.apply_wand_snapshot(&wand_snapshot, root.clone());
                                context
                                    .assume_package_snapshot_definition(
                                        &factory.equals(lookup, snapshot),
                                    )
                                    .map_err(PackageExecutionError::Service)?;
                                state.exhale_ext = false;
                                state.old_heaps = outer.old_heaps.clone();
                                state
                                    .packaging_wand_snapshots
                                    .retain(|(term, _)| term != &root);
                                state.parallelize_branches = outer.parallelize_branches;
                                let paths = context
                                    .package_paths_after(mark)
                                    .map_err(PackageExecutionError::Service)?;
                                branches.push((state, paths));
                                Ok(crate::interfaces::verification::VerificationResult::success())
                            },
                        )
                    },
                )
            })
        })?;
        let (state, chunk) = finalize_wand_package(
            factory,
            context,
            &outer,
            empty_state,
            wand,
            &args,
            arg_exps.as_deref(),
            &root,
            &wand_snapshot,
            branches,
        )
        .map_err(PackageExecutionError::Finalization)?;
        if !result.continue_verification() {
            return Ok(result);
        }
        let next = continuation(context, state, chunk)?;
        Ok(result.combine(|| next, false))
    })
}
