//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/ChunkSupporter.scala
//!
//! Purpose:
//! Consume, produce and look up nonquantified resource chunks.
//!
//! Planned Rust structure:
//! ChunkSupportRules and chunkSupporter implement consume/consume2/consumeGreedy, produce,
//! lookup/lookupGreedy, findChunk, findChunksWithID and splitHeap.
//!
//! Behavior to preserve:
//! Find literal aliases first then ask solver; splitHeap rejects matching quantified chunks. Greedy
//! exact read takes min and removes or reinserts residual chunk, checks remaining permissions;
//! constrainable read assumes strict bound, read-only checks positive access without removal. In
//! package mode transfer through wand reserves; otherwise retry with temporary main heap, choosing
//! complete or greedy exhale. Smoke-dead paths return Success, except package lookup yields fresh
//! value; ordinary failures build counterexample. Missing returned snapshot creates and records a
//! fresh snapshot despite stale upstream comment suggesting unit. Produce consolidates and assumes
//! properties.
//!
//! Integration:
//! rules::more_complete_exhale_supporter, magic_wand_supporter, state_consolidator,
//! consumption_result and resources::properties.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Alias matching, snapshots and continuations with heap supporter.
//!
//! Status: partial; exact source greedy chunk lookup, splitting and permission consumption implemented.
//! Retry, complete-exhale, consolidation and wand transfer use verifier services.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk};
use crate::rules::consumption_result::ConsumptionResult;
use crate::state::{
    chunks::{Chunk, ChunkIdentifier},
    heap::{Heap, ListBackedHeap},
    state::State,
    terms::{Term, TermFactory, consume_exact_read},
};
use ferrum_silver::ast::expression::{Exp, ExpKind};
use std::sync::Arc;

#[derive(Debug)]
pub enum ChunkSupportError<E> {
    Solver(E),
    MissingDebugPermission,
    UnexpectedQuantifiedChunk,
}
/// Solver and resource-property assumptions are verifier-owned, and all failures propagate.
pub trait ChunkSolver<P, D, J> {
    type Error;
    fn factory(&self) -> &TermFactory;
    fn check(&mut self, term: &Term, timeout_ms: i32) -> Result<bool, Self::Error>;
    fn check_timeout(&self) -> i32;
    fn assert_timeout(&self) -> i32;
    fn assume(&mut self, term: &Term, debug: Option<&Exp>) -> Result<(), Self::Error>;
    fn assume_properties(
        &mut self,
        state: &State<P, D, J>,
        heap: &ListBackedHeap,
        chunk: &Chunk,
    ) -> Result<(), Self::Error>;
}
fn chunk_data(chunk: &Chunk) -> Option<(ChunkIdentifier, &[Term], &Term, Option<Exp>, &Term)> {
    match chunk {
        Chunk::Basic(c) => Some((
            c.identifier(),
            c.args(),
            c.perm_ref(),
            c.permission_exp(),
            c.snap_ref(),
        )),
        Chunk::MagicWand(c) => Some((
            c.identifier(),
            c.args(),
            c.perm_ref(),
            c.permission_exp(),
            c.snap_ref(),
        )),
        _ => None,
    }
}
fn with_permission(chunk: &Chunk, permission: Term, expression: Option<Exp>) -> Chunk {
    match chunk {
        Chunk::Basic(c) => Chunk::Basic(c.with_permission(permission, expression)),
        Chunk::MagicWand(c) => Chunk::MagicWand(c.with_permission(permission, expression)),
        _ => unreachable!("not a nonquantified chunk"),
    }
}
/// Literal argument matches are chosen before any solver-based aliases, in heap order.
pub fn find_chunk<P, D, J, S: ChunkSolver<P, D, J>>(
    solver: &mut S,
    heap: &ListBackedHeap,
    identifier: &ChunkIdentifier,
    arguments: &[Term],
) -> Result<Option<usize>, ChunkSupportError<S::Error>> {
    let relevant: Vec<_> = heap
        .values()
        .iter()
        .enumerate()
        .filter_map(|(i, c)| {
            chunk_data(c).and_then(|(id, args, _, _, _)| (id == *identifier).then_some((i, args)))
        })
        .collect();
    if let Some((index, _)) = relevant.iter().find(|(_, args)| *args == arguments) {
        return Ok(Some(*index));
    }
    let factory = solver.factory().clone();
    let timeout = solver.check_timeout();
    for (index, args) in relevant {
        if args.len() == arguments.len() {
            let equality = factory.and(
                args.iter()
                    .zip(arguments)
                    .map(|(a, b)| factory.equals(a.clone(), b.clone())),
            );
            if solver
                .check(&equality, timeout)
                .map_err(ChunkSupportError::Solver)?
            {
                return Ok(Some(index));
            }
        }
    }
    Ok(None)
}
/// Source split uses prepending for both outputs and rejects quantified chunks of this id.
pub fn split_heap(
    heap: &ListBackedHeap,
    identifier: &ChunkIdentifier,
) -> Result<(Vec<Chunk>, Vec<Chunk>), ChunkSupportError<std::convert::Infallible>> {
    let mut relevant = Vec::new();
    let mut other = Vec::new();
    for chunk in heap.values() {
        if let Some((id, _, _, _, _)) = chunk_data(chunk) {
            if &id == identifier {
                relevant.insert(0, chunk.clone());
                continue;
            }
        }
        let quantified_id = match chunk {
            Chunk::QuantifiedField(c) => Some(c.identifier()),
            Chunk::QuantifiedPredicate(c) => Some(c.identifier()),
            Chunk::QuantifiedMagicWand(c) => Some(c.identifier()),
            _ => None,
        };
        if quantified_id.as_ref() == Some(identifier) {
            return Err(ChunkSupportError::UnexpectedQuantifiedChunk);
        }
        other.insert(0, chunk.clone());
    }
    Ok((relevant, other))
}
/// Result of one greedy consume attempt; completion is a solver proof, never assumed.
pub struct GreedyConsumption<P, D, J> {
    pub result: ConsumptionResult,
    pub state: State<P, D, J>,
    pub heap: Arc<ListBackedHeap>,
    pub taken: Option<Chunk>,
}
pub fn consume_greedy<P, D, J: Clone, S: ChunkSolver<P, D, J>>(
    solver: &mut S,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    identifier: &ChunkIdentifier,
    arguments: &[Term],
    permission: Term,
    permission_exp: Option<Exp>,
) -> Result<GreedyConsumption<P, D, J>, ChunkSupportError<S::Error>> {
    let factory = solver.factory().clone();
    let exact = consume_exact_read(&permission, &state.constrainable_arps);
    let Some(index) = find_chunk(solver, &heap, identifier, arguments)? else {
        let complete = exact
            && state.retrying
            && solver
                .check(
                    &factory.equals(permission.clone(), factory.no_perm()),
                    solver.check_timeout(),
                )
                .map_err(ChunkSupportError::Solver)?;
        return Ok(GreedyConsumption {
            result: if complete {
                ConsumptionResult::Complete
            } else {
                ConsumptionResult::Incomplete {
                    perms_needed: permission,
                    perms_needed_exp: permission_exp,
                }
            },
            state,
            heap,
            taken: None,
        });
    };
    let chunk = heap.values()[index].clone();
    let (_, _, owned, owned_exp, _) = chunk_data(&chunk).expect("selected chunk");
    let owned = owned.clone();
    if state.assert_read_access_only {
        let condition = factory.implies(
            factory.is_positive_perm(permission.clone()),
            factory.is_positive_perm(owned),
        );
        let complete = solver
            .check(&condition, solver.assert_timeout())
            .map_err(ChunkSupportError::Solver)?;
        return Ok(GreedyConsumption {
            result: if complete {
                ConsumptionResult::Complete
            } else {
                ConsumptionResult::Incomplete {
                    perms_needed: permission,
                    perms_needed_exp: permission_exp,
                }
            },
            state,
            heap,
            taken: complete.then_some(chunk),
        });
    }
    if exact {
        let take = factory.perm_min(owned.clone(), permission.clone());
        let take_exp = if let Some(p) = &permission_exp {
            let own = owned_exp
                .clone()
                .ok_or(ChunkSupportError::MissingDebugPermission)?;
            let meta = ferrum_silver::ast::ast::Metadata {
                position: own.metadata().position.clone(),
                info: own.metadata().info.clone(),
                error_trafo: Default::default(),
            };
            Some(Exp::new(ExpKind::DebugPermMin(own, p.clone()), meta))
        } else {
            None
        };
        let new_exp = if let Some(p) = &permission_exp {
            Some(Exp::new(
                ExpKind::PermSub(
                    owned_exp
                        .clone()
                        .ok_or(ChunkSupportError::MissingDebugPermission)?,
                    take_exp
                        .clone()
                        .ok_or(ChunkSupportError::MissingDebugPermission)?,
                ),
                p.metadata().clone(),
            ))
        } else {
            None
        };
        let new_chunk = with_permission(&chunk, factory.perm_minus(owned, take.clone()), new_exp);
        let taken = with_permission(&chunk, take.clone(), take_exp.clone());
        let mut new_heap = heap.without_chunk(&chunk);
        let (_, _, new_permission, _, _) = chunk_data(&new_chunk).expect("new chunk");
        if !solver
            .check(
                &factory.equals(new_permission.clone(), factory.no_perm()),
                solver.check_timeout(),
            )
            .map_err(ChunkSupportError::Solver)?
        {
            new_heap = new_heap.with_chunk(new_chunk.clone());
            solver
                .assume_properties(&state, &new_heap, &new_chunk)
                .map_err(ChunkSupportError::Solver)?;
        }
        let remaining = factory.perm_minus(permission.clone(), take);
        let remaining_exp = if let Some(p) = &permission_exp {
            Some(Exp::new(
                ExpKind::PermSub(
                    p.clone(),
                    take_exp.ok_or(ChunkSupportError::MissingDebugPermission)?,
                ),
                p.metadata().clone(),
            ))
        } else {
            None
        };
        let result = ConsumptionResult::check(
            &factory,
            remaining,
            remaining_exp,
            &[],
            0,
            |term, timeout| solver.check(term, timeout),
        )
        .map_err(ChunkSupportError::Solver)?;
        return Ok(GreedyConsumption {
            result,
            state,
            heap: Arc::new(new_heap),
            taken: Some(taken),
        });
    }
    if solver
        .check(
            &factory.not(factory.equals(owned.clone(), factory.no_perm())),
            solver.check_timeout(),
        )
        .map_err(ChunkSupportError::Solver)?
    {
        let debug_constraint = if let Some(p) = &permission_exp {
            Some(Exp::new(
                ExpKind::PermLtCmp(
                    p.clone(),
                    owned_exp
                        .clone()
                        .ok_or(ChunkSupportError::MissingDebugPermission)?,
                ),
                p.metadata().clone(),
            ))
        } else {
            None
        };
        solver
            .assume(
                &factory.perm_less(permission.clone(), owned.clone()),
                debug_constraint.as_ref(),
            )
            .map_err(ChunkSupportError::Solver)?;
        let new_exp = if let Some(p) = &permission_exp {
            Some(Exp::new(
                ExpKind::PermSub(
                    owned_exp.ok_or(ChunkSupportError::MissingDebugPermission)?,
                    p.clone(),
                ),
                p.metadata().clone(),
            ))
        } else {
            None
        };
        let new_chunk = with_permission(
            &chunk,
            factory.perm_minus(owned, permission.clone()),
            new_exp,
        );
        let taken = with_permission(&chunk, permission.clone(), permission_exp.clone());
        let new_heap = heap.without_chunk(&chunk).with_chunk(new_chunk.clone());
        solver
            .assume_properties(&state, &new_heap, &new_chunk)
            .map_err(ChunkSupportError::Solver)?;
        Ok(GreedyConsumption {
            result: ConsumptionResult::Complete,
            state,
            heap: Arc::new(new_heap),
            taken: Some(taken),
        })
    } else {
        Ok(GreedyConsumption {
            result: ConsumptionResult::Incomplete {
                perms_needed: permission,
                perms_needed_exp: permission_exp,
            },
            state,
            heap,
            taken: None,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resources::resources::BaseId;
    use crate::state::{
        chunks::{BasicChunk, BasicChunkIdentifier},
        terms::{TermKind, TermOptions},
    };
    use ferrum_silver::ast::{ast::Metadata, program::Program};
    struct Solver {
        factory: TermFactory,
        checks: Vec<Term>,
    }
    impl ChunkSolver<(), (), ()> for Solver {
        type Error = ();
        fn factory(&self) -> &TermFactory {
            &self.factory
        }
        fn check(&mut self, term: &Term, _: i32) -> Result<bool, ()> {
            self.checks.push(term.clone());
            Ok(matches!(term.kind(), TermKind::True))
        }
        fn check_timeout(&self) -> i32 {
            10
        }
        fn assert_timeout(&self) -> i32 {
            20
        }
        fn assume(&mut self, _: &Term, _: Option<&Exp>) -> Result<(), ()> {
            Ok(())
        }
        fn assume_properties(
            &mut self,
            _: &State<(), (), ()>,
            _: &ListBackedHeap,
            _: &Chunk,
        ) -> Result<(), ()> {
            panic!("fully consumed chunk has no properties")
        }
    }
    #[test]
    fn exact_consumption_removes_empty_chunk_and_checks_completion() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let state = State::new(
            program,
            Default::default(),
            Default::default(),
            (),
            &factory,
            false,
            false,
        );
        let id = BasicChunkIdentifier("f".into());
        let chunk = Chunk::Basic(BasicChunk::new(
            BaseId::Field,
            id.clone(),
            vec![],
            None,
            factory.int_literal(8),
            None,
            factory.full_perm(),
            None,
            None,
        ));
        let heap = Arc::new(ListBackedHeap::from_chunks([chunk]));
        let mut solver = Solver {
            factory: factory.clone(),
            checks: Vec::new(),
        };
        let outcome = consume_greedy(
            &mut solver,
            state,
            heap,
            &ChunkIdentifier::Basic(id),
            &[],
            factory.full_perm(),
            None,
        )
        .unwrap();
        assert!(outcome.result.is_complete());
        assert!(outcome.heap.values().is_empty());
        assert!(outcome.taken.is_some());
        assert_eq!(solver.checks.len(), 2);
    }
}

#[derive(Debug)]
pub enum ChunkExecutionError<E> {
    Context(E),
    Greedy(ChunkSupportError<E>),
    UnexpectedTransferredChunk,
    MissingLookupSnapshot,
}
/// Runtime services for source retry, consolidation, quantified alternatives and wand transfer.
pub trait ChunkExecutionContext<P, D, J, V>: ChunkSolver<P, D, J> + Sized {
    type VerificationError;
    fn retry_chunk(
        &mut self,
        state: State<P, D, J>,
        action: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                State<P, D, J>,
                Arc<ListBackedHeap>,
                Option<Term>,
            ) -> Result<
                crate::interfaces::verification::VerificationResult<V>,
                ChunkExecutionError<Self::Error>,
            >,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        ChunkExecutionError<Self::Error>,
    >;
    fn consume_complete(
        &mut self,
        state: State<P, D, J>,
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
            State<P, D, J>,
            Arc<ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        ChunkExecutionError<Self::Error>,
    >;
    fn transfer_wand(
        &mut self,
        state: State<P, D, J>,
        permission: &Term,
        debug_permission: Option<&Exp>,
        identifier: &ChunkIdentifier,
        args: &[Term],
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Vec<Chunk>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        ChunkExecutionError<Self::Error>,
    >;
    fn smoke(&mut self, is_assert: bool) -> Result<bool, Self::Error>;
    fn consumption_failure(
        &mut self,
        state: &State<P, D, J>,
        error: &Self::VerificationError,
        description: &str,
        generate_model: bool,
    ) -> Result<crate::interfaces::verification::VerificationResult<V>, Self::Error>;
    fn fresh_snapshot(
        &mut self,
        sort: &crate::state::terms::Sort,
    ) -> Result<(Term, crate::state::terms::ApplicationTarget), Self::Error>;
    fn lookup_complete(
        &mut self,
        state: State<P, D, J>,
        heap: Arc<ListBackedHeap>,
        resource: &crate::state::terms::ResourceKey,
        args: &[Term],
        debug_args: Option<&[Exp]>,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Term,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            ChunkExecutionError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        ChunkExecutionError<Self::Error>,
    >;
    fn resource_snapshot_sort(
        &mut self,
        state: &State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
    ) -> Result<crate::state::terms::Sort, Self::Error>;
    fn merge_chunk(
        &mut self,
        state: &State<P, D, J>,
        heap: &ListBackedHeap,
        chunk: &Chunk,
    ) -> Result<
        (
            crate::supporters::functions::function_recorder::FunctionRecorder<D>,
            ListBackedHeap,
        ),
        Self::Error,
    >;
}
/// Source outer consume converts consumed values to Snap and creates a tracked fresh Snap if empty.
pub fn consume<P, D, J: Clone, V, C: ChunkExecutionContext<P, D, J, V>>(
    context: &mut C,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    resource: &crate::state::terms::ResourceKey,
    identifier: &ChunkIdentifier,
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
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        ChunkExecutionError<C::Error>,
    >,
) -> Result<crate::interfaces::verification::VerificationResult<V>, ChunkExecutionError<C::Error>> {
    use crate::interfaces::verification::VerificationResult;
    let factory = context.factory().clone();
    let mut outer = |context: &mut C, mut state: State<P, D, J>, heap, snapshot: Option<Term>| {
        let snapshot = match snapshot {
            Some(snapshot) => Some(factory.sort_wrapper(snapshot, crate::state::terms::Sort::Snap)),
            None if return_snapshot => {
                let (fresh, target) = context
                    .fresh_snapshot(&crate::state::terms::Sort::Snap)
                    .map_err(ChunkExecutionError::Context)?;
                state.function_recorder = state.function_recorder.record_fresh_snapshot(target);
                Some(fresh)
            }
            None => None,
        };
        continuation(context, state, heap, snapshot)
    };
    if state.exhale_ext {
        let original_heap = heap.clone();
        return context.transfer_wand(
            state,
            permission,
            debug_permission,
            identifier,
            args,
            error,
            &mut |context, state, chunks| {
                let snap = if return_snapshot {
                    match chunks.last() {
                        Some(chunk) => Some(
                            chunk_data(chunk)
                                .ok_or(ChunkExecutionError::UnexpectedTransferredChunk)?
                                .4
                                .clone(),
                        ),
                        None => None,
                    }
                } else {
                    None
                };
                outer(context, state, original_heap.clone(), snap)
            },
        );
    }
    let original_heap = state.h.clone();
    let mut retry_state = state;
    retry_state.h = heap;
    context.retry_chunk(
        retry_state,
        &mut |context, state, done| {
            if state.more_complete_exhale {
                let heap = state.h.clone();
                context.consume_complete(
                    state,
                    heap,
                    resource,
                    args,
                    debug_args,
                    permission,
                    debug_permission,
                    return_snapshot,
                    error,
                    &mut |context, mut state, heap, snap| {
                        state.h = original_heap.clone();
                        done(context, state, heap, snap)
                    },
                )
            } else {
                let heap = state.h.clone();
                let outcome = consume_greedy(
                    context,
                    state,
                    heap,
                    identifier,
                    args,
                    permission.clone(),
                    debug_permission.cloned(),
                )
                .map_err(ChunkExecutionError::Greedy)?;
                if outcome.result.is_complete() {
                    let snapshot = if return_snapshot {
                        if let Some(chunk) = outcome.taken.as_ref() {
                            let snap = chunk_data(chunk).expect("taken chunk").4.clone();
                            let positive = factory.is_positive_perm(permission.clone());
                            if context
                                .check(&positive, context.check_timeout())
                                .map_err(ChunkExecutionError::Context)?
                            {
                                Some(snap)
                            } else {
                                Some(factory.ite(
                                    positive,
                                    factory.sort_wrapper(snap, crate::state::terms::Sort::Snap),
                                    factory.unit(),
                                ))
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    let mut state = outcome.state;
                    state.h = original_heap.clone();
                    done(context, state, outcome.heap, snapshot)
                } else if context.smoke(true).map_err(ChunkExecutionError::Context)? {
                    Ok(VerificationResult::success())
                } else {
                    context
                        .consumption_failure(&outcome.state, error, "consuming chunk", true)
                        .map_err(ChunkExecutionError::Context)
                }
            }
        },
        &mut outer,
    )
}
/// Merge the incoming chunk through the state consolidator before continuing.
pub fn produce<P, D, J: Clone, V, C: ChunkExecutionContext<P, D, J, V>>(
    context: &mut C,
    mut state: State<P, D, J>,
    heap: &ListBackedHeap,
    chunk: &Chunk,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        ChunkExecutionError<C::Error>,
    >,
) -> Result<crate::interfaces::verification::VerificationResult<V>, ChunkExecutionError<C::Error>> {
    let (recorder, heap) = context
        .merge_chunk(&state, heap, chunk)
        .map_err(ChunkExecutionError::Context)?;
    state.function_recorder = recorder;
    continuation(context, state, Arc::new(heap))
}

/// Source lookup retries on the temporary consume heap; dead packaging paths receive a fresh snapshot.
pub fn lookup<P, D, J: Clone, V, C: ChunkExecutionContext<P, D, J, V>>(
    context: &mut C,
    state: State<P, D, J>,
    heap: Arc<ListBackedHeap>,
    resource: &crate::state::terms::ResourceKey,
    identifier: &ChunkIdentifier,
    args: &[Term],
    debug_args: Option<&[Exp]>,
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        Arc<ListBackedHeap>,
        Term,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        ChunkExecutionError<C::Error>,
    >,
) -> Result<crate::interfaces::verification::VerificationResult<V>, ChunkExecutionError<C::Error>> {
    use crate::interfaces::verification::VerificationResult;
    let original_heap = state.h.clone();
    let mut retry_state = state;
    retry_state.h = heap;
    context.retry_chunk(
        retry_state,
        &mut |context, state, done| {
            if state.more_complete_exhale {
                let heap = state.h.clone();
                context.lookup_complete(
                    state,
                    heap,
                    resource,
                    args,
                    debug_args,
                    error,
                    &mut |context, mut state, snapshot| {
                        let heap = state.h.clone();
                        state.h = original_heap.clone();
                        done(context, state, heap, Some(snapshot))
                    },
                )
            } else {
                let heap = state.h.clone();
                let factory = context.factory().clone();
                let found = find_chunk(context, &heap, identifier, args)
                    .map_err(ChunkExecutionError::Greedy)?;
                if let Some(index) = found {
                    let (_, _, permission, _, snapshot) =
                        chunk_data(&heap.values()[index]).expect("selected chunk");
                    if context
                        .check(
                            &factory.is_positive_perm(permission.clone()),
                            context.assert_timeout(),
                        )
                        .map_err(ChunkExecutionError::Context)?
                    {
                        let snapshot = snapshot.clone();
                        let mut state = state;
                        state.h = original_heap.clone();
                        return done(context, state, heap, Some(snapshot));
                    }
                }
                if context.smoke(true).map_err(ChunkExecutionError::Context)? {
                    if state.is_in_package {
                        let sort = context
                            .resource_snapshot_sort(&state, resource)
                            .map_err(ChunkExecutionError::Context)?;
                        let (snapshot, _) = context
                            .fresh_snapshot(&sort)
                            .map_err(ChunkExecutionError::Context)?;
                        let mut state = state;
                        state.h = original_heap.clone();
                        return done(context, state, heap, Some(snapshot));
                    }
                    Ok(VerificationResult::success())
                } else {
                    context
                        .consumption_failure(&state, error, "looking up chunk", true)
                        .map_err(ChunkExecutionError::Context)
                }
            }
        },
        &mut |context, state, heap, snapshot| {
            continuation(
                context,
                state,
                heap,
                snapshot.ok_or(ChunkExecutionError::MissingLookupSnapshot)?,
            )
        },
    )
}
