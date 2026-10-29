//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Joiner.scala
//!
//! Purpose:
//! Collect local branch results and join states with their path conditions.
//!
//! Planned Rust structure:
//! JoinDataEntry supports path-condition-aware merge with or without consolidation; JoiningRules
//! and joiner.join collect entries via local execution, a merge callback and continuation Q.
//!
//! Behavior to preserve:
//! Reset selected store, heap, join, cache, partially consumed heap, invariant and retry fields
//! when requested; no collected entries returns Success without Q. Otherwise merge, optionally
//! record debug heap, assume each conditionalized path and disjunction of feasible branch
//! conditions, then invoke Q. Preserve ordered collection and result combine.
//!
//! Integration:
//! rules::execution_flow_controller, rules::brancher, state::state and decider::path_conditions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Join callbacks, result sequencing and context ownership.
//!
//! Status: partial; join data, source state restoration and conditionalized paths implemented.
//! Full orchestration uses explicit context callbacks for debug, consolidation and solver ownership.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::decider::path_conditions::RecordedPathConditions;
use crate::state::state::{State, StateMergeError};
use crate::state::terms::{Term, TermFactory};

#[derive(Clone, Debug)]
pub struct JoinDataEntry<P, D, J, T> {
    pub state: State<P, D, J>,
    pub data: T,
    pub path_conditions: RecordedPathConditions,
}
impl<P, D, J: Clone + PartialEq, T> JoinDataEntry<P, D, J, T> {
    pub fn merge_without_consolidation(
        &self,
        other: &Self,
        factory: &TermFactory,
        debugging: bool,
        warn: &mut impl FnMut(String),
    ) -> Result<State<P, D, J>, StateMergeError> {
        self.state.merge_recorded(
            &self.path_conditions,
            &other.state,
            &other.path_conditions,
            factory,
            debugging,
            warn,
        )
    }
    pub fn merge_with_consolidation<E>(
        &self,
        other: &Self,
        factory: &TermFactory,
        debugging: bool,
        warn: &mut impl FnMut(String),
        consolidate: impl FnOnce(State<P, D, J>) -> Result<State<P, D, J>, E>,
    ) -> Result<State<P, D, J>, JoinMergeError<E>> {
        let merged = self
            .merge_without_consolidation(other, factory, debugging, warn)
            .map_err(JoinMergeError::State)?;
        consolidate(merged).map_err(JoinMergeError::Consolidation)
    }
}
#[derive(Debug)]
pub enum JoinMergeError<E> {
    State(StateMergeError),
    Consolidation(E),
}
/// The exact state fields restored by the source joiner. This snapshot contains
/// no verifier, solver or generic supporter data and can travel with a value receiver.
#[derive(Clone)]
pub struct JoinRestoreState {
    store: std::sync::Arc<crate::state::store::MapBackedStore>,
    heap: std::sync::Arc<crate::state::heap::ListBackedHeap>,
    under_join: bool,
    ss_cache: crate::state::package::SsCache,
    partial_heap: Option<std::sync::Arc<crate::state::heap::ListBackedHeap>>,
    invariants: Vec<std::sync::Arc<crate::state::heap::ListBackedHeap>>,
    retrying: bool,
}
impl JoinRestoreState {
    pub fn capture<P, D, J>(initial: &State<P, D, J>) -> Self {
        Self {
            store: initial.g.clone(),
            heap: initial.h.clone(),
            under_join: initial.under_join,
            ss_cache: initial.ss_cache.clone(),
            partial_heap: initial.partially_consumed_heap.clone(),
            invariants: initial.invariant_contexts.clone(),
            retrying: initial.retrying,
        }
    }
    pub fn restore<P, D, J>(&self, state: State<P, D, J>) -> State<P, D, J> {
        self.clone().restore_owned(state)
    }
    fn restore_owned<P, D, J>(self, mut state: State<P, D, J>) -> State<P, D, J> {
        state.g = self.store;
        state.h = self.heap;
        state.under_join = self.under_join;
        state.ss_cache = self.ss_cache;
        state.partially_consumed_heap = self.partial_heap;
        state.invariant_contexts = self.invariants;
        state.retrying = self.retrying;
        state
    }
}
/// Reset only the state properties explicitly restored by the source joiner.
pub fn restore_state<P, D, J: Clone>(
    final_state: State<P, D, J>,
    initial: &State<P, D, J>,
) -> State<P, D, J> {
    JoinRestoreState::capture(initial).restore_owned(final_state)
}
/// Returns each branch's conditional assumptions and the disjunction of feasible branches.
/// Source prepends each branch condition, hence the final disjunction uses reverse entry order.
pub fn joined_conditions<P, D, J, T>(
    entries: &[JoinDataEntry<P, D, J, T>],
    factory: &TermFactory,
) -> (Vec<Vec<Term>>, Term) {
    let assumptions = entries
        .iter()
        .map(|entry| entry.path_conditions.conditionalized(factory))
        .collect();
    let feasible = factory.or(entries
        .iter()
        .rev()
        .map(|entry| factory.and(entry.path_conditions.branch_conditions())));
    (assumptions, feasible)
}

/// Verifier-owned path scopes, logging and solver assumptions needed by source joining.
pub trait JoinContext<P, D, J>: crate::rules::execution_flow_controller::ScopedContext {
    type Mark: Clone;
    fn open_join(&mut self, state: &State<P, D, J>) -> Result<(), Self::Error>;
    fn close_join(&mut self) -> Result<(), Self::Error>;
    fn mark(&mut self) -> Self::Mark;
    fn after(&mut self, mark: &Self::Mark) -> Result<RecordedPathConditions, Self::Error>;
    fn record_joined_state(&mut self, state: State<P, D, J>)
    -> Result<State<P, D, J>, Self::Error>;
    /// Emit the source comment, conditional assumptions and any corresponding debug expressions.
    fn assume_joined_path(
        &mut self,
        conditions: &RecordedPathConditions,
        terms: &[Term],
    ) -> Result<(), Self::Error>;
    /// Also creates the source feasible-branches debug expression where enabled.
    fn assume_feasible(
        &mut self,
        branches: &[RecordedPathConditions],
        term: &Term,
    ) -> Result<(), Self::Error>;
}
/// A block can branch and invoke its collector once for each reachable path.
pub trait JoinBlock<C, P, D, J, T, V>
where
    C: JoinContext<P, D, J>,
{
    fn run(
        &mut self,
        context: &mut C,
        state: State<P, D, J>,
        collect: &mut dyn FnMut(
            &mut C,
            State<P, D, J>,
            T,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            C::Error,
        >,
    ) -> Result<crate::interfaces::verification::VerificationResult<V>, C::Error>;
}
#[derive(Debug)]
pub enum JoinExecutionError<E> {
    Context(E),
    BlockAndCleanup { block: E, cleanup: E },
}
/// Join actual branch outcomes; an empty set terminates the path with source Success.
/// Context callbacks own verifier-specific state consolidation, debug terms and solver lifecycle.
pub fn join<C, P, D, J: Clone, T, Joined, V, B>(
    context: &mut C,
    initial: State<P, D, J>,
    reset: bool,
    factory: &TermFactory,
    block: &mut B,
    merge: impl FnOnce(
        &mut C,
        &[JoinDataEntry<P, D, J, T>],
    ) -> Result<(State<P, D, J>, Joined), C::Error>,
    continuation: impl FnOnce(
        &mut C,
        State<P, D, J>,
        Joined,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        C::Error,
    >,
) -> Result<crate::interfaces::verification::VerificationResult<V>, JoinExecutionError<C::Error>>
where
    C: JoinContext<P, D, J>,
    B: JoinBlock<C, P, D, J, T, V>,
{
    use crate::interfaces::verification::VerificationResult;
    context
        .open_join(&initial)
        .map_err(JoinExecutionError::Context)?;
    context.push_scope().map_err(JoinExecutionError::Context)?;
    let mark = context.mark();
    let mut under_join = initial.clone();
    under_join.under_join = true;
    let mut entries = Vec::new();
    let block_result = block.run(context, under_join, &mut |context, state, data| {
        let state = if reset {
            restore_state(state, &initial)
        } else {
            state
        };
        entries.push(JoinDataEntry {
            state,
            data,
            path_conditions: context.after(&mark)?,
        });
        Ok(VerificationResult::success())
    });
    let cleanup = context.pop_scope();
    let block_result = match (block_result, cleanup) {
        (Ok(result), Ok(())) => result,
        (Err(block), Err(cleanup)) => {
            return Err(JoinExecutionError::BlockAndCleanup { block, cleanup });
        }
        (Err(error), Ok(())) | (Ok(_), Err(error)) => {
            return Err(JoinExecutionError::Context(error));
        }
    };
    // locally() wraps its inner result in a successful local result and combines histories.
    let local_result = VerificationResult::success().and_then(|| block_result);
    if !local_result.continue_verification() {
        return Ok(local_result);
    }
    context.close_join().map_err(JoinExecutionError::Context)?;
    let result = if entries.is_empty() {
        VerificationResult::success()
    } else {
        let (state, data) = merge(context, &entries).map_err(JoinExecutionError::Context)?;
        let state = context
            .record_joined_state(state)
            .map_err(JoinExecutionError::Context)?;
        let (conditions, feasible) = joined_conditions(&entries, factory);
        for (entry, terms) in entries.iter().zip(&conditions) {
            context
                .assume_joined_path(&entry.path_conditions, terms)
                .map_err(JoinExecutionError::Context)?;
        }
        let paths: Vec<_> = entries
            .iter()
            .map(|entry| entry.path_conditions.clone())
            .collect();
        context
            .assume_feasible(&paths, &feasible)
            .map_err(JoinExecutionError::Context)?;
        continuation(context, state, data).map_err(JoinExecutionError::Context)?
    };
    Ok(local_result.combine(|| result, false))
}
