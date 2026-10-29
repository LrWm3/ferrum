//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Producer.scala
//!
//! Purpose:
//! Produce assertions and permissions into symbolic state using snapshot functions.
//!
//! Planned Rust structure:
//! ProductionRules and producer implement produce/produces, recursive produceR, ordered
//! produceTlcs, wrappedProduceTlc and produceTlc. Dispatch impure implication/conditional with
//! branch or more-joins, impure let, ordinary access, quantified permissions, invalid inhale-exhale
//! node and pure expressions.
//!
//! Behavior to preserve:
//! Select whenInhaling, adapt and split snapshot functions per conjunct, retaining error
//! attribution and order. If snapshot pairing throws illegal argument, return Unreachable only when
//! solver proves False; otherwise propagate exception. Implication false branch assumes empty
//! snapshot constraint. Extended exhale updates reserve heap before Q. Access evaluates args then
//! permissions, checks nonnegative, restores ARPs, scales permissions with configured wildcard
//! optimization and produces a chunk. Quantified path tracks recorder and delegates
//! injectivity/negative-permission checks; pure expression assumes its value after empty snapshot
//! constraint. Preserve impure join consolidation differences and logging scope.
//!
//! Integration:
//! rules::consumer, evaluator, brancher, joiner, heap_supporter, permission_supporter and
//! supporters::snapshot_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Snapshot-function, continuation and branch context ownership with consumer.
//!
//! Status: partial; CPS conjunct production, snapshot splitting and pure assertions implemented.
//! Ordinary and quantified access sequencing, impure branches and let composition implemented.
//! Quantifier evaluation, heap mutation and verifier services remain integration boundaries.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::verification::VerificationResult;
use crate::state::{state::State, terms::Term};
use ferrum_silver::ast::{
    expression::{Exp, ExpKind},
    utility::expressions::{UnsupportedExtensionProjection, when_inhaling},
};

#[derive(Debug)]
pub enum ProductionError<E> {
    Context(E),
    Projection(UnsupportedExtensionProjection),
    InvalidSnapshotSplit,
    MissingPredicate(String),
    Wand(ferrum_silver::ast::utility::expressions::MagicWandError),
    MissingDebugExpression,
    OwnedSchedulerUnavailable,
}
#[derive(Clone, Debug)]
pub struct QuantifiedProductionData {
    pub qvars: Vec<Term>,
    pub qvar_expressions: Option<Vec<ferrum_silver::ast::program::LocalVarDecl>>,
    pub condition: Term,
    pub condition_exp: Option<Exp>,
    pub permission: Term,
    pub permission_exp: Option<Exp>,
    pub arguments: Vec<Term>,
    pub argument_expressions: Option<Vec<Exp>>,
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
/// A projected assertion suffix and its snapshot, retained across branch jobs.
#[derive(Clone)]
pub enum OwnedProductionRemainder<S, E> {
    Assertions {
        snapshot: S,
        assertions: Vec<Exp>,
        errors: Vec<E>,
    },
    Finish {
        conditional: bool,
    },
}

#[derive(Clone)]
pub enum OwnedProductionTerminal {
    Inhale(crate::rules::executor::CfgStatementTail),
    MethodPre(crate::supporters::method_supporter::MethodPreContinuation),
    MethodWellformed,
    CallPost(crate::rules::executor::MethodCallPreFrame),
    Unfold(crate::rules::predicate_supporter::OwnedUnfoldFinish),
}

/// Complete non-joined producer branch and the explicitly owned statement tail.
#[derive(Clone)]
pub struct OwnedProductionAction<S, E> {
    pub snapshot: S,
    pub body: Option<Exp>,
    pub error: E,
    pub remaining: Vec<OwnedProductionRemainder<S, E>>,
    pub tail: OwnedProductionTerminal,
}

/// Verifier-owned evaluator, brancher, heap supporter, snapshot functions and logging.
pub trait ProductionContext<P, D, J, V>: Sized {
    type Error;
    type PartialError: Clone;
    type Snapshot: Clone;
    fn supports_owned_production(&self, _state: &State<P, D, J>) -> bool {
        false
    }
    fn try_branch_owned_production(
        &mut self,
        _state: &State<P, D, J>,
        _condition: &Term,
        _original: &Exp,
        _rewritten: Option<&Exp>,
        _yes: OwnedProductionAction<Self::Snapshot, Self::PartialError>,
        _no: OwnedProductionAction<Self::Snapshot, Self::PartialError>,
    ) -> Option<Result<VerificationResult<V>, ProductionError<Self::Error>>> {
        None
    }
    fn finish_owned_production(
        &mut self,
        _state: State<P, D, J>,
        _tail: &OwnedProductionTerminal,
    ) -> Result<VerificationResult<V>, ProductionError<Self::Error>> {
        Err(ProductionError::OwnedSchedulerUnavailable)
    }
    fn adapt_snapshot(
        &mut self,
        state: &State<P, D, J>,
        snapshot: Self::Snapshot,
        assertions: &[Exp],
    ) -> Result<Self::Snapshot, Self::Error>;
    /// None denotes source's unit-snapshot decomposition error.
    fn split_snapshot(
        &mut self,
        state: &State<P, D, J>,
        snapshot: &Self::Snapshot,
        first: &Exp,
        rest: &[Exp],
    ) -> Result<Option<(Self::Snapshot, Self::Snapshot)>, Self::Error>;
    fn assert_false(&mut self) -> Result<bool, Self::Error>;
    fn open_produce(&mut self, state: &State<P, D, J>, assertion: &Exp) -> Result<(), Self::Error>;
    fn close_produce(&mut self) -> Result<(), Self::Error>;
    /// Return the source scope ID, retaining legacy disabled-log behavior by default.
    fn open_produce_scope(
        &mut self,
        state: &State<P, D, J>,
        assertion: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        self.open_produce(state, assertion)?;
        Ok(None)
    }
    fn close_produce_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        self.close_produce()
    }

    /// Source impure implication or conditional-expression scope.
    fn open_production_conditional_scope(
        &mut self,
        _state: &State<P, D, J>,
        _assertion: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn close_production_conditional_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn assume_empty_snapshot(
        &mut self,
        state: &State<P, D, J>,
        snapshot: &Self::Snapshot,
    ) -> Result<(), Self::Error>;
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
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ProductionError<Self::Error>>;
    fn assume(
        &mut self,
        term: &Term,
        original: &Exp,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn factory(&self) -> &crate::state::terms::TermFactory;
    fn debugging(&self) -> bool;
    fn unsafe_wildcard_optimization(&self) -> bool;
    fn snapshot_for_resource(
        &mut self,
        state: &State<P, D, J>,
        snapshot: &Self::Snapshot,
        resource: &crate::state::terms::ResourceKey,
    ) -> Result<Term, Self::Error>;
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
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ProductionError<Self::Error>>;
    fn produce_single(
        &mut self,
        state: State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
        arguments: &[Term],
        argument_expressions: Option<&[Exp]>,
        snapshot: Term,
        gain: Term,
        gain_exp: Option<Exp>,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ProductionError<Self::Error>>;
    /// Execute and optionally join the two source branches; the context owns verifier scopes.
    /// Joined implications merge without consolidation; joined conditionals consolidate.
    fn branch_production(
        &mut self,
        state: State<P, D, J>,
        condition: Term,
        original: &Exp,
        rewritten: Option<&Exp>,
        join: bool,
        consolidate_on_merge: bool,
        when_true: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                State<P, D, J>,
            )
                -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
        when_false: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                State<P, D, J>,
            )
                -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ProductionError<Self::Error>>;
    fn join_impure(&self, state: &State<P, D, J>) -> bool;
    /// Delegate evaluation of nested let bindings to the shared continuation-driven let supporter.
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
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ProductionError<Self::Error>>;
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
            Option<QuantifiedProductionData>,
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ProductionError<Self::Error>>;
    fn produce_quantified(
        &mut self,
        state: State<P, D, J>,
        snapshot: &Self::Snapshot,
        forall: &Exp,
        resource: &crate::state::terms::ResourceKey,
        qid: &str,
        data: &QuantifiedProductionData,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ProductionError<Self::Error>>;
    /// Handles impure implications, conditionals, lets, resource and quantified permissions.
    fn produce_special(
        &mut self,
        state: State<P, D, J>,
        snapshot: &Self::Snapshot,
        assertion: &Exp,
        error: &Self::PartialError,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ProductionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ProductionError<Self::Error>>;
}
/// Project inhale/exhale expressions and preserve each original assertion's error context.
pub fn produce_all<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    snapshot: C::Snapshot,
    assertions: &[Exp],
    error_for: &impl Fn(&Exp) -> C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    let mut conjuncts = Vec::new();
    let mut errors = Vec::new();
    for assertion in assertions {
        let projected = when_inhaling(assertion).map_err(ProductionError::Projection)?;
        let parts = projected.top_level_conjuncts();
        let error = error_for(assertion);
        errors.extend(std::iter::repeat_n(error, parts.len()));
        conjuncts.extend(parts);
    }
    let snapshot = context
        .adapt_snapshot(&state, snapshot, &conjuncts)
        .map_err(ProductionError::Context)?;
    produce_conjuncts(context, state, snapshot, &conjuncts, &errors, continuation)
}
/// Production from a direct CFG inhale with an explicitly transferable caller.
pub(crate) fn produce_all_owned<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    snapshot: C::Snapshot,
    assertions: &[Exp],
    error_for: &impl Fn(&Exp) -> C::PartialError,
    tail: &OwnedProductionTerminal,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    let mut conjuncts = Vec::new();
    let mut errors = Vec::new();
    for assertion in assertions {
        let projected = when_inhaling(assertion).map_err(ProductionError::Projection)?;
        let parts = projected.top_level_conjuncts();
        let error = error_for(assertion);
        errors.extend(std::iter::repeat_n(error, parts.len()));
        conjuncts.extend(parts);
    }
    let assertions = conjuncts;
    let snapshot = context
        .adapt_snapshot(&state, snapshot, &assertions)
        .map_err(ProductionError::Context)?;
    produce_owned_conjuncts(
        context,
        state,
        snapshot,
        &assertions,
        &errors,
        &[],
        tail,
        continuation,
    )
}

fn produce_owned_conjuncts<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    snapshot: C::Snapshot,
    assertions: &[Exp],
    errors: &[C::PartialError],
    remaining: &[OwnedProductionRemainder<C::Snapshot, C::PartialError>],
    tail: &OwnedProductionTerminal,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    let Some((first, rest)) = assertions.split_first() else {
        return resume_owned_production(context, state, remaining, tail, continuation);
    };
    let first = when_inhaling(first).map_err(ProductionError::Projection)?;
    let (left, pending) = if rest.is_empty() {
        (snapshot, remaining.to_vec())
    } else {
        let Some((left, right)) = context
            .split_snapshot(&state, &snapshot, &first, rest)
            .map_err(ProductionError::Context)?
        else {
            return if context.assert_false().map_err(ProductionError::Context)? {
                Ok(VerificationResult::unreachable())
            } else {
                Err(ProductionError::InvalidSnapshotSplit)
            };
        };
        let mut pending = vec![OwnedProductionRemainder::Assertions {
            snapshot: right,
            assertions: rest.to_vec(),
            errors: errors[1..].to_vec(),
        }];
        pending.extend_from_slice(remaining);
        (left, pending)
    };
    let conditional = if !first.is_pure() {
        match first.kind() {
            ExpKind::Implies(condition, yes) => Some((condition, yes, None)),
            ExpKind::CondExp(condition, yes, no) => Some((condition, yes, Some(no))),
            _ => None,
        }
    } else {
        None
    };
    if let Some((condition, yes, no)) = conditional {
        if context.supports_owned_production(&state) && !context.join_impure(&state) {
            let scope = context
                .open_produce_scope(&state, &first)
                .map_err(ProductionError::Context)?;
            let conditional_scope = context
                .open_production_conditional_scope(&state, &first)
                .map_err(ProductionError::Context)?;
            if scope.is_some() || conditional_scope.is_some() {
                return Err(ProductionError::OwnedSchedulerUnavailable);
            }
            return context.evaluate(
                state,
                condition,
                &errors[0],
                &mut |context, state, term, rewritten| {
                    let mk = |body| {
                        let mut remaining =
                            vec![OwnedProductionRemainder::Finish { conditional: true }];
                        remaining.extend_from_slice(&pending);
                        OwnedProductionAction {
                            snapshot: left.clone(),
                            body,
                            error: errors[0].clone(),
                            remaining,
                            tail: tail.clone(),
                        }
                    };
                    context
                        .try_branch_owned_production(
                            &state,
                            &term,
                            condition,
                            rewritten.as_ref(),
                            mk(Some(yes.clone())),
                            mk(no.cloned()),
                        )
                        .ok_or(ProductionError::OwnedSchedulerUnavailable)?
                },
            );
        }
    }
    if !first.is_pure()
        && matches!(first.kind(), ExpKind::Let(..))
        && context.supports_owned_production(&state)
    {
        let scope = context
            .open_produce_scope(&state, &first)
            .map_err(ProductionError::Context)?;
        if scope.is_some() {
            return Err(ProductionError::OwnedSchedulerUnavailable);
        }
        return context.handle_let(
            state,
            &first,
            &errors[0],
            &mut |context, mut state, bindings, body| {
                state.g = std::sync::Arc::new(state.g.with_store(&bindings));
                let assertions = body.top_level_conjuncts();
                let body_errors = vec![errors[0].clone(); assertions.len()];
                let mut next = vec![OwnedProductionRemainder::Finish { conditional: false }];
                next.extend_from_slice(&pending);
                produce_owned_conjuncts(
                    context,
                    state,
                    left.clone(),
                    &assertions,
                    &body_errors,
                    &next,
                    tail,
                    continuation,
                )
            },
        );
    }
    produce_one(
        context,
        state,
        &left,
        &first,
        &errors[0],
        &mut |context, state| resume_owned_production(context, state, &pending, tail, continuation),
    )
}

fn resume_owned_production<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    remaining: &[OwnedProductionRemainder<C::Snapshot, C::PartialError>],
    tail: &OwnedProductionTerminal,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    let Some((first, later)) = remaining.split_first() else {
        return continuation(context, state);
    };
    match first {
        OwnedProductionRemainder::Assertions {
            snapshot,
            assertions,
            errors,
        } => produce_owned_conjuncts(
            context,
            state,
            snapshot.clone(),
            assertions,
            errors,
            later,
            tail,
            continuation,
        ),
        OwnedProductionRemainder::Finish { conditional } => {
            if *conditional {
                context
                    .close_production_conditional_scope(None)
                    .map_err(ProductionError::Context)?;
            }
            if state.exhale_ext {
                if state.reserve_heaps.is_empty() {
                    state.reserve_heaps.push(state.h.clone());
                } else {
                    state.reserve_heaps[0] = state.h.clone();
                }
            }
            context
                .close_produce_scope(None)
                .map_err(ProductionError::Context)?;
            resume_owned_production(context, state, later, tail, continuation)
        }
    }
}

/// Execute a transferred producer branch, including all owned assertion and statement tails.
pub(crate) fn execute_owned_production_action<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    action: &OwnedProductionAction<C::Snapshot, C::PartialError>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    // The captured frames retain the success-only source scope closes.
    if let Some(body) = &action.body {
        let assertions = body.top_level_conjuncts();
        let errors = vec![action.error.clone(); assertions.len()];
        produce_owned_conjuncts(
            context,
            state,
            action.snapshot.clone(),
            &assertions,
            &errors,
            &action.remaining,
            &action.tail,
            &mut |context, state| context.finish_owned_production(state, &action.tail),
        )
    } else {
        context
            .assume_empty_snapshot(&state, &action.snapshot)
            .map_err(ProductionError::Context)?;
        resume_owned_production(
            context,
            state,
            &action.remaining,
            &action.tail,
            &mut |context, state| context.finish_owned_production(state, &action.tail),
        )
    }
}

/// Recursive entries project and split again, preserving conditional-body conjuncts.
pub fn produce_recursive<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    snapshot: C::Snapshot,
    assertion: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    let conjuncts = assertion.top_level_conjuncts();
    let errors = vec![error.clone(); conjuncts.len()];
    produce_conjuncts(context, state, snapshot, &conjuncts, &errors, continuation)
}
fn produce_conjuncts<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    snapshot: C::Snapshot,
    assertions: &[Exp],
    errors: &[C::PartialError],
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    let Some((first, rest)) = assertions.split_first() else {
        return continuation(context, state);
    };
    let first = when_inhaling(first).map_err(ProductionError::Projection)?;
    if rest.is_empty() {
        return produce_one(context, state, &snapshot, &first, &errors[0], continuation);
    }
    let split = context
        .split_snapshot(&state, &snapshot, &first, rest)
        .map_err(ProductionError::Context)?;
    let Some((left, right)) = split else {
        return if context.assert_false().map_err(ProductionError::Context)? {
            Ok(VerificationResult::unreachable())
        } else {
            Err(ProductionError::InvalidSnapshotSplit)
        };
    };
    produce_one(
        context,
        state,
        &left,
        &first,
        &errors[0],
        &mut |context, state| {
            produce_conjuncts(
                context,
                state,
                right.clone(),
                rest,
                &errors[1..],
                continuation,
            )
        },
    )
}
fn produce_one<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    snapshot: &C::Snapshot,
    assertion: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    let scope = context
        .open_produce_scope(&state, assertion)
        .map_err(ProductionError::Context)?;
    let mut finish = |context: &mut C, mut state: State<P, D, J>| {
        if state.exhale_ext {
            if state.reserve_heaps.is_empty() {
                state.reserve_heaps.push(state.h.clone());
            } else {
                state.reserve_heaps[0] = state.h.clone();
            }
        }
        context
            .close_produce_scope(scope)
            .map_err(ProductionError::Context)?;
        continuation(context, state)
    };
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
                .open_production_conditional_scope(&state, assertion)
                .map_err(ProductionError::Context)?;
            return context.evaluate(
                state,
                condition,
                error,
                &mut |context, state, term, rewritten| {
                    let join = context.join_impure(&state);
                    context.branch_production(
                        state,
                        term,
                        condition,
                        rewritten.as_ref(),
                        join,
                        no.is_some(),
                        &mut |context, state, done| {
                            produce_recursive(
                                context,
                                state,
                                snapshot.clone(),
                                yes,
                                error,
                                &mut |context, state| {
                                    context
                                        .close_production_conditional_scope(conditional_scope)
                                        .map_err(ProductionError::Context)?;
                                    done(context, state)
                                },
                            )
                        },
                        &mut |context, state, done| {
                            if let Some(no) = no {
                                produce_recursive(
                                    context,
                                    state,
                                    snapshot.clone(),
                                    no,
                                    error,
                                    &mut |context, state| {
                                        context
                                            .close_production_conditional_scope(conditional_scope)
                                            .map_err(ProductionError::Context)?;
                                        done(context, state)
                                    },
                                )
                            } else {
                                context
                                    .assume_empty_snapshot(&state, snapshot)
                                    .map_err(ProductionError::Context)?;
                                context
                                    .close_production_conditional_scope(conditional_scope)
                                    .map_err(ProductionError::Context)?;
                                done(context, state)
                            }
                        },
                        &mut finish,
                    )
                },
            );
        }
    }
    if !assertion.is_pure() && matches!(assertion.kind(), ExpKind::Let(..)) {
        return context.handle_let(
            state,
            assertion,
            error,
            &mut |context, mut state, bindings, body| {
                state.g = std::sync::Arc::new(state.g.with_store(&bindings));
                produce_recursive(context, state, snapshot.clone(), &body, error, &mut finish)
            },
        );
    }
    if matches!(
        assertion.kind(),
        ExpKind::FieldAccessPredicate(..)
            | ExpKind::PredicateAccessPredicate(..)
            | ExpKind::MagicWand(..)
    ) {
        return produce_access(context, state, snapshot, assertion, error, &mut finish);
    }
    if ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(
        assertion,
    )
    .is_some()
    {
        return produce_quantified_assertion(
            context,
            state,
            snapshot,
            assertion,
            error,
            &mut finish,
        );
    }
    if special {
        return context.produce_special(state, snapshot, assertion, error, &mut finish);
    }
    context
        .assume_empty_snapshot(&state, snapshot)
        .map_err(ProductionError::Context)?;
    context.evaluate(
        state,
        assertion,
        error,
        &mut |context, state, term, rewritten| {
            context
                .assume(&term, assertion, rewritten.as_ref())
                .map_err(ProductionError::Context)?;
            finish(context, state)
        },
    )
}

/// Ordinary access production follows source argument evaluation and permission scaling.
fn produce_access<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    snapshot: &C::Snapshot,
    assertion: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    use crate::state::{chunks::MagicWandIdentifier, terms::ResourceKey};
    use std::sync::Arc;
    let (resource, args) = match assertion.kind() {
        ExpKind::FieldAccessPredicate(access, _) => (
            ResourceKey::Field(Arc::new(access.field.clone())),
            vec![access.receiver.clone()],
        ),
        ExpKind::PredicateAccessPredicate(access) => {
            let name = &access.location.predicate_name;
            let pred = state
                .program
                .predicates
                .iter()
                .find(|p| &p.name == name)
                .ok_or_else(|| ProductionError::MissingPredicate(name.clone()))?;
            (
                ResourceKey::Predicate(Arc::new(pred.clone())),
                access.location.args.clone(),
            )
        }
        ExpKind::MagicWand(..) => (
            ResourceKey::Wand(
                MagicWandIdentifier::new(assertion.clone(), &state.program)
                    .map_err(ProductionError::Wand)?,
            ),
            assertion
                .magic_wand_subexpressions(&state.program)
                .map_err(ProductionError::Wand)?,
        ),
        _ => unreachable!(),
    };
    let permission = assertion.permission_or_full().expect("access predicate");
    let original_arps = state.constrainable_arps.clone();
    evaluate_arguments(
        context,
        state,
        &args,
        error,
        &mut |context, state, terms, arg_exps| {
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
                        &mut |context, mut state| {
                            state.constrainable_arps = original_arps.clone();
                            let snap = context
                                .snapshot_for_resource(&state, snapshot, &resource)
                                .map_err(ProductionError::Context)?;
                            let factory = context.factory();
                            let strict = !context.unsafe_wildcard_optimization()
                                || (!matches!(resource, ResourceKey::Wand(_))
                                    && state.perm_locations.contains(&resource));
                            let gain = if strict {
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
                            let gain_exp = if let Some(p) = &permission_exp {
                                let scale = state
                                    .permission_scaling_factor_exp
                                    .clone()
                                    .ok_or(ProductionError::MissingDebugExpression)?;
                                Some(Exp::new(
                                    ExpKind::PermMul(p.clone(), scale),
                                    p.metadata().clone(),
                                ))
                            } else {
                                None
                            };
                            context.produce_single(
                                state,
                                &resource,
                                &terms,
                                arg_exps.as_deref(),
                                snap,
                                gain,
                                gain_exp,
                                error,
                                continuation,
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
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
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
                    let mut tail = tail_debug.ok_or(ProductionError::MissingDebugExpression)?;
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

fn produce_quantified_assertion<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    snapshot: &C::Snapshot,
    assertion: &Exp,
    error: &C::PartialError,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ProductionError<C::Error>>,
) -> Result<VerificationResult<V>, ProductionError<C::Error>>
where
    C: ProductionContext<P, D, J, V>,
{
    use crate::state::{chunks::MagicWandIdentifier, terms::ResourceKey};
    use std::sync::Arc;
    let (forall, condition, access) =
        ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion(
            assertion,
        )
        .expect("quantified assertion");
    let (resource, arguments, qid) = match access.kind() {
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
                .ok_or_else(|| ProductionError::MissingPredicate(name.clone()))?;
            (
                ResourceKey::Predicate(Arc::new(decl.clone())),
                predicate.location.args.clone(),
                name.clone(),
            )
        }
        ExpKind::MagicWand(..) => {
            let wand = MagicWandIdentifier::new(access.clone(), &state.program)
                .map_err(ProductionError::Wand)?;
            let id = wand.to_string();
            let args = access
                .magic_wand_subexpressions(&state.program)
                .map_err(ProductionError::Wand)?;
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
        &arguments,
        &qid,
        error,
        &mut |context, mut state, data| {
            state.constrainable_arps = original_arps.clone();
            if let Some(data) = data {
                context.produce_quantified(
                    state,
                    snapshot,
                    &forall,
                    &resource,
                    &qid,
                    &data,
                    error,
                    &mut |context, mut state| {
                        state.function_recorder =
                            state.function_recorder.leave_quantified(assertion);
                        continuation(context, state)
                    },
                )
            } else {
                continuation(context, state)
            }
        },
    )
}
