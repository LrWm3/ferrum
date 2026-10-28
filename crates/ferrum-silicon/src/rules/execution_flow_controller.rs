//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/ExecutionFlowController.scala
//!
//! Purpose:
//! Scope local execution and retry failed symbolic operations.
//!
//! Planned Rust structure:
//! ExecutionFlowRules and executionFlowController implement locallyWithResult/locally and
//! tryOrFail0/1/2 through private tryOrFailWithResult.
//!
//! Behavior to preserve:
//! Push/pop solver scope before inspecting local result; invoke Q only on nonfatal result with
//! exactly one captured datum. Initial attempt increments retryLevel and restores it at Q; retry
//! only after fatal result with no local continuation success, rewind path conditions, consolidate,
//! choose temporary more-complete modes from member annotations/config. On retry continuation,
//! restore the two mode flags and set retrying to false. Preserve upstream caveat for a successful
//! branch followed by a failing branch.
//!
//! Integration:
//! rules::state_consolidator, interfaces::verification, decider::path_conditions and
//! supporters::annotation_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Closure/result protocol and solver scope ownership.
//!
//! Status: partial; scoped execution, result uniqueness and continuation implemented.
//! Retry uses explicit consolidator, annotation and logging services; verifier integration remains.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::verification::VerificationResult;

pub trait ScopedContext {
    type Error;
    fn push_scope(&mut self) -> Result<(), Self::Error>;
    fn pop_scope(&mut self) -> Result<(), Self::Error>;
}
#[derive(Debug)]
pub enum LocalError<E> {
    Scope(E),
    Block(E),
    MultipleResults,
    BlockAndCleanup {
        block: Box<LocalError<E>>,
        cleanup: E,
    },
}
/// Execute a local solver scope; its continuation runs only after scope cleanup and a
/// nonfatal block result. Multiple data results are the source's assertion failure.
pub fn locally_with_result<C: ScopedContext, D, V>(
    context: &mut C,
    block: impl FnOnce(
        &mut C,
        &mut dyn FnMut(D) -> Result<VerificationResult<V>, LocalError<C::Error>>,
    ) -> Result<VerificationResult<V>, LocalError<C::Error>>,
    continuation: impl FnOnce(D) -> VerificationResult<V>,
) -> Result<VerificationResult<V>, LocalError<C::Error>> {
    context.push_scope().map_err(LocalError::Scope)?;
    let mut data = None;
    let result = block(context, &mut |value| {
        if data.is_some() {
            return Err(LocalError::MultipleResults);
        }
        data = Some(value);
        Ok(VerificationResult::success())
    });
    let cleanup = context.pop_scope();
    let result = match (result, cleanup) {
        (Ok(result), Ok(())) => result,
        (Err(block), Err(cleanup)) => {
            return Err(LocalError::BlockAndCleanup {
                block: Box::new(block),
                cleanup,
            });
        }
        (Err(error), _) => return Err(error),
        (Ok(_), Err(error)) => return Err(LocalError::Scope(error)),
    };
    Ok(if result.is_fatal() {
        result
    } else if let Some(data) = data {
        result.and_then(|| continuation(data))
    } else {
        result
    })
}

impl<P: crate::interfaces::decider::prover::Prover> ScopedContext
    for crate::decider::decider::DefaultDecider<P>
{
    type Error = crate::decider::decider::DeciderError<P::Error>;
    fn push_scope(&mut self) -> Result<(), Self::Error> {
        crate::decider::decider::DefaultDecider::push_scope(self)
    }
    fn pop_scope(&mut self) -> Result<(), Self::Error> {
        crate::decider::decider::DefaultDecider::pop_scope(self)
    }
}

/// Retry services belong to the current verifier/solver, not the symbolic state value.
pub trait RetryContext<P, D, J>: ScopedContext {
    type Mark;
    fn mark(&mut self) -> Self::Mark;
    fn rollback_to(&mut self, mark: Self::Mark) -> Result<(), Self::Error>;
    fn consolidate(
        &mut self,
        state: crate::state::state::State<P, D, J>,
    ) -> Result<crate::state::state::State<P, D, J>, Self::Error>;
    /// Honor member annotations first, then global exhale settings for ordinary and QP paths.
    fn retry_exhale_modes(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
    ) -> Result<(bool, bool), Self::Error>;
    fn open_retry_log(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
    ) -> Result<(), Self::Error>;
    fn close_retry_log(&mut self) -> Result<(), Self::Error>;
    fn open_retry_scope(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
    ) -> Result<Option<i32>, Self::Error> {
        self.open_retry_log(state)?;
        Ok(None)
    }
    fn close_retry_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        self.close_retry_log()
    }
}
pub trait RetryAction<C, P, D, J, Data, Diagnostic>
where
    C: RetryContext<P, D, J>,
{
    /// The optional owned continuation must carry this exact invocation's retry boundary.
    fn set_owned_attempt(&mut self, _attempt: RetryAttempt) {}
    fn run(
        &mut self,
        context: &mut C,
        state: crate::state::state::State<P, D, J>,
        continuation: &mut dyn FnMut(
            &mut C,
            crate::state::state::State<P, D, J>,
            Data,
        ) -> Result<VerificationResult<Diagnostic>, C::Error>,
    ) -> Result<VerificationResult<Diagnostic>, C::Error>;
}
/// Per-attempt completion signal shared with an owned, transferable continuation.
/// A fresh signal must be used for each retry invocation.
#[derive(Clone, Default)]
pub struct RetrySuccess(std::sync::Arc<std::sync::atomic::AtomicBool>);
impl RetrySuccess {
    /// Record entry into the first-attempt success continuation, before running Q.
    pub fn mark(&self) {
        self.0.store(true, std::sync::atomic::Ordering::SeqCst);
    }
    pub fn observed(&self) -> bool {
        self.0.load(std::sync::atomic::Ordering::SeqCst)
    }
}

/// Source success-continuation boundary for a particular retry invocation.
#[derive(Clone)]
pub enum RetryAttempt {
    First {
        success: RetrySuccess,
        retry_level: i32,
    },
    Retry {
        scope: Option<i32>,
        more_complete: bool,
        more_complete_qp: bool,
    },
}
impl RetryAttempt {
    pub fn resume<C, P, D, J>(
        &self,
        context: &mut C,
        mut state: crate::state::state::State<P, D, J>,
    ) -> Result<crate::state::state::State<P, D, J>, C::Error>
    where
        C: RetryContext<P, D, J>,
    {
        match self {
            Self::First {
                success,
                retry_level,
            } => {
                success.mark();
                state.retry_level = *retry_level;
            }
            Self::Retry {
                scope,
                more_complete,
                more_complete_qp,
            } => {
                context.close_retry_scope(*scope)?;
                state.retrying = false;
                state.more_complete_exhale = *more_complete;
                state.more_complete_exhale_qp = *more_complete_qp;
            }
        }
        Ok(state)
    }
}

/// Retry only when no action continuation succeeded and the first result was fatal.
/// On retry, restore caller retry/exhale flags only on a successful continuation, as upstream.
pub fn try_or_fail<C, P, D, J: Clone, Data, Diagnostic, A>(
    context: &mut C,
    state: crate::state::state::State<P, D, J>,
    action: &mut A,
    continuation: &mut impl FnMut(
        &mut C,
        crate::state::state::State<P, D, J>,
        Data,
    ) -> Result<VerificationResult<Diagnostic>, C::Error>,
) -> Result<VerificationResult<Diagnostic>, C::Error>
where
    C: RetryContext<P, D, J>,
    A: RetryAction<C, P, D, J, Data, Diagnostic>,
{
    let mark = context.mark();
    let retry_level = state.retry_level;
    let mut first_state = state.clone();
    first_state.retry_level = retry_level.wrapping_add(1);
    let mut local_success = false;
    let first = action.run(
        context,
        first_state,
        &mut |context, mut result_state, data| {
            local_success = true;
            result_state.retry_level = retry_level;
            continuation(context, result_state, data)
        },
    )?;
    if local_success || !first.is_fatal() {
        return Ok(first);
    }
    context.rollback_to(mark)?;
    let original = context.consolidate(state)?;
    let retry_scope = context.open_retry_scope(&original)?;
    let (more_complete, more_complete_qp) = context.retry_exhale_modes(&original)?;
    let mut retry_state = original.clone();
    retry_state.retrying = true;
    retry_state.retry_level = retry_level;
    retry_state.more_complete_exhale = more_complete;
    retry_state.more_complete_exhale_qp = more_complete_qp;
    action.run(
        context,
        retry_state,
        &mut |context, mut result_state, data| {
            context.close_retry_scope(retry_scope)?;
            result_state.retrying = false;
            result_state.more_complete_exhale = original.more_complete_exhale;
            result_state.more_complete_exhale_qp = original.more_complete_exhale_qp;
            continuation(context, result_state, data)
        },
    )
}

/// Like `try_or_fail`, with a fresh signal that an owned continuation can carry.
pub fn try_or_fail_with_success<C, P, D, J: Clone, Data, Diagnostic, A>(
    context: &mut C,
    state: crate::state::state::State<P, D, J>,
    action: &mut A,
    success: RetrySuccess,
    continuation: &mut impl FnMut(
        &mut C,
        crate::state::state::State<P, D, J>,
        Data,
    ) -> Result<VerificationResult<Diagnostic>, C::Error>,
) -> Result<VerificationResult<Diagnostic>, C::Error>
where
    C: RetryContext<P, D, J>,
    A: RetryAction<C, P, D, J, Data, Diagnostic>,
{
    let mark = context.mark();
    let retry_level = state.retry_level;
    let mut first_state = state.clone();
    first_state.retry_level = retry_level.wrapping_add(1);
    let first_attempt = RetryAttempt::First {
        success: success.clone(),
        retry_level,
    };
    action.set_owned_attempt(first_attempt.clone());
    let first = action.run(context, first_state, &mut |context, result_state, data| {
        let result_state = first_attempt.resume(context, result_state)?;
        continuation(context, result_state, data)
    })?;
    if success.observed() || !first.is_fatal() {
        return Ok(first);
    }
    context.rollback_to(mark)?;
    let original = context.consolidate(state)?;
    let retry_scope = context.open_retry_scope(&original)?;
    let (more_complete, more_complete_qp) = context.retry_exhale_modes(&original)?;
    let mut retry_state = original.clone();
    retry_state.retrying = true;
    retry_state.retry_level = retry_level;
    retry_state.more_complete_exhale = more_complete;
    retry_state.more_complete_exhale_qp = more_complete_qp;
    let retry_attempt = RetryAttempt::Retry {
        scope: retry_scope,
        more_complete: original.more_complete_exhale,
        more_complete_qp: original.more_complete_exhale_qp,
    };
    action.set_owned_attempt(retry_attempt.clone());
    action.run(context, retry_state, &mut |context, result_state, data| {
        let result_state = retry_attempt.resume(context, result_state)?;
        continuation(context, result_state, data)
    })
}

#[cfg(test)]
mod transferable_retry_tests {
    use super::*;
    use crate::state::{
        state::State,
        terms::{TermFactory, TermOptions},
    };
    use ferrum_silver::ast::{ast::Metadata, program::Program};
    struct Context {
        rollbacks: usize,
    }
    impl ScopedContext for Context {
        type Error = ();
        fn push_scope(&mut self) -> Result<(), ()> {
            Ok(())
        }
        fn pop_scope(&mut self) -> Result<(), ()> {
            Ok(())
        }
    }
    impl RetryContext<(), (), ()> for Context {
        type Mark = ();
        fn mark(&mut self) {}
        fn rollback_to(&mut self, _: ()) -> Result<(), ()> {
            self.rollbacks += 1;
            Ok(())
        }
        fn consolidate(&mut self, state: State<(), (), ()>) -> Result<State<(), (), ()>, ()> {
            Ok(state)
        }
        fn retry_exhale_modes(&mut self, _: &State<(), (), ()>) -> Result<(bool, bool), ()> {
            Ok((false, false))
        }
        fn open_retry_log(&mut self, _: &State<(), (), ()>) -> Result<(), ()> {
            Ok(())
        }
        fn close_retry_log(&mut self) -> Result<(), ()> {
            Ok(())
        }
    }
    struct Action {
        signal: RetrySuccess,
        success: bool,
        calls: usize,
    }
    impl RetryAction<Context, (), (), (), (), ()> for Action {
        fn run(
            &mut self,
            _: &mut Context,
            _: State<(), (), ()>,
            _: &mut dyn FnMut(
                &mut Context,
                State<(), (), ()>,
                (),
            ) -> Result<VerificationResult<()>, ()>,
        ) -> Result<VerificationResult<()>, ()> {
            self.calls += 1;
            if self.success {
                let signal = self.signal.clone();
                std::thread::spawn(move || signal.mark()).join().unwrap();
            }
            Ok(VerificationResult::failure((), false))
        }
    }
    #[test]
    fn transferred_success_prevents_retry_of_downstream_failure() {
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
        for success in [false, true] {
            let state = State::new(
                program.clone(),
                Default::default(),
                Default::default(),
                (),
                &factory,
                false,
                false,
            );
            let signal = RetrySuccess::default();
            let mut action = Action {
                signal: signal.clone(),
                success,
                calls: 0,
            };
            let mut context = Context { rollbacks: 0 };
            assert!(
                try_or_fail_with_success(
                    &mut context,
                    state,
                    &mut action,
                    signal,
                    &mut |_, _, _| Ok(VerificationResult::success())
                )
                .unwrap()
                .is_fatal()
            );
            assert_eq!(action.calls, if success { 1 } else { 2 });
            assert_eq!(context.rollbacks, if success { 0 } else { 1 });
        }
    }
}
