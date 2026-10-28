//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/Verification.scala
//!
//! Purpose:
//! Model verification outcomes and failure contexts/counterexamples.
//!
//! Planned Rust structure:
//! VerificationResult, FatalResult, NonFatalResult, Success, Unreachable, Failure;
//! SiliconFailureContext and SiliconDebuggingFailureContext; native, variable and mapped
//! SiliconCounterexample variants.
//!
//! Behavior to preserve:
//! combine lazily evaluates other only if continuation permits, except alwaysWaitForOther;
//! retain ordered previous chains, fatal head selection and isReported. Variable model
//! includes mapped variables and integer/boolean literals. Mapped model interprets labels
//! and renames snapshot values consistently as hp_N.
//!
//! Integration:
//! ferrum_silver::verifier, reporting converter/interpreter, state and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Result mutability and continuation ownership with rules and reporting.
//!
//! Status: partial; Silicon result combination/control flow implemented. Failure contexts and
//! counterexample types await model, state and diagnostic integration.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use std::sync::{Arc, Mutex};

/// Silicon control-flow result, separate from Silver's final aggregated result.
#[derive(Clone, Debug)]
pub enum ResultKind<E> {
    Success,
    Unreachable,
    Failure(E),
}
#[derive(Debug)]
struct ResultData<E> {
    kind: ResultKind<E>,
    continue_verification: bool,
    reported: bool,
    previous: Vec<VerificationResult<E>>,
}
/// Handles share mutations to `previous` and `reported`, matching source result identity.
#[derive(Debug)]
pub struct VerificationResult<E>(Arc<Mutex<ResultData<E>>>);
impl<E> Clone for VerificationResult<E> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<E> VerificationResult<E> {
    pub fn success() -> Self {
        Self::new(ResultKind::Success, true)
    }
    pub fn unreachable() -> Self {
        Self::new(ResultKind::Unreachable, true)
    }
    pub fn failure(error: E, continue_verification: bool) -> Self {
        Self::new(ResultKind::Failure(error), continue_verification)
    }
    fn new(kind: ResultKind<E>, continue_verification: bool) -> Self {
        Self(Arc::new(Mutex::new(ResultData {
            kind,
            continue_verification,
            reported: false,
            previous: vec![],
        })))
    }
    pub fn is_fatal(&self) -> bool {
        matches!(
            self.0.lock().expect("poisoned verification result").kind,
            ResultKind::Failure(_)
        )
    }
    pub fn continue_verification(&self) -> bool {
        self.0
            .lock()
            .expect("poisoned verification result")
            .continue_verification
    }
    pub fn is_reported(&self) -> bool {
        self.0
            .lock()
            .expect("poisoned verification result")
            .reported
    }
    pub fn set_reported(&self, value: bool) {
        self.0
            .lock()
            .expect("poisoned verification result")
            .reported = value;
    }
    pub fn previous(&self) -> Vec<Self> {
        self.0
            .lock()
            .expect("poisoned verification result")
            .previous
            .clone()
    }
    pub fn with_kind<R>(&self, inspect: impl FnOnce(&ResultKind<E>) -> R) -> R {
        inspect(&self.0.lock().expect("poisoned verification result").kind)
    }
    fn append_history(&self, other: &Self) {
        let history = other.previous();
        let mut data = self.0.lock().expect("poisoned verification result");
        data.previous.push(other.clone());
        data.previous.extend(history);
    }
    /// Fatal results short-circuit; otherwise append the receiver and its history to the result.
    pub fn and_then(self, other: impl FnOnce() -> Self) -> Self {
        if self.is_fatal() {
            return self;
        }
        let result = other();
        result.append_history(&self);
        result
    }
    /// Combine keeps fatal results as head unless the other result stops verification.
    pub fn combine(self, other: impl FnOnce() -> Self, always_wait_for_other: bool) -> Self {
        if !self.continue_verification() {
            if always_wait_for_other {
                other();
            }
            return self;
        }
        let result = other();
        if self.is_fatal() && result.continue_verification() {
            self.append_history(&result);
            self
        } else {
            result.append_history(&self);
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn combination_respects_fatal_head_and_stopping_result() {
        let failed = VerificationResult::failure("first", true);
        let alternate = VerificationResult::failure("second", false);
        let combined = failed.clone().combine(|| alternate.clone(), false);
        assert!(Arc::ptr_eq(&combined.0, &alternate.0));
        assert!(Arc::ptr_eq(&combined.previous()[0].0, &failed.0));
        let mut evaluated = false;
        let again = combined.clone().combine(
            || {
                evaluated = true;
                VerificationResult::success()
            },
            false,
        );
        assert!(!evaluated);
        assert!(Arc::ptr_eq(&again.0, &combined.0));
        combined.combine(
            || {
                evaluated = true;
                VerificationResult::success()
            },
            true,
        );
        assert!(evaluated);
    }
}
