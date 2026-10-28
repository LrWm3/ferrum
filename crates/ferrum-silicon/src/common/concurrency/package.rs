//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/concurrency/package.scala
//!
//! Purpose:
//! Adapt a deferred computation to synchronous Future semantics.
//!
//! Planned Rust structure:
//! SynchronousFuture stores callable and optional result; functionToCallable wraps a
//! by-name function.
//!
//! Behavior to preserve:
//! get executes on first successful call and caches result; isDone reflects cache,
//! isCancelled is false. Timed get and cancel are upstream unimplemented.
//!
//! Integration:
//! verifier worker and execution scheduling.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Represent unimplemented timed get/cancel explicitly without reporting success.
//!
//! Status: implemented; integration and broad differential checks remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use std::time::Duration;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct UnsupportedSynchronousFutureOperation;

/// Lazy synchronous computation. Failed calls are retried; only success is cached.
/// This is worker-local, as is the unsynchronized Scala implementation.
pub struct SynchronousFuture<T, E, F: FnMut() -> Result<T, E>> {
    callable: F,
    result: Option<T>,
}
impl<T, E, F: FnMut() -> Result<T, E>> SynchronousFuture<T, E, F> {
    pub fn new(callable: F) -> Self {
        Self {
            callable,
            result: None,
        }
    }
    pub fn is_cancelled(&self) -> bool {
        false
    }
    pub fn is_done(&self) -> bool {
        self.result.is_some()
    }
    pub fn get(&mut self) -> Result<&T, E> {
        if self.result.is_none() {
            self.result = Some((self.callable)()?);
        }
        Ok(self
            .result
            .as_ref()
            .expect("successful computation is cached"))
    }
    /// Source timed get and cancellation deliberately throw NotImplementedError.
    pub fn get_timeout(
        &mut self,
        _: Duration,
    ) -> Result<&T, UnsupportedSynchronousFutureOperation> {
        Err(UnsupportedSynchronousFutureOperation)
    }
    pub fn cancel(&mut self, _: bool) -> Result<bool, UnsupportedSynchronousFutureOperation> {
        Err(UnsupportedSynchronousFutureOperation)
    }
}
pub fn function_to_callable<T>(f: impl FnMut() -> T) -> impl FnMut() -> T {
    f
}
