//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/VerificationPoolManager.scala
//!
//! Purpose:
//! Manage reusable worker verifiers and parallel verification tasks.
//!
//! Planned Rust structure:
//! VerificationPoolManager owns workers, synchronized blocking object pool, ForkJoinPool and
//! pooledVerifiers broadcast ProverLike; nested worker thread factory/worker/task bind one borrowed
//! worker per thread.
//!
//! Behavior to preserve:
//! Start creates configured workers, starts them, and creates executor; reset each worker; nested
//! tasks fork on worker threads, external calls submit. Broadcast preamble operations in worker
//! order and lazily evaluate comment. Shutdown attempts every worker stop, thread
//! shutdown/ten-second wait and pool close even after errors; interrupted teardown restores
//! interrupt and warns, other first exception propagates.
//!
//! Integration:
//! verifier::worker_verifier, verifier::default_main_verifier, interfaces::decider::prover and
//! rules::brancher.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Thread-local solver ownership, nested scheduling and cancellation cleanup.
//!
//! Status: partial; pooled-prover broadcast, worker ownership and lifecycle implemented.
//! Worker-aware nested task scheduling and cancellation-aware teardown remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::interfaces::decider::prover::{ProverLike, ProverStateSaturationTimeout, TextEmitter};
use crate::state::terms::{Declaration, Term};

#[derive(Debug)]
pub enum BroadcastError<E> {
    Prover(E),
    NoWorkers,
}
/// Preamble operations broadcast in worker order; failures stop at the failing worker.
/// The pool must be started before constructing this view.
pub struct PooledProvers<'a, P: ProverLike> {
    pub workers: &'a mut [P],
}
impl<P: ProverLike> TextEmitter for PooledProvers<'_, P> {
    type Error = BroadcastError<P::Error>;
    fn emit(&mut self, content: &str) -> Result<(), Self::Error> {
        for worker in &mut *self.workers {
            worker.emit(content).map_err(BroadcastError::Prover)?;
        }
        Ok(())
    }
    fn emit_all(&mut self, contents: &[String]) -> Result<(), Self::Error> {
        for worker in &mut *self.workers {
            worker.emit_all(contents).map_err(BroadcastError::Prover)?;
        }
        Ok(())
    }
    fn emit_settings(&mut self, contents: &[String]) -> Result<(), Self::Error> {
        for worker in &mut *self.workers {
            worker
                .emit_settings(contents)
                .map_err(BroadcastError::Prover)?;
        }
        Ok(())
    }
}
impl<P: ProverLike> ProverLike for PooledProvers<'_, P> {
    fn assume_axioms(
        &mut self,
        terms: &InsertionOrderedSet<Term>,
        description: &str,
    ) -> Result<(), Self::Error> {
        for worker in &mut *self.workers {
            worker
                .assume_axioms(terms, description)
                .map_err(BroadcastError::Prover)?;
        }
        Ok(())
    }
    fn set_option(&mut self, name: &str, value: &str) -> Result<String, Self::Error> {
        let mut first = None;
        for worker in &mut *self.workers {
            let result = worker
                .set_option(name, value)
                .map_err(BroadcastError::Prover)?;
            if first.is_none() {
                first = Some(result);
            }
        }
        first.ok_or(BroadcastError::NoWorkers)
    }
    fn assume(&mut self, term: &Term) -> Result<(), Self::Error> {
        for worker in &mut *self.workers {
            worker.assume(term).map_err(BroadcastError::Prover)?;
        }
        Ok(())
    }
    fn declare(&mut self, declaration: &Declaration) -> Result<(), Self::Error> {
        for worker in &mut *self.workers {
            worker
                .declare(declaration)
                .map_err(BroadcastError::Prover)?;
        }
        Ok(())
    }
    fn comment(&mut self, content: &mut dyn FnMut() -> String) -> Result<(), Self::Error> {
        let mut cached = None;
        for worker in &mut *self.workers {
            worker
                .comment(&mut || cached.get_or_insert_with(&mut *content).clone())
                .map_err(BroadcastError::Prover)?;
        }
        Ok(())
    }
    fn saturate(&mut self, timeout_ms: i32, comment: &str) -> Result<(), Self::Error> {
        for worker in &mut *self.workers {
            worker
                .saturate(timeout_ms, comment)
                .map_err(BroadcastError::Prover)?;
        }
        Ok(())
    }
    fn saturate_configured(
        &mut self,
        data: Option<&ProverStateSaturationTimeout>,
    ) -> Result<(), Self::Error> {
        for worker in &mut *self.workers {
            worker
                .saturate_configured(data)
                .map_err(BroadcastError::Prover)?;
        }
        Ok(())
    }
}

pub trait ManagedWorker {
    type Error;
    fn start_worker(&mut self) -> Result<(), Self::Error>;
    fn reset_worker(&mut self) -> Result<(), Self::Error>;
    fn stop_worker(&mut self) -> Result<(), Self::Error>;
}
#[derive(Debug)]
pub enum PoolLifecycleError<E> {
    NoWorkers,
    AlreadyStarted,
    NotStarted,
    Worker(E),
}
/// Owns and resets the actual worker instances; asynchronous scheduling is a separate
/// integration boundary because nested fork/join tasks require worker-aware execution.
pub struct VerificationPoolManager<W: ManagedWorker> {
    worker_count: usize,
    workers: Option<Vec<W>>,
}
impl<W: ManagedWorker> VerificationPoolManager<W> {
    pub fn new(worker_count: usize) -> Self {
        Self {
            worker_count,
            workers: None,
        }
    }
    pub fn workers(&self) -> Option<&[W]> {
        self.workers.as_deref()
    }
    pub fn workers_mut(&mut self) -> Option<&mut [W]> {
        self.workers.as_deref_mut()
    }
    pub fn start(
        &mut self,
        mut create: impl FnMut() -> Result<W, W::Error>,
    ) -> Result<(), PoolLifecycleError<W::Error>> {
        if self.workers.is_some() {
            return Err(PoolLifecycleError::AlreadyStarted);
        }
        if self.worker_count == 0 {
            return Err(PoolLifecycleError::NoWorkers);
        }
        self.workers = Some(Vec::new());
        for _ in 0..self.worker_count {
            let worker = create().map_err(PoolLifecycleError::Worker)?;
            self.workers
                .as_mut()
                .expect("installed pool")
                .insert(0, worker);
        }
        for worker in self.workers.as_mut().expect("installed pool") {
            worker.start_worker().map_err(PoolLifecycleError::Worker)?;
        }
        Ok(())
    }
    pub fn reset(&mut self) -> Result<(), PoolLifecycleError<W::Error>> {
        for worker in self
            .workers
            .as_mut()
            .ok_or(PoolLifecycleError::NotStarted)?
        {
            worker.reset_worker().map_err(PoolLifecycleError::Worker)?;
        }
        Ok(())
    }
    /// Attempt every worker teardown even when one fails, then return the first error.
    pub fn stop(&mut self) -> Result<(), PoolLifecycleError<W::Error>> {
        let mut first = None;
        if let Some(workers) = &mut self.workers {
            for worker in workers {
                if let Err(error) = worker.stop_worker()
                    && first.is_none()
                {
                    first = Some(error);
                }
            }
        }
        self.workers = None;
        match first {
            Some(error) => Err(PoolLifecycleError::Worker(error)),
            None => Ok(()),
        }
    }
}
