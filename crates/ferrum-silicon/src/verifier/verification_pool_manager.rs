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
//! Status: partial; ordered pooled broadcast, worker ownership/lifecycle and dedicated
//! thread-bound top-level task scheduling are implemented. Concrete native verification,
//! nested branch scheduling and interruption-aware teardown remain pending.

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

/// One source `ProverLike` preamble operation, replayed identically on each worker.
/// The main verifier must emit the same operation before the worker broadcast.
#[derive(Clone)]
pub enum WorkerPreambleCommand {
    Emit(String),
    EmitAll(Vec<String>),
    EmitSettings(Vec<String>),
    Declare(Declaration),
    Assume(Term),
    AssumeAxioms(InsertionOrderedSet<Term>, String),
    Comment(LazyWorkerComment),
    Saturate(i32, String),
    SaturateConfigured(Option<ProverStateSaturationTimeout>),
    SetOption(String, String),
}
/// Match the source by-name comment: evaluate only if a prover asks, at most once
/// across the main prover and all worker broadcasts.
#[derive(Clone)]
pub struct LazyWorkerComment(std::sync::Arc<LazyWorkerCommentData>);
struct LazyWorkerCommentData {
    value: std::sync::OnceLock<String>,
    render: Box<dyn Fn() -> String + Send + Sync>,
}
impl LazyWorkerComment {
    pub fn new(render: impl Fn() -> String + Send + Sync + 'static) -> Self {
        Self(std::sync::Arc::new(LazyWorkerCommentData {
            value: std::sync::OnceLock::new(),
            render: Box::new(render),
        }))
    }
    pub fn value(&self) -> String {
        self.0.value.get_or_init(|| (self.0.render)()).clone()
    }
}
impl WorkerPreambleCommand {
    pub fn apply<P: ProverLike>(&self, prover: &mut P) -> Result<Option<String>, P::Error> {
        match self {
            Self::Emit(text) => prover.emit(text)?,
            Self::EmitAll(text) => prover.emit_all(text)?,
            Self::EmitSettings(text) => prover.emit_settings(text)?,
            Self::Declare(decl) => prover.declare(decl)?,
            Self::Assume(term) => prover.assume(term)?,
            Self::AssumeAxioms(terms, desc) => prover.assume_axioms(terms, desc)?,
            Self::Comment(comment) => prover.comment(&mut || comment.value())?,
            Self::Saturate(timeout, comment) => prover.saturate(*timeout, comment)?,
            Self::SaturateConfigured(config) => prover.saturate_configured(config.as_ref())?,
            Self::SetOption(name, value) => return prover.set_option(name, value).map(Some),
        }
        Ok(None)
    }
}

/// A verifier constructed, started, used and stopped on one dedicated pool thread.
/// The verifier itself need not implement `Send`, which also permits linked Z3 contexts.
pub trait ThreadBoundWorker: 'static {
    type Error: Send + 'static;
    type Broadcast: Clone + Send + 'static;
    type BroadcastResult: Send + 'static;
    type Task: Send + 'static;
    type Output: Send + 'static;

    fn start(&mut self) -> Result<(), Self::Error>;
    fn broadcast(&mut self, command: Self::Broadcast)
    -> Result<Self::BroadcastResult, Self::Error>;
    fn verify(&mut self, task: Self::Task) -> Result<Self::Output, Self::Error>;
    fn reset(&mut self) -> Result<(), Self::Error>;
    fn stop(&mut self) -> Result<(), Self::Error>;
}

#[derive(Debug)]
pub enum ThreadPoolError<E> {
    NoWorkers,
    InvalidStackSize,
    Busy,
    Cancelled,
    Stopped,
    Worker(E),
    WorkerPanicked,
    WorkerDisconnected,
    ThreadSpawn(std::io::Error),
}

enum ThreadCommand<W: ThreadBoundWorker> {
    Start(std::sync::mpsc::Sender<Result<(), ThreadPoolError<W::Error>>>),
    Broadcast(
        W::Broadcast,
        std::sync::mpsc::Sender<Result<W::BroadcastResult, ThreadPoolError<W::Error>>>,
    ),
    Verify(
        W::Task,
        std::sync::mpsc::Sender<Result<W::Output, ThreadPoolError<W::Error>>>,
    ),
    Reset(std::sync::mpsc::Sender<Result<(), ThreadPoolError<W::Error>>>),
    Stop(std::sync::mpsc::Sender<Result<(), ThreadPoolError<W::Error>>>),
}
struct ThreadWork<W: ThreadBoundWorker> {
    target: Option<usize>,
    command: ThreadCommand<W>,
}
struct ThreadQueue<W: ThreadBoundWorker> {
    items: std::collections::VecDeque<ThreadWork<W>>,
    pending: usize,
    stopped: bool,
}
type SharedThreadQueue<W> = std::sync::Arc<(std::sync::Mutex<ThreadQueue<W>>, std::sync::Condvar)>;

/// A result handle retains submission order independently of task completion order.
pub struct VerificationTask<O, E>(std::sync::mpsc::Receiver<Result<O, ThreadPoolError<E>>>);
impl<O, E> VerificationTask<O, E> {
    pub fn wait(self) -> Result<O, ThreadPoolError<E>> {
        self.0
            .recv()
            .map_err(|_| ThreadPoolError::WorkerDisconnected)?
    }
}

fn finish_task_batch<O, E>(
    tasks: Vec<VerificationTask<O, E>>,
    mut error: Option<ThreadPoolError<E>>,
) -> Result<Vec<O>, ThreadPoolError<E>> {
    let mut results = Vec::new();
    for task in tasks {
        match task.wait() {
            Ok(value) => results.push(value),
            Err(failure) if error.is_none() => error = Some(failure),
            Err(_) => (),
        }
    }
    match error {
        Some(error) => Err(error),
        None => Ok(results),
    }
}

/// Worker-affine scheduler with source-ordered preamble broadcast and dynamic task assignment.
/// Broadcast and reset require an idle pool; branch-level nested fork/join is not yet exposed.
/// Every factory and solver is created on its permanent worker thread. Dropping the pool cancels
/// queued tasks and waits for active tasks; Rust cannot forcibly interrupt a blocked prover call.
pub struct ThreadVerificationPool<W: ThreadBoundWorker> {
    queue: SharedThreadQueue<W>,
    threads: Vec<std::thread::JoinHandle<()>>,
}
impl<W: ThreadBoundWorker> ThreadVerificationPool<W> {
    /// Match the pinned Silicon launcher `run / javaOptions += "-Xss128m"`:
    /// https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/build.sbt#L39
    /// This finite native stack remains a mitigation until recursive execution is reduced.
    pub const DEFAULT_STACK_SIZE: usize = 128 * 1024 * 1024;
    pub fn start(
        count: usize,
        create: impl Fn(usize) -> Result<W, W::Error> + Send + Sync + 'static,
    ) -> Result<Self, ThreadPoolError<W::Error>> {
        Self::start_with_stack(count, Self::DEFAULT_STACK_SIZE, create)
    }
    pub fn start_with_stack(
        count: usize,
        stack_size: usize,
        create: impl Fn(usize) -> Result<W, W::Error> + Send + Sync + 'static,
    ) -> Result<Self, ThreadPoolError<W::Error>> {
        use std::sync::{Arc, Condvar, Mutex, mpsc};
        if count == 0 {
            return Err(ThreadPoolError::NoWorkers);
        }
        if stack_size == 0 {
            return Err(ThreadPoolError::InvalidStackSize);
        }
        let queue = Arc::new((
            Mutex::new(ThreadQueue {
                items: Default::default(),
                pending: 0,
                stopped: false,
            }),
            Condvar::new(),
        ));
        let create = Arc::new(create);
        let mut threads = Vec::with_capacity(count);
        for index in 0..count {
            let worker_queue = Arc::clone(&queue);
            let create = Arc::clone(&create);
            let (tx, rx) = mpsc::channel();
            let thread = std::thread::Builder::new()
                .name(format!("silicon-worker-{index}"))
                .stack_size(stack_size)
                .spawn(move || {
                    let queue = worker_queue;
                    let make =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| create(index)));
                    let mut worker = match make {
                        Ok(Ok(worker)) => worker,
                        Ok(Err(error)) => {
                            let _ = tx.send(Err(ThreadPoolError::Worker(error)));
                            return;
                        }
                        Err(_) => {
                            let _ = tx.send(Err(ThreadPoolError::WorkerPanicked));
                            return;
                        }
                    };
                    if tx.send(Ok(())).is_err() {
                        let _ = worker.stop();
                        return;
                    }
                    loop {
                        let work = {
                            let (lock, ready) = &*queue;
                            let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
                            loop {
                                if let Some(position) = guard.items.iter().position(|item| {
                                    item.target.is_none_or(|target| target == index)
                                }) {
                                    break Some(
                                        guard.items.remove(position).expect("position from queue"),
                                    );
                                }
                                if guard.stopped {
                                    break None;
                                }
                                guard = ready.wait(guard).unwrap_or_else(|e| e.into_inner());
                            }
                        };
                        let Some(work) = work else {
                            let _ = worker.stop();
                            break;
                        };
                        match work.command {
                            ThreadCommand::Start(tx) => {
                                let result =
                                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                        worker.start()
                                    }));
                                let _ = tx.send(match result {
                                    Ok(value) => value.map_err(ThreadPoolError::Worker),
                                    Err(_) => Err(ThreadPoolError::WorkerPanicked),
                                });
                            }
                            ThreadCommand::Verify(task, tx) => {
                                let result =
                                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                        worker.verify(task)
                                    }));
                                let result = match result {
                                    Ok(value) => value.map_err(ThreadPoolError::Worker),
                                    Err(_) => Err(ThreadPoolError::WorkerPanicked),
                                };
                                let panicked =
                                    matches!(result, Err(ThreadPoolError::WorkerPanicked));
                                let (lock, ready) = &*queue;
                                let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
                                guard.pending -= 1;
                                let abandoned = if panicked {
                                    guard.stopped = true;
                                    let abandoned: Vec<_> = guard.items.drain(..).collect();
                                    guard.pending -= abandoned
                                        .iter()
                                        .filter(|work| {
                                            matches!(work.command, ThreadCommand::Verify(..))
                                        })
                                        .count();
                                    abandoned
                                } else {
                                    Vec::new()
                                };
                                ready.notify_all();
                                drop(guard);
                                drop(abandoned);
                                let _ = tx.send(result);
                                if panicked {
                                    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                                        || worker.stop(),
                                    ));
                                    break;
                                }
                            }
                            ThreadCommand::Broadcast(command, tx) => {
                                let result =
                                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                        worker.broadcast(command)
                                    }));
                                let _ = tx.send(match result {
                                    Ok(value) => value.map_err(ThreadPoolError::Worker),
                                    Err(_) => Err(ThreadPoolError::WorkerPanicked),
                                });
                            }
                            ThreadCommand::Reset(tx) => {
                                let result =
                                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                        worker.reset()
                                    }));
                                let _ = tx.send(match result {
                                    Ok(value) => value.map_err(ThreadPoolError::Worker),
                                    Err(_) => Err(ThreadPoolError::WorkerPanicked),
                                });
                            }
                            ThreadCommand::Stop(tx) => {
                                let result =
                                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                        worker.stop()
                                    }));
                                let _ = tx.send(match result {
                                    Ok(value) => value.map_err(ThreadPoolError::Worker),
                                    Err(_) => Err(ThreadPoolError::WorkerPanicked),
                                });
                                break;
                            }
                        }
                    }
                });
            match thread {
                Ok(thread) => threads.push(thread),
                Err(error) => {
                    let mut pool = Self { queue, threads };
                    pool.abort_and_join();
                    return Err(ThreadPoolError::ThreadSpawn(error));
                }
            }
            if let Err(error) = rx
                .recv()
                .unwrap_or(Err(ThreadPoolError::WorkerDisconnected))
            {
                let mut pool = Self { queue, threads };
                pool.abort_and_join();
                return Err(error);
            }
        }
        let mut pool = Self { queue, threads };
        for index in (0..count).rev() {
            let (tx, rx) = mpsc::channel();
            if let Err(error) = pool.enqueue_control(index, ThreadCommand::Start(tx)) {
                pool.abort_and_join();
                return Err(error);
            }
            if let Err(error) = rx
                .recv()
                .unwrap_or(Err(ThreadPoolError::WorkerDisconnected))
            {
                pool.abort_and_join();
                return Err(error);
            }
        }
        Ok(pool)
    }
    pub fn submit(
        &mut self,
        task: W::Task,
    ) -> Result<VerificationTask<W::Output, W::Error>, ThreadPoolError<W::Error>> {
        let (tx, rx) = std::sync::mpsc::channel();
        let (lock, ready) = &*self.queue;
        let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
        if guard.stopped {
            return Err(ThreadPoolError::Stopped);
        }
        guard.pending += 1;
        guard.items.push_back(ThreadWork {
            target: None,
            command: ThreadCommand::Verify(task, tx),
        });
        ready.notify_all();
        Ok(VerificationTask(rx))
    }
    /// Cancel tasks which have not yet been picked up. Running solver calls are
    /// not interrupted; their handles continue to resolve normally.
    pub fn cancel_pending(&mut self) -> Result<usize, ThreadPoolError<W::Error>> {
        let (lock, ready) = &*self.queue;
        let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
        if guard.stopped {
            return Err(ThreadPoolError::Stopped);
        }
        let mut kept = std::collections::VecDeque::new();
        let mut cancelled = Vec::new();
        while let Some(work) = guard.items.pop_front() {
            match work.command {
                ThreadCommand::Verify(_, sender) => cancelled.push(sender),
                command => kept.push_back(ThreadWork {
                    target: work.target,
                    command,
                }),
            }
        }
        guard.items = kept;
        guard.pending -= cancelled.len();
        ready.notify_all();
        drop(guard);
        let count = cancelled.len();
        for sender in cancelled {
            let _ = sender.send(Err(ThreadPoolError::Cancelled));
        }
        Ok(count)
    }
    fn enqueue_control(
        &self,
        target: usize,
        command: ThreadCommand<W>,
    ) -> Result<(), ThreadPoolError<W::Error>> {
        let (lock, ready) = &*self.queue;
        let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
        if guard.stopped {
            return Err(ThreadPoolError::Stopped);
        }
        if guard.pending != 0 {
            return Err(ThreadPoolError::Busy);
        }
        guard.items.push_back(ThreadWork {
            target: Some(target),
            command,
        });
        ready.notify_all();
        Ok(())
    }
    /// Apply the command to every worker in worker-vector order, stopping at the first error.
    pub fn broadcast(
        &mut self,
        command: W::Broadcast,
    ) -> Result<Vec<W::BroadcastResult>, ThreadPoolError<W::Error>> {
        let mut results = Vec::with_capacity(self.threads.len());
        for index in (0..self.threads.len()).rev() {
            let (tx, rx) = std::sync::mpsc::channel();
            self.enqueue_control(index, ThreadCommand::Broadcast(command.clone(), tx))?;
            let result = rx
                .recv()
                .map_err(|_| ThreadPoolError::WorkerDisconnected)
                .and_then(|value| value);
            match result {
                Ok(value) => results.push(value),
                Err(error) => {
                    self.abort_and_join();
                    return Err(error);
                }
            }
        }
        Ok(results)
    }
    pub fn reset(&mut self) -> Result<(), ThreadPoolError<W::Error>> {
        for index in (0..self.threads.len()).rev() {
            let (tx, rx) = std::sync::mpsc::channel();
            self.enqueue_control(index, ThreadCommand::Reset(tx))?;
            let result = rx
                .recv()
                .map_err(|_| ThreadPoolError::WorkerDisconnected)
                .and_then(|value| value);
            if let Err(error) = result {
                self.abort_and_join();
                return Err(error);
            }
        }
        Ok(())
    }
    pub fn shutdown(mut self) -> Result<(), ThreadPoolError<W::Error>> {
        {
            let (lock, ready) = &*self.queue;
            let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
            while guard.pending != 0 {
                guard = ready.wait(guard).unwrap_or_else(|e| e.into_inner());
            }
        }
        let mut first = None;
        for index in (0..self.threads.len()).rev() {
            let (tx, rx) = std::sync::mpsc::channel();
            let result = self
                .enqueue_control(index, ThreadCommand::Stop(tx))
                .and_then(|_| {
                    rx.recv()
                        .map_err(|_| ThreadPoolError::WorkerDisconnected)
                        .and_then(|v| v)
                });
            if first.is_none() {
                first = result.err();
            }
        }
        self.abort_and_join();
        match first {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
    fn abort_and_join(&mut self) {
        let (lock, ready) = &*self.queue;
        let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
        guard.stopped = true;
        let abandoned: Vec<_> = guard.items.drain(..).collect();
        guard.pending -= abandoned
            .iter()
            .filter(|work| matches!(work.command, ThreadCommand::Verify(..)))
            .count();
        ready.notify_all();
        drop(guard);
        for work in abandoned {
            if let ThreadCommand::Verify(_, sender) = work.command {
                let _ = sender.send(Err(ThreadPoolError::Cancelled));
            }
        }
        for handle in self.threads.drain(..) {
            let _ = handle.join();
        }
    }
}
impl<W: ThreadBoundWorker> Drop for ThreadVerificationPool<W> {
    fn drop(&mut self) {
        self.abort_and_join();
    }
}

/// ProverLike sink which broadcasts each source preamble operation synchronously.
/// It preserves the source first-worker result for `set_option` and keeps a
/// borrowed by-name comment live until all workers have decided whether to use it.
pub struct ThreadPoolPreambleSink<
    'a,
    W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>,
> {
    pub pool: &'a mut ThreadVerificationPool<W>,
}
impl<W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>>
    TextEmitter for ThreadPoolPreambleSink<'_, W>
{
    type Error = ThreadPoolError<W::Error>;
    fn emit(&mut self, content: &str) -> Result<(), Self::Error> {
        self.pool
            .broadcast(WorkerPreambleCommand::Emit(content.into()))
            .map(|_| ())
    }
    fn emit_all(&mut self, content: &[String]) -> Result<(), Self::Error> {
        self.pool
            .broadcast(WorkerPreambleCommand::EmitAll(content.to_vec()))
            .map(|_| ())
    }
    fn emit_settings(&mut self, content: &[String]) -> Result<(), Self::Error> {
        self.pool
            .broadcast(WorkerPreambleCommand::EmitSettings(content.to_vec()))
            .map(|_| ())
    }
}
impl<W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>>
    ProverLike for ThreadPoolPreambleSink<'_, W>
{
    fn assume_axioms(
        &mut self,
        terms: &InsertionOrderedSet<Term>,
        desc: &str,
    ) -> Result<(), Self::Error> {
        self.pool
            .broadcast(WorkerPreambleCommand::AssumeAxioms(
                terms.clone(),
                desc.into(),
            ))
            .map(|_| ())
    }
    fn set_option(&mut self, name: &str, value: &str) -> Result<String, Self::Error> {
        let results = self
            .pool
            .broadcast(WorkerPreambleCommand::SetOption(name.into(), value.into()))?;
        results
            .into_iter()
            .next()
            .flatten()
            .ok_or(ThreadPoolError::WorkerDisconnected)
    }
    fn assume(&mut self, term: &Term) -> Result<(), Self::Error> {
        self.pool
            .broadcast(WorkerPreambleCommand::Assume(term.clone()))
            .map(|_| ())
    }
    fn declare(&mut self, decl: &Declaration) -> Result<(), Self::Error> {
        self.pool
            .broadcast(WorkerPreambleCommand::Declare(decl.clone()))
            .map(|_| ())
    }
    fn comment(&mut self, content: &mut dyn FnMut() -> String) -> Result<(), Self::Error> {
        use std::sync::mpsc::{self, RecvTimeoutError};
        let mut cached: Option<String> = None;
        for index in (0..self.pool.threads.len()).rev() {
            let (request_tx, request_rx) = mpsc::channel::<mpsc::SyncSender<String>>();
            let lazy = LazyWorkerComment::new(move || {
                let (reply_tx, reply_rx) = mpsc::sync_channel(1);
                request_tx.send(reply_tx).expect("comment request receiver");
                reply_rx.recv().expect("comment response sender")
            });
            let (done_tx, done_rx) = mpsc::channel();
            self.pool.enqueue_control(
                index,
                ThreadCommand::Broadcast(WorkerPreambleCommand::Comment(lazy), done_tx),
            )?;
            let result = loop {
                while let Ok(reply) = request_rx.try_recv() {
                    let value = cached.get_or_insert_with(&mut *content).clone();
                    let _ = reply.send(value);
                }
                match done_rx.recv_timeout(std::time::Duration::from_millis(1)) {
                    Ok(result) => break result,
                    Err(RecvTimeoutError::Timeout) => (),
                    Err(RecvTimeoutError::Disconnected) => {
                        break Err(ThreadPoolError::WorkerDisconnected);
                    }
                }
            };
            if let Err(error) = result {
                self.pool.abort_and_join();
                return Err(error);
            }
        }
        Ok(())
    }
    fn saturate(&mut self, timeout_ms: i32, comment: &str) -> Result<(), Self::Error> {
        self.pool
            .broadcast(WorkerPreambleCommand::Saturate(timeout_ms, comment.into()))
            .map(|_| ())
    }
    fn saturate_configured(
        &mut self,
        data: Option<&ProverStateSaturationTimeout>,
    ) -> Result<(), Self::Error> {
        self.pool
            .broadcast(WorkerPreambleCommand::SaturateConfigured(data.cloned()))
            .map(|_| ())
    }
}

#[derive(Debug)]
pub enum DualPreambleError<M, W> {
    Main(M),
    Workers(ThreadPoolError<W>),
}
/// Source allProvers sink: the main prover receives each operation first, then
/// the worker vector in its source order. The workers' first option result wins.
pub struct DualPreambleSink<
    'a,
    P: ProverLike,
    W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>,
> {
    pub main: &'a mut P,
    pub workers: ThreadPoolPreambleSink<'a, W>,
}
impl<
    P: ProverLike,
    W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>,
> TextEmitter for DualPreambleSink<'_, P, W>
{
    type Error = DualPreambleError<P::Error, W::Error>;
    fn emit(&mut self, value: &str) -> Result<(), Self::Error> {
        self.main.emit(value).map_err(DualPreambleError::Main)?;
        self.workers.emit(value).map_err(DualPreambleError::Workers)
    }
    fn emit_all(&mut self, value: &[String]) -> Result<(), Self::Error> {
        self.main.emit_all(value).map_err(DualPreambleError::Main)?;
        self.workers
            .emit_all(value)
            .map_err(DualPreambleError::Workers)
    }
    fn emit_settings(&mut self, value: &[String]) -> Result<(), Self::Error> {
        self.main
            .emit_settings(value)
            .map_err(DualPreambleError::Main)?;
        self.workers
            .emit_settings(value)
            .map_err(DualPreambleError::Workers)
    }
}
impl<
    P: ProverLike,
    W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>,
> ProverLike for DualPreambleSink<'_, P, W>
{
    fn assume_axioms(
        &mut self,
        terms: &InsertionOrderedSet<Term>,
        desc: &str,
    ) -> Result<(), Self::Error> {
        self.main
            .assume_axioms(terms, desc)
            .map_err(DualPreambleError::Main)?;
        self.workers
            .assume_axioms(terms, desc)
            .map_err(DualPreambleError::Workers)
    }
    fn set_option(&mut self, name: &str, value: &str) -> Result<String, Self::Error> {
        self.main
            .set_option(name, value)
            .map_err(DualPreambleError::Main)?;
        self.workers
            .set_option(name, value)
            .map_err(DualPreambleError::Workers)
    }
    fn assume(&mut self, term: &Term) -> Result<(), Self::Error> {
        self.main.assume(term).map_err(DualPreambleError::Main)?;
        self.workers
            .assume(term)
            .map_err(DualPreambleError::Workers)
    }
    fn declare(&mut self, decl: &Declaration) -> Result<(), Self::Error> {
        self.main.declare(decl).map_err(DualPreambleError::Main)?;
        self.workers
            .declare(decl)
            .map_err(DualPreambleError::Workers)
    }
    fn comment(&mut self, content: &mut dyn FnMut() -> String) -> Result<(), Self::Error> {
        let mut cached = None;
        let mut lazy = || cached.get_or_insert_with(&mut *content).clone();
        self.main
            .comment(&mut lazy)
            .map_err(DualPreambleError::Main)?;
        self.workers
            .comment(&mut lazy)
            .map_err(DualPreambleError::Workers)
    }
    fn saturate(&mut self, timeout: i32, comment: &str) -> Result<(), Self::Error> {
        self.main
            .saturate(timeout, comment)
            .map_err(DualPreambleError::Main)?;
        self.workers
            .saturate(timeout, comment)
            .map_err(DualPreambleError::Workers)
    }
    fn saturate_configured(
        &mut self,
        data: Option<&ProverStateSaturationTimeout>,
    ) -> Result<(), Self::Error> {
        self.main
            .saturate_configured(data)
            .map_err(DualPreambleError::Main)?;
        self.workers
            .saturate_configured(data)
            .map_err(DualPreambleError::Workers)
    }
}

#[derive(Debug)]
pub enum BroadcastingProverError<M, W> {
    Main(M),
    Workers(ThreadPoolError<W>),
    Unsupported(&'static str),
}
/// Main solver wrapper. During contributor analysis, preamble operations are
/// synchronously broadcast after the main solver; verification is main-only.
/// The pool handle stays on the coordinating thread and never moves solvers.
pub struct BroadcastingProver<
    P: crate::interfaces::decider::prover::Prover,
    W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>,
> {
    pub main: P,
    pub pool: std::rc::Rc<std::cell::RefCell<ThreadVerificationPool<W>>>,
    broadcast: bool,
}
impl<
    P: crate::interfaces::decider::prover::Prover,
    W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>,
> BroadcastingProver<P, W>
{
    pub fn new(main: P, pool: std::rc::Rc<std::cell::RefCell<ThreadVerificationPool<W>>>) -> Self {
        Self {
            main,
            pool,
            broadcast: false,
        }
    }
    pub fn set_preamble_broadcast(&mut self, enabled: bool) {
        self.broadcast = enabled;
    }
    fn dual<R>(
        &mut self,
        action: impl FnOnce(
            &mut DualPreambleSink<'_, P, W>,
        ) -> Result<R, DualPreambleError<P::Error, W::Error>>,
    ) -> Result<R, BroadcastingProverError<P::Error, W::Error>> {
        let mut pool = self.pool.borrow_mut();
        let mut sink = DualPreambleSink {
            main: &mut self.main,
            workers: ThreadPoolPreambleSink { pool: &mut pool },
        };
        action(&mut sink).map_err(|e| match e {
            DualPreambleError::Main(e) => BroadcastingProverError::Main(e),
            DualPreambleError::Workers(e) => BroadcastingProverError::Workers(e),
        })
    }
    fn require_main_only(&self) -> Result<(), BroadcastingProverError<P::Error, W::Error>> {
        if self.broadcast {
            Err(BroadcastingProverError::Unsupported(
                "scoped solver operation during worker preamble",
            ))
        } else {
            Ok(())
        }
    }
}
impl<
    P: crate::interfaces::decider::prover::Prover,
    W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>,
> TextEmitter for BroadcastingProver<P, W>
{
    type Error = BroadcastingProverError<P::Error, W::Error>;
    fn emit(&mut self, value: &str) -> Result<(), Self::Error> {
        if self.broadcast {
            self.dual(|s| s.emit(value))
        } else {
            self.main.emit(value).map_err(BroadcastingProverError::Main)
        }
    }
    fn emit_all(&mut self, value: &[String]) -> Result<(), Self::Error> {
        if self.broadcast {
            self.dual(|s| s.emit_all(value))
        } else {
            self.main
                .emit_all(value)
                .map_err(BroadcastingProverError::Main)
        }
    }
    fn emit_settings(&mut self, value: &[String]) -> Result<(), Self::Error> {
        if self.broadcast {
            self.dual(|s| s.emit_settings(value))
        } else {
            self.main
                .emit_settings(value)
                .map_err(BroadcastingProverError::Main)
        }
    }
}
impl<
    P: crate::interfaces::decider::prover::Prover,
    W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>,
> ProverLike for BroadcastingProver<P, W>
{
    fn assume_axioms(
        &mut self,
        terms: &InsertionOrderedSet<Term>,
        desc: &str,
    ) -> Result<(), Self::Error> {
        if self.broadcast {
            self.dual(|s| s.assume_axioms(terms, desc))
        } else {
            self.main
                .assume_axioms(terms, desc)
                .map_err(BroadcastingProverError::Main)
        }
    }
    fn set_option(&mut self, name: &str, value: &str) -> Result<String, Self::Error> {
        if self.broadcast {
            self.dual(|s| s.set_option(name, value))
        } else {
            self.main
                .set_option(name, value)
                .map_err(BroadcastingProverError::Main)
        }
    }
    fn assume(&mut self, term: &Term) -> Result<(), Self::Error> {
        if self.broadcast {
            self.dual(|s| s.assume(term))
        } else {
            self.main
                .assume(term)
                .map_err(BroadcastingProverError::Main)
        }
    }
    fn declare(&mut self, decl: &Declaration) -> Result<(), Self::Error> {
        if self.broadcast {
            self.dual(|s| s.declare(decl))
        } else {
            self.main
                .declare(decl)
                .map_err(BroadcastingProverError::Main)
        }
    }
    fn comment(&mut self, content: &mut dyn FnMut() -> String) -> Result<(), Self::Error> {
        if self.broadcast {
            self.dual(|s| s.comment(content))
        } else {
            self.main
                .comment(content)
                .map_err(BroadcastingProverError::Main)
        }
    }
    fn saturate(&mut self, timeout: i32, comment: &str) -> Result<(), Self::Error> {
        if self.broadcast {
            self.dual(|s| s.saturate(timeout, comment))
        } else {
            self.main
                .saturate(timeout, comment)
                .map_err(BroadcastingProverError::Main)
        }
    }
    fn saturate_configured(
        &mut self,
        data: Option<&ProverStateSaturationTimeout>,
    ) -> Result<(), Self::Error> {
        if self.broadcast {
            self.dual(|s| s.saturate_configured(data))
        } else {
            self.main
                .saturate_configured(data)
                .map_err(BroadcastingProverError::Main)
        }
    }
}
impl<
    P: crate::interfaces::decider::prover::Prover,
    W: ThreadBoundWorker<Broadcast = WorkerPreambleCommand, BroadcastResult = Option<String>>,
> crate::interfaces::decider::prover::Prover for BroadcastingProver<P, W>
{
    type Model = P::Model;
    type Version = P::Version;
    fn start(&mut self, args: Option<&str>) -> Result<(), Self::Error> {
        self.require_main_only()?;
        self.main.start(args).map_err(BroadcastingProverError::Main)
    }
    fn reset(&mut self) -> Result<(), Self::Error> {
        self.require_main_only()?;
        self.main.reset().map_err(BroadcastingProverError::Main)
    }
    fn stop(&mut self) -> Result<(), Self::Error> {
        self.require_main_only()?;
        self.main.stop().map_err(BroadcastingProverError::Main)
    }
    fn assert_goal(&mut self, goal: &Term, timeout: Option<i32>) -> Result<bool, Self::Error> {
        self.require_main_only()?;
        self.main
            .assert_goal(goal, timeout)
            .map_err(BroadcastingProverError::Main)
    }
    fn check(
        &mut self,
        timeout: Option<i32>,
    ) -> Result<crate::interfaces::decider::prover::SatResult, Self::Error> {
        self.require_main_only()?;
        self.main
            .check(timeout)
            .map_err(BroadcastingProverError::Main)
    }
    fn fresh(
        &mut self,
        id: &str,
        args: &[crate::state::terms::Sort],
        result: &crate::state::terms::Sort,
    ) -> Result<crate::state::terms::ApplicationTarget, Self::Error> {
        self.require_main_only()?;
        self.main
            .fresh(id, args, result)
            .map_err(BroadcastingProverError::Main)
    }
    fn statistics(&mut self) -> Result<Vec<(String, String)>, Self::Error> {
        self.main
            .statistics()
            .map_err(BroadcastingProverError::Main)
    }
    fn has_model(&self) -> bool {
        self.main.has_model()
    }
    fn is_model_valid(&self) -> bool {
        self.main.is_model_valid()
    }
    fn get_model(&mut self) -> Result<Self::Model, Self::Error> {
        self.main.get_model().map_err(BroadcastingProverError::Main)
    }
    fn get_reason_unknown(&mut self) -> Result<String, Self::Error> {
        self.main
            .get_reason_unknown()
            .map_err(BroadcastingProverError::Main)
    }
    fn clear_last_assert(&mut self) {
        self.main.clear_last_assert()
    }
    fn name(&self) -> &str {
        self.main.name()
    }
    fn min_version(&self) -> Self::Version {
        self.main.min_version()
    }
    fn max_version(&self) -> Option<Self::Version> {
        self.main.max_version()
    }
    fn version(&mut self) -> Result<Self::Version, Self::Error> {
        self.main.version().map_err(BroadcastingProverError::Main)
    }
    fn static_preamble(&self) -> &str {
        self.main.static_preamble()
    }
    fn randomize_seeds_options(&self) -> &[String] {
        self.main.randomize_seeds_options()
    }
    fn push_pop_scope_depth(&self) -> usize {
        self.main.push_pop_scope_depth()
    }
    fn push(&mut self, n: usize, timeout: Option<i32>) -> Result<(), Self::Error> {
        self.require_main_only()?;
        self.main
            .push(n, timeout)
            .map_err(BroadcastingProverError::Main)
    }
    fn pop(&mut self, n: usize) -> Result<(), Self::Error> {
        self.require_main_only()?;
        self.main.pop(n).map_err(BroadcastingProverError::Main)
    }
    fn all_declarations(&self) -> Vec<Declaration> {
        self.main.all_declarations()
    }
    fn all_emits(&self) -> Vec<String> {
        self.main.all_emits()
    }
}

fn set_verification_scope(
    results: &[crate::interfaces::verification::VerificationResult<
        ferrum_silver::verifier::verification_error::VerificationError,
    >],
    member: std::sync::Arc<ferrum_silver::ast::program::Member>,
) {
    for result in results {
        result.with_kind(|kind| {
            if let crate::interfaces::verification::ResultKind::Failure(error) = kind {
                error.set_scope(Some(member.clone()));
            }
        });
    }
}
fn report_member_results(
    reporter: &dyn ferrum_silver::reporter::reporter::Reporter,
    member: Option<std::sync::Arc<ferrum_silver::ast::program::Member>>,
    elapsed: std::time::Duration,
    results: &[crate::interfaces::verification::VerificationResult<
        ferrum_silver::verifier::verification_error::VerificationError,
    >],
) -> Result<(), ferrum_silver::reporter::reporter::ReportError> {
    use ferrum_silver::{
        reporter::message::Message,
        verifier::{
            verification_error::{NativeErrorNodeRenderer, RenderedVerificationError},
            verification_result::AbstractError,
        },
    };
    let mut errors = Vec::new();
    for result in results {
        result.with_kind(
            |kind| -> Result<(), ferrum_silver::reporter::reporter::ReportError> {
                if let crate::interfaces::verification::ResultKind::Failure(error) = kind {
                    let error = RenderedVerificationError::new(
                        error.clone(),
                        std::sync::Arc::new(NativeErrorNodeRenderer),
                    )?;
                    errors.push(AbstractError::Verification(std::sync::Arc::new(error)));
                }
                Ok(())
            },
        )?;
    }
    let time = i64::try_from(elapsed.as_millis()).unwrap_or(i64::MAX);
    let message = match (member, errors.is_empty()) {
        (Some(concerning), true) => Message::EntitySuccess {
            verifier: "silicon".into(),
            concerning,
            time,
            cached: false,
        },
        (Some(concerning), false) => Message::EntityFailure {
            verifier: "silicon".into(),
            concerning,
            time,
            errors,
            cached: false,
        },
        (None, true) => Message::OverallSuccess {
            verifier: "silicon".into(),
            time,
        },
        (None, false) => Message::OverallFailure {
            verifier: "silicon".into(),
            time,
            errors,
        },
    };
    reporter.report(message)
}

/// Source method or standalone CFG task after main analysis.
pub enum NativeWorkerTarget {
    Method(ferrum_silver::ast::program::Method),
    Cfg(ferrum_silver::cfg::silver::silver_cfg::SilverCfg),
}
pub struct NativeWorkerTask {
    pub analysis: std::sync::Arc<super::native_context::NativeWorkerAnalysis>,
    pub target: NativeWorkerTarget,
    pub reporter: Option<std::sync::Arc<dyn ferrum_silver::reporter::reporter::Reporter>>,
    pub warning_sink: Option<std::sync::Arc<std::sync::Mutex<Vec<String>>>>,
}
/// Concrete worker over the real native execution context. `start` installs the
/// context's static preamble; broadcast only the later analysis and post-verification
/// contributions, in source order, to avoid duplicating the static preamble.
pub struct NativeMethodWorker<S: crate::interfaces::decider::prover::Prover> {
    pub context: super::native_context::NativeVerifierContext<
        S,
        crate::supporters::predicate_verification_unit::PredicateData,
        super::native_context::NativeFunctionData,
    >,
    pub user_args: Option<String>,
    pub config_options: Vec<String>,
}
/// Construct a native worker on its eventual owner thread. The caller supplies
/// the same identifier factory used by its prover, preventing fresh-name collisions.
pub fn native_method_worker<S: crate::interfaces::decider::prover::Prover>(
    unique_id: String,
    prover: S,
    identifiers: crate::state::identifiers::DefaultIdentifierFactory,
    factory: crate::state::terms::TermFactory,
    options: super::native_context::NativeOptions,
    config: &crate::config::Config,
) -> NativeMethodWorker<S> {
    let config_options = if config.prover == "Z3-API" {
        Vec::new()
    } else {
        config
            .prover_config_args
            .iter()
            .map(|(key, value)| format!("(set-option :{key} {value})"))
            .collect()
    };
    let decider = crate::decider::decider::DefaultDecider::new(
        prover,
        config.enable_debugging,
        config.assert_timeout,
        Some(config.check_timeout),
        Some(config.push_timeout),
    );
    let base = super::base_verifier::BaseVerifier::new_with_identifiers(
        unique_id,
        decider,
        factory.clone(),
        config.mask_heap_mode,
        config.state_consolidation_mode,
        identifiers,
    );
    NativeMethodWorker {
        context: super::native_context::NativeVerifierContext::new(base, factory, options),
        user_args: config.prover_args.clone(),
        config_options,
    }
}

impl<S> ThreadBoundWorker for NativeMethodWorker<S>
where
    S: crate::interfaces::decider::prover::Prover + 'static,
    S::Error: Send + std::fmt::Debug + 'static,
{
    type Error = super::native_context::NativeError<S::Error>;
    type Broadcast = WorkerPreambleCommand;
    type BroadcastResult = Option<String>;
    type Task = NativeWorkerTask;
    type Output = Vec<
        crate::interfaces::verification::VerificationResult<
            ferrum_silver::verifier::verification_error::VerificationError,
        >,
    >;
    fn start(&mut self) -> Result<(), Self::Error> {
        self.context
            .start(self.user_args.as_deref(), &self.config_options)
    }
    fn broadcast(&mut self, command: WorkerPreambleCommand) -> Result<Option<String>, Self::Error> {
        command
            .apply(&mut self.context.base.decider.prover)
            .map_err(|e| {
                super::native_context::NativeError::Decider(
                    crate::decider::decider::DeciderError::Prover(e),
                )
            })
    }
    fn verify(&mut self, task: NativeWorkerTask) -> Result<Self::Output, Self::Error> {
        let start = std::time::Instant::now();
        let outcome = match &task.target {
            NativeWorkerTarget::Method(method) => {
                self.context.verify_worker_method(&task.analysis, method)
            }
            NativeWorkerTarget::Cfg(cfg) => self.context.verify_worker_cfg(&task.analysis, cfg),
        };
        let warnings = std::mem::take(&mut self.context.warnings);
        if !warnings.is_empty() {
            if let Some(sink) = &task.warning_sink {
                sink.lock()
                    .expect("poisoned native warning sink")
                    .extend(warnings);
            } else if let Some(reporter) = &task.reporter {
                use ferrum_silver::{
                    ast::position::Position,
                    reporter::message::Message,
                    verifier::verification_result::{FrontendError, FrontendErrorKind},
                };
                reporter
                    .report(Message::WarningsDuringVerification {
                        warnings: warnings
                            .into_iter()
                            .map(|warning| {
                                FrontendError::new(
                                    FrontendErrorKind::VerifierWarning(warning),
                                    Position::NoPosition,
                                )
                            })
                            .collect(),
                    })
                    .map_err(|error| {
                        super::native_context::NativeError::Diagnostic(format!(
                            "worker warning reporter: {error:?}"
                        ))
                    })?;
            } else {
                return Err(super::native_context::NativeError::Unsupported(
                    "worker warnings require reporter or warning sink",
                ));
            }
        }
        let results = outcome?;
        let member = match task.target {
            NativeWorkerTarget::Method(method) => Some(std::sync::Arc::new(
                ferrum_silver::ast::program::Member::Method(method),
            )),
            NativeWorkerTarget::Cfg(_) => None,
        };
        if let Some(reporter) = task.reporter {
            report_member_results(reporter.as_ref(), member.clone(), start.elapsed(), &results)
                .map_err(|error| {
                    super::native_context::NativeError::Diagnostic(format!(
                        "worker result reporter: {error:?}"
                    ))
                })?;
        }
        if let Some(member) = member {
            set_verification_scope(&results, member);
        }
        Ok(results)
    }
    fn reset(&mut self) -> Result<(), Self::Error> {
        self.context.reset()
    }
    fn stop(&mut self) -> Result<(), Self::Error> {
        self.context.stop()
    }
}

#[derive(Debug)]
pub enum NativeParallelError<E> {
    Main(
        super::native_context::NativeError<
            BroadcastingProverError<E, super::native_context::NativeError<E>>,
        >,
    ),
    Worker(ThreadPoolError<super::native_context::NativeError<E>>),
    Reporter(ferrum_silver::reporter::reporter::ReportError),
    Unsupported(&'static str),
}
/// Run source member ordering on an already started main context and worker pool.
/// Each context must have installed its own static preamble and share the term
/// factory mode. Nested branch parallelism remains unavailable; CFG resource
/// analysis has the same unimplemented boundaries as the source contributor setup.
pub fn verify_native_parallel<P>(
    context: &mut super::native_context::NativeVerifierContext<
        BroadcastingProver<P, NativeMethodWorker<P>>,
        crate::supporters::predicate_verification_unit::PredicateData,
        super::native_context::NativeFunctionData,
    >,
    original: &ferrum_silver::ast::program::Program,
    cfgs: &[ferrum_silver::cfg::silver::silver_cfg::SilverCfg],
    input_file: Option<&str>,
) -> Result<
    Vec<
        crate::interfaces::verification::VerificationResult<
            ferrum_silver::verifier::verification_error::VerificationError,
        >,
    >,
    NativeParallelError<P::Error>,
>
where
    P: crate::interfaces::decider::prover::Prover + 'static,
    P::Error: Send + std::fmt::Debug + 'static,
{
    verify_native_parallel_with_reporter(context, original, cfgs, input_file, None)
}
pub fn verify_native_parallel_with_reporter<P>(
    context: &mut super::native_context::NativeVerifierContext<
        BroadcastingProver<P, NativeMethodWorker<P>>,
        crate::supporters::predicate_verification_unit::PredicateData,
        super::native_context::NativeFunctionData,
    >,
    original: &ferrum_silver::ast::program::Program,
    cfgs: &[ferrum_silver::cfg::silver::silver_cfg::SilverCfg],
    input_file: Option<&str>,
    reporter: Option<std::sync::Arc<dyn ferrum_silver::reporter::reporter::Reporter>>,
) -> Result<
    Vec<
        crate::interfaces::verification::VerificationResult<
            ferrum_silver::verifier::verification_error::VerificationError,
        >,
    >,
    NativeParallelError<P::Error>,
>
where
    P: crate::interfaces::decider::prover::Prover + 'static,
    P::Error: Send + std::fmt::Debug + 'static,
{
    verify_native_parallel_with_reporting(context, original, cfgs, input_file, reporter, None)
}
pub fn verify_native_parallel_with_reporting<P>(
    context: &mut super::native_context::NativeVerifierContext<
        BroadcastingProver<P, NativeMethodWorker<P>>,
        crate::supporters::predicate_verification_unit::PredicateData,
        super::native_context::NativeFunctionData,
    >,
    original: &ferrum_silver::ast::program::Program,
    cfgs: &[ferrum_silver::cfg::silver::silver_cfg::SilverCfg],
    input_file: Option<&str>,
    reporter: Option<std::sync::Arc<dyn ferrum_silver::reporter::reporter::Reporter>>,
    warning_sink: Option<std::sync::Arc<std::sync::Mutex<Vec<String>>>>,
) -> Result<
    Vec<
        crate::interfaces::verification::VerificationResult<
            ferrum_silver::verifier::verification_error::VerificationError,
        >,
    >,
    NativeParallelError<P::Error>,
>
where
    P: crate::interfaces::decider::prover::Prover + 'static,
    P::Error: Send + std::fmt::Debug + 'static,
{
    use super::default_main_verifier::MainVerificationServices;
    use crate::interfaces::decider::prover::Prover;
    let program = context
        .preprocess(original)
        .map_err(NativeParallelError::Main)?;
    context
        .setup_predicate_snapshots(&program)
        .map_err(NativeParallelError::Main)?;
    context
        .begin_preamble(input_file)
        .map_err(NativeParallelError::Main)?;
    context
        .emit_static_preamble()
        .map_err(NativeParallelError::Main)?;
    context.base.decider.prover.set_preamble_broadcast(true);
    let initial = (|| {
        let analysis = context.analyze_and_emit_contributions(&program)?;
        context.end_preamble_and_saturate()?;
        Ok::<
            _,
            super::native_context::NativeError<
                BroadcastingProverError<P::Error, super::native_context::NativeError<P::Error>>,
            >,
        >(analysis)
    })();
    context.base.decider.prover.set_preamble_broadcast(false);
    let analysis = initial.map_err(NativeParallelError::Main)?;
    let mut results = Vec::new();
    for function in context
        .function_units()
        .map_err(NativeParallelError::Main)?
    {
        let member = std::sync::Arc::new(ferrum_silver::ast::program::Member::Function(
            function.clone(),
        ));
        let start = std::time::Instant::now();
        let function_results = context
            .verify_function_unscoped(&program, &analysis, &function)
            .map_err(NativeParallelError::Main)?;
        if let Some(reporter) = &reporter {
            report_member_results(
                reporter.as_ref(),
                Some(member.clone()),
                start.elapsed(),
                &function_results,
            )
            .map_err(NativeParallelError::Reporter)?;
        }
        set_verification_scope(&function_results, member);
        results.extend(function_results);
    }
    for predicate in context
        .predicate_units()
        .map_err(NativeParallelError::Main)?
    {
        let member = std::sync::Arc::new(ferrum_silver::ast::program::Member::Predicate(
            predicate.clone(),
        ));
        let start = std::time::Instant::now();
        let predicate_results = context
            .verify_predicate_unscoped(&program, &analysis, &predicate)
            .map_err(NativeParallelError::Main)?;
        if let Some(reporter) = &reporter {
            report_member_results(
                reporter.as_ref(),
                Some(member.clone()),
                start.elapsed(),
                &predicate_results,
            )
            .map_err(NativeParallelError::Reporter)?;
        }
        set_verification_scope(&predicate_results, member);
        results.extend(predicate_results);
    }
    let worker_analysis = std::sync::Arc::new(context.worker_analysis(&program, &analysis));
    context.base.decider.prover.stop().map_err(|error| {
        NativeParallelError::Main(super::native_context::NativeError::Decider(
            crate::decider::decider::DeciderError::Prover(error),
        ))
    })?;
    let pool = context.base.decider.prover.pool.clone();
    {
        let mut borrowed = pool.borrow_mut();
        let mut sink = ThreadPoolPreambleSink {
            pool: &mut borrowed,
        };
        context
            .emit_worker_post_preamble(&analysis, &mut sink)
            .map_err(NativeParallelError::Worker)?;
    }
    let mut tasks = Vec::new();
    let mut task_error = None;
    for method in &program.methods {
        if !context.excluded_method(method) {
            match pool.borrow_mut().submit(NativeWorkerTask {
                analysis: worker_analysis.clone(),
                target: NativeWorkerTarget::Method(method.clone()),
                reporter: reporter.clone(),
                warning_sink: warning_sink.clone(),
            }) {
                Ok(task) => tasks.push(task),
                Err(error) => {
                    task_error = Some(error);
                    break;
                }
            }
        }
    }
    if task_error.is_none() {
        for cfg in cfgs {
            match pool.borrow_mut().submit(NativeWorkerTask {
                analysis: worker_analysis.clone(),
                target: NativeWorkerTarget::Cfg(cfg.clone()),
                reporter: reporter.clone(),
                warning_sink: warning_sink.clone(),
            }) {
                Ok(task) => tasks.push(task),
                Err(error) => {
                    task_error = Some(error);
                    break;
                }
            }
        }
    }
    for outcome in finish_task_batch(tasks, task_error).map_err(NativeParallelError::Worker)? {
        results.extend(outcome);
    }
    if let Some(reporter) = &reporter {
        reporter
            .report(ferrum_silver::reporter::message::Message::VerificationTermination)
            .map_err(NativeParallelError::Reporter)?;
    }
    context
        .report_termination_and_optional_trace()
        .map_err(NativeParallelError::Main)?;
    context
        .run_optional_debugger(&results)
        .map_err(NativeParallelError::Main)?;
    Ok(results)
}

#[cfg(test)]
mod thread_pool_tests {
    use super::*;
    use std::sync::{Arc, Mutex};

    #[test]
    fn failed_batch_waits_for_every_submitted_task() {
        let (first_tx, first_rx) = std::sync::mpsc::channel();
        let (second_tx, second_rx) = std::sync::mpsc::channel();
        let (done_tx, done_rx) = std::sync::mpsc::channel();
        first_tx
            .send(Err(ThreadPoolError::Worker("first")))
            .unwrap();
        let waiter = std::thread::spawn(move || {
            done_tx
                .send(finish_task_batch(
                    vec![VerificationTask(first_rx), VerificationTask(second_rx)],
                    None,
                ))
                .unwrap();
        });
        assert!(
            done_rx
                .recv_timeout(std::time::Duration::from_millis(50))
                .is_err()
        );
        second_tx.send(Ok(7)).unwrap();
        assert!(matches!(
            done_rx.recv().unwrap(),
            Err(ThreadPoolError::Worker("first"))
        ));
        waiter.join().unwrap();
    }

    struct Worker {
        id: usize,
        owner: std::thread::ThreadId,
        _not_send: std::rc::Rc<()>,
        events: Arc<Mutex<Vec<(usize, &'static str)>>>,
        preamble: Vec<u8>,
    }
    impl Worker {
        fn event(&self, event: &'static str) {
            assert_eq!(self.owner, std::thread::current().id());
            self.events.lock().unwrap().push((self.id, event));
        }
    }
    impl ThreadBoundWorker for Worker {
        type Error = &'static str;
        type Broadcast = u8;
        type BroadcastResult = ();
        type Task = usize;
        type Output = usize;
        fn start(&mut self) -> Result<(), Self::Error> {
            self.event("start");
            Ok(())
        }
        fn broadcast(&mut self, command: u8) -> Result<(), Self::Error> {
            self.event("broadcast");
            self.preamble.push(command);
            Ok(())
        }
        fn verify(&mut self, task: usize) -> Result<usize, Self::Error> {
            self.event("verify");
            if self.preamble != [1, 2] {
                return Err("incomplete preamble");
            }
            Ok(task)
        }
        fn reset(&mut self) -> Result<(), Self::Error> {
            self.event("reset");
            self.preamble.clear();
            Ok(())
        }
        fn stop(&mut self) -> Result<(), Self::Error> {
            self.event("stop");
            Ok(())
        }
    }
    #[test]
    fn source_preamble_command_is_send_and_comment_is_lazy_shared() {
        fn assert_send<T: Send>() {}
        assert_send::<WorkerPreambleCommand>();
        let count = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let captured = count.clone();
        let comment = LazyWorkerComment::new(move || {
            captured.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            "message".into()
        });
        let other = comment.clone();
        assert_eq!(count.load(std::sync::atomic::Ordering::SeqCst), 0);
        assert_eq!(other.value(), "message");
        assert_eq!(comment.value(), "message");
        assert_eq!(count.load(std::sync::atomic::Ordering::SeqCst), 1);
    }
    #[test]
    fn pooled_comment_evaluates_only_on_request_and_once() {
        struct CommentWorker {
            use_comment: bool,
        }
        impl ThreadBoundWorker for CommentWorker {
            type Error = ();
            type Broadcast = WorkerPreambleCommand;
            type BroadcastResult = Option<String>;
            type Task = ();
            type Output = ();
            fn start(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn broadcast(&mut self, command: WorkerPreambleCommand) -> Result<Option<String>, ()> {
                match command {
                    WorkerPreambleCommand::Emit(_) => self.use_comment = true,
                    WorkerPreambleCommand::Comment(comment) if self.use_comment => {
                        assert_eq!(comment.value(), "lazy");
                    }
                    _ => (),
                }
                Ok(None)
            }
            fn verify(&mut self, _: ()) -> Result<(), ()> {
                Ok(())
            }
            fn reset(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), ()> {
                Ok(())
            }
        }
        let mut pool =
            ThreadVerificationPool::start(2, |_| Ok(CommentWorker { use_comment: false })).unwrap();
        let count = std::cell::Cell::new(0);
        {
            let mut sink = ThreadPoolPreambleSink { pool: &mut pool };
            sink.comment(&mut || {
                count.set(count.get() + 1);
                "lazy".into()
            })
            .unwrap();
            assert_eq!(count.get(), 0);
            sink.emit("enable").unwrap();
            sink.comment(&mut || {
                count.set(count.get() + 1);
                "lazy".into()
            })
            .unwrap();
            assert_eq!(count.get(), 1);
        }
        pool.shutdown().unwrap();
    }
    #[test]
    fn thread_bound_workers_receive_ordered_preambles_and_results() {
        let events = Arc::new(Mutex::new(Vec::new()));
        let sink = events.clone();
        let mut pool = ThreadVerificationPool::start(3, move |id| {
            Ok(Worker {
                id,
                owner: std::thread::current().id(),
                _not_send: std::rc::Rc::new(()),
                events: sink.clone(),
                preamble: vec![],
            })
        })
        .unwrap();
        pool.broadcast(1).unwrap();
        pool.broadcast(2).unwrap();
        let tasks = (0..40).map(|n| pool.submit(n).unwrap()).collect::<Vec<_>>();
        let results = tasks
            .into_iter()
            .map(|task| task.wait().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(results, (0..40).collect::<Vec<_>>());
        pool.reset().unwrap();
        pool.shutdown().unwrap();
        let events = events.lock().unwrap();
        let broadcasts = events
            .iter()
            .filter(|(_, e)| *e == "broadcast")
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        let starts = events
            .iter()
            .filter(|(_, e)| *e == "start")
            .map(|(id, _)| *id)
            .collect::<Vec<_>>();
        assert_eq!(starts, [2, 1, 0]);
        assert_eq!(broadcasts, [2, 1, 0, 2, 1, 0]);
        assert_eq!(events.iter().filter(|(_, e)| *e == "stop").count(), 3);
    }
    #[test]
    fn cancel_pending_leaves_running_worker_and_reports_cancelled_jobs() {
        struct BlockingWorker(Arc<std::sync::Barrier>, Arc<std::sync::Barrier>);
        impl ThreadBoundWorker for BlockingWorker {
            type Error = ();
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = usize;
            type Output = usize;
            fn start(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), ()> {
                Ok(())
            }
            fn verify(&mut self, value: usize) -> Result<usize, ()> {
                self.0.wait();
                self.1.wait();
                Ok(value)
            }
            fn reset(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), ()> {
                Ok(())
            }
        }
        let started = Arc::new(std::sync::Barrier::new(2));
        let finish = Arc::new(std::sync::Barrier::new(2));
        let (a, b) = (started.clone(), finish.clone());
        let mut pool =
            ThreadVerificationPool::start(1, move |_| Ok(BlockingWorker(a.clone(), b.clone())))
                .unwrap();
        let running = pool.submit(1).unwrap();
        started.wait();
        let queued1 = pool.submit(2).unwrap();
        let queued2 = pool.submit(3).unwrap();
        assert_eq!(pool.cancel_pending().unwrap(), 2);
        assert!(matches!(queued1.wait(), Err(ThreadPoolError::Cancelled)));
        assert!(matches!(queued2.wait(), Err(ThreadPoolError::Cancelled)));
        finish.wait();
        assert_eq!(running.wait().unwrap(), 1);
        pool.shutdown().unwrap();
    }
    #[test]
    fn drop_cancels_queued_work_and_waits_for_running_worker() {
        struct BlockingWorker(Arc<std::sync::Barrier>, Arc<std::sync::Barrier>);
        impl ThreadBoundWorker for BlockingWorker {
            type Error = ();
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = ();
            type Output = ();
            fn start(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), ()> {
                Ok(())
            }
            fn verify(&mut self, _: ()) -> Result<(), ()> {
                self.0.wait();
                self.1.wait();
                Ok(())
            }
            fn reset(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), ()> {
                Ok(())
            }
        }
        let started = Arc::new(std::sync::Barrier::new(2));
        let finish = Arc::new(std::sync::Barrier::new(2));
        let (a, b) = (started.clone(), finish.clone());
        let mut pool =
            ThreadVerificationPool::start(1, move |_| Ok(BlockingWorker(a.clone(), b.clone())))
                .unwrap();
        let running = pool.submit(()).unwrap();
        started.wait();
        let queued = pool.submit(()).unwrap();
        let dropping = std::thread::spawn(move || drop(pool));
        assert!(matches!(queued.wait(), Err(ThreadPoolError::Cancelled)));
        finish.wait();
        dropping.join().unwrap();
        assert!(running.wait().is_ok());
    }
    #[test]
    fn panic_cancels_queued_work_and_does_not_hang_shutdown() {
        struct PanicWorker(Arc<std::sync::Barrier>);
        impl ThreadBoundWorker for PanicWorker {
            type Error = ();
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = usize;
            type Output = usize;
            fn start(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), ()> {
                Ok(())
            }
            fn verify(&mut self, _: usize) -> Result<usize, ()> {
                self.0.wait();
                panic!("worker failure")
            }
            fn reset(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), ()> {
                Ok(())
            }
        }
        let barrier = Arc::new(std::sync::Barrier::new(2));
        let b = barrier.clone();
        let mut pool =
            ThreadVerificationPool::start(1, move |_| Ok(PanicWorker(b.clone()))).unwrap();
        let first = pool.submit(0).unwrap();
        let second = pool.submit(1).unwrap();
        barrier.wait();
        assert!(matches!(first.wait(), Err(ThreadPoolError::WorkerPanicked)));
        assert!(matches!(
            second.wait(),
            Err(ThreadPoolError::WorkerDisconnected)
        ));
        assert!(matches!(pool.submit(2), Err(ThreadPoolError::Stopped)));
        assert!(matches!(pool.shutdown(), Err(ThreadPoolError::Stopped)));
    }
    #[test]
    fn shutdown_attempts_every_worker_after_a_stop_error() {
        struct StopWorker {
            id: usize,
            stopped: Arc<Mutex<Vec<usize>>>,
        }
        impl ThreadBoundWorker for StopWorker {
            type Error = usize;
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = ();
            type Output = ();
            fn start(&mut self) -> Result<(), usize> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), usize> {
                Ok(())
            }
            fn verify(&mut self, _: ()) -> Result<(), usize> {
                Ok(())
            }
            fn reset(&mut self) -> Result<(), usize> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), usize> {
                self.stopped.lock().unwrap().push(self.id);
                if self.id == 1 { Err(self.id) } else { Ok(()) }
            }
        }
        let stopped = Arc::new(Mutex::new(Vec::new()));
        let record = stopped.clone();
        let pool = ThreadVerificationPool::start(3, move |id| {
            Ok(StopWorker {
                id,
                stopped: record.clone(),
            })
        })
        .unwrap();
        assert!(matches!(pool.shutdown(), Err(ThreadPoolError::Worker(1))));
        assert_eq!(*stopped.lock().unwrap(), [2, 1, 0]);
    }
    fn run_parallel_source_with_warnings<P, F>(
        source: &str,
        workers: usize,
        make: F,
        standalone_cfg: bool,
    ) -> (Vec<bool>, Vec<String>)
    where
        P: crate::interfaces::decider::prover::Prover + 'static,
        P::Error: Send + std::fmt::Debug + 'static,
        F: Fn(
                String,
                crate::state::terms::TermFactory,
            ) -> (P, crate::state::identifiers::DefaultIdentifierFactory)
            + Clone
            + Send
            + Sync
            + 'static,
    {
        use crate::{
            config::Config,
            decider::decider::DefaultDecider,
            state::terms::{TermFactory, TermOptions},
            verifier::{
                base_verifier::BaseVerifier,
                native_context::{NativeOptions, NativeVerifierContext},
            },
        };
        use ferrum_silver::frontend::{
            frontend::FrontendPhases,
            sil_front_end_config::SilFrontendConfig,
            sil_frontend::{SilFrontendPhases, standard_plugin_manager},
        };
        let config = Config::default();
        let native_options = NativeOptions::from_config(&config).unwrap();
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let worker_factory = factory.clone();
        let worker_options = native_options.clone();
        let worker_config = config.clone();
        let worker_make = make.clone();
        let pool = ThreadVerificationPool::start(workers, move |id| {
            let name = format!("worker-{id}");
            let (prover, identifiers) = worker_make(name.clone(), worker_factory.clone());
            Ok(native_method_worker(
                name,
                prover,
                identifiers,
                worker_factory.clone(),
                worker_options.clone(),
                &worker_config,
            ))
        })
        .unwrap();
        let pool = std::rc::Rc::new(std::cell::RefCell::new(pool));
        let (prover, identifiers) = make("main".into(), factory.clone());
        let prover = BroadcastingProver::new(prover, pool.clone());
        let decider = DefaultDecider::new(prover, false, None, None, None);
        let base = BaseVerifier::new_with_identifiers(
            "main".into(),
            decider,
            factory.clone(),
            false,
            crate::config::StateConsolidationMode::Default,
            identifiers,
        );
        let mut context = NativeVerifierContext::new(base, factory, native_options);
        context.start(None, &[]).unwrap();
        let frontend_config = SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            std::path::PathBuf::from("test.vpr"),
            standard_plugin_manager(&frontend_config).unwrap(),
        );
        let parsed = phases.parse(source).unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        let cfgs = if standalone_cfg {
            program
                .methods
                .iter()
                .map(|method| {
                    ferrum_silver::cfg::silver::cfg_generator::statement_to_cfg(
                        method.body.as_ref().unwrap(),
                        true,
                        true,
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let program = if standalone_cfg {
            program.copy_with(|data| data.methods.clear())
        } else {
            program
        };
        struct CapturingReporter(std::sync::Mutex<Vec<ferrum_silver::reporter::message::Message>>);
        impl ferrum_silver::reporter::reporter::Reporter for CapturingReporter {
            fn name(&self) -> &str {
                "test"
            }
            fn report(
                &self,
                message: ferrum_silver::reporter::message::Message,
            ) -> Result<(), ferrum_silver::reporter::reporter::ReportError> {
                if let ferrum_silver::reporter::message::Message::EntityFailure { errors, .. } =
                    &message
                {
                    for error in errors {
                        assert!(
                            error.scope().unwrap().is_none(),
                            "source reports before assigning scope"
                        );
                    }
                }
                self.0.lock().unwrap().push(message);
                Ok(())
            }
        }
        let reporter = std::sync::Arc::new(CapturingReporter(std::sync::Mutex::new(Vec::new())));
        let worker_warnings = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let results = verify_native_parallel_with_reporting(
            &mut context,
            &program,
            &cfgs,
            None,
            Some(reporter.clone()),
            Some(worker_warnings.clone()),
        )
        .unwrap();
        let reports = reporter.0.lock().unwrap();
        assert!(matches!(
            reports.last(),
            Some(ferrum_silver::reporter::message::Message::VerificationTermination)
        ));
        let failures = reports
            .iter()
            .filter_map(|message| match message {
                ferrum_silver::reporter::message::Message::EntityFailure { errors, .. }
                | ferrum_silver::reporter::message::Message::OverallFailure { errors, .. } => {
                    Some(errors)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(failures.len(), 1);
        if standalone_cfg {
            assert!(failures[0][0].scope().unwrap().is_none());
        } else {
            let scope = failures[0][0]
                .scope()
                .unwrap()
                .expect("reported error scope");
            assert_eq!(scope.name(), "bad");
        }
        drop(reports);
        for result in &results {
            result.with_kind(|kind| {
                if let crate::interfaces::verification::ResultKind::Failure(error) = kind {
                    if standalone_cfg {
                        assert!(error.scope().is_none());
                    } else {
                        let scope = error.scope().expect("member scope on failure");
                        assert_eq!(scope.name(), "bad");
                    }
                }
            });
        }
        let fatal = results.iter().map(|result| result.is_fatal()).collect();
        drop(context);
        std::rc::Rc::try_unwrap(pool)
            .ok()
            .unwrap()
            .into_inner()
            .shutdown()
            .unwrap();
        let warnings = std::mem::take(&mut *worker_warnings.lock().unwrap());
        (fatal, warnings)
    }
    #[cfg(feature = "native-z3")]
    fn run_parallel_source<P, F>(source: &str, workers: usize, make: F) -> Vec<bool>
    where
        P: crate::interfaces::decider::prover::Prover + 'static,
        P::Error: Send + std::fmt::Debug + 'static,
        F: Fn(
                String,
                crate::state::terms::TermFactory,
            ) -> (P, crate::state::identifiers::DefaultIdentifierFactory)
            + Clone
            + Send
            + Sync
            + 'static,
    {
        run_parallel_source_with_warnings(source, workers, make, false).0
    }
    #[cfg(feature = "native-z3")]
    fn run_parallel_linked(source: &str, workers: usize) -> Vec<bool> {
        use crate::decider::{
            native_z3::{LinkedProverOptions, LinkedZ3Prover},
            z3_prover_api::ApiTimeoutSettings,
        };
        let make = |name: String, factory: crate::state::terms::TermFactory| {
            let prover = LinkedZ3Prover::new(
                name,
                factory,
                LinkedProverOptions {
                    timeout: ApiTimeoutSettings {
                        default_timeout_ms: 0,
                        use_time_bounds: true,
                        resources_per_millisecond: 1,
                    },
                    counterexamples: false,
                    report_reason_unknown: false,
                    debug: false,
                    soft_assertions: false,
                    custom_options: vec![],
                    disable_nonlinear: false,
                },
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        run_parallel_source(source, workers, make)
    }
    #[cfg(unix)]
    #[test]
    fn real_parallel_stdio_transports_worker_warnings() {
        use crate::decider::{prover_std_io::ProverEvent, z3_prover_std_io};
        use std::os::unix::fs::PermissionsExt;
        if std::env::var_os("FERRUM_TEST_Z3").is_none() {
            eprintln!("skipping stdio solver integration: FERRUM_TEST_Z3 is unset");
            return;
        }
        let wrapper =
            std::env::temp_dir().join(format!("ferrum-parallel-z3-wrapper-{}", std::process::id()));
        std::fs::write(
            &wrapper,
            "#!/bin/sh\nprintf 'WARNING pool transport\\n'\nexec \"$FERRUM_TEST_Z3\" \"$@\"\n",
        )
        .unwrap();
        std::fs::set_permissions(&wrapper, std::fs::Permissions::from_mode(0o700)).unwrap();
        let warnings = Arc::new(Mutex::new(Vec::new()));
        let sink = warnings.clone();
        let path = wrapper.clone();
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let events = sink.clone();
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                move |event| {
                    if let ProverEvent::Warning(warning) = event {
                        events.lock().unwrap().push(warning);
                    }
                },
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = "function f(x: Int): Int { x + 1 } @moreJoins(\"bogus\") method good() { assert f(1) == 2; } method bad() { assert f(1) == 3; } method good2() { assert f(2) == 3; } method good3() { assert f(3) == 4; }";
        let (fatal, worker_warnings) = run_parallel_source_with_warnings(source, 2, make, false);
        assert_eq!(fatal.iter().filter(|value| **value).count(), 1);
        assert!(
            worker_warnings
                .iter()
                .any(|w| w.contains("invalid moreJoins"))
        );
        assert_eq!(warnings.lock().unwrap().len(), 3);
        std::fs::remove_file(wrapper).unwrap();
    }
    #[cfg(feature = "native-z3")]
    #[test]
    fn linked_parallel_transports_worker_warnings() {
        use crate::decider::{
            native_z3::{LinkedProverOptions, LinkedZ3Prover},
            z3_prover_api::ApiTimeoutSettings,
        };
        let warnings = Arc::new(Mutex::new(Vec::new()));
        let sink = warnings.clone();
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let mut prover = LinkedZ3Prover::new(
                name,
                factory,
                LinkedProverOptions {
                    timeout: ApiTimeoutSettings {
                        default_timeout_ms: 0,
                        use_time_bounds: true,
                        resources_per_millisecond: 1,
                    },
                    counterexamples: false,
                    report_reason_unknown: false,
                    debug: false,
                    soft_assertions: false,
                    custom_options: vec![("ferrum_unknown_option".into(), "true".into())],
                    disable_nonlinear: false,
                },
            );
            let events = sink.clone();
            prover.set_warning_reporter(move |warning| {
                events.lock().unwrap().push(warning.to_owned())
            });
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = "function f(x: Int): Int { x + 1 } @moreJoins(\"bogus\") method good() { assert f(1) == 2; } method bad() { assert f(1) == 3; } method good2() { assert f(2) == 3; } method good3() { assert f(3) == 4; }";
        let (fatal, worker_warnings) = run_parallel_source_with_warnings(source, 2, make, false);
        assert_eq!(fatal.iter().filter(|value| **value).count(), 1);
        assert!(
            worker_warnings
                .iter()
                .any(|w| w.contains("invalid moreJoins"))
        );
        assert_eq!(warnings.lock().unwrap().len(), 3);
    }
    #[cfg(feature = "native-z3")]
    #[test]
    fn real_parallel_cfgs_report_ordered_positive_and_negative_results() {
        use crate::decider::{
            native_z3::{LinkedProverOptions, LinkedZ3Prover},
            z3_prover_api::ApiTimeoutSettings,
        };
        let make = |name: String, factory: crate::state::terms::TermFactory| {
            let prover = LinkedZ3Prover::new(
                name,
                factory,
                LinkedProverOptions {
                    timeout: ApiTimeoutSettings {
                        default_timeout_ms: 0,
                        use_time_bounds: true,
                        resources_per_millisecond: 1,
                    },
                    counterexamples: false,
                    report_reason_unknown: false,
                    debug: false,
                    soft_assertions: false,
                    custom_options: vec![],
                    disable_nonlinear: false,
                },
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let (fatal, warnings) = run_parallel_source_with_warnings(
            "method good() { assert true; } method bad() { assert false; }",
            2,
            make,
            true,
        );
        assert_eq!(fatal.iter().filter(|value| **value).count(), 1);
        assert!(!fatal[0]);
        assert!(warnings.is_empty());
    }
    #[cfg(feature = "native-z3")]
    #[test]
    fn failed_function_is_reported_before_attaching_its_scope() {
        let fatal = run_parallel_linked(
            "function bad(x: Int): Int ensures result == 0 { 1 } method good() { assert true; }",
            2,
        );
        assert_eq!(fatal.iter().filter(|value| **value).count(), 1);
    }
    #[cfg(feature = "native-z3")]
    #[test]
    fn real_parallel_methods_share_verified_function_axioms() {
        let source = "function f(x: Int): Int { x + 1 } method good() { assert f(1) == 2; } method bad() { assert f(1) == 3; }";
        for workers in [1, 2] {
            let fatal = run_parallel_linked(source, workers);
            assert_eq!(fatal.iter().filter(|f| **f).count(), 1);
            assert!(!fatal[0]);
        }
    }
    #[cfg(feature = "native-z3")]
    #[test]
    fn real_parallel_methods_share_heap_and_predicate_preamble() {
        let fatal = run_parallel_linked(
            "field f: Int predicate P(r: Ref) { acc(r.f) } method good(r: Ref) requires acc(r.f) { r.f := 2; fold acc(P(r)); unfold acc(P(r)); assert r.f == 2; } method bad(r: Ref) requires acc(r.f) { r.f := 2; assert r.f == 3; }",
            2,
        );
        assert_eq!(fatal.iter().filter(|f| **f).count(), 1);
        assert!(!fatal[0]);
    }
    #[cfg(feature = "native-z3")]
    #[test]
    fn real_parallel_methods_share_adt_collection_axioms() {
        let fatal = run_parallel_linked(
            "adt Box[T] { Boxed(value: T) } method good() { var xs: Seq[Box[Int]] := Seq(Boxed(1)); assert |xs| == 1; assert xs[0].value == 1; } method bad() { var xs: Seq[Box[Int]] := Seq(Boxed(1)); assert xs[0].value == 2; }",
            2,
        );
        assert_eq!(fatal.iter().filter(|f| **f).count(), 1);
        assert!(!fatal[0]);
    }
    #[cfg(feature = "native-z3")]
    #[test]
    fn source_preamble_replays_on_linked_provers() {
        use crate::decider::{
            native_z3::{LinkedProverError, LinkedProverOptions, LinkedZ3Prover},
            z3_prover_api::ApiTimeoutSettings,
        };
        use crate::interfaces::decider::prover::Prover;
        use crate::state::terms::{Term, TermFactory, TermOptions};
        struct Solver(LinkedZ3Prover);
        impl ThreadBoundWorker for Solver {
            type Error = LinkedProverError;
            type Broadcast = WorkerPreambleCommand;
            type BroadcastResult = Option<String>;
            type Task = Term;
            type Output = bool;
            fn start(&mut self) -> Result<(), Self::Error> {
                self.0.start(None)
            }
            fn broadcast(
                &mut self,
                command: Self::Broadcast,
            ) -> Result<Self::BroadcastResult, Self::Error> {
                command.apply(&mut self.0)
            }
            fn verify(&mut self, task: Term) -> Result<bool, Self::Error> {
                self.0.assert_goal(&task, None)
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                self.0.reset()
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                self.0.stop()
            }
        }
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let workers_factory = factory.clone();
        let pool = ThreadVerificationPool::start(2, move |id| {
            Ok(Solver(LinkedZ3Prover::new(
                format!("worker-{id}"),
                workers_factory.clone(),
                LinkedProverOptions {
                    timeout: ApiTimeoutSettings {
                        default_timeout_ms: 0,
                        use_time_bounds: true,
                        resources_per_millisecond: 1,
                    },
                    counterexamples: false,
                    report_reason_unknown: false,
                    debug: false,
                    soft_assertions: false,
                    custom_options: vec![],
                    disable_nonlinear: false,
                },
            )))
        })
        .unwrap();
        let main = LinkedZ3Prover::new(
            "main",
            factory.clone(),
            LinkedProverOptions {
                timeout: ApiTimeoutSettings {
                    default_timeout_ms: 0,
                    use_time_bounds: true,
                    resources_per_millisecond: 1,
                },
                counterexamples: false,
                report_reason_unknown: false,
                debug: false,
                soft_assertions: false,
                custom_options: vec![],
                disable_nonlinear: false,
            },
        );
        let pool = std::rc::Rc::new(std::cell::RefCell::new(pool));
        let mut main = BroadcastingProver::new(main, pool.clone());
        main.start(None).unwrap();
        main.set_preamble_broadcast(true);
        main.assume(&factory.boolean(true)).unwrap();
        main.saturate_configured(None).unwrap();
        assert!(matches!(
            main.assert_goal(&factory.boolean(true), None),
            Err(BroadcastingProverError::Unsupported(_))
        ));
        main.set_preamble_broadcast(false);
        assert!(main.assert_goal(&factory.boolean(true), None).unwrap());
        assert!(!main.assert_goal(&factory.boolean(false), None).unwrap());
        main.assume(&factory.boolean(false)).unwrap();
        assert!(main.assert_goal(&factory.boolean(false), None).unwrap());
        let yes = pool.borrow_mut().submit(factory.boolean(true)).unwrap();
        let no = pool.borrow_mut().submit(factory.boolean(false)).unwrap();
        assert!(yes.wait().unwrap());
        assert!(!no.wait().unwrap());
        drop(main);
        let pool = std::rc::Rc::try_unwrap(pool).ok().unwrap().into_inner();
        pool.shutdown().unwrap();
    }
    #[cfg(feature = "native-z3")]
    #[test]
    fn thread_pool_runs_independent_linked_solver_contexts() {
        use crate::decider::{
            native_z3::{LinkedZ3, NativeZ3Error},
            term_to_z3_api_converter::{NativeLiteral, NativeSort, Z3NativeContext},
            z3_prover_api::NativeZ3Solver,
        };
        use crate::interfaces::decider::prover::SatResult;
        struct SolverWorker(LinkedZ3);
        impl ThreadBoundWorker for SolverWorker {
            type Error = NativeZ3Error;
            type Broadcast = bool;
            type BroadcastResult = ();
            type Task = bool;
            type Output = SatResult;
            fn start(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn broadcast(&mut self, value: bool) -> Result<(), Self::Error> {
                let sort = self.0.sort(NativeSort::Bool)?;
                let term = self.0.literal(NativeLiteral::Bool(value), &sort)?;
                self.0.add(&term)
            }
            fn verify(&mut self, value: bool) -> Result<SatResult, Self::Error> {
                self.0.push()?;
                let sort = self.0.sort(NativeSort::Bool)?;
                let term = self.0.literal(NativeLiteral::Bool(value), &sort)?;
                self.0.add(&term)?;
                let result = self.0.check();
                self.0.pop(1)?;
                result
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
        }
        let mut pool = ThreadVerificationPool::start(3, |_| {
            LinkedZ3::new_with_source_options().map(SolverWorker)
        })
        .unwrap();
        pool.broadcast(true).unwrap();
        let tasks = (0..12)
            .map(|i| pool.submit(i % 2 == 0).unwrap())
            .collect::<Vec<_>>();
        let results = tasks
            .into_iter()
            .map(|task| task.wait().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            results,
            (0..12)
                .map(|i| if i % 2 == 0 {
                    SatResult::Sat
                } else {
                    SatResult::Unsat
                })
                .collect::<Vec<_>>()
        );
        pool.shutdown().unwrap();
    }
}
