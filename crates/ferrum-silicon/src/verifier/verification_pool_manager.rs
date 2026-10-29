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
//! Status: partial; owner-thread solvers, pooled native verification, cooperative branch
//! jobs and cancellation cleanup are connected. Joined and owned terminal jobs remain
//! internally gated pending broader continuation and source compatibility checks.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::interfaces::decider::prover::{ProverLike, ProverStateSaturationTimeout, TextEmitter};
use crate::state::terms::{Declaration, Term};
use std::sync::Arc;

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
    /// Run a task on this worker's owner thread. Implementations that submit
    /// nested work may use the handle to wait cooperatively on the same worker.
    fn verify_cooperative(
        &mut self,
        task: Self::Task,
        _queue: &WorkerQueueHandle<Self>,
    ) -> Result<Self::Output, Self::Error>
    where
        Self: Sized,
    {
        self.verify(task)
    }
    fn reset(&mut self) -> Result<(), Self::Error>;
    fn stop(&mut self) -> Result<(), Self::Error>;
}

#[derive(Debug)]
pub enum ThreadPoolError<E> {
    NoWorkers,
    WrongWorkerThread,
    InvalidStackSize,
    Busy,
    Cancelled,
    Stopped,
    Worker(E),
    WorkerPanicked,
    WorkerDisconnected,
    ThreadSpawn(std::io::Error),
    /// Original failure together with errors observed while stopping workers.
    Cleanup {
        primary: Box<ThreadPoolError<E>>,
        errors: Vec<ThreadPoolError<E>>,
    },
}

fn with_cleanup<E>(
    primary: ThreadPoolError<E>,
    errors: Vec<ThreadPoolError<E>>,
) -> ThreadPoolError<E> {
    if errors.is_empty() {
        primary
    } else {
        ThreadPoolError::Cleanup {
            primary: Box::new(primary),
            errors,
        }
    }
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
    nested_identity: Option<Arc<NestedTaskIdentity>>,
    command: ThreadCommand<W>,
}
struct ThreadQueue<W: ThreadBoundWorker> {
    items: std::collections::VecDeque<ThreadWork<W>>,
    pending: usize,
    stopped: bool,
    cleanup_errors: Vec<ThreadPoolError<W::Error>>,
}
type SharedThreadQueue<W> = std::sync::Arc<(std::sync::Mutex<ThreadQueue<W>>, std::sync::Condvar)>;

/// Queue access restricted to an already running worker. The verifier remains
/// on its original thread; only owned task data crosses worker boundaries.
pub struct WorkerQueueHandle<W: ThreadBoundWorker> {
    queue: SharedThreadQueue<W>,
    owner: std::thread::ThreadId,
}

/// The caller uses both flags to apply the source brancher's restoration rule,
/// including when the awaited task failed or was cancelled.
pub struct CooperativeWait<O, E> {
    pub result: Result<O, ThreadPoolError<E>>,
    pub executed_other_task: bool,
    pub awaited_executed_on_current_worker: bool,
}

pub struct NestedVerificationTask<O, E> {
    task: VerificationTask<O, E>,
    identity: Arc<NestedTaskIdentity>,
}

#[derive(Default)]
struct NestedTaskIdentity {
    executing_thread: std::sync::OnceLock<std::thread::ThreadId>,
}

impl<W: ThreadBoundWorker> Clone for WorkerQueueHandle<W> {
    fn clone(&self) -> Self {
        Self {
            queue: self.queue.clone(),
            owner: self.owner,
        }
    }
}

impl<W: ThreadBoundWorker> WorkerQueueHandle<W> {
    pub fn submit(
        &self,
        task: W::Task,
    ) -> Result<NestedVerificationTask<W::Output, W::Error>, ThreadPoolError<W::Error>> {
        let (tx, rx) = std::sync::mpsc::channel();
        let identity = Arc::new(NestedTaskIdentity::default());
        let (lock, ready) = &*self.queue;
        let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
        if guard.stopped {
            return Err(ThreadPoolError::Stopped);
        }
        guard.pending += 1;
        guard.items.push_back(ThreadWork {
            target: None,
            nested_identity: Some(identity.clone()),
            command: ThreadCommand::Verify(task, tx),
        });
        ready.notify_all();
        Ok(NestedVerificationTask {
            task: VerificationTask(rx),
            identity,
        })
    }

    /// Wait for a nested task while executing other untargeted verification
    /// tasks on this same owner thread. The caller must restore its verifier
    /// state after an intervening task, as required by Brancher.scala.
    pub fn wait_cooperatively(
        &self,
        worker: &mut W,
        task: NestedVerificationTask<W::Output, W::Error>,
    ) -> CooperativeWait<W::Output, W::Error> {
        self.wait_cooperatively_with(task, |nested| worker.verify_cooperative(nested, self))
    }

    /// Run queued owned tasks through an executor borrowing only the worker state
    /// it needs. This permits a verifier context to cooperate without borrowing
    /// its enclosing worker a second time.
    pub fn wait_cooperatively_with(
        &self,
        task: NestedVerificationTask<W::Output, W::Error>,
        mut execute: impl FnMut(W::Task) -> Result<W::Output, W::Error>,
    ) -> CooperativeWait<W::Output, W::Error> {
        use std::sync::mpsc::TryRecvError;
        if std::thread::current().id() != self.owner {
            return CooperativeWait {
                result: Err(ThreadPoolError::WrongWorkerThread),
                executed_other_task: false,
                awaited_executed_on_current_worker: false,
            };
        }
        let mut executed_other_task = false;
        loop {
            match task.task.0.try_recv() {
                Ok(result) => {
                    return CooperativeWait {
                        result,
                        executed_other_task,
                        awaited_executed_on_current_worker: task.identity.executing_thread.get()
                            == Some(&self.owner),
                    };
                }
                Err(TryRecvError::Disconnected) => {
                    return CooperativeWait {
                        result: Err(ThreadPoolError::WorkerDisconnected),
                        executed_other_task,
                        awaited_executed_on_current_worker: task.identity.executing_thread.get()
                            == Some(&self.owner),
                    };
                }
                Err(TryRecvError::Empty) => {}
            }
            let (lock, ready) = &*self.queue;
            let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
            let position = guard.items.iter().position(|work| {
                work.target.is_none() && matches!(work.command, ThreadCommand::Verify(..))
            });
            let Some(position) = position else {
                // Completion arrives on an independent channel; a bounded wait
                // closes the notification race between the queue and that channel.
                let _ = ready
                    .wait_timeout(guard, std::time::Duration::from_millis(5))
                    .unwrap_or_else(|e| e.into_inner());
                continue;
            };
            let work = guard
                .items
                .remove(position)
                .expect("queued verification task");
            drop(guard);
            if !work
                .nested_identity
                .as_ref()
                .is_some_and(|id| Arc::ptr_eq(id, &task.identity))
            {
                executed_other_task = true;
            }
            if let Some(identity) = &work.nested_identity {
                let _ = identity.executing_thread.set(self.owner);
            }
            let ThreadCommand::Verify(nested, sender) = work.command else {
                unreachable!()
            };
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| execute(nested)));
            let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
            guard.pending -= 1;
            ready.notify_all();
            drop(guard);
            match result {
                Ok(value) => {
                    let _ = sender.send(value.map_err(ThreadPoolError::Worker));
                }
                Err(panic) => {
                    let _ = sender.send(Err(ThreadPoolError::WorkerPanicked));
                    // The outer owner-thread dispatcher handles panic shutdown,
                    // queued cancellation and worker cleanup exactly once.
                    std::panic::resume_unwind(panic);
                }
            }
            ready.notify_all();
        }
    }
}

/// Latched cross-thread cancellation for one verification run. Interrupt callbacks
/// may only access independently synchronized solver cancellation handles, never
/// the thread-bound verifier itself. Pure Rust work must call `checkpoint`.
#[derive(Clone, Default)]
pub struct CancellationController(std::sync::Arc<std::sync::Mutex<CancellationState>>);
#[derive(Default)]
struct CancellationState {
    cancelled: bool,
    interrupts: Vec<std::sync::Arc<dyn Fn() -> Result<(), String> + Send + Sync>>,
    errors: Vec<String>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerificationCancelled;
impl CancellationController {
    pub fn is_cancelled(&self) -> bool {
        self.0.lock().unwrap_or_else(|e| e.into_inner()).cancelled
    }
    pub fn checkpoint(&self) -> Result<(), VerificationCancelled> {
        if self.is_cancelled() {
            Err(VerificationCancelled)
        } else {
            Ok(())
        }
    }
    /// Register before startup. If cancellation already happened, interrupt at once;
    /// the owner must still check after installing/starting a new solver session.
    pub fn register(&self, interrupt: impl Fn() -> Result<(), String> + Send + Sync + 'static) {
        let interrupt: std::sync::Arc<dyn Fn() -> Result<(), String> + Send + Sync> =
            std::sync::Arc::new(interrupt);
        let cancelled = {
            let mut state = self.0.lock().unwrap_or_else(|e| e.into_inner());
            state.interrupts.push(interrupt.clone());
            state.cancelled
        };
        if cancelled {
            self.invoke(&interrupt);
        }
    }
    fn invoke(&self, interrupt: &std::sync::Arc<dyn Fn() -> Result<(), String> + Send + Sync>) {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| interrupt()));
        let error = match result {
            Ok(Ok(())) => None,
            Ok(Err(error)) => Some(error),
            Err(_) => Some("cancellation callback panicked".into()),
        };
        if let Some(error) = error {
            let mut state = self.0.lock().unwrap_or_else(|e| e.into_inner());
            if !state.errors.contains(&error) {
                state.errors.push(error);
            }
        }
    }
    /// Latch before interrupting, so concurrent registrations and checkpoints see it.
    pub fn cancel(&self) {
        let interrupts = {
            let mut state = self.0.lock().unwrap_or_else(|e| e.into_inner());
            if state.cancelled {
                return;
            }
            state.cancelled = true;
            state.interrupts.clone()
        };
        for interrupt in interrupts {
            self.invoke(&interrupt);
        }
    }
    /// Retry interrupts after a startup/reset race. A deadline monitor may call
    /// this until owner threads finish; checkpoints still stop pure Rust work.
    pub fn interrupt_again(&self) {
        let interrupts = {
            let state = self.0.lock().unwrap_or_else(|e| e.into_inner());
            if !state.cancelled {
                return;
            }
            state.interrupts.clone()
        };
        for interrupt in interrupts {
            self.invoke(&interrupt);
        }
    }
    /// Inspect after joining owners so errors from late registrations are included.
    pub fn take_errors(&self) -> Vec<String> {
        std::mem::take(&mut self.0.lock().unwrap_or_else(|e| e.into_inner()).errors)
    }
    pub fn register_stdio(&self, handle: crate::decider::prover_std_io::StdioCancellationHandle) {
        self.register(move || {
            handle
                .cancel()
                .map(|_| ())
                .map_err(|error| error.to_string())
        });
    }
    pub fn register_pool<W: ThreadBoundWorker>(&self, handle: PoolCancellationHandle<W>) {
        self.register(move || {
            handle.cancel();
            Ok(())
        });
    }
    #[cfg(feature = "native-z3")]
    pub fn register_linked(&self, handle: crate::decider::native_z3::LinkedZ3CancellationHandle) {
        self.register(move || {
            handle.interrupt();
            Ok(())
        });
    }
}

/// Thread-safe queue-only cancellation; the pool and each worker remain on their
/// original threads. Rejects future submissions and cancels queued control work too.
pub struct PoolCancellationHandle<W: ThreadBoundWorker>(SharedThreadQueue<W>);
impl<W: ThreadBoundWorker> Clone for PoolCancellationHandle<W> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<W: ThreadBoundWorker> PoolCancellationHandle<W> {
    pub fn cancel(&self) {
        let (lock, ready) = &*self.0;
        let mut state = lock.lock().unwrap_or_else(|e| e.into_inner());
        state.stopped = true;
        let abandoned: Vec<_> = state.items.drain(..).collect();
        state.pending -= abandoned
            .iter()
            .filter(|work| matches!(work.command, ThreadCommand::Verify(..)))
            .count();
        ready.notify_all();
        drop(state);
        for work in abandoned {
            match work.command {
                ThreadCommand::Verify(_, sender) => {
                    let _ = sender.send(Err(ThreadPoolError::Cancelled));
                }
                ThreadCommand::Broadcast(_, sender) => {
                    let _ = sender.send(Err(ThreadPoolError::Cancelled));
                }
                ThreadCommand::Start(sender)
                | ThreadCommand::Reset(sender)
                | ThreadCommand::Stop(sender) => {
                    let _ = sender.send(Err(ThreadPoolError::Cancelled));
                }
            }
        }
    }
}

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
    pub fn cancellation_handle(&self) -> PoolCancellationHandle<W> {
        PoolCancellationHandle(self.queue.clone())
    }
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
        Self::start_inner(count, stack_size, None, create)
    }
    /// Register the queue before starting worker threads so a deadline can reject
    /// startup or cancel a queued startup/broadcast operation.
    pub fn start_with_cancellation(
        count: usize,
        stack_size: usize,
        cancellation: CancellationController,
        create: impl Fn(usize) -> Result<W, W::Error> + Send + Sync + 'static,
    ) -> Result<Self, ThreadPoolError<W::Error>> {
        Self::start_inner(count, stack_size, Some(cancellation), create)
    }
    fn start_inner(
        count: usize,
        stack_size: usize,
        cancellation: Option<CancellationController>,
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
                cleanup_errors: Vec::new(),
            }),
            Condvar::new(),
        ));
        if let Some(cancellation) = &cancellation {
            cancellation.register_pool(PoolCancellationHandle(queue.clone()));
            if cancellation.is_cancelled() {
                return Err(ThreadPoolError::Cancelled);
            }
        }
        let create = Arc::new(create);
        let mut threads = Vec::with_capacity(count);
        for index in 0..count {
            if cancellation
                .as_ref()
                .is_some_and(CancellationController::is_cancelled)
            {
                let mut pool = Self { queue, threads };
                let cleanup = pool.abort_and_join();
                return Err(with_cleanup(ThreadPoolError::Cancelled, cleanup));
            }
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
                            let stopped =
                                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                    worker.stop()
                                }));
                            let error = match stopped {
                                Ok(Ok(())) => None,
                                Ok(Err(error)) => Some(ThreadPoolError::Worker(error)),
                                Err(_) => Some(ThreadPoolError::WorkerPanicked),
                            };
                            if let Some(error) = error {
                                queue
                                    .0
                                    .lock()
                                    .unwrap_or_else(|e| e.into_inner())
                                    .cleanup_errors
                                    .push(error);
                            }
                            break;
                        };
                        if let Some(identity) = &work.nested_identity {
                            let _ = identity.executing_thread.set(std::thread::current().id());
                        }
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
                                        worker.verify_cooperative(
                                            task,
                                            &WorkerQueueHandle {
                                                queue: queue.clone(),
                                                owner: std::thread::current().id(),
                                            },
                                        )
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
                                    let stopped = std::panic::catch_unwind(
                                        std::panic::AssertUnwindSafe(|| worker.stop()),
                                    );
                                    let error = match stopped {
                                        Ok(Ok(())) => None,
                                        Ok(Err(error)) => Some(ThreadPoolError::Worker(error)),
                                        Err(_) => Some(ThreadPoolError::WorkerPanicked),
                                    };
                                    if let Some(error) = error {
                                        queue
                                            .0
                                            .lock()
                                            .unwrap_or_else(|e| e.into_inner())
                                            .cleanup_errors
                                            .push(error);
                                    }
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
                    let cleanup = pool.abort_and_join();
                    return Err(with_cleanup(ThreadPoolError::ThreadSpawn(error), cleanup));
                }
            }
            if let Err(error) = rx
                .recv()
                .unwrap_or(Err(ThreadPoolError::WorkerDisconnected))
            {
                let mut pool = Self { queue, threads };
                let cleanup = pool.abort_and_join();
                return Err(with_cleanup(error, cleanup));
            }
        }
        let mut pool = Self { queue, threads };
        for index in (0..count).rev() {
            let (tx, rx) = mpsc::channel();
            if let Err(error) = pool.enqueue_control(index, ThreadCommand::Start(tx)) {
                let cleanup = pool.abort_and_join();
                return Err(with_cleanup(error, cleanup));
            }
            if let Err(error) = rx
                .recv()
                .unwrap_or(Err(ThreadPoolError::WorkerDisconnected))
            {
                let cleanup = pool.abort_and_join();
                return Err(with_cleanup(error, cleanup));
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
            nested_identity: None,
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
                    nested_identity: work.nested_identity,
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
            nested_identity: None,
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
            if let Err(error) =
                self.enqueue_control(index, ThreadCommand::Broadcast(command.clone(), tx))
            {
                let cleanup = self.abort_and_join();
                return Err(with_cleanup(error, cleanup));
            }
            let result = rx
                .recv()
                .map_err(|_| ThreadPoolError::WorkerDisconnected)
                .and_then(|value| value);
            match result {
                Ok(value) => results.push(value),
                Err(error) => {
                    let cleanup = self.abort_and_join();
                    return Err(with_cleanup(error, cleanup));
                }
            }
        }
        Ok(results)
    }
    pub fn reset(&mut self) -> Result<(), ThreadPoolError<W::Error>> {
        for index in (0..self.threads.len()).rev() {
            let (tx, rx) = std::sync::mpsc::channel();
            if let Err(error) = self.enqueue_control(index, ThreadCommand::Reset(tx)) {
                let cleanup = self.abort_and_join();
                return Err(with_cleanup(error, cleanup));
            }
            let result = rx
                .recv()
                .map_err(|_| ThreadPoolError::WorkerDisconnected)
                .and_then(|value| value);
            if let Err(error) = result {
                let cleanup = self.abort_and_join();
                return Err(with_cleanup(error, cleanup));
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
        let mut rest = Vec::new();
        for index in (0..self.threads.len()).rev() {
            let (tx, rx) = std::sync::mpsc::channel();
            let result = self
                .enqueue_control(index, ThreadCommand::Stop(tx))
                .and_then(|_| {
                    rx.recv()
                        .map_err(|_| ThreadPoolError::WorkerDisconnected)
                        .and_then(|v| v)
                });
            if let Err(error) = result {
                if first.is_none() {
                    first = Some(error);
                } else {
                    rest.push(error);
                }
            }
        }
        let mut cleanup = self.abort_and_join();
        rest.append(&mut cleanup);
        match first {
            Some(error) => Err(with_cleanup(error, rest)),
            None if !rest.is_empty() => Err(with_cleanup(ThreadPoolError::Stopped, rest)),
            None => Ok(()),
        }
    }
    /// Cancel the queue and join all owner threads, returning every observed
    /// worker-stop or thread-panic failure. Active work must first be interrupted
    /// through the registered solver handles; pure computation remains cooperative.
    pub fn cancel_and_join(mut self) -> Vec<ThreadPoolError<W::Error>> {
        self.cancellation_handle().cancel();
        let mut errors = Vec::new();
        for thread in self.threads.drain(..) {
            if thread.join().is_err() {
                errors.push(ThreadPoolError::WorkerPanicked);
            }
        }
        let mut queue = self.queue.0.lock().unwrap_or_else(|e| e.into_inner());
        errors.append(&mut queue.cleanup_errors);
        errors
    }
    fn abort_and_join(&mut self) -> Vec<ThreadPoolError<W::Error>> {
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
        let mut errors = Vec::new();
        for handle in self.threads.drain(..) {
            if handle.join().is_err() {
                errors.push(ThreadPoolError::WorkerPanicked);
            }
        }
        errors.append(
            &mut self
                .queue
                .0
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .cleanup_errors,
        );
        errors
    }
}
impl<W: ThreadBoundWorker> Drop for ThreadVerificationPool<W> {
    fn drop(&mut self) {
        let _ = self.abort_and_join();
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
            if let Err(error) = self.pool.enqueue_control(
                index,
                ThreadCommand::Broadcast(WorkerPreambleCommand::Comment(lazy), done_tx),
            ) {
                let cleanup = self.pool.abort_and_join();
                return Err(with_cleanup(error, cleanup));
            }
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
                let cleanup = self.pool.abort_and_join();
                return Err(with_cleanup(error, cleanup));
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
    type Version = P::Version;
    fn comment_fallible(
        &mut self,
        content: &mut dyn FnMut() -> Result<String, String>,
    ) -> Result<(), crate::interfaces::decider::prover::CommentError<Self::Error>> {
        use crate::interfaces::decider::prover::CommentError;
        self.require_main_only().map_err(CommentError::Prover)?;
        self.main
            .comment_fallible(content)
            .map_err(|error| match error {
                CommentError::Render(error) => CommentError::Render(error),
                CommentError::Prover(error) => {
                    CommentError::Prover(BroadcastingProverError::Main(error))
                }
            })
    }
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
    fn get_model(
        &mut self,
    ) -> Result<ferrum_silver::verifier::verification_error::Model, Self::Error> {
        self.main.get_model().map_err(BroadcastingProverError::Main)
    }
    fn get_reason_unknown(&mut self) -> Result<Option<String>, Self::Error> {
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
pub(crate) fn report_member_results(
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

pub type NativeBranchState = crate::state::state::State<
    crate::supporters::predicate_verification_unit::PredicateData,
    super::native_context::NativeFunctionData,
    crate::config::JoinMode,
>;
pub type NativeBranchEntry = crate::rules::joiner::JoinDataEntry<
    crate::supporters::predicate_verification_unit::PredicateData,
    super::native_context::NativeFunctionData,
    crate::config::JoinMode,
    (Term, Option<ferrum_silver::ast::expression::Exp>),
>;
#[derive(Clone)]
pub struct NativeEvaluationBranch {
    pub source_worker_id: String,
    pub snapshot: crate::rules::brancher::BranchTransferSnapshot,
    pub state: NativeBranchState,
    pub initial_state: NativeBranchState,
    pub mark: crate::decider::path_conditions::Mark,
    pub condition: Term,
    pub original: ferrum_silver::ast::expression::Exp,
    pub rewritten: Option<ferrum_silver::ast::expression::Exp>,
    pub action: crate::rules::evaluator::EvaluationBranchAction<
        ferrum_silver::verifier::verification_error::PartialVerificationError,
    >,
}
pub struct NativeEvaluationBranchOutput {
    pub result: crate::interfaces::verification::VerificationResult<
        ferrum_silver::verifier::verification_error::VerificationError,
    >,
    pub entries: Vec<NativeBranchEntry>,
    pub declarations: crate::rules::brancher::BranchJoinDeclarations,
    pub warnings: Vec<String>,
}
/// Source-eligible branch actions that terminate at a join collector.
pub enum NativeJoinAction<
    PD = crate::supporters::predicate_verification_unit::PredicateData,
    FD = super::native_context::NativeFunctionData,
> {
    Cfg(crate::rules::executor::CfgJoinBranch),
    Predicate(crate::rules::predicate_supporter::PredicateContentsAction),
    PredicateEvaluation {
        action: crate::rules::predicate_supporter::PredicateContentsAction,
        frame: crate::rules::predicate_supporter::OwnedUnfoldEvaluation<PD, FD>,
    },
    PredicateContinuation {
        action: crate::rules::predicate_supporter::PredicateContentsAction,
        finish: crate::rules::predicate_supporter::OwnedUnfoldFinish,
    },
    Continuation(crate::rules::executor::CfgContinuationAction),
    Production(
        crate::rules::producer::OwnedProductionAction<
            super::native_context::NativeSnapshot,
            ferrum_silver::verifier::verification_error::PartialVerificationError,
            PD,
            FD,
        >,
    ),
    Consumption(
        crate::rules::consumer::OwnedConsumptionAction<
            ferrum_silver::verifier::verification_error::PartialVerificationError,
            PD,
            FD,
            crate::config::JoinMode,
        >,
    ),
}
impl<PD, FD> Clone for NativeJoinAction<PD, FD> {
    fn clone(&self) -> Self {
        match self {
            Self::Cfg(a) => Self::Cfg(a.clone()),
            Self::Predicate(a) => Self::Predicate(a.clone()),
            Self::Continuation(a) => Self::Continuation(a.clone()),
            Self::Production(a) => Self::Production(a.clone()),
            Self::Consumption(a) => Self::Consumption(a.clone()),
            Self::PredicateEvaluation { action, frame } => Self::PredicateEvaluation {
                action: action.clone(),
                frame: frame.clone(),
            },
            Self::PredicateContinuation { action, finish } => Self::PredicateContinuation {
                action: action.clone(),
                finish: finish.clone(),
            },
        }
    }
}
pub struct NativeJoinJob<
    PD = crate::supporters::predicate_verification_unit::PredicateData,
    FD = super::native_context::NativeFunctionData,
> {
    pub source_worker_id: String,
    pub snapshot: crate::rules::brancher::BranchTransferSnapshot,
    pub state: crate::state::state::State<PD, FD, crate::config::JoinMode>,
    pub mark: Option<crate::decider::path_conditions::Mark>,
    pub condition: Term,
    pub original: ferrum_silver::ast::expression::Exp,
    pub rewritten: Option<ferrum_silver::ast::expression::Exp>,
    pub action: NativeJoinAction<PD, FD>,
    #[cfg(test)]
    pub after_start: Option<Arc<dyn Fn() + Send + Sync>>,
    #[cfg(test)]
    pub replay_check: Option<Term>,
}
pub struct NativeJoinOutput<
    PD = crate::supporters::predicate_verification_unit::PredicateData,
    FD = super::native_context::NativeFunctionData,
> {
    pub result: crate::interfaces::verification::VerificationResult<
        ferrum_silver::verifier::verification_error::VerificationError,
    >,
    pub entries: Vec<crate::rules::joiner::JoinDataEntry<PD, FD, crate::config::JoinMode, ()>>,
    pub(crate) evaluation_entries: Option<(
        Arc<()>,
        Vec<
            crate::rules::joiner::JoinDataEntry<
                PD,
                FD,
                crate::config::JoinMode,
                (Term, Option<ferrum_silver::ast::expression::Exp>),
            >,
        >,
    )>,
    pub(crate) phases: Option<(
        Arc<()>,
        Vec<crate::rules::executor::LoopPhase<PD, FD, crate::config::JoinMode>>,
    )>,
    pub declarations: crate::rules::brancher::BranchJoinDeclarations,
    pub warnings: Vec<String>,
}
#[cfg(test)]
static CFG_JOIN_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static CONTINUATION_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static CONTINUATION_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LOOP_ESTABLISH_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LOOP_ESTABLISH_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LOOP_BACKEDGE_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LOOP_BACKEDGE_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LOOP_PHASE_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LOOP_PHASE_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RETURN_STRICT_LEFT_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RETURN_STRICT_LEFT_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RETURN_STRICT_RIGHT_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RETURN_STRICT_RIGHT_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RETURN_ADD_LEFT_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RETURN_ADD_RIGHT_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RETURN_ADD_LEFT_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static INNER_RECEIVER_CANCEL_HOOKS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RETURN_RIGHT_CANCEL_HOOKS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RETURN_ADD_RIGHT_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static NESTED_RETURN_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static NESTED_RETURN_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LET_RECEIVER_CANCEL_HOOKS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LET_VALUE_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LET_VALUE_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LET_BODY_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static LET_BODY_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static ASSERTING_BODY_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static ASSERTING_BODY_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static ASSERTING_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static ASSERTING_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static OLD_ASSERTING_SUBMISSIONS: [std::sync::atomic::AtomicUsize; 2] =
    [const { std::sync::atomic::AtomicUsize::new(0) }; 2];
#[cfg(test)]
pub(crate) static OLD_ASSERTING_EXECUTIONS: [std::sync::atomic::AtomicUsize; 2] =
    [const { std::sync::atomic::AtomicUsize::new(0) }; 2];
#[cfg(test)]
pub(crate) static FUNCTION_PRE_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static FUNCTION_PRE_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static UNFOLD_EVALUATION_PRODUCTION_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static UNFOLD_EVALUATION_PRODUCTION_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static PREDICATE_EVALUATION_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static PREDICATE_EVALUATION_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static UNFOLD_TREE_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static UNFOLD_TREE_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static FOLD_BODY_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static FOLD_BODY_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static CALL_PRE_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static CALL_PRE_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static CALL_POST_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static CALL_POST_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static ASSERT_PROBE_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static ASSERT_PROBE_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RULE_CONSUMPTION_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RULE_CONSUMPTION_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static UNFOLD_PRODUCTION_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static UNFOLD_PRODUCTION_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RULE_PRODUCTION_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static RULE_PRODUCTION_TEST_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub(crate) static CONTINUATION_TEST_FOREIGN_EXECUTIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
static PREDICATE_JOIN_TEST_SUBMISSIONS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);
pub(crate) trait NativeJoinFuture<S: crate::interfaces::decider::prover::Prover, PD, FD> {
    fn wait(
        self: Box<Self>,
        context: &mut super::native_context::NativeVerifierContext<S, PD, FD>,
    ) -> CooperativeWait<NativeJoinOutput<PD, FD>, super::native_context::NativeError<S::Error>>;
}
pub(crate) trait NativeJoinScheduler<S: crate::interfaces::decider::prover::Prover, PD, FD> {
    fn report_failure(
        &self,
        member: Option<&ferrum_silver::ast::program::Member>,
        result: &crate::interfaces::verification::VerificationResult<
            ferrum_silver::verifier::verification_error::VerificationError,
        >,
    ) -> Result<(), super::native_context::NativeError<S::Error>>;
    fn submit(
        &self,
        job: NativeJoinJob<PD, FD>,
    ) -> Result<
        Box<dyn NativeJoinFuture<S, PD, FD>>,
        ThreadPoolError<super::native_context::NativeError<S::Error>>,
    >;
}
struct NativeJoinQueueScheduler<S: crate::interfaces::decider::prover::Prover + 'static>
where
    S::Error: Send + std::fmt::Debug + 'static,
{
    queue: WorkerQueueHandle<NativeMethodWorker<S>>,
    analysis: Arc<super::native_context::NativeWorkerAnalysis>,
    reporter: Option<Arc<dyn ferrum_silver::reporter::reporter::Reporter>>,
    warning_sink: Option<Arc<std::sync::Mutex<Vec<String>>>>,
}
struct NativeJoinQueueFuture<S: crate::interfaces::decider::prover::Prover + 'static>
where
    S::Error: Send + std::fmt::Debug + 'static,
{
    queue: WorkerQueueHandle<NativeMethodWorker<S>>,
    task: NestedVerificationTask<NativeWorkerOutput, super::native_context::NativeError<S::Error>>,
}
impl<S>
    NativeJoinScheduler<
        S,
        crate::supporters::predicate_verification_unit::PredicateData,
        super::native_context::NativeFunctionData,
    > for NativeJoinQueueScheduler<S>
where
    S: crate::interfaces::decider::prover::Prover + 'static,
    S::Error: Send + std::fmt::Debug + 'static,
{
    fn report_failure(
        &self,
        member: Option<&ferrum_silver::ast::program::Member>,
        result: &crate::interfaces::verification::VerificationResult<
            ferrum_silver::verifier::verification_error::VerificationError,
        >,
    ) -> Result<(), super::native_context::NativeError<S::Error>> {
        let (Some(reporter), Some(member)) = (&self.reporter, member) else {
            return Ok(());
        };
        if !result.is_fatal() || result.is_reported() {
            return Ok(());
        }
        use ferrum_silver::{
            reporter::message::Message,
            verifier::{
                verification_error::{NativeErrorNodeRenderer, RenderedVerificationError},
                verification_result::AbstractError,
            },
        };
        let errors = result
            .with_kind(|kind| match kind {
                crate::interfaces::verification::ResultKind::Failure(error) => {
                    RenderedVerificationError::new(error.clone(), Arc::new(NativeErrorNodeRenderer))
                        .map(|error| vec![AbstractError::Verification(Arc::new(error))])
                }
                _ => Ok(Vec::new()),
            })
            .map_err(|error| {
                super::native_context::NativeError::Diagnostic(format!(
                    "branch error rendering: {error:?}"
                ))
            })?;
        result.set_reported(true);
        reporter
            .report(Message::BranchFailure {
                verifier: "silicon".into(),
                concerning: Arc::new(member.clone()),
                errors,
                cached: false,
            })
            .map_err(|error| {
                super::native_context::NativeError::Diagnostic(format!(
                    "branch failure reporter: {error:?}"
                ))
            })
    }
    fn submit(
        &self,
        job: NativeJoinJob,
    ) -> Result<
        Box<
            dyn NativeJoinFuture<
                    S,
                    crate::supporters::predicate_verification_unit::PredicateData,
                    super::native_context::NativeFunctionData,
                >,
        >,
        ThreadPoolError<super::native_context::NativeError<S::Error>>,
    > {
        #[cfg(test)]
        match &job.action {
            NativeJoinAction::Cfg(_) => {
                CFG_JOIN_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            }
            NativeJoinAction::Predicate(_) => {
                PREDICATE_JOIN_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            }
            NativeJoinAction::PredicateEvaluation { .. } => {
                PREDICATE_EVALUATION_TEST_SUBMISSIONS
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            }
            NativeJoinAction::PredicateContinuation { .. } => {
                UNFOLD_TREE_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            }
            NativeJoinAction::Continuation(_) => {
                CONTINUATION_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            }
            NativeJoinAction::Production(action) => {
                if matches!(
                    &action.tail,
                    crate::rules::producer::OwnedProductionTerminal::UnfoldEvaluation(_)
                ) {
                    UNFOLD_EVALUATION_PRODUCTION_TEST_SUBMISSIONS
                        .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
                if matches!(
                    &action.tail,
                    crate::rules::producer::OwnedProductionTerminal::LoopPhaseCollect { .. }
                ) {
                    LOOP_PHASE_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
                if matches!(
                    &action.tail,
                    crate::rules::producer::OwnedProductionTerminal::CallPost(_)
                ) {
                    CALL_POST_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
                if matches!(
                    &action.tail,
                    crate::rules::producer::OwnedProductionTerminal::Unfold(_)
                ) {
                    UNFOLD_PRODUCTION_TEST_SUBMISSIONS
                        .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
                RULE_PRODUCTION_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            }
            NativeJoinAction::Consumption(action) => {
                for f in &action.frames {
                    if let crate::rules::consumer::OwnedConsumptionFrame::Finish {
                        terminal: crate::rules::consumer::OwnedConsumptionTerminal::Asserting(frame),
                        ..
                    } = f
                    {
                        if frame.return_frames.iter().any(|f| {
                            matches!(
                                f,
                                crate::rules::evaluator::OwnedEvaluationReturnFrame::AddLeft { .. }
                            )
                        }) {
                            RETURN_ADD_LEFT_SUBMISSIONS
                                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        }
                        if frame.return_frames.iter().any(|f| {
                            matches!(
                                f,
                                crate::rules::evaluator::OwnedEvaluationReturnFrame::AddRight { .. }
                            )
                        }) {
                            RETURN_ADD_RIGHT_SUBMISSIONS
                                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        }
                        if frame.return_frames.iter().any(|f| matches!(f, crate::rules::evaluator::OwnedEvaluationReturnFrame::StrictLeft { .. })) {
                            RETURN_STRICT_LEFT_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        }
                        if frame.return_frames.iter().any(|f| matches!(f, crate::rules::evaluator::OwnedEvaluationReturnFrame::StrictRight { .. })) {
                            RETURN_STRICT_RIGHT_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        }
                        if frame.return_frames.iter().any(|f| {
                            matches!(
                                f,
                                crate::rules::evaluator::OwnedEvaluationReturnFrame::Asserting(_)
                            )
                        }) {
                            ASSERTING_BODY_SUBMISSIONS
                                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        }
                        if frame.return_frames.iter().any(|f| {
                            matches!(
                                f,
                                crate::rules::evaluator::OwnedEvaluationReturnFrame::LetValue(_)
                            )
                        }) {
                            LET_VALUE_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        }
                        if frame.return_frames.iter().any(|f| {
                            matches!(
                                f,
                                crate::rules::evaluator::OwnedEvaluationReturnFrame::LetBody { .. }
                            )
                        }) {
                            LET_BODY_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        }
                        if frame.return_frames.len() >= 2 {
                            NESTED_RETURN_SUBMISSIONS
                                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        }
                        for old in frame.return_frames.iter().filter_map(|entry| match entry {
                            crate::rules::evaluator::OwnedEvaluationReturnFrame::Old(old) => {
                                Some(old)
                            }
                            _ => None,
                        }) {
                            OLD_ASSERTING_SUBMISSIONS[usize::from(old.kind != 0)]
                                .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                        }
                    }
                }
                if action.frames.iter().any(|f| {
                    matches!(
                        f,
                        crate::rules::consumer::OwnedConsumptionFrame::Finish {
                            terminal: crate::rules::consumer::OwnedConsumptionTerminal::Asserting(
                                _
                            ),
                            ..
                        }
                    )
                }) {
                    ASSERTING_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
                if action.frames.iter().any(|f| {
                    matches!(
                        f,
                        crate::rules::consumer::OwnedConsumptionFrame::Finish {
                            terminal: crate::rules::consumer::OwnedConsumptionTerminal::FunctionPre(
                                _
                            ),
                            ..
                        }
                    )
                }) {
                    FUNCTION_PRE_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
                if action.frames.iter().any(|frame| matches!(frame, crate::rules::consumer::OwnedConsumptionFrame::Finish { terminal: crate::rules::consumer::OwnedConsumptionTerminal::LoopBackedgeSuccess, .. })) { LOOP_BACKEDGE_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst); }
                if action.frames.iter().any(|frame| matches!(frame, crate::rules::consumer::OwnedConsumptionFrame::Finish { terminal: crate::rules::consumer::OwnedConsumptionTerminal::LoopEstablish { .. }, .. })) { LOOP_ESTABLISH_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst); }
                if action.frames.iter().any(|frame| {
                    matches!(
                        frame,
                        crate::rules::consumer::OwnedConsumptionFrame::Finish {
                            terminal: crate::rules::consumer::OwnedConsumptionTerminal::FoldBody(_),
                            ..
                        }
                    )
                }) {
                    FOLD_BODY_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
                if action.frames.iter().any(|frame| {
                    matches!(
                        frame,
                        crate::rules::consumer::OwnedConsumptionFrame::Finish {
                            terminal:
                                crate::rules::consumer::OwnedConsumptionTerminal::MethodCallPre(_),
                            ..
                        }
                    )
                }) {
                    CALL_PRE_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
                if action.frames.iter().any(|frame| {
                    matches!(
                        frame,
                        crate::rules::consumer::OwnedConsumptionFrame::Finish {
                            terminal: crate::rules::consumer::OwnedConsumptionTerminal::AssertProbe,
                            ..
                        }
                    )
                }) {
                    ASSERT_PROBE_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                }
                RULE_CONSUMPTION_TEST_SUBMISSIONS.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
            }
        }
        let task = self.queue.submit(NativeWorkerTask {
            analysis: self.analysis.clone(),
            target: NativeWorkerTarget::Join(Box::new(job)),
            reporter: self.reporter.clone(),
            warning_sink: self.warning_sink.clone(),
        })?;
        Ok(Box::new(NativeJoinQueueFuture {
            queue: self.queue.clone(),
            task,
        }))
    }
}
impl<S>
    NativeJoinFuture<
        S,
        crate::supporters::predicate_verification_unit::PredicateData,
        super::native_context::NativeFunctionData,
    > for NativeJoinQueueFuture<S>
where
    S: crate::interfaces::decider::prover::Prover + 'static,
    S::Error: Send + std::fmt::Debug + 'static,
{
    fn wait(
        self: Box<Self>,
        context: &mut super::native_context::NativeVerifierContext<
            S,
            crate::supporters::predicate_verification_unit::PredicateData,
            super::native_context::NativeFunctionData,
        >,
    ) -> CooperativeWait<NativeJoinOutput, super::native_context::NativeError<S::Error>> {
        let waited = self.queue.wait_cooperatively_with(self.task, |job| {
            execute_intervening_native_worker_task(context, job)
        });
        CooperativeWait {
            result: waited.result.and_then(|output| match output {
                NativeWorkerOutput::Join(output) => Ok(output),
                _ => Err(ThreadPoolError::Stopped),
            }),
            executed_other_task: waited.executed_other_task,
            awaited_executed_on_current_worker: waited.awaited_executed_on_current_worker,
        }
    }
}

pub enum NativeWorkerOutput {
    Member(
        Vec<
            crate::interfaces::verification::VerificationResult<
                ferrum_silver::verifier::verification_error::VerificationError,
            >,
        >,
    ),
    EvaluationBranch(NativeEvaluationBranchOutput),
    Join(NativeJoinOutput),
}

/// Source method or standalone CFG task after main analysis.
pub enum NativeWorkerTarget {
    Method(ferrum_silver::ast::program::Method),
    Cfg(ferrum_silver::cfg::silver::silver_cfg::SilverCfg),
    EvaluationBranch(Box<NativeEvaluationBranch>),
    Join(Box<NativeJoinJob>),
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
    preamble_frame_ready: bool,
}
impl<S: crate::interfaces::decider::prover::Prover> NativeMethodWorker<S> {
    pub fn set_cancellation(&mut self, cancellation: CancellationController) {
        self.context.set_cancellation(cancellation);
    }
    pub(crate) fn ensure_preamble_frame(
        &mut self,
    ) -> Result<(), super::native_context::NativeError<S::Error>> {
        self.context.checkpoint()?;
        if !self.preamble_frame_ready {
            self.context
                .base
                .decider
                .prover
                .push(1, self.context.base.decider.push_timeout)
                .map_err(|e| {
                    super::native_context::NativeError::Decider(
                        crate::decider::decider::DeciderError::Prover(e),
                    )
                })?;
            self.preamble_frame_ready = true;
        }
        Ok(())
    }
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
    let mut context = super::native_context::NativeVerifierContext::new(base, factory, options);
    context.joined_branch_scheduler_enabled = config.parallelize_branches;
    NativeMethodWorker {
        context,
        user_args: config.prover_args.clone(),
        config_options,
        preamble_frame_ready: false,
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
    type Output = NativeWorkerOutput;
    fn start(&mut self) -> Result<(), Self::Error> {
        self.preamble_frame_ready = false;
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
        self.ensure_preamble_frame()?;
        execute_native_worker_task(&mut self.context, task)
    }
    fn verify_cooperative(
        &mut self,
        task: Self::Task,
        queue: &WorkerQueueHandle<Self>,
    ) -> Result<Self::Output, Self::Error> {
        self.ensure_preamble_frame()?;
        let scheduler = std::rc::Rc::new(NativeJoinQueueScheduler {
            queue: queue.clone(),
            analysis: task.analysis.clone(),
            reporter: task.reporter.clone(),
            warning_sink: task.warning_sink.clone(),
        });
        let previous = self.context.joined_branch_scheduler.replace(scheduler);
        let result = execute_native_worker_task(&mut self.context, task);
        self.context.joined_branch_scheduler = previous;
        result
    }
    fn reset(&mut self) -> Result<(), Self::Error> {
        self.preamble_frame_ready = false;
        self.context.reset()?;
        Ok(())
    }
    fn stop(&mut self) -> Result<(), Self::Error> {
        self.context.stop()
    }
}

/// Dispatch every queued native task using only the worker-owned context.
/// Cooperative execution uses the same reporting and scope behavior as the
/// ordinary worker dispatcher.
pub(super) fn execute_intervening_native_worker_task<S>(
    context: &mut super::native_context::NativeVerifierContext<
        S,
        crate::supporters::predicate_verification_unit::PredicateData,
        super::native_context::NativeFunctionData,
    >,
    task: NativeWorkerTask,
) -> Result<NativeWorkerOutput, super::native_context::NativeError<S::Error>>
where
    S: crate::interfaces::decider::prover::Prover,
    S::Error: std::fmt::Debug,
{
    use super::native_context::NativeError;
    use std::sync::atomic::Ordering;
    if matches!(
        task.target,
        NativeWorkerTarget::EvaluationBranch(_) | NativeWorkerTarget::Join(_)
    ) {
        return execute_native_worker_task(context, task);
    }
    let saved = crate::rules::brancher::BranchTransferSnapshot::capture(
        &context.base.decider,
        context.base.errors_reported.load(Ordering::SeqCst),
    );
    let setup = context
        .base
        .decider
        .reset_options()
        .and_then(|_| {
            context.base.decider.set_path_conditions(
                crate::decider::path_conditions::LayeredPathConditionStack::new(
                    context.base.decider.debug_mode,
                ),
            )
        })
        .map_err(NativeError::Decider);
    let result = match setup {
        Ok(()) => {
            context.base.errors_reported.store(0, Ordering::SeqCst);
            execute_native_worker_task(context, task)
        }
        Err(error) => Err(error),
    };
    let saturation = context.options.after_inhale_timeout.map(|timeout_ms| {
        crate::interfaces::decider::prover::ProverStateSaturationTimeout {
            timeout_ms,
            comment: "after inhale".into(),
        }
    });
    let cleanup = saved
        .restore_after_cooperative_join(
            &saved,
            &mut context.base.decider,
            &context.base.errors_reported,
            saturation.as_ref(),
        )
        .map_err(NativeError::Decider);
    match (result, cleanup) {
        (Ok(output), Ok(())) => Ok(output),
        (Err(primary), Ok(())) => Err(primary),
        (Ok(_), Err(cleanup)) => Err(cleanup),
        (Err(primary), Err(cleanup)) => Err(NativeError::Cleanup(format!(
            "intervening task failed: {primary:?}; restoration failed: {cleanup:?}"
        ))),
    }
}

pub(super) fn execute_native_worker_task<S>(
    context: &mut super::native_context::NativeVerifierContext<
        S,
        crate::supporters::predicate_verification_unit::PredicateData,
        super::native_context::NativeFunctionData,
    >,
    task: NativeWorkerTask,
) -> Result<NativeWorkerOutput, super::native_context::NativeError<S::Error>>
where
    S: crate::interfaces::decider::prover::Prover,
    S::Error: std::fmt::Debug,
{
    let outer_warnings = std::mem::take(&mut context.warnings);
    let previous_reporter = context.replace_preprocessing_reporter(task.reporter.clone());
    let result = execute_native_worker_task_inner(context, task);
    context.replace_preprocessing_reporter(previous_reporter);
    let inner_warnings = std::mem::replace(&mut context.warnings, outer_warnings);
    context.warnings.extend(inner_warnings);
    result
}
fn finish_worker_warning_delivery<T, E: std::fmt::Debug>(
    outcome: Result<T, super::native_context::NativeError<E>>,
    warnings: Vec<String>,
    delivery: Result<(), super::native_context::NativeError<E>>,
) -> Result<T, super::native_context::NativeError<E>> {
    use super::native_context::NativeError;
    match (outcome, delivery) {
        (result, Ok(())) => result,
        (Ok(_), Err(delivery)) => Err(NativeError::BranchWarnings {
            primary: Box::new(delivery),
            warnings,
        }),
        (Err(primary), Err(delivery)) => {
            let mut warnings = warnings;
            warnings.push(format!("warning delivery failed: {delivery:?}"));
            Err(NativeError::BranchWarnings {
                primary: Box::new(primary),
                warnings,
            })
        }
    }
}

fn execute_native_worker_task_inner<S>(
    context: &mut super::native_context::NativeVerifierContext<
        S,
        crate::supporters::predicate_verification_unit::PredicateData,
        super::native_context::NativeFunctionData,
    >,
    task: NativeWorkerTask,
) -> Result<NativeWorkerOutput, super::native_context::NativeError<S::Error>>
where
    S: crate::interfaces::decider::prover::Prover,
    S::Error: std::fmt::Debug,
{
    if let NativeWorkerTarget::Join(job) = task.target {
        return context
            .verify_worker_join(&task.analysis, *job)
            .map(NativeWorkerOutput::Join);
    }
    if let NativeWorkerTarget::EvaluationBranch(branch) = task.target {
        return context
            .verify_worker_evaluation_branch(&task.analysis, *branch)
            .map(NativeWorkerOutput::EvaluationBranch);
    }
    context.validate_trace_worker(&task.analysis)?;
    let start = std::time::Instant::now();
    let outcome = match &task.target {
        NativeWorkerTarget::Method(method) => context.verify_worker_method(&task.analysis, method),
        NativeWorkerTarget::Cfg(cfg) => context.verify_worker_cfg(&task.analysis, cfg),
        NativeWorkerTarget::EvaluationBranch(_) | NativeWorkerTarget::Join(_) => unreachable!(),
    };
    if outcome.is_err() {
        match &task.target {
            NativeWorkerTarget::Method(method) => {
                context.log_entity_exception("method", Some(&method.name))
            }
            NativeWorkerTarget::Cfg(_) => context.log_entity_exception("cfg", None),
            _ => unreachable!(),
        }
    }
    let warnings = std::mem::take(&mut context.warnings);
    let delivery = if warnings.is_empty() {
        Ok(())
    } else {
        if let Some(sink) = &task.warning_sink {
            sink.lock()
                .expect("poisoned native warning sink")
                .extend(warnings.iter().cloned());
        }
        if let Some(reporter) = &task.reporter {
            use ferrum_silver::{
                ast::position::Position,
                reporter::message::Message,
                verifier::verification_result::{FrontendError, FrontendErrorKind},
            };
            reporter
                .report(Message::WarningsDuringVerification {
                    warnings: warnings
                        .iter()
                        .cloned()
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
                })
        } else if task.warning_sink.is_some() {
            Ok(())
        } else {
            Err(super::native_context::NativeError::Unsupported(
                "worker warnings require reporter or warning sink",
            ))
        }
    };
    let results = finish_worker_warning_delivery(outcome, warnings, delivery)?;
    let member = match task.target {
        NativeWorkerTarget::Method(method) => Some(std::sync::Arc::new(
            ferrum_silver::ast::program::Member::Method(method),
        )),
        NativeWorkerTarget::Cfg(_) => None,
        NativeWorkerTarget::EvaluationBranch(_) | NativeWorkerTarget::Join(_) => unreachable!(),
    };
    let elapsed = start.elapsed();
    if let Some(reporter) = task.reporter {
        report_member_results(reporter.as_ref(), member.clone(), elapsed, &results).map_err(
            |error| {
                super::native_context::NativeError::Diagnostic(format!(
                    "worker result reporter: {error:?}"
                ))
            },
        )?;
    }
    let name = match member.as_deref() {
        Some(ferrum_silver::ast::program::Member::Method(method)) => method.name.as_str(),
        None => "CFG",
        _ => unreachable!(),
    };
    context.log_member_result("method", name, elapsed, &results)?;
    if let Some(member) = member {
        set_verification_scope(&results, member);
    }
    Ok(NativeWorkerOutput::Member(results))
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
    context.set_preprocessing_reporter(reporter.clone());
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
        let warning_start = context.warnings.len();
        let start = std::time::Instant::now();
        let outcome = context.verify_function_unscoped(&program, &analysis, &function);
        if outcome.is_err() {
            context.log_entity_exception("function", Some(&function.name));
        }
        let delivery = super::native_context::report_single_warnings(
            reporter.as_deref(),
            &context.warnings[warning_start..],
        );
        let function_results = super::native_context::combine_single_delivery(outcome, delivery)
            .map_err(NativeParallelError::Main)?;
        let elapsed = start.elapsed();
        if let Some(reporter) = &reporter {
            report_member_results(
                reporter.as_ref(),
                Some(member.clone()),
                elapsed,
                &function_results,
            )
            .map_err(NativeParallelError::Reporter)?;
        }
        context
            .log_member_result("function", &function.name, elapsed, &function_results)
            .map_err(NativeParallelError::Main)?;
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
        let warning_start = context.warnings.len();
        let start = std::time::Instant::now();
        let outcome = context.verify_predicate_unscoped(&program, &analysis, &predicate);
        if outcome.is_err() {
            context.log_entity_exception("predicate", Some(&predicate.name));
        }
        let delivery = super::native_context::report_single_warnings(
            reporter.as_deref(),
            &context.warnings[warning_start..],
        );
        let predicate_results = super::native_context::combine_single_delivery(outcome, delivery)
            .map_err(NativeParallelError::Main)?;
        let elapsed = start.elapsed();
        if let Some(reporter) = &reporter {
            report_member_results(
                reporter.as_ref(),
                Some(member.clone()),
                elapsed,
                &predicate_results,
            )
            .map_err(NativeParallelError::Reporter)?;
        }
        context
            .log_member_result("predicate", &predicate.name, elapsed, &predicate_results)
            .map_err(NativeParallelError::Main)?;
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
        match outcome {
            NativeWorkerOutput::Member(member_results) => results.extend(member_results),
            NativeWorkerOutput::EvaluationBranch(_) | NativeWorkerOutput::Join(_) => {
                return Err(NativeParallelError::Unsupported(
                    "unexpected branch result in member batch",
                ));
            }
        }
    }
    context
        .report_trace_before_termination(&analysis)
        .map_err(NativeParallelError::Main)?;
    if let Some(reporter) = &reporter {
        reporter
            .report(ferrum_silver::reporter::message::Message::VerificationTermination)
            .map_err(NativeParallelError::Reporter)?;
    }
    // Parallel delivery above owns the termination event; suppress the single-owner hook.
    context.set_preprocessing_reporter(None);
    let termination = context.report_termination_and_optional_trace();
    context.set_preprocessing_reporter(reporter.clone());
    termination.map_err(NativeParallelError::Main)?;
    context
        .run_optional_debugger(&results)
        .map_err(NativeParallelError::Main)?;
    Ok(results)
}

#[cfg(test)]
mod thread_pool_tests {
    use super::*;
    use std::sync::{Arc, Mutex};

    #[cfg(feature = "native-z3")]
    #[test]
    fn controller_interrupts_linked_worker_and_joins() {
        use crate::{
            decider::{
                native_z3::{LinkedProverError, LinkedProverOptions, LinkedZ3Prover},
                z3_prover_api::ApiTimeoutSettings,
            },
            interfaces::decider::prover::Prover,
            state::terms::{TermFactory, TermOptions},
        };
        struct LinkedWorker(LinkedZ3Prover, std::sync::mpsc::Sender<()>);
        impl ThreadBoundWorker for LinkedWorker {
            type Error = LinkedProverError;
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = ();
            type Output = ();
            fn start(&mut self) -> Result<(), Self::Error> {
                self.0.start(None)
            }
            fn broadcast(&mut self, _: ()) -> Result<(), Self::Error> {
                Ok(())
            }
            fn verify(&mut self, _: ()) -> Result<(), Self::Error> {
                for i in 0..15 {
                    for j in 0..14 {
                        self.0.emit(&format!("(declare-const p{i}_{j} Bool)"))?;
                    }
                    self.0.emit(&format!(
                        "(assert (or {}))",
                        (0..14)
                            .map(|j| format!("p{i}_{j}"))
                            .collect::<Vec<_>>()
                            .join(" ")
                    ))?;
                }
                for j in 0..14 {
                    for i in 0..15 {
                        for k in i + 1..15 {
                            self.0
                                .emit(&format!("(assert (or (not p{i}_{j}) (not p{k}_{j})))"))?;
                        }
                    }
                }
                self.0.push(1, None)?;
                self.0.pop(1)?;
                self.1.send(()).unwrap();
                self.0.check(None).map(|_| ())
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                self.0.reset()
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                self.0.stop()
            }
        }
        let controller = CancellationController::default();
        let worker_controller = controller.clone();
        let (started_tx, started_rx) = std::sync::mpsc::channel();
        let mut pool = ThreadVerificationPool::start_with_cancellation(
            1,
            8 * 1024 * 1024,
            controller.clone(),
            move |_| {
                let factory = TermFactory::new(TermOptions {
                    use_flyweight: false,
                    use_old_axiomatization: false,
                    mask_heap_mode: false,
                });
                let prover = LinkedZ3Prover::new(
                    "blocked",
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
                worker_controller.register_linked(prover.cancellation_handle());
                Ok(LinkedWorker(prover, started_tx.clone()))
            },
        )
        .unwrap();
        let running = pool.submit(()).unwrap();
        started_rx.recv().unwrap();
        let queued = pool.submit(()).unwrap();
        std::thread::sleep(std::time::Duration::from_millis(100));
        assert!(
            matches!(
                running.0.try_recv(),
                Err(std::sync::mpsc::TryRecvError::Empty)
            ),
            "solver query ended before cancellation"
        );
        let cancel = controller.clone();
        std::thread::spawn(move || cancel.cancel()).join().unwrap();
        assert!(matches!(queued.wait(), Err(ThreadPoolError::Cancelled)));
        // Z3 reports interruption as unknown or an error; the run-level latch is
        // authoritative, so neither result may turn a timeout into success.
        let _ = running.wait();
        assert!(controller.is_cancelled());
        assert!(pool.cancel_and_join().is_empty());
        assert!(controller.take_errors().is_empty());
    }

    #[test]
    fn cancelled_pool_reports_worker_cleanup_failures() {
        struct CleanupFailure;
        impl ThreadBoundWorker for CleanupFailure {
            type Error = &'static str;
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = ();
            type Output = ();
            fn start(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), Self::Error> {
                Ok(())
            }
            fn verify(&mut self, _: ()) -> Result<(), Self::Error> {
                Ok(())
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                Err("cleanup failed")
            }
        }
        let controller = CancellationController::default();
        let pool = ThreadVerificationPool::start_with_cancellation(
            1,
            1024 * 1024,
            controller.clone(),
            |_| Ok(CleanupFailure),
        )
        .unwrap();
        controller.cancel();
        assert!(matches!(
            pool.cancel_and_join().as_slice(),
            [ThreadPoolError::Worker("cleanup failed")]
        ));
    }

    #[cfg(unix)]
    #[test]
    fn controller_interrupts_blocked_stdio_worker_and_joins() {
        use crate::{
            decider::{
                prover_std_io::{ProverError, ProverSettings, ProverStdIo},
                z3_prover_std_io,
            },
            interfaces::decider::prover::Prover,
            state::terms::{TermFactory, TermOptions},
        };
        use std::os::unix::fs::PermissionsExt;
        struct StdioWorker(ProverStdIo, std::sync::mpsc::Sender<()>);
        impl ThreadBoundWorker for StdioWorker {
            type Error = ProverError;
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = ();
            type Output = ();
            fn start(&mut self) -> Result<(), Self::Error> {
                self.0.start(None)
            }
            fn broadcast(&mut self, _: ()) -> Result<(), Self::Error> {
                Ok(())
            }
            fn verify(&mut self, _: ()) -> Result<(), Self::Error> {
                self.1.send(()).unwrap();
                self.0.check(None).map(|_| ())
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                self.0.reset()
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                self.0.stop()
            }
        }
        let script =
            std::env::temp_dir().join(format!("ferrum-pool-blocked-solver-{}", std::process::id()));
        std::fs::write(&script, "#!/bin/sh\nexec /bin/sleep 60\n").unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o700)).unwrap();
        let controller = CancellationController::default();
        let worker_controller = controller.clone();
        let worker_path = script.clone();
        let (started_tx, started_rx) = std::sync::mpsc::channel();
        let mut pool = ThreadVerificationPool::start_with_cancellation(
            1,
            1024 * 1024,
            controller.clone(),
            move |_| {
                let factory = TermFactory::new(TermOptions {
                    use_flyweight: false,
                    use_old_axiomatization: false,
                    mask_heap_mode: false,
                });
                let prover = z3_prover_std_io::new(
                    "blocked".into(),
                    ProverSettings::new(worker_path.clone(), 10000),
                    factory,
                    |_| {},
                );
                worker_controller.register_stdio(prover.cancellation_handle());
                Ok(StdioWorker(prover, started_tx.clone()))
            },
        )
        .unwrap();
        let running = pool.submit(()).unwrap();
        started_rx.recv().unwrap();
        let queued = pool.submit(()).unwrap();
        let cancel = controller.clone();
        std::thread::spawn(move || cancel.cancel()).join().unwrap();
        assert!(matches!(queued.wait(), Err(ThreadPoolError::Cancelled)));
        assert!(matches!(running.wait(), Err(ThreadPoolError::Worker(_))));
        let cleanup = pool.cancel_and_join();
        assert!(cleanup.is_empty(), "{cleanup:?}");
        assert!(controller.take_errors().is_empty());
        std::fs::remove_file(script).unwrap();
    }

    #[test]
    fn latched_cancellation_interrupts_running_and_rejects_queued_work() {
        struct Blocking {
            started: std::sync::mpsc::Sender<()>,
            release: std::sync::mpsc::Receiver<()>,
        }
        impl ThreadBoundWorker for Blocking {
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
                self.started.send(()).unwrap();
                self.release.recv().unwrap();
                Ok(())
            }
            fn reset(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), ()> {
                Ok(())
            }
        }
        let controller = CancellationController::default();
        let (started_tx, started_rx) = std::sync::mpsc::channel();
        let (release_tx, release_rx) = std::sync::mpsc::channel();
        let receiver = Arc::new(Mutex::new(Some(release_rx)));
        let worker_receiver = receiver.clone();
        let mut pool = ThreadVerificationPool::start_with_cancellation(
            1,
            1024 * 1024,
            controller.clone(),
            move |_| {
                Ok(Blocking {
                    started: started_tx.clone(),
                    release: worker_receiver.lock().unwrap().take().unwrap(),
                })
            },
        )
        .unwrap();
        controller.register(move || release_tx.send(()).map_err(|e| e.to_string()));
        let running = pool.submit(()).unwrap();
        started_rx.recv().unwrap();
        let queued = pool.submit(()).unwrap();
        let signal = controller.clone();
        std::thread::spawn(move || signal.cancel()).join().unwrap();
        assert!(controller.checkpoint().is_err());
        assert!(matches!(queued.wait(), Err(ThreadPoolError::Cancelled)));
        assert!(running.wait().is_ok());
        assert!(matches!(pool.submit(()), Err(ThreadPoolError::Stopped)));
        let late = Arc::new(std::sync::atomic::AtomicBool::new(false));
        let observed = late.clone();
        controller.register(move || {
            observed.store(true, std::sync::atomic::Ordering::SeqCst);
            Ok(())
        });
        assert!(late.load(std::sync::atomic::Ordering::SeqCst));
        assert!(pool.cancel_and_join().is_empty());
        assert!(controller.take_errors().is_empty());
    }

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
    fn branch_transfer_payload_types_are_send() {
        fn require_send<T: Send>() {}
        type S = crate::state::state::State<
            crate::supporters::predicate_verification_unit::PredicateData,
            super::super::native_context::NativeFunctionData,
            crate::config::JoinMode,
        >;
        require_send::<S>();
        require_send::<NativeEvaluationBranch>();
        require_send::<NativeEvaluationBranchOutput>();
        require_send::<NativeJoinJob>();
        require_send::<NativeJoinOutput>();
        require_send::<crate::rules::brancher::BranchTransferSnapshot>();
        require_send::<
            crate::rules::joiner::JoinDataEntry<
                crate::supporters::predicate_verification_unit::PredicateData,
                super::super::native_context::NativeFunctionData,
                crate::config::JoinMode,
                (Term, Option<ferrum_silver::ast::expression::Exp>),
            >,
        >();
    }

    #[test]
    fn worker_failure_and_warning_delivery_failure_are_both_retained() {
        use super::super::native_context::NativeError;
        let outcome: Result<(), NativeError<()>> = Err(NativeError::Cancelled);
        let delivery = Err(NativeError::Diagnostic("reporter failed".into()));
        match finish_worker_warning_delivery(outcome, vec!["unsent warning".into()], delivery) {
            Err(NativeError::BranchWarnings { primary, warnings }) => {
                assert_eq!(warnings[0], "unsent warning");
                assert!(warnings[1].contains("reporter failed"));
                assert!(matches!(*primary, NativeError::Cancelled));
            }
            _ => panic!("lost worker failure or warning"),
        }
        let outcome: Result<(), NativeError<()>> = Err(NativeError::Cancelled);
        assert!(matches!(
            finish_worker_warning_delivery(outcome, vec![], Ok(())),
            Err(NativeError::Cancelled)
        ));
    }

    #[test]
    fn nested_wait_executes_on_single_owner_thread_without_deadlock() {
        struct Nested {
            owner: std::thread::ThreadId,
            _not_send: std::rc::Rc<()>,
            stopped: Arc<std::sync::atomic::AtomicUsize>,
        }
        impl ThreadBoundWorker for Nested {
            type Error = &'static str;
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = usize;
            type Output = usize;
            fn start(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), Self::Error> {
                Ok(())
            }
            fn verify(&mut self, _: usize) -> Result<usize, Self::Error> {
                Err("missing cooperative context")
            }
            fn verify_cooperative(
                &mut self,
                depth: usize,
                queue: &WorkerQueueHandle<Self>,
            ) -> Result<usize, Self::Error> {
                assert_eq!(self.owner, std::thread::current().id());
                if depth == 0 {
                    return Ok(0);
                }
                let task = queue.submit(depth - 1).map_err(|_| "submit")?;
                let waited = queue
                    .wait_cooperatively_with(task, |nested| self.verify_cooperative(nested, queue));
                assert!(waited.awaited_executed_on_current_worker);
                assert!(!waited.executed_other_task);
                waited.result.map(|value| value + 1).map_err(|_| "wait")
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                self.stopped
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                Ok(())
            }
        }
        let stopped = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let stopped_worker = stopped.clone();
        let mut pool = ThreadVerificationPool::start(1, move |_| {
            Ok(Nested {
                owner: std::thread::current().id(),
                _not_send: std::rc::Rc::new(()),
                stopped: stopped_worker.clone(),
            })
        })
        .unwrap();
        assert_eq!(pool.submit(8).unwrap().wait().unwrap(), 8);
        pool.shutdown().unwrap();
        assert_eq!(stopped.load(std::sync::atomic::Ordering::SeqCst), 1);
    }

    #[test]
    fn cancelled_nested_task_wakes_cooperative_waiter() {
        struct NestedCancel {
            queued: std::sync::mpsc::Sender<()>,
            resume: std::sync::mpsc::Receiver<()>,
        }
        impl ThreadBoundWorker for NestedCancel {
            type Error = &'static str;
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = bool;
            type Output = bool;
            fn start(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), Self::Error> {
                Ok(())
            }
            fn verify(&mut self, task: bool) -> Result<bool, Self::Error> {
                Ok(task)
            }
            fn verify_cooperative(
                &mut self,
                task: bool,
                queue: &WorkerQueueHandle<Self>,
            ) -> Result<bool, Self::Error> {
                if !task {
                    return Ok(false);
                }
                let nested = queue.submit(false).map_err(|_| "submit")?;
                self.queued.send(()).map_err(|_| "notify")?;
                self.resume.recv().map_err(|_| "resume")?;
                let waited = queue.wait_cooperatively(self, nested);
                assert!(matches!(waited.result, Err(ThreadPoolError::Cancelled)));
                assert!(!waited.executed_other_task);
                assert!(!waited.awaited_executed_on_current_worker);
                Ok(true)
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
        }
        let (queued_tx, queued_rx) = std::sync::mpsc::channel();
        let (resume_tx, resume_rx) = std::sync::mpsc::channel();
        let receiver = Arc::new(Mutex::new(Some(resume_rx)));
        let mut pool = ThreadVerificationPool::start(1, move |_| {
            Ok(NestedCancel {
                queued: queued_tx.clone(),
                resume: receiver.lock().unwrap().take().expect("one worker"),
            })
        })
        .unwrap();
        let parent = pool.submit(true).unwrap();
        queued_rx.recv().unwrap();
        assert_eq!(pool.cancel_pending().unwrap(), 1);
        resume_tx.send(()).unwrap();
        assert!(parent.wait().unwrap());
        pool.shutdown().unwrap();
    }

    #[test]
    fn nested_panic_uses_owner_shutdown_path() {
        struct NestedPanic(Arc<std::sync::atomic::AtomicUsize>);
        impl ThreadBoundWorker for NestedPanic {
            type Error = ();
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = bool;
            type Output = ();
            fn start(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), ()> {
                Ok(())
            }
            fn verify(&mut self, _: bool) -> Result<(), ()> {
                Ok(())
            }
            fn verify_cooperative(
                &mut self,
                task: bool,
                queue: &WorkerQueueHandle<Self>,
            ) -> Result<(), ()> {
                if !task {
                    panic!("nested task failure");
                }
                let nested = queue.submit(false).unwrap();
                let _ = queue.wait_cooperatively(self, nested);
                Ok(())
            }
            fn reset(&mut self) -> Result<(), ()> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), ()> {
                self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                Ok(())
            }
        }
        let stopped = Arc::new(std::sync::atomic::AtomicUsize::new(0));
        let worker_stopped = stopped.clone();
        let mut pool =
            ThreadVerificationPool::start(1, move |_| Ok(NestedPanic(worker_stopped.clone())))
                .unwrap();
        assert!(matches!(
            pool.submit(true).unwrap().wait(),
            Err(ThreadPoolError::WorkerPanicked)
        ));
        assert!(matches!(pool.shutdown(), Err(ThreadPoolError::Stopped)));
        assert_eq!(stopped.load(std::sync::atomic::Ordering::SeqCst), 1);
    }

    #[test]
    fn cooperative_wait_reports_interruption_and_remote_completion() {
        #[derive(Clone, Copy)]
        enum Job {
            Outer,
            Awaited,
            Intervening,
        }
        struct NestedRemote(Arc<(Mutex<(bool, bool, bool)>, std::sync::Condvar)>);
        impl ThreadBoundWorker for NestedRemote {
            type Error = &'static str;
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = Job;
            type Output = ();
            fn start(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), Self::Error> {
                Ok(())
            }
            fn verify(&mut self, _: Job) -> Result<(), Self::Error> {
                Err("missing queue")
            }
            fn verify_cooperative(
                &mut self,
                job: Job,
                queue: &WorkerQueueHandle<Self>,
            ) -> Result<(), Self::Error> {
                let shared = self.0.clone();
                let (lock, ready) = &*shared;
                match job {
                    Job::Outer => {
                        let task = queue.submit(Job::Awaited).map_err(|_| "submit")?;
                        let mut state = lock.lock().unwrap();
                        while !state.0 {
                            state = ready.wait(state).unwrap();
                        }
                        state.1 = true;
                        ready.notify_all();
                        drop(state);
                        let waited = queue.wait_cooperatively(self, task);
                        assert!(waited.executed_other_task);
                        assert!(!waited.awaited_executed_on_current_worker);
                        waited.result.map_err(|_| "wait")
                    }
                    Job::Awaited => {
                        let mut state = lock.lock().unwrap();
                        state.0 = true;
                        ready.notify_all();
                        while !state.2 {
                            state = ready.wait(state).unwrap();
                        }
                        Ok(())
                    }
                    Job::Intervening => {
                        let mut state = lock.lock().unwrap();
                        state.2 = true;
                        ready.notify_all();
                        Ok(())
                    }
                }
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
        }
        let shared = Arc::new((Mutex::new((false, false, false)), std::sync::Condvar::new()));
        let worker_shared = shared.clone();
        let mut pool =
            ThreadVerificationPool::start(2, move |_| Ok(NestedRemote(worker_shared.clone())))
                .unwrap();
        let parent = pool.submit(Job::Outer).unwrap();
        let (lock, ready) = &*shared;
        let mut state = lock.lock().unwrap();
        while !state.1 {
            state = ready.wait(state).unwrap();
        }
        drop(state);
        let intervening = pool.submit(Job::Intervening).unwrap();
        parent.wait().unwrap();
        intervening.wait().unwrap();
        pool.shutdown().unwrap();
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
    fn broadcast_failure_retains_worker_cleanup_errors() {
        struct FailingWorker(usize);
        impl ThreadBoundWorker for FailingWorker {
            type Error = &'static str;
            type Broadcast = ();
            type BroadcastResult = ();
            type Task = ();
            type Output = ();
            fn start(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn broadcast(&mut self, _: ()) -> Result<(), Self::Error> {
                Err("broadcast")
            }
            fn verify(&mut self, _: ()) -> Result<(), Self::Error> {
                Ok(())
            }
            fn reset(&mut self) -> Result<(), Self::Error> {
                Ok(())
            }
            fn stop(&mut self) -> Result<(), Self::Error> {
                if self.0 == 0 { Err("stop") } else { Ok(()) }
            }
        }
        let mut pool = ThreadVerificationPool::start(2, |id| Ok(FailingWorker(id))).unwrap();
        match pool.broadcast(()) {
            Err(ThreadPoolError::Cleanup { primary, errors }) => {
                assert!(matches!(*primary, ThreadPoolError::Worker("broadcast")));
                assert!(matches!(
                    errors.as_slice(),
                    [ThreadPoolError::Worker("stop")]
                ));
            }
            other => panic!("expected aggregated failure, got {other:?}"),
        }
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
    fn run_parallel_source_with_warnings_impl<P, F>(
        source: &str,
        workers: usize,
        make: F,
        standalone_cfg: bool,
        cfg_scheduler: bool,
        nonjoined: bool,
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
        run_parallel_source_with_profile(
            source,
            workers,
            make,
            standalone_cfg,
            cfg_scheduler,
            nonjoined,
            true,
            false,
        )
    }
    fn run_parallel_source_with_profile<P, F>(
        source: &str,
        workers: usize,
        make: F,
        standalone_cfg: bool,
        cfg_scheduler: bool,
        nonjoined: bool,
        simplified_unfolds: bool,
        disable_subsumption: bool,
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
        let mut config = Config::default();
        config.disable_subsumption = disable_subsumption;
        if nonjoined {
            config.number_of_errors_to_report = 2;
            config.more_joins = crate::config::JoinMode::Off;
        }
        if cfg_scheduler {
            config.more_joins = if nonjoined {
                crate::config::JoinMode::Off
            } else {
                crate::config::JoinMode::All
            };
            config.enable_simplified_unfolds = simplified_unfolds;
        }
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
            let mut worker = native_method_worker(
                name,
                prover,
                identifiers,
                worker_factory.clone(),
                worker_options.clone(),
                &worker_config,
            );
            worker.context.joined_branch_scheduler_enabled = cfg_scheduler;
            Ok(worker)
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
                .filter(|method| !source.contains("// manual_") || method.name != "scaffold")
                .map(|method| {
                    if source.contains("// manual_") {
                        use ferrum_silver::ast::statement::{Stmt, StmtKind};
                        fn transform(body: &Stmt, depth: usize, wrap_try: bool) -> Stmt {
                            let StmtKind::Seqn {
                                statements,
                                declarations,
                            } = body.kind()
                            else {
                                return body.clone();
                            };
                            let locals = declarations.iter().filter_map(|d| match d {
                                ferrum_silver::ast::program::Declaration::Local(local) => {
                                    Some(Stmt::new(
                                        StmtKind::LocalVarDeclStmt(local.clone()),
                                        body.metadata().clone(),
                                    ))
                                }
                                _ => None,
                            });
                            let statements = locals
                                .chain(
                                    statements
                                        .iter()
                                        .map(|stmt| transform(stmt, depth + 1, wrap_try)),
                                )
                                .collect();
                            let seq = Stmt::new(
                                StmtKind::Seqn {
                                    statements,
                                    declarations: declarations.clone(),
                                },
                                body.metadata().clone(),
                            );
                            if depth >= 2 && wrap_try {
                                crate::extensions::try_block_stmt::TryBlock {
                                    body: seq,
                                    meta: body.metadata().clone(),
                                }
                                .statement()
                            } else {
                                seq
                            }
                        }
                        let body = transform(
                            method.body.as_ref().unwrap(),
                            0,
                            source.contains("// manual_try_cfg"),
                        );
                        if source.contains("// manual_loop_cfg") {
                            use ferrum_silver::cfg::{
                                block::Block,
                                edge::{Edge, Kind},
                            };
                            let entry = Block::statement(vec![]);
                            let head = Block::loop_head(vec![], vec![body], None);
                            let exit = Block::statement(vec![]);
                            let edges = vec![
                                Edge::unconditional(entry.clone(), head.clone(), Kind::In),
                                Edge::unconditional(head.clone(), exit.clone(), Kind::Out),
                            ];
                            ferrum_silver::cfg::silver::silver_cfg::SilverCfg::new(
                                vec![entry.clone(), head, exit.clone()],
                                edges,
                                entry,
                                Some(exit),
                            )
                        } else {
                            let block = ferrum_silver::cfg::block::Block::statement(vec![body]);
                            ferrum_silver::cfg::silver::silver_cfg::SilverCfg::new(
                                vec![block.clone()],
                                vec![],
                                block.clone(),
                                Some(block),
                            )
                        }
                    } else {
                        ferrum_silver::cfg::silver::cfg_generator::statement_to_cfg(
                            method.body.as_ref().unwrap(),
                            true,
                            true,
                        )
                        .unwrap()
                    }
                })
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
        let program = if standalone_cfg {
            program.copy_with(|data| {
                if source.contains("// manual_") {
                    data.methods.retain(|method| method.name == "scaffold");
                } else {
                    data.methods.clear();
                }
            })
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
        if !disable_subsumption {
            assert_eq!(failures.len(), 1);
            if source.contains("r := old[L](asserting (b ? acc(x.f) : acc(y.f)) in 1)") {
                assert!(
                    failures[0]
                        .iter()
                        .any(|error| error.full_id().contains("insufficient.permission")),
                    "{failures:?}"
                );
            }
            if source.contains("// owned_return_right_failure_check") {
                assert!(
                    failures[0]
                        .iter()
                        .any(|error| error.full_id().contains("insufficient.permission")),
                    "right assertion permission error missing: {failures:?}"
                );
            }
            if source.contains("// owned_return_tail_check") {
                assert!(
                    failures[0]
                        .iter()
                        .any(|error| error.full_id().contains("assertion.false")),
                    "tail assertion error missing: {failures:?}"
                );
            }
            if source.contains("if (b) { label L; }") {
                assert!(
                    failures[0]
                        .iter()
                        .any(|error| error.full_id().contains("labelled.state.not.reached")),
                    "{failures:?}"
                );
            }
            if source.contains("if (b) { assert false; } else { assert false; }") {
                assert_eq!(
                    failures[0].len(),
                    2,
                    "both branch failures must be retained"
                );
            }
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
        } else {
            drop(reports);
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
    fn run_parallel_source_with_warnings<P, F>(
        source: &str,
        workers: usize,
        make: F,
        standalone_cfg: bool,
        cfg_scheduler: bool,
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
        run_parallel_source_with_warnings_impl(
            source,
            workers,
            make,
            standalone_cfg,
            cfg_scheduler,
            false,
        )
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
        run_parallel_source_with_warnings(source, workers, make, false, false).0
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
        let (fatal, worker_warnings) =
            run_parallel_source_with_warnings(source, 2, make, false, false);
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
        let (fatal, worker_warnings) =
            run_parallel_source_with_warnings(source, 2, make, false, false);
        assert_eq!(fatal.iter().filter(|value| **value).count(), 1);
        assert!(
            worker_warnings
                .iter()
                .any(|w| w.contains("invalid moreJoins"))
        );
        assert_eq!(warnings.lock().unwrap().len(), 3);
    }
    #[test]
    fn real_stdio_nonjoined_cfg_continuations_reach_method_terminal() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
method good(x: Ref, b: Bool, c: Bool) returns (r: Int)
  requires acc(x.f)
  ensures acc(x.f, 1/2) && r == x.f && r >= 1
{
  if (b) { x.f := 1; } else { if (c) { x.f := 2; } else { x.f := 3; } }
  r := x.f;
  exhale acc(x.f, 1/2);
}
method bad(x: Ref, b: Bool) returns (r: Int)
  requires acc(x.f)
  ensures acc(x.f, 1/2) && r > 0
{
  if (b) { x.f := 1; } else { x.f := 0; }
  r := x.f;
  exhale acc(x.f, 1/2);
}
method unrelated(x: Ref) requires acc(x.f) ensures acc(x.f) { x.f := 5; }
"#;
        let both_fail = source.replace(
            "if (b) { x.f := 1; } else { x.f := 0; }",
            "if (b) { assert false; } else { assert false; }",
        );
        let permission_fail = source.replace(
            "if (b) { x.f := 1; } else { x.f := 0; }",
            "if (b) { x.f := 1; } else { x.f := 0; exhale acc(x.f); }",
        );
        for (source, expected_failures) in [
            (source, 1),
            (both_fail.as_str(), 2),
            (permission_fail.as_str(), 1),
        ] {
            for workers in [1, 2] {
                let before =
                    CONTINUATION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed =
                    CONTINUATION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert_eq!(
                    fatal.iter().filter(|fatal| **fatal).count(),
                    expected_failures
                );
                assert!(!fatal[0]);
                assert!(
                    CONTINUATION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > before,
                    "nonjoined CFG continuation never submitted"
                );
                assert!(
                    CONTINUATION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > executed,
                    "nonjoined CFG continuation never executed"
                );
            }
        }
    }

    #[test]
    fn real_stdio_nonjoined_cfg_continuations_cross_loop_boundaries() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
method good(x: Ref, b: Bool, c: Bool) returns (r: Int)
  requires acc(x.f)
  ensures acc(x.f) && r >= 1
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant acc(x.f)
    invariant i == 1 ==> x.f >= 1
  {
    if (b) { x.f := 1; } else { x.f := 2; }
    i := i + 1;
  }
  if (c) { r := x.f; } else { r := x.f + 1; }
}
method bad(x: Ref, b: Bool) returns (r: Int)
  requires acc(x.f)
  ensures acc(x.f) && r == 0
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant acc(x.f)
    invariant i == 1 ==> x.f >= 1
  {
    if (b) { x.f := 1; } else { x.f := 2; }
    i := i + 1;
  }
  r := x.f;
}
"#;
        let body_only = source.replace("if (c) { r := x.f; } else { r := x.f + 1; }", "r := x.f;");
        let exit_only = source.replace("if (b) { x.f := 1; } else { x.f := 2; }", "x.f := 1;");
        for source in [body_only.as_str(), exit_only.as_str()] {
            for workers in [1, 2] {
                let before = CONTINUATION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
                assert!(
                    CONTINUATION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > before,
                    "loop continuation never executed"
                );
            }
        }
    }

    #[test]
    fn real_stdio_owned_producer_permission_tails() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let cases = [
            r#"field f: Int
method producer(b: Bool, x: Ref, y: Ref)
  requires x != y
  ensures b ? acc(x.f) : acc(y.f)
{
  inhale b ? acc(x.f) : acc(y.f);
  assert b ? acc(x.f) : acc(y.f);
}
method consumer(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
  ensures b ? acc(y.f) : acc(x.f)
{
  exhale b ? acc(x.f) : acc(y.f);
  assert b ? acc(y.f) : acc(x.f);
}
method bad(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
{
  exhale b ? acc(x.f) : acc(y.f);
  assert false;
}
"#,
            r#"field f: Int
method good(b: Bool, x: Ref, y: Ref, z: Ref)
  requires x != y && x != z && y != z
  ensures b ? acc(x.f) && acc(z.f) : acc(y.f) && acc(z.f)
{
  inhale (b ? (let a == (x) in acc(a.f) && acc(z.f)) : (let a == (y) in acc(a.f) && acc(z.f)));
  assert b ? acc(x.f) && acc(z.f) : acc(y.f) && acc(z.f);
}
method nested(b: Bool, x: Ref, y: Ref)
  requires x != y
  ensures b ? acc(x.f) : acc(y.f)
{
  inhale let a == (x) in (b ? acc(a.f) : acc(y.f));
}
method bad() { assert false; }
"#,
            r#"field f: Int
method good(b: Bool, x: Ref, y: Ref)
  requires x != y
  ensures b ? acc(x.f) : acc(y.f)
{
  inhale b ? acc(x.f) : acc(y.f);
}
method bad(b: Bool, x: Ref, y: Ref)
  requires x != y
  ensures acc(x.f)
{
  inhale b ? acc(x.f) : acc(y.f);
}
"#,
        ];
        for source in cases {
            for workers in [1, 2] {
                let submitted =
                    RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed =
                    RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert!(fatal.iter().any(|fatal| *fatal));
                assert!(
                    RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > submitted,
                    "no production job submitted"
                );
                assert!(
                    RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > executed,
                    "no production job executed"
                );
            }
        }
    }

    #[test]
    fn real_stdio_owned_consumer_permission_tails() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let cases = [
            r#"field f: Int
method producer(b: Bool, x: Ref, y: Ref)
  requires x != y
  ensures b ? acc(x.f) : acc(y.f)
{
  inhale b ? acc(x.f) : acc(y.f);
  assert b ? acc(x.f) : acc(y.f);
}
method consumer(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
  ensures b ? acc(y.f) : acc(x.f)
{
  exhale b ? acc(x.f) : acc(y.f);
  assert b ? acc(y.f) : acc(x.f);
}
method bad(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
{
  exhale b ? acc(x.f) : acc(y.f);
  assert false;
}
"#,
            r#"field f: Int
method good(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref)
  requires acc(x.f) && acc(y.f) && acc(z.f)
  ensures b ? (c ? acc(y.f) && acc(z.f) : acc(x.f) && acc(z.f)) : acc(x.f) && acc(y.f)
{
  exhale b ? (c ? acc(x.f) : acc(y.f)) : acc(z.f);
  assert b ? (c ? acc(y.f) && acc(z.f) : acc(x.f) && acc(z.f)) : acc(x.f) && acc(y.f);
}
method bad(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
{
  exhale (b ? acc(x.f) : acc(y.f)) && true;
  assert false;
}
"#,
            r#"field f: Int
method good(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
  ensures acc(x.f) && acc(y.f)
{
  assert b ? acc(x.f) : acc(y.f);
  assert b ? acc(y.f) : acc(x.f);
}
method bad(b: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f)
{
  exhale b ? acc(x.f) : acc(y.f);
}
"#,
        ];
        for source in cases {
            for workers in [1, 2] {
                let submitted =
                    RULE_CONSUMPTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed =
                    RULE_CONSUMPTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert!(fatal.iter().any(|fatal| *fatal));
                assert!(
                    RULE_CONSUMPTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > submitted,
                    "no consumption job submitted"
                );
                assert!(
                    RULE_CONSUMPTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > executed,
                    "no consumption job executed"
                );
            }
        }
    }

    #[test]
    fn real_stdio_owned_conditional_method_postconditions() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
method good(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
  ensures b ? acc(x.f) : acc(y.f)
{}
method bad(b: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f)
  ensures b ? acc(x.f) : acc(y.f)
{}
"#;
        for workers in [1, 2] {
            let submitted =
                RULE_CONSUMPTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed =
                RULE_CONSUMPTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                RULE_CONSUMPTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > submitted
            );
            assert!(
                RULE_CONSUMPTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > executed
            );
        }
    }

    #[test]
    fn real_stdio_nested_sequence_try_cfg_continuations() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = "// manual_try_cfg\nfield f: Int method scaffold() requires forall z: Ref :: acc(z.f) {} method good() { var b: Bool; var x: Ref; var y: Ref; { inhale b ? acc(x.f) : acc(y.f); } assert b ? acc(x.f) : acc(y.f); } method bad() { assert false; }";
        let try_failure = source.replace(
            "inhale b ? acc(x.f) : acc(y.f); } assert b ? acc(x.f) : acc(y.f);",
            "inhale b ? acc(x.f) : acc(y.f); assert false; } assert perm(x.f) == none && perm(y.f) == none;",
        );
        for source in [source, try_failure.as_str()] {
            for workers in [1, 2] {
                let submitted =
                    RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed =
                    RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    true,
                    true,
                    true,
                );
                assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
                assert!(
                    RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > submitted
                );
                assert!(
                    RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > executed
                );
            }
        }
    }

    #[test]
    fn real_stdio_loop_head_statement_continuations() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = "// manual_loop_cfg\nfield f: Int method scaffold() requires forall z: Ref :: acc(z.f) {} method good() { var b: Bool; var x: Ref; var y: Ref; { inhale b ? acc(x.f) : acc(y.f); } assert b ? acc(x.f) : acc(y.f); } method bad() { assert false; }";
        for workers in [1, 2] {
            let submitted =
                RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed =
                RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                true,
                true,
                true,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > submitted
            );
            assert!(
                RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > executed
            );
        }
    }

    #[test]
    fn real_stdio_producer_conditional_inside_let_executes_on_owned_worker() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = "field f: Int method good(b: Bool, x: Ref, y: Ref) requires x != y ensures b ? acc(x.f) : acc(y.f) { inhale let a == (x) in (b ? acc(a.f) : acc(y.f)); } method bad() { assert false; }";
        for workers in [1, 2] {
            let submitted =
                RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed =
                RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert!(fatal.iter().any(|fatal| *fatal));
            assert!(
                RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > submitted
            );
            assert!(
                RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > executed
            );
        }
    }

    #[test]
    fn real_stdio_owned_consumer_let_continuations() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let cases = [
            r#"field f: Int
method good(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
  ensures b ? acc(y.f) : acc(x.f)
{
  exhale let a == (x) in (b ? acc(a.f) : acc(y.f));
}
method bad(b: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f)
{
  exhale let a == (x) in (b ? acc(a.f) : acc(y.f));
}
"#,
            r#"field f: Int
method good(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
  ensures let a == (x) in (b ? acc(a.f) : acc(y.f))
{}
method bad(b: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f)
  ensures let a == (x) in (b ? acc(a.f) : acc(y.f))
{}
"#,
        ];
        for source in cases {
            for workers in [1, 2] {
                let submitted =
                    RULE_CONSUMPTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed =
                    RULE_CONSUMPTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
                assert!(
                    RULE_CONSUMPTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > submitted
                );
                assert!(
                    RULE_CONSUMPTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > executed
                );
            }
        }
    }

    #[test]
    fn real_stdio_owned_producer_contract_continuations() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let cases = [
            r#"field f: Int
method good(b: Bool, x: Ref, y: Ref)
  requires b ? acc(x.f) : acc(y.f)
  ensures b ? acc(x.f) : acc(y.f)
{}
method bad(b: Bool, x: Ref, y: Ref)
  requires x != y
  requires b ? acc(x.f) : acc(y.f)
  ensures acc(x.f)
{}
"#,
            r#"field f: Int
method good(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
  ensures b ? acc(x.f) : acc(y.f)
{}
method bad(b: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f)
  ensures b ? acc(x.f) : acc(y.f)
{}
"#,
        ];
        for source in cases {
            for workers in [1, 2] {
                let submitted =
                    RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed =
                    RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
                assert!(
                    RULE_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > submitted
                );
                assert!(
                    RULE_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > executed
                );
            }
        }
    }

    #[test]
    fn real_stdio_owned_fold_conditional_snapshot() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
predicate P(b: Bool, x: Ref, y: Ref) { b ? (acc(x.f) && x.f == 1) : (acc(y.f) && y.f == 2) }
method good(b: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f) && acc(y.f) && x.f == 1 && y.f == 2
{
  fold acc(P(b, x, y));
  unfold acc(P(b, x, y));
  assert b ? x.f == 1 : y.f == 2;
}
method bad(b: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f) && x.f == 1
{
  fold acc(P(b, x, y));
}
"#;
        for workers in [1, 2] {
            let submitted = FOLD_BODY_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed = FOLD_BODY_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                FOLD_BODY_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > submitted
            );
            assert!(FOLD_BODY_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > executed);
        }
    }

    #[test]
    fn real_stdio_owned_method_call_conditionals() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
method callee(b: Bool, c: Bool, x: Ref, y: Ref) returns (r: Int)
  requires (b ? acc(x.f, 1/2) : acc(y.f, 1/2)) && acc(x.f, 1/2) && acc(y.f, 1/2)
  ensures c ? acc(x.f, 1/2) : acc(y.f, 1/2)
  ensures r == old(x.f)
method good(b: Bool, c: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
{
  var r: Int;
  var before: Int := x.f;
  r := callee(b, c, x, y);
  assert r == before;
}
method bad(b: Bool, c: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f)
{
  var r: Int;
  r := callee(b, c, x, y);
}
"#;
        for workers in [1, 2] {
            let ps = CALL_POST_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let pe = CALL_POST_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let cs = CALL_PRE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let ce = CALL_PRE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (baseline, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                false,
                true,
            );
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            eprintln!("baseline: {baseline:?}, actual: {fatal:?}");
            assert_eq!(
                fatal.iter().filter(|v| **v).count(),
                baseline.iter().filter(|v| **v).count()
            );
            eprintln!(
                "call post submit={} exec={} pre submit={} exec={}",
                CALL_POST_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) - ps,
                CALL_POST_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) - pe,
                CALL_PRE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) - cs,
                CALL_PRE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) - ce
            );
            assert!(CALL_POST_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > ps);
            assert!(CALL_POST_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > pe);
            assert!(CALL_PRE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > cs);
            assert!(CALL_PRE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > ce);
        }
    }

    #[test]
    fn real_stdio_owned_cached_unfold_tree() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
field g: Int
predicate P(x: Ref, b: Bool) { b ? (acc(x.f) && x.f == 7) : (acc(x.g) && x.g == 8) }
method good(x: Ref, b: Bool)
  requires acc(P(x, b))
{
  unfold acc(P(x, b));
  assert b ? (acc(x.f) && x.f == 7) : (acc(x.g) && x.g == 8);
}
method bad(x: Ref, b: Bool)
  requires acc(P(x, b))
{
  unfold acc(P(x, b));
  assert b ? (acc(x.f) && x.f == 9) : (acc(x.g) && x.g == 8);
}
"#;
        for workers in [1, 2] {
            let submitted = UNFOLD_TREE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed = UNFOLD_TREE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                UNFOLD_TREE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > submitted
            );
            assert!(
                UNFOLD_TREE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > executed
            );
        }
    }

    #[test]
    fn real_stdio_owned_uncached_unfold_production() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
field g: Int
predicate P(x: Ref, b: Bool) { b ? (acc(x.f) && x.f == 7) : (acc(x.g) && x.g == 8) }
method good(x: Ref, b: Bool)
  requires acc(P(x, b))
{
  unfold acc(P(x, b));
  assert b ? (acc(x.f) && x.f == 7) : (acc(x.g) && x.g == 8);
}
method bad(x: Ref, b: Bool)
  requires acc(P(x, b))
{
  unfold acc(P(x, b));
  assert b ? (acc(x.f) && x.f == 9) : (acc(x.g) && x.g == 8);
}
"#;
        for workers in [1, 2] {
            let submitted =
                UNFOLD_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed =
                UNFOLD_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_profile(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
                false,
                false,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                UNFOLD_PRODUCTION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > submitted
            );
            assert!(
                UNFOLD_PRODUCTION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > executed
            );
        }
    }

    #[test]
    fn real_stdio_owned_loop_phase_collector() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let cases = [
            r#"field f: Int
method good(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant b ? acc(x.f) : acc(y.f)
  { i := i + 1; }
}
method bad(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant b ? acc(x.f) : acc(y.f)
  { exhale b ? acc(x.f) : acc(y.f); i := i + 1; }
}
"#,
            r#"field f: Int
method good(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref)
  requires acc(x.f) && acc(y.f) && acc(z.f)
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant b ? (c ? acc(x.f) : acc(y.f)) : acc(z.f)
  { i := i + 1; }
}
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref)
  requires acc(x.f) && acc(y.f) && acc(z.f)
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant b ? (c ? acc(x.f) : acc(y.f)) : acc(z.f)
  { exhale b ? (c ? acc(x.f) : acc(y.f)) : acc(z.f); i := i + 1; }
}
"#,
        ];
        for source in cases {
            for workers in [1, 2] {
                let submitted =
                    LOOP_PHASE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed = LOOP_PHASE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert!(fatal.iter().any(|fatal| *fatal));
                assert!(
                    LOOP_PHASE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > submitted
                );
                assert!(
                    LOOP_PHASE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > executed
                );
            }
        }
    }

    #[test]
    fn real_stdio_owned_loop_establishment() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let cases = [
            r#"field f: Int
method good(b: Bool, x: Ref, y: Ref)
  requires acc(x.f) && acc(y.f)
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant b ? acc(x.f) : acc(y.f)
  { i := i + 1; }
}
method bad(b: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f)
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant b ? acc(x.f) : acc(y.f)
  { i := i + 1; }
}
"#,
            r#"field f: Int
method good(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref)
  requires acc(x.f) && acc(y.f) && acc(z.f)
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant b ? (c ? acc(x.f) : acc(y.f)) : acc(z.f)
  { i := i + 1; }
}
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref)
  requires x != y && x != z && acc(x.f)
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant b ? (c ? acc(x.f) : acc(y.f)) : acc(z.f)
  { i := i + 1; }
}
"#,
        ];
        for source in cases {
            for workers in [1, 2] {
                let submitted =
                    LOOP_ESTABLISH_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed =
                    LOOP_ESTABLISH_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert!(fatal.iter().any(|fatal| *fatal));
                assert!(
                    LOOP_ESTABLISH_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > submitted
                );
                assert!(
                    LOOP_ESTABLISH_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > executed
                );
            }
        }
    }

    #[test]
    fn real_stdio_owned_loop_backedge_invariants() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
method choose() returns (r: Bool)
method good(x: Ref)
  requires acc(x.f)
{
  var i: Int := 0;
  var c: Bool;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant c ? acc(x.f) : acc(x.f)
  {
    c := choose();
    i := i + 1;
  }
}
method bad(x: Ref)
  requires acc(x.f)
{
  var i: Int := 0;
  var c: Bool;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant c ? acc(x.f) : acc(x.f)
  {
    exhale acc(x.f);
    c := choose();
    i := i + 1;
  }
}
"#;
        for workers in [1, 2] {
            let submitted =
                LOOP_BACKEDGE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed = LOOP_BACKEDGE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert!(fatal.iter().any(|fatal| *fatal));
            assert!(
                LOOP_BACKEDGE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > submitted
            );
            assert!(
                LOOP_BACKEDGE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > executed
            );
        }
    }

    #[test]
    fn real_stdio_integrated_call_fold_unfold_loop() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
predicate P(b: Bool, x: Ref, y: Ref) { b ? (acc(x.f) && x.f == 1) : (acc(y.f) && y.f == 2) }
method callee(b: Bool, c: Bool, x: Ref, y: Ref) returns (r: Int)
  requires (b ? acc(x.f, 1/2) : acc(y.f, 1/2)) && acc(x.f, 1/2) && acc(y.f, 1/2)
  ensures c ? acc(x.f, 1/2) : acc(y.f, 1/2)
  ensures r == old(x.f)
method good(b: Bool, c: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f) && acc(y.f) && x.f == 1 && y.f == 2
{
  var i: Int := 0;
  while (i < 1)
    invariant 0 <= i && i <= 1
    invariant acc(x.f) && acc(y.f) && x.f == 1 && y.f == 2
  {
    fold acc(P(b, x, y));
    unfold acc(P(b, x, y));
    i := i + 1;
  }
  var r: Int;
  r := callee(b, c, x, y);
  assert r == 1;
}
method bad(b: Bool, c: Bool, x: Ref, y: Ref)
  requires x != y && acc(x.f) && acc(y.f) && x.f == 1 && y.f == 2
{
  var r: Int;
  r := callee(b, c, x, y);
  assert r == 9;
}
method extra(b: Bool, x: Ref, y: Ref)
  requires acc(P(b, x, y))
{
  unfold acc(P(b, x, y));
  assert b ? x.f == 1 : y.f == 2;
}
"#;
        for workers in [1, 2, 4] {
            let counters = [
                &CALL_PRE_TEST_EXECUTIONS,
                &CALL_POST_TEST_EXECUTIONS,
                &FOLD_BODY_TEST_EXECUTIONS,
                &UNFOLD_TREE_TEST_EXECUTIONS,
            ];
            let before = counters.map(|counter| counter.load(std::sync::atomic::Ordering::SeqCst));
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert!(fatal.iter().any(|fatal| *fatal));
            for (counter, previous) in counters.into_iter().zip(before) {
                assert!(
                    counter.load(std::sync::atomic::Ordering::SeqCst) > previous,
                    "an owned action never executed"
                );
            }
        }
    }

    #[test]
    fn real_stdio_owned_uncached_unfolding_expression() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
field g: Int
predicate P(x: Ref, b: Bool) { b ? (acc(x.f) && x.f == 7) : (acc(x.g) && x.g == 8) }
method good(x: Ref, b: Bool) returns (r: Int)
  requires acc(P(x, b))
  ensures acc(P(x, b)) && (b ? r == 7 : r == 8)
{
  r := unfolding acc(P(x, b)) in (b ? x.f : x.g);
}
method bad(x: Ref, b: Bool) returns (r: Int)
  requires acc(P(x, b))
  ensures acc(P(x, b)) && r == 9
{
  r := unfolding acc(P(x, b)) in (b ? x.f : x.g);
}
"#;
        for workers in [1, 2] {
            let submitted = UNFOLD_EVALUATION_PRODUCTION_TEST_SUBMISSIONS
                .load(std::sync::atomic::Ordering::SeqCst);
            let executed = UNFOLD_EVALUATION_PRODUCTION_TEST_EXECUTIONS
                .load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_profile(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
                false,
                false,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                UNFOLD_EVALUATION_PRODUCTION_TEST_SUBMISSIONS
                    .load(std::sync::atomic::Ordering::SeqCst)
                    > submitted
            );
            assert!(
                UNFOLD_EVALUATION_PRODUCTION_TEST_EXECUTIONS
                    .load(std::sync::atomic::Ordering::SeqCst)
                    > executed
            );
        }
    }

    #[test]
    fn real_stdio_owned_unfolding_expression_tree() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
field g: Int
predicate P(x: Ref, b: Bool) { b ? (acc(x.f) && x.f == 7) : (acc(x.g) && x.g == 8) }
method good(x: Ref, b: Bool) returns (r: Int)
  requires acc(P(x, b))
  ensures acc(P(x, b)) && (b ? r == 7 : r == 8)
{
  r := unfolding acc(P(x, b)) in (b ? x.f : x.g);
}
method bad(x: Ref, b: Bool) returns (r: Int)
  requires acc(P(x, b))
  ensures acc(P(x, b)) && r == 9
{
  r := unfolding acc(P(x, b)) in (b ? x.f : x.g);
}
"#;
        for workers in [1, 2] {
            let submitted =
                PREDICATE_EVALUATION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed =
                PREDICATE_EVALUATION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                PREDICATE_EVALUATION_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > submitted
            );
            assert!(
                PREDICATE_EVALUATION_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                    > executed
            );
        }
    }

    #[test]
    fn real_stdio_owned_function_precondition() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
function get(b: Bool, x: Ref, y: Ref): Int
  requires b ? acc(x.f) : acc(y.f)
{ b ? x.f : y.f }
method good(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires acc(x.f) && acc(y.f) && x.f == 7 && y.f == 8
  ensures b ? r == 7 : r == 8
{
  r := get(b, x, y);
}
method bad(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires x != y && acc(x.f)
{
  r := get(b, x, y);
}
"#;
        for workers in [1, 2] {
            let submitted = FUNCTION_PRE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed = FUNCTION_PRE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                FUNCTION_PRE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > submitted
            );
            assert!(
                FUNCTION_PRE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > executed
            );
        }
    }

    #[test]
    fn real_stdio_owned_assert_probe_restores_heap_and_tail() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = crate::decider::z3_prover_std_io::new(
                name,
                crate::decider::z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let prefix = "field f: Int method m(x: Ref, y: Ref, b: Bool) requires acc(x.f) && acc(y.f) { assert (b ? acc(x.f) : acc(y.f)); exhale acc(x.f) && acc(y.f);";
        for workers in [1, 2] {
            for (tail, expected) in [("}", false), ("assert false; }", true)] {
                let submitted =
                    ASSERT_PROBE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed =
                    ASSERT_PROBE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_profile(
                    &format!("{prefix} {tail}"),
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                    true,
                    true,
                );
                assert_eq!(
                    fatal.iter().any(|f| *f),
                    expected,
                    "workers={workers}, {fatal:?}"
                );
                assert!(
                    ASSERT_PROBE_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > submitted,
                    "no assert-probe job submitted"
                );
                assert!(
                    ASSERT_PROBE_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst)
                        > executed,
                    "no assert-probe job executed"
                );
            }
        }
    }

    #[test]
    fn real_stdio_cancel_after_owned_right_receiver_starts() {
        cancel_after_owned_receiver_starts(0);
    }

    #[test]
    fn real_stdio_cancel_after_inner_asserting_receiver_starts() {
        cancel_after_owned_receiver_starts(1);
    }

    #[test]
    fn real_stdio_cancel_after_let_body_receiver_starts() {
        cancel_after_owned_receiver_starts(2);
    }

    fn cancel_after_owned_receiver_starts(kind: u8) {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::{
            config::Config,
            decider::{decider::DefaultDecider, z3_prover_std_io},
            state::terms::{TermFactory, TermOptions},
            verifier::{
                base_verifier::BaseVerifier,
                native_context::{NativeError, NativeOptions, NativeVerifierContext},
            },
        };
        use ferrum_silver::frontend::{
            frontend::FrontendPhases,
            sil_front_end_config::SilFrontendConfig,
            sil_frontend::{SilFrontendPhases, standard_plugin_manager},
        };
        let source = if kind == 2 {
            r#"field f: Int
method cancel_let(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int)
 requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
{ r := (let v == (asserting (b ? acc(x.f) : acc(y.f)) in 1) in (asserting (c ? acc(z.f) : acc(w.f)) in v)); }
"#
        } else if kind == 1 {
            r#"field f: Int
method cancel_inner(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int)
 requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
{ label L;
  r := old(asserting (b ? acc(x.f) : acc(y.f)) in -(old[L](asserting (c ? acc(z.f) : acc(w.f)) in 2)));
}
"#
        } else {
            r#"field f: Int
method cancel_right(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int)
 requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
{ label L;
  r := -(old(asserting (b ? acc(x.f) : acc(y.f)) in 1) + old[L](asserting (c ? acc(z.f) : acc(w.f)) in 2));
}
"#
        };
        for workers in [1, 2] {
            let cancellation = CancellationController::default();
            let config = Config::default();
            let mut config = config;
            config.more_joins = crate::config::JoinMode::Off;
            config.number_of_errors_to_report = 2;
            let options = NativeOptions::from_config(&config).unwrap();
            let factory = TermFactory::new(TermOptions {
                use_flyweight: false,
                use_old_axiomatization: false,
                mask_heap_mode: false,
            });
            let worker_factory = factory.clone();
            let worker_options = options.clone();
            let worker_config = config.clone();
            let worker_cancel = cancellation.clone();
            let path = std::path::PathBuf::from(&z3);
            let pool = ThreadVerificationPool::start_with_cancellation(
                workers,
                ThreadVerificationPool::<
                    NativeMethodWorker<crate::decider::prover_std_io::ProverStdIo>,
                >::DEFAULT_STACK_SIZE,
                cancellation.clone(),
                move |id| {
                    let name = format!("right-cancel-{id}");
                    let prover = z3_prover_std_io::new(
                        name.clone(),
                        z3_prover_std_io::settings(path.clone()),
                        worker_factory.clone(),
                        |_| {},
                    );
                    let identifiers = prover.identifier_factory();
                    let mut worker = native_method_worker(
                        name,
                        prover,
                        identifiers,
                        worker_factory.clone(),
                        worker_options.clone(),
                        &worker_config,
                    );
                    worker.context.joined_branch_scheduler_enabled = true;
                    worker.set_cancellation(worker_cancel.clone());
                    if kind == 2 {
                        worker.context.test_cancel_owned_let = Some(worker_cancel.clone());
                    } else if kind == 1 {
                        worker.context.test_cancel_owned_inner = Some(worker_cancel.clone());
                    } else {
                        worker.context.test_cancel_owned_right = Some(worker_cancel.clone());
                    }
                    Ok(worker)
                },
            )
            .unwrap();
            let pool = std::rc::Rc::new(std::cell::RefCell::new(pool));
            let prover = z3_prover_std_io::new(
                "main".into(),
                z3_prover_std_io::settings(std::path::PathBuf::from(&z3)),
                factory.clone(),
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            let decider = DefaultDecider::new(
                BroadcastingProver::new(prover, pool.clone()),
                false,
                None,
                None,
                None,
            );
            let base = BaseVerifier::new_with_identifiers(
                "main".into(),
                decider,
                factory.clone(),
                false,
                crate::config::StateConsolidationMode::Default,
                identifiers,
            );
            let mut context = NativeVerifierContext::new(base, factory, options);
            context.set_cancellation(cancellation.clone());
            context.start(None, &[]).unwrap();
            let cfg = SilFrontendConfig::new("test");
            let mut phases =
                SilFrontendPhases::new("test.vpr".into(), standard_plugin_manager(&cfg).unwrap());
            let parsed = phases.parse(source).unwrap();
            let checked = phases.analyze(parsed).unwrap();
            let program = phases.translate(checked).unwrap();
            let program = phases.check_consistency(program).unwrap();
            let program = phases.prepare_verification(program).unwrap();
            let (submission_counter, hook_counter) = if kind == 2 {
                (&LET_BODY_SUBMISSIONS, &LET_RECEIVER_CANCEL_HOOKS)
            } else if kind == 1 {
                (&ASSERTING_BODY_SUBMISSIONS, &INNER_RECEIVER_CANCEL_HOOKS)
            } else {
                (&RETURN_ADD_RIGHT_SUBMISSIONS, &RETURN_RIGHT_CANCEL_HOOKS)
            };
            let submitted = submission_counter.load(std::sync::atomic::Ordering::SeqCst);
            let hooks = hook_counter.load(std::sync::atomic::Ordering::SeqCst);
            let result = verify_native_parallel_with_reporting(
                &mut context,
                &program,
                &[],
                None,
                None,
                None,
            );
            assert!(
                submission_counter.load(std::sync::atomic::Ordering::SeqCst) > submitted,
                "right branch never transferred: {result:?}"
            );
            assert!(
                hook_counter.load(std::sync::atomic::Ordering::SeqCst) > hooks,
                "right receiver never began: {result:?}"
            );
            assert!(
                matches!(
                    result,
                    Err(NativeParallelError::Worker(ThreadPoolError::Worker(
                        NativeError::Cancelled
                    )))
                ),
                "{result:?}"
            );
            drop(context);
            let pool = std::rc::Rc::try_unwrap(pool).ok().unwrap().into_inner();
            assert!(pool.cancel_and_join().is_empty());
        }
    }

    #[test]
    fn real_stdio_owned_let_value_and_body() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = crate::decider::z3_prover_std_io::new(
                name,
                crate::decider::z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"// owned_return_tail_check
field f: Int
method good(k: Int, b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int)
  requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
  requires x.f == 7 && y.f == 8 && z.f == 4 && w.f == 5
  ensures acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f) && x.f == 11
  ensures r == (b ? 7 : 8) + k + 1 + (c ? 4 : 5)
{
  label L; x.f := 11;
  r := (let v == (old(asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f))) in
        (let u == (v + k + 1) in old[L](asserting (c ? acc(z.f) : acc(w.f)) in (u + (c ? z.f : w.f)))));
  assert x.f == 11;
}
method bad() { assert false; }
"#;
        for workers in [1, 2] {
            let before = [
                LET_VALUE_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                LET_VALUE_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
                LET_BODY_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                LET_BODY_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
            ];
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert_eq!(
                fatal.iter().filter(|v| **v).count(),
                1,
                "workers={workers}: {fatal:?}"
            );
            let after = [
                LET_VALUE_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                LET_VALUE_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
                LET_BODY_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                LET_BODY_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
            ];
            assert!(
                before
                    .iter()
                    .zip(after)
                    .all(|(before, after)| after > *before),
                "let value/body jobs did not run: {before:?} -> {after:?}"
            );
        }
    }

    #[test]
    fn real_stdio_nested_asserting_body_transfers() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = crate::decider::z3_prover_std_io::new(
                name,
                crate::decider::z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"// owned_return_tail_check
field f: Int
method good(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int)
 requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
 requires x.f == 7 && y.f == 8 && z.f == 4 && w.f == 5
 ensures acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f) && x.f == 11
 ensures r == -(c ? 4 : 5)
{ label L; x.f := 11;
  r := old(asserting (b ? acc(x.f) : acc(y.f)) in -(old[L](asserting (c ? acc(z.f) : acc(w.f)) in (c ? z.f : w.f))));
  assert x.f == 11;
}
method bad() { assert false; }
"#;
        for workers in [1, 2] {
            let before = [
                ASSERTING_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                ASSERTING_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
                ASSERTING_BODY_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                ASSERTING_BODY_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
            ];
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert_eq!(
                fatal.iter().filter(|v| **v).count(),
                1,
                "workers={workers}: {fatal:?}"
            );
            let after = [
                ASSERTING_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                ASSERTING_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
                ASSERTING_BODY_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                ASSERTING_BODY_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
            ];
            assert!(
                after[2] > before[2] && after[3] > before[3],
                "inner jobs did not execute: {before:?} -> {after:?}"
            );
            assert!(
                after[0] - before[0] > after[2] - before[2]
                    && after[1] - before[1] > after[3] - before[3],
                "outer jobs did not execute: {before:?} -> {after:?}"
            );
        }
    }

    #[test]
    fn real_stdio_owned_strict_operators() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = crate::decider::z3_prover_std_io::new(
                name,
                crate::decider::z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"// owned_return_tail_check
field f: Int
method good(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int, q: Bool)
  requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
  ensures acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
{
  label L;
  r := old(asserting (b ? acc(x.f) : acc(y.f)) in 7) - old[L](asserting (c ? acc(z.f) : acc(w.f)) in 4);
  assert r == 3;
  r := (asserting (b ? acc(x.f) : acc(y.f)) in 7) * (asserting (c ? acc(z.f) : acc(w.f)) in 4);
  assert r == 28;
  q := !((asserting (b ? acc(x.f) : acc(y.f)) in 7) == (asserting (c ? acc(z.f) : acc(w.f)) in 4));
  assert q;
  q := (asserting (b ? acc(x.f) : acc(y.f)) in 7) <= (asserting (c ? acc(z.f) : acc(w.f)) in 4); assert !q;
  q := (asserting (b ? acc(x.f) : acc(y.f)) in 7) < (asserting (c ? acc(z.f) : acc(w.f)) in 4); assert !q;
  q := (asserting (b ? acc(x.f) : acc(y.f)) in 7) >= (asserting (c ? acc(z.f) : acc(w.f)) in 4); assert q;
  q := (asserting (b ? acc(x.f) : acc(y.f)) in 7) > (asserting (c ? acc(z.f) : acc(w.f)) in 4); assert q;
}
method bad() { assert false; }
"#;
        for workers in [1, 2] {
            let before = [
                RETURN_STRICT_LEFT_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                RETURN_STRICT_RIGHT_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                RETURN_STRICT_LEFT_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
                RETURN_STRICT_RIGHT_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
            ];
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert_eq!(
                fatal.iter().filter(|value| **value).count(),
                1,
                "workers={workers}: {fatal:?}"
            );
            let after = [
                RETURN_STRICT_LEFT_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                RETURN_STRICT_RIGHT_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst),
                RETURN_STRICT_LEFT_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
                RETURN_STRICT_RIGHT_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst),
            ];
            assert!(
                before
                    .iter()
                    .zip(after)
                    .all(|(before, after)| after > *before),
                "strict jobs did not run: {before:?} -> {after:?}"
            );
        }
    }

    #[test]
    fn real_stdio_owned_both_add_operands() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"// owned_return_right_failure_check
field f: Int
method good(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int)
  requires acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f)
  requires x.f == 7 && y.f == 8 && z.f == 4 && w.f == 5
  ensures acc(x.f) && acc(y.f) && acc(z.f) && acc(w.f) && x.f == 11
  ensures r == -((b ? 7 : 8) + (c ? 4 : 5))
{ label L; x.f := 11;
  r := -(old(asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f)) + old[L](asserting (c ? acc(z.f) : acc(w.f)) in (c ? z.f : w.f)));
  assert x.f == 11;
}
method bad(b: Bool, c: Bool, x: Ref, y: Ref, z: Ref, w: Ref) returns (r: Int)
  requires w != x && w != y && w != z && acc(x.f) && acc(y.f) && acc(z.f)
{ label L;
  r := -(old(asserting (b ? acc(x.f) : acc(y.f)) in 1) + old[L](asserting (c ? acc(z.f) : acc(w.f)) in 2));
}
"#;
        for workers in [1, 2] {
            let ls = RETURN_ADD_LEFT_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let rs = RETURN_ADD_RIGHT_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let le = RETURN_ADD_LEFT_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let re = RETURN_ADD_RIGHT_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert!(
                fatal.iter().any(|value| *value),
                "workers={workers}: {fatal:?}"
            );
            assert!(RETURN_ADD_LEFT_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > ls);
            assert!(RETURN_ADD_RIGHT_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > rs);
            assert!(RETURN_ADD_LEFT_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > le);
            assert!(RETURN_ADD_RIGHT_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > re);
        }
    }

    #[test]
    fn real_stdio_nested_owned_return_stack() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let cases = [
            (
                "-(old(asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f)) + x.f)",
                "b ? -18 : -19",
            ),
            (
                "old(x.f) + -(old(asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f)))",
                "b ? 0 : -1",
            ),
            (
                "-(old[L](asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f))) + x.f",
                "b ? 4 : 3",
            ),
            (
                "old(-((asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f)) + x.f))",
                "b ? -14 : -15",
            ),
            (
                "(b ? 2 : 3) + -(old(asserting (b ? acc(x.f) : acc(y.f)) in 1))",
                "b ? 1 : 2",
            ),
        ];
        for workers in [1, 2] {
            for (rhs, expected) in cases {
                let source = format!(
                    r#"field f: Int
method good(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires x != y && acc(x.f) && acc(y.f) && x.f == 7 && y.f == 8
  ensures acc(x.f) && acc(y.f) && x.f == 11 && r == ({expected})
{{ label L; x.f := 11; r := {rhs}; assert x.f == 11; assert r == ({expected}); }}
method bad(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires x != y && acc(x.f)
{{ label L; r := {rhs}; }}
"#
                );
                let submitted = NESTED_RETURN_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
                let executed = NESTED_RETURN_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    &source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert_eq!(
                    fatal.iter().filter(|value| **value).count(),
                    1,
                    "{rhs}, workers={workers}: {fatal:?}"
                );
                assert!(
                    NESTED_RETURN_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > submitted,
                    "no nested return submission: {rhs}"
                );
                assert!(
                    NESTED_RETURN_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > executed,
                    "no nested return execution: {rhs}"
                );
            }
            let tail_source = r#"// owned_return_tail_check
field f: Int
method good(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires x != y && acc(x.f) && acc(y.f) && x.f == 7 && y.f == 8
{ r := -(old(asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f)) + x.f); assert true; }
method bad(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires x != y && acc(x.f) && acc(y.f) && x.f == 7 && y.f == 8
{ r := -(old(asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f)) + x.f); assert false; }
"#;
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                tail_source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert!(
                fatal.iter().any(|value| *value),
                "captured tail not executed: {fatal:?}"
            );
        }
    }

    #[test]
    fn real_stdio_owned_asserting_assignment() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
method good(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires acc(x.f) && acc(y.f) && x.f == 7 && y.f == 8
  ensures acc(x.f) && acc(y.f) && (b ? r == 7 : r == 8)
{
  r := asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f);
}
method bad(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires x != y && acc(x.f)
{
  r := asserting (b ? acc(x.f) : acc(y.f)) in 1;
}
"#;
        for workers in [1, 2] {
            let submitted = ASSERTING_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let executed = ASSERTING_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings_impl(
                source,
                workers,
                make.clone(),
                false,
                true,
                true,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1, "{fatal:?}");
            assert!(
                ASSERTING_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > submitted
            );
            assert!(ASSERTING_TEST_EXECUTIONS.load(std::sync::atomic::Ordering::SeqCst) > executed);
        }
    }

    #[test]
    fn real_stdio_owned_old_asserting_assignment() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = r#"field f: Int
method good(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires acc(x.f) && acc(y.f) && x.f == 7 && y.f == 8
  ensures acc(x.f) && acc(y.f) && (b ? r == 7 : r == 8)
{
  x.f := 11;
  r := old(asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f));
}
method bad(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires x != y && acc(x.f)
{
  r := old(asserting (b ? acc(x.f) : acc(y.f)) in 1);
}
"#;
        let labelled_source = r#"field f: Int
method labelled(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires acc(x.f) && acc(y.f) && x.f == 7 && y.f == 8
  ensures acc(x.f) && acc(y.f) && (b ? r == 11 : r == 8)
{
  x.f := 11;
  label L;
  x.f := 12;
  r := old[L](asserting (b ? acc(x.f) : acc(y.f)) in (b ? x.f : y.f));
  assert x.f == 12;
}
method bad(b: Bool, x: Ref, y: Ref) returns (r: Int)
  requires x != y && acc(x.f)
{
  label L;
  r := old[L](asserting (b ? acc(x.f) : acc(y.f)) in 1);
}
"#;
        let missing_label_source = r#"field f: Int
method bad(b: Bool, c: Bool, x: Ref, y: Ref) returns (r: Int)
  requires acc(x.f) && acc(y.f)
{
  if (b) { label L; }
  r := old[L](asserting (c ? acc(x.f) : acc(y.f)) in 1);
}
"#;
        for (kind, source, failures) in [
            (0, source, 1),
            (1, labelled_source, 1),
            (1, missing_label_source, 1),
        ] {
            for workers in [1, 2] {
                let submitted =
                    OLD_ASSERTING_SUBMISSIONS[kind].load(std::sync::atomic::Ordering::SeqCst);
                let executed =
                    OLD_ASSERTING_EXECUTIONS[kind].load(std::sync::atomic::Ordering::SeqCst);
                let (fatal, _) = run_parallel_source_with_warnings_impl(
                    source,
                    workers,
                    make.clone(),
                    false,
                    true,
                    true,
                );
                assert_eq!(
                    fatal.iter().filter(|fatal| **fatal).count(),
                    failures,
                    "{fatal:?}"
                );
                assert!(
                    OLD_ASSERTING_SUBMISSIONS[kind].load(std::sync::atomic::Ordering::SeqCst)
                        > submitted
                );
                assert!(
                    OLD_ASSERTING_EXECUTIONS[kind].load(std::sync::atomic::Ordering::SeqCst)
                        > executed
                );
            }
        }
    }

    #[test]
    fn real_stdio_cfg_joins_use_owned_worker_jobs() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        for workers in [1, 2] {
            let before = CFG_JOIN_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings(
                "method good() { var b: Bool; if (b) { assert true; } else { assert true; } assert true; } method bad() { var b: Bool; if (b) { assert false; } else { assert true; } assert true; }",
                workers,
                make.clone(),
                true,
                true,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                CFG_JOIN_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > before,
                "CFG join never submitted owned work"
            );
        }
    }

    #[test]
    fn real_stdio_predicate_joins_use_owned_worker_jobs() {
        let Some(z3) = std::env::var_os("FERRUM_TEST_Z3") else {
            return;
        };
        use crate::decider::z3_prover_std_io;
        let path = std::path::PathBuf::from(z3);
        let make = move |name: String, factory: crate::state::terms::TermFactory| {
            let prover = z3_prover_std_io::new(
                name,
                z3_prover_std_io::settings(path.clone()),
                factory,
                |_| {},
            );
            let identifiers = prover.identifier_factory();
            (prover, identifiers)
        };
        let source = "field f: Int field g: Int predicate P(x: Ref, b: Bool) { b ? (acc(x.f) && x.f == 7) : (acc(x.g) && x.g == 8) } method good(x: Ref, b: Bool) requires acc(P(x,b)) { unfold acc(P(x,b), 1/2); assert b ? (acc(x.f, 1/2) && x.f == 7) : (acc(x.g, 1/2) && x.g == 8); } method bad(x: Ref, b: Bool) requires acc(P(x,b)) { unfold acc(P(x,b), 1/2); assert b ? (acc(x.f, 1/2) && x.f == 9) : (acc(x.g, 1/2) && x.g == 8); }";
        for workers in [1, 2] {
            let before = PREDICATE_JOIN_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) =
                run_parallel_source_with_warnings(source, workers, make.clone(), false, true);
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                PREDICATE_JOIN_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > before,
                "predicate join never submitted owned work"
            );
        }
    }

    #[cfg(feature = "native-z3")]
    #[test]
    fn real_linked_predicate_joins_use_owned_worker_jobs() {
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
        let source = "field f: Int field g: Int predicate P(x: Ref, b: Bool) { b ? (acc(x.f) && x.f == 7) : (acc(x.g) && x.g == 8) } method good(x: Ref, b: Bool) requires acc(P(x,b)) { unfold acc(P(x,b), 1/2); assert b ? (acc(x.f, 1/2) && x.f == 7) : (acc(x.g, 1/2) && x.g == 8); } method bad(x: Ref, b: Bool) requires acc(P(x,b)) { unfold acc(P(x,b), 1/2); assert b ? (acc(x.f, 1/2) && x.f == 9) : (acc(x.g, 1/2) && x.g == 8); }";
        for workers in [1, 2] {
            let before = PREDICATE_JOIN_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings(source, workers, make, false, true);
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(
                PREDICATE_JOIN_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > before,
                "predicate join never submitted owned work"
            );
        }
    }

    #[cfg(feature = "native-z3")]
    #[test]
    fn real_linked_cfg_joins_use_owned_worker_jobs() {
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
        for workers in [1, 2] {
            let before = CFG_JOIN_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst);
            let (fatal, _) = run_parallel_source_with_warnings(
                "method good() { var b: Bool; if (b) { assert true; } else { assert true; } assert true; } method bad() { var b: Bool; if (b) { assert false; } else { assert true; } assert true; }",
                workers,
                make,
                true,
                true,
            );
            assert_eq!(fatal.iter().filter(|fatal| **fatal).count(), 1);
            assert!(CFG_JOIN_TEST_SUBMISSIONS.load(std::sync::atomic::Ordering::SeqCst) > before);
        }
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
            false,
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
