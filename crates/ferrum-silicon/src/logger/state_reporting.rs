//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/StateReporting.scala
//!
//! Purpose:
//! Report verifier state when a member log stops making progress.
//!
//! Planned Rust structure:
//! Port StateReporter, TakenBranch variants and StateReportingMemberSymbExLogger scope/branch
//! hooks, currentState and stall detection.
//!
//! Behavior to preserve:
//! Require positive threshold; poll at threshold/10 clamped 50–1000ms on lazily started daemon.
//! Synchronize active logs and per-log frames, track scope closures separately per branch and
//! across branches, report once until next progress, unregister on finish. Prefer source branch
//! expression, then term, else alternative index; truncate multiline step description.
//!
//! Integration:
//! logger::symb_ex_logger/records, Silver reporter VerifierStateMessage and verification
//! lifecycle.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for worker lifecycle, locks, timing and diagnostics.
//!
//! Open decisions:
//! Agree on scheduler shutdown and branch-path snapshot ownership with symb_ex_logger and
//! reporter.
//!
//! Status: partial; branch/scope tracking, owned fixed-delay polling and member hooks exist.
//! Verifier lifecycle integration remains to be connected.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.

use super::records::{
    data::data_record::DataRecord,
    structural::branching_record::BranchingRecord,
    symbolic_record::{RecordError, RecordRef, RecordRenderer},
};
use crate::state::terms::{Term, TermFactory};
use ferrum_silver::{
    ast::{
        expression::{Exp, ExpKind},
        utility::nodes::Node,
    },
    reporter::{
        message::{
            BranchCondition, Message, ReportNode, VerifierState, VerifierStateFrame, VerifierStep,
        },
        package::Entity,
        reporter::{ReportError, Reporter},
    },
};
use std::{
    collections::HashSet,
    sync::{Arc, Mutex},
};

/// Source AST and Silicon renderers for ordinary state-reporting records.
/// Unsupported extension printers and node kinds are reported explicitly.
pub struct NativeStateRecordRenderer<'a> {
    pub factory: &'a TermFactory,
}

#[derive(Debug)]
struct NativeReportNode {
    node: Node,
    position: ferrum_silver::ast::position::Position,
}
impl ReportNode for NativeReportNode {
    fn position(&self) -> ferrum_silver::ast::position::Position {
        self.position.clone()
    }
    fn as_any(&self) -> &dyn std::any::Any {
        use ferrum_silver::ast::program::Member;
        match &self.node {
            Node::Exp(v) => v,
            Node::Stmt(v) => v,
            Node::Member(Member::Domain(v)) => v,
            Node::Member(Member::Field(v)) => v,
            Node::Member(Member::Function(v)) => v,
            Node::Member(Member::Predicate(v)) => v,
            Node::Member(Member::Method(v)) => v,
            Node::Member(Member::Extension(v)) => v.0.as_any(),
            _ => &self.node,
        }
    }
}
fn report_position(node: &Node) -> Result<ferrum_silver::ast::position::Position, RecordError> {
    use ferrum_silver::ast::program::Member;
    let metadata = match node {
        Node::Exp(v) => v.metadata(),
        Node::Stmt(v) => v.metadata(),
        Node::Member(Member::Domain(v)) => &v.meta,
        Node::Member(Member::Field(v)) => &v.meta,
        Node::Member(Member::Function(v)) => &v.meta,
        Node::Member(Member::Predicate(v)) => &v.meta,
        Node::Member(Member::Method(v)) => &v.meta,
        Node::Member(Member::Extension(v)) => {
            v.0.metadata()
                .map_err(|_| RecordError::Unsupported("extension member position"))?
        }
        _ => return Err(RecordError::Unsupported("report node position")),
    };
    Ok(metadata.position.clone())
}
impl RecordRenderer for NativeStateRecordRenderer<'_> {
    fn node(&self, node: &Node) -> Result<String, RecordError> {
        use ferrum_silver::ast::pretty::pretty_printer::{expression_to_string, pretty_node};
        match node {
            Node::Exp(exp) => expression_to_string(exp),
            Node::Stmt(_) | Node::Member(_) => pretty_node(node),
            _ => return Err(RecordError::Unsupported("report node rendering")),
        }
        .map_err(|_| RecordError::Unsupported("report node rendering"))
    }
    fn term(&self, term: &Term) -> Result<String, RecordError> {
        crate::reporting::formatters::render_diagnostic_term(term)
            .map_err(|_| RecordError::Unsupported("term rendering"))
    }
    fn chunk(&self, chunk: &crate::state::chunks::Chunk) -> Result<String, RecordError> {
        crate::reporting::formatters::render_diagnostic_chunk_with_factory(chunk, self.factory)
            .map_err(|_| RecordError::Unsupported("chunk rendering"))
    }
    fn source_line_column(&self, node: &Node) -> Result<String, RecordError> {
        let position = report_position(node)?;
        Ok(position.line_column().map_or_else(
            || position.to_string(),
            |p| format!("{}:{}", p.line(), p.column()),
        ))
    }
}
impl StateRecordRenderer for NativeStateRecordRenderer<'_> {
    fn report_node(&self, node: Node) -> Result<Arc<dyn ReportNode>, RecordError> {
        let position = report_position(&node)?;
        Ok(Arc::new(NativeReportNode { node, position }))
    }
}

/// Native callers provide the complete source node-to-reporter adapter.
pub trait StateRecordRenderer: RecordRenderer {
    fn report_node(&self, node: Node) -> Result<Arc<dyn ReportNode>, RecordError>;
}
pub fn step(
    record: &dyn DataRecord,
    renderer: &dyn StateRecordRenderer,
) -> Result<VerifierStep, RecordError> {
    let text = record.simple_string(renderer)?;
    // Scala linesIterator accepts CR, LF, and CRLF; it does not include the terminator.
    let first = text.split(['\n', '\r']).next().unwrap_or("");
    let description = if first.len() < text.len() {
        format!("{first} ...")
    } else {
        first.into()
    };
    Ok(VerifierStep {
        kind: record.type_string().into(),
        node: record
            .value()
            .map(|n| renderer.report_node(n))
            .transpose()?,
        description,
    })
}
#[derive(Clone)]
pub enum TakenBranch {
    Exp(Exp),
    Term(Term),
    Alternative { index: i32, count: i32 },
}
impl TakenBranch {
    pub fn first(record: &BranchingRecord) -> Result<Self, RecordError> {
        Ok(if let Some(exp) = &record.condition_exp {
            Self::Exp(exp.clone())
        } else if let Some(term) = &record.condition {
            Self::Term(term.clone())
        } else {
            Self::Alternative {
                index: 0,
                count: record.branch_infos()?.len() as i32,
            }
        })
    }
    pub fn next(&self, factory: &TermFactory) -> Self {
        match self {
            Self::Exp(exp) => Self::Exp(match exp.kind() {
                ExpKind::Not(inner) => inner.clone(),
                _ => {
                    let mut meta = exp.metadata().clone();
                    meta.error_trafo = Default::default();
                    Exp::new(ExpKind::Not(exp.clone()), meta)
                }
            }),
            Self::Term(term) => Self::Term(factory.not(term.clone())),
            Self::Alternative { index, count } => Self::Alternative {
                index: index.wrapping_add(1),
                count: *count,
            },
        }
    }
    pub fn condition(
        &self,
        renderer: &dyn StateRecordRenderer,
    ) -> Result<BranchCondition, RecordError> {
        Ok(match self {
            Self::Exp(exp) => BranchCondition::Condition(exp.clone()),
            Self::Term(term) => BranchCondition::OpaqueCondition(renderer.term(term)?),
            Self::Alternative { index, count } => BranchCondition::Alternative {
                index: *index,
                count: *count,
            },
        })
    }
}
#[derive(Default)]
struct ScopeFrame {
    open: Vec<RecordRef>,
    closed_current: HashSet<i32>,
    closed_any: HashSet<i32>,
}
/// Outermost frames are stored first; all mutation is serialized by the member lock.
struct ProgressState {
    frames: Vec<ScopeFrame>,
    branches: Vec<TakenBranch>,
    last_progress_ms: i64,
    reported: bool,
    finished: bool,
}
pub struct StateReportingMember {
    pub member: Entity,
    state: Mutex<ProgressState>,
}
impl StateReportingMember {
    pub fn new(member: Entity, now_ms: i64) -> Self {
        Self {
            member,
            state: Mutex::new(ProgressState {
                frames: vec![ScopeFrame::default()],
                branches: vec![],
                last_progress_ms: now_ms,
                reported: false,
                finished: false,
            }),
        }
    }
    fn update(
        &self,
        now_ms: i64,
        action: impl FnOnce(&mut ProgressState) -> Result<(), RecordError>,
    ) -> Result<(), RecordError> {
        let mut s = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        action(&mut s)?;
        s.last_progress_ms = now_ms;
        s.reported = false;
        Ok(())
    }
    /// Invoke after the member logger has appended a data record.
    pub fn append_data(&self, record: RecordRef, now_ms: i64) -> Result<(), RecordError> {
        if record.as_data_record().is_none() {
            return Err(RecordError::Unsupported("expected data record"));
        }
        self.update(now_ms, |s| {
            let frame = s.frames.last_mut().ok_or(RecordError::InvalidBranch)?;
            if let Some(old) = frame.open.iter_mut().find(|old| old.id() == record.id()) {
                *old = record;
            } else {
                frame.open.push(record);
            }
            Ok(())
        })
    }
    pub fn close_scope(
        &self,
        reference: i32,
        main_id: Option<i32>,
        now_ms: i64,
    ) -> Result<(), RecordError> {
        self.update(now_ms, |s| {
            let frame = s.frames.last_mut().ok_or(RecordError::InvalidBranch)?;
            if frame.open.iter().any(|r| r.id() == reference) {
                frame.open.retain(|r| r.id() != reference);
            } else {
                frame.closed_current.insert(reference);
                frame.closed_any.insert(reference);
            }
            if main_id == Some(reference) {
                s.finished = true;
            }
            Ok(())
        })
    }
    pub fn append_branch(&self, record: &BranchingRecord, now_ms: i64) -> Result<(), RecordError> {
        let branch = TakenBranch::first(record)?;
        self.update(now_ms, |s| {
            s.frames.push(ScopeFrame::default());
            s.branches.push(branch);
            Ok(())
        })
    }
    pub fn next_branch(&self, factory: &TermFactory, now_ms: i64) -> Result<(), RecordError> {
        self.update(now_ms, |s| {
            let branch = s.branches.last_mut().ok_or(RecordError::InvalidBranch)?;
            *branch = branch.next(factory);
            let frame = s.frames.last_mut().ok_or(RecordError::InvalidBranch)?;
            frame.open.clear();
            frame.closed_current.clear();
            Ok(())
        })
    }
    pub fn mark_reachable(&self, now_ms: i64) -> Result<(), RecordError> {
        self.update(now_ms, |_| Ok(()))
    }
    pub fn end_branch(&self, now_ms: i64) -> Result<(), RecordError> {
        self.update(now_ms, |s| {
            if s.branches.is_empty() {
                return Err(RecordError::InvalidBranch);
            }
            let completed = s.frames.pop().ok_or(RecordError::InvalidBranch)?;
            for frame in &mut s.frames {
                frame
                    .open
                    .retain(|r| !completed.closed_any.contains(&r.id()));
            }
            s.branches.pop();
            Ok(())
        })
    }
    pub fn finish(&self) -> Result<(), RecordError> {
        self.state
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .finished = true;
        Ok(())
    }
    pub fn stalled_message(
        &self,
        now_ms: i64,
        after_ms: i64,
        renderer: &dyn StateRecordRenderer,
    ) -> Result<Option<Message>, RecordError> {
        let mut s = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        let elapsed = now_ms.wrapping_sub(s.last_progress_ms);
        if s.finished || s.reported || elapsed < after_ms {
            return Ok(None);
        }
        // Source marks reported before rendering, even if rendering fails.
        s.reported = true;
        let hidden: HashSet<_> = s
            .frames
            .iter()
            .flat_map(|f| f.closed_current.iter().copied())
            .collect();
        let mut frames = Vec::new();
        for (index, frame) in s.frames.iter().enumerate() {
            let mut records: Vec<_> = frame
                .open
                .iter()
                .filter(|r| !hidden.contains(&r.id()))
                .collect();
            records.sort_by_key(|r| r.id());
            let steps = records
                .into_iter()
                .map(|r| step(r.as_data_record().expect("data record retained"), renderer))
                .collect::<Result<_, _>>()?;
            frames.push(VerifierStateFrame {
                branch_condition: if index == 0 {
                    None
                } else {
                    Some(s.branches[index - 1].condition(renderer)?)
                },
                steps,
            });
        }
        Ok(Some(Message::VerifierState {
            verifier: "Silicon".into(),
            concerning: self.member.clone(),
            millis_since_progress: elapsed,
            state: VerifierState { frames },
        }))
    }
}
#[derive(Debug)]
pub enum StateReportError {
    Record(RecordError),
    Report(ReportError),
    Panicked(String),
}
#[derive(Default)]
struct ActiveMembers {
    closed: bool,
    logs: Vec<Arc<StateReportingMember>>,
}
/// Registry and ordered polling. A native scheduler must call `poll` with the
/// source fixed-delay interval; hook integration into member logs remains explicit.
pub struct StateReporter {
    pub report_after_ms: i64,
    pub poll_interval_ms: i64,
    active: Mutex<ActiveMembers>,
}
impl StateReporter {
    pub fn new(report_after_ms: i64) -> Result<Self, RecordError> {
        if report_after_ms <= 0 {
            return Err(RecordError::Unsupported(
                "reportAfterMillis must be positive",
            ));
        }
        Ok(Self {
            report_after_ms,
            poll_interval_ms: (report_after_ms / 10).clamp(50, 1000),
            active: Mutex::new(ActiveMembers::default()),
        })
    }
    pub fn register(&self, log: Arc<StateReportingMember>) -> Result<(), RecordError> {
        let mut s = self.active.lock().map_err(|_| RecordError::Poisoned)?;
        if !s.closed && !s.logs.iter().any(|old| Arc::ptr_eq(old, &log)) {
            s.logs.push(log);
        }
        Ok(())
    }
    pub fn unregister(&self, log: &Arc<StateReportingMember>) -> Result<(), RecordError> {
        self.active
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .logs
            .retain(|old| !Arc::ptr_eq(old, log));
        Ok(())
    }
    pub fn close(&self) -> Result<(), RecordError> {
        let mut s = self.active.lock().map_err(|_| RecordError::Poisoned)?;
        s.closed = true;
        s.logs.clear();
        Ok(())
    }
    /// Preserve per-member failure isolation. The caller sends these failures to
    /// the warning sink; report callbacks execute after releasing member locks.
    pub fn poll(
        &self,
        now_ms: i64,
        renderer: &dyn StateRecordRenderer,
        reporter: &dyn Reporter,
    ) -> Result<Vec<StateReportError>, RecordError> {
        let logs = self
            .active
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .logs
            .clone();
        let mut errors = Vec::new();
        for log in logs {
            let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                match log.stalled_message(now_ms, self.report_after_ms, renderer) {
                    Ok(Some(message)) => reporter.report(message).map_err(StateReportError::Report),
                    Ok(None) => Ok(()),
                    Err(error) => Err(StateReportError::Record(error)),
                }
            }));
            match outcome {
                Ok(Ok(())) => {}
                Ok(Err(error)) => errors.push(error),
                Err(panic) => {
                    let detail = panic
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| panic.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                        .unwrap_or_else(|| "non-string panic".into());
                    errors.push(StateReportError::Panicked(detail));
                }
            }
        }
        Ok(errors)
    }
}

/// Owned fixed-delay polling worker. The first poll occurs one interval after
/// registration, and each subsequent delay starts after the preceding poll.
/// Stopping joins outside registry locks; a blocking reporter can therefore delay
/// shutdown because Rust cannot interrupt an arbitrary callback. A callback which
/// stops its own worker signals it and leaves that one handle detached instead of
/// attempting to join itself; the worker retains its owned dependencies until exit.
pub struct ScheduledStateReporter {
    registry: Arc<StateReporter>,
    reporter: Arc<dyn Reporter>,
    factory: TermFactory,
    on_error: Arc<dyn Fn(StateReportError) + Send + Sync>,
    worker: Mutex<Option<StateReporterWorker>>,
}
struct StateReporterWorker {
    stop: std::sync::mpsc::Sender<()>,
    thread: std::thread::JoinHandle<()>,
}
#[derive(Debug)]
pub enum StateSchedulerError {
    Record(RecordError),
    Spawn(std::io::Error),
    WorkerPanicked,
}
impl ScheduledStateReporter {
    pub fn new(
        report_after_ms: i64,
        reporter: Arc<dyn Reporter>,
        factory: TermFactory,
        on_error: impl Fn(StateReportError) + Send + Sync + 'static,
    ) -> Result<Self, RecordError> {
        Ok(Self {
            registry: Arc::new(StateReporter::new(report_after_ms)?),
            reporter,
            factory,
            on_error: Arc::new(on_error),
            worker: Mutex::new(None),
        })
    }
    pub fn factory(&self) -> &TermFactory {
        &self.factory
    }
    pub fn register(&self, log: Arc<StateReportingMember>) -> Result<(), StateSchedulerError> {
        let mut worker = self
            .worker
            .lock()
            .map_err(|_| StateSchedulerError::Record(RecordError::Poisoned))?;
        let mut active = self
            .registry
            .active
            .lock()
            .map_err(|_| StateSchedulerError::Record(RecordError::Poisoned))?;
        if active.closed {
            return Ok(());
        }
        let added = !active.logs.iter().any(|old| Arc::ptr_eq(old, &log));
        if added {
            active.logs.push(log.clone());
        }
        if worker.is_none() {
            let (stop, receiver) = std::sync::mpsc::channel();
            let registry = self.registry.clone();
            let reporter = self.reporter.clone();
            let factory = self.factory.clone();
            let on_error = self.on_error.clone();
            let interval = std::time::Duration::from_millis(registry.poll_interval_ms as u64);
            let spawned = std::thread::Builder::new()
                .name("silicon-state-reporter".into())
                // The source launcher supplies -Xss128m and this thread traverses
                // the same recursive state/AST structures as verification workers.
                .stack_size(128 * 1024 * 1024)
                .spawn(move || {
                    loop {
                        match receiver.recv_timeout(interval) {
                            Ok(()) | Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => break,
                            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {}
                        }
                        let now = match std::time::SystemTime::now()
                            .duration_since(std::time::UNIX_EPOCH)
                        {
                            Ok(d) => d.as_millis() as i64,
                            Err(e) => -(e.duration().as_millis() as i64),
                        };
                        let renderer = NativeStateRecordRenderer { factory: &factory };
                        match registry.poll(now, &renderer, reporter.as_ref()) {
                            Ok(errors) => {
                                for error in errors {
                                    on_error(error);
                                }
                            }
                            Err(error) => on_error(StateReportError::Record(error)),
                        }
                    }
                });
            match spawned {
                Ok(thread) => *worker = Some(StateReporterWorker { stop, thread }),
                Err(error) => {
                    if added {
                        active.logs.retain(|old| !Arc::ptr_eq(old, &log));
                    }
                    return Err(StateSchedulerError::Spawn(error));
                }
            }
        }
        Ok(())
    }
    pub fn unregister(&self, log: &Arc<StateReportingMember>) -> Result<(), StateSchedulerError> {
        let stopped = {
            let mut worker = self
                .worker
                .lock()
                .map_err(|_| StateSchedulerError::Record(RecordError::Poisoned))?;
            let mut active = self
                .registry
                .active
                .lock()
                .map_err(|_| StateSchedulerError::Record(RecordError::Poisoned))?;
            active.logs.retain(|old| !Arc::ptr_eq(old, log));
            if active.logs.is_empty() {
                worker.take()
            } else {
                None
            }
        };
        Self::stop(stopped)
    }
    pub fn close(&self) -> Result<(), StateSchedulerError> {
        let stopped = {
            let mut worker = self
                .worker
                .lock()
                .map_err(|_| StateSchedulerError::Record(RecordError::Poisoned))?;
            let mut active = self
                .registry
                .active
                .lock()
                .map_err(|_| StateSchedulerError::Record(RecordError::Poisoned))?;
            active.closed = true;
            active.logs.clear();
            worker.take()
        };
        Self::stop(stopped)
    }
    fn stop(worker: Option<StateReporterWorker>) -> Result<(), StateSchedulerError> {
        if let Some(worker) = worker {
            let _ = worker.stop.send(());
            if worker.thread.thread().id() != std::thread::current().id() {
                worker
                    .thread
                    .join()
                    .map_err(|_| StateSchedulerError::WorkerPanicked)?;
            }
        }
        Ok(())
    }
}
impl Drop for ScheduledStateReporter {
    fn drop(&mut self) {
        let _ = self.close();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logger::records::{
        data::comment_record::CommentRecord, symbolic_record::SymbolicRecord,
    };
    use crate::state::{chunks::Chunk, terms::TermOptions};
    use ferrum_silver::ast::{
        program::{Field, FieldData, Member},
        r#type::Type,
    };
    struct Text;
    #[test]
    fn scheduled_poller_starts_lazily_restarts_and_closes() {
        struct ChannelReporter(std::sync::mpsc::Sender<Message>);
        impl Reporter for ChannelReporter {
            fn name(&self) -> &str {
                "channel"
            }
            fn report(&self, message: Message) -> Result<(), ReportError> {
                let _ = self.0.send(message);
                Ok(())
            }
        }
        let (tx, rx) = std::sync::mpsc::channel();
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let scheduler =
            ScheduledStateReporter::new(1, Arc::new(ChannelReporter(tx)), factory, |error| {
                panic!("unexpected scheduler error: {error:?}")
            })
            .unwrap();
        let make_log = || {
            Arc::new(StateReportingMember::new(
                Arc::new(Member::Field(Field::new(FieldData {
                    name: "f".into(),
                    typ: Type::Int,
                    meta: Default::default(),
                }))),
                0,
            ))
        };
        let first = make_log();
        assert!(rx.try_recv().is_err());
        let started = std::time::Instant::now();
        scheduler.register(first.clone()).unwrap();
        assert!(matches!(
            rx.recv_timeout(std::time::Duration::from_secs(2)).unwrap(),
            Message::VerifierState { .. }
        ));
        assert!(started.elapsed() >= std::time::Duration::from_millis(50));
        scheduler.unregister(&first).unwrap();
        let second = make_log();
        scheduler.register(second.clone()).unwrap();
        assert!(matches!(
            rx.recv_timeout(std::time::Duration::from_secs(2)).unwrap(),
            Message::VerifierState { .. }
        ));
        scheduler.close().unwrap();
        scheduler.register(make_log()).unwrap();
        assert!(
            rx.recv_timeout(std::time::Duration::from_millis(100))
                .is_err()
        );
    }
    #[test]
    fn polling_continues_after_one_reporter_failure() {
        struct FailsOnce(std::sync::atomic::AtomicUsize);
        impl Reporter for FailsOnce {
            fn name(&self) -> &str {
                "fails once"
            }
            fn report(&self, _: Message) -> Result<(), ReportError> {
                if self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst) == 0 {
                    Err(ReportError::Unsupported("first"))
                } else {
                    Ok(())
                }
            }
        }
        let registry = StateReporter::new(1).unwrap();
        for name in ["a", "b"] {
            let member = Arc::new(Member::Field(Field::new(FieldData {
                name: name.into(),
                typ: Type::Int,
                meta: Default::default(),
            })));
            registry
                .register(Arc::new(StateReportingMember::new(member, 0)))
                .unwrap();
        }
        let reporter = FailsOnce(std::sync::atomic::AtomicUsize::new(0));
        let errors = registry.poll(1, &Text, &reporter).unwrap();
        assert_eq!(errors.len(), 1);
        assert_eq!(reporter.0.load(std::sync::atomic::Ordering::SeqCst), 2);
    }
    #[test]
    fn scheduled_reporter_can_close_from_callback() {
        struct ClosingReporter {
            scheduler: Mutex<Option<std::sync::Weak<ScheduledStateReporter>>>,
            done: std::sync::mpsc::Sender<()>,
        }
        impl Reporter for ClosingReporter {
            fn name(&self) -> &str {
                "closing"
            }
            fn report(&self, _: Message) -> Result<(), ReportError> {
                self.scheduler
                    .lock()
                    .unwrap()
                    .as_ref()
                    .unwrap()
                    .upgrade()
                    .unwrap()
                    .close()
                    .unwrap();
                self.done.send(()).unwrap();
                Ok(())
            }
        }
        let (done, completed) = std::sync::mpsc::channel();
        let reporter = Arc::new(ClosingReporter {
            scheduler: Mutex::new(None),
            done,
        });
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let scheduler =
            Arc::new(ScheduledStateReporter::new(1, reporter.clone(), factory, |_| {}).unwrap());
        *reporter.scheduler.lock().unwrap() = Some(Arc::downgrade(&scheduler));
        let member = Arc::new(Member::Field(Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: Default::default(),
        })));
        scheduler
            .register(Arc::new(StateReportingMember::new(member, 0)))
            .unwrap();
        completed
            .recv_timeout(std::time::Duration::from_secs(2))
            .unwrap();
        scheduler.close().unwrap();
    }
    #[test]
    fn native_renderer_preserves_position_node_and_source_text() {
        use crate::state::terms::TermOptions;
        use ferrum_silver::ast::{
            ast::Metadata,
            position::{LineColumnPosition, Position},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let renderer = NativeStateRecordRenderer { factory: &factory };
        let mut meta = Metadata::default();
        meta.position = Position::LineColumn(LineColumnPosition::new(12, 7).into());
        let exp = Exp::new(ExpKind::TrueLit, meta);
        let node = Node::Exp(exp.clone());
        assert_eq!(renderer.node(&node).unwrap(), "true");
        assert_eq!(renderer.source_line_column(&node).unwrap(), "12:7");
        assert_eq!(renderer.term(&factory.boolean(true)).unwrap(), "True");
        let reported = renderer.report_node(node).unwrap();
        assert_eq!(reported.position(), exp.metadata().position);
        assert!(
            reported
                .as_any()
                .downcast_ref::<Exp>()
                .unwrap()
                .same_node(&exp)
        );
    }
    impl RecordRenderer for Text {
        fn node(&self, _: &Node) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("node"))
        }
        fn term(&self, _: &Term) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("term"))
        }
        fn chunk(&self, _: &Chunk) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("chunk"))
        }
        fn source_line_column(&self, _: &Node) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("position"))
        }
    }
    impl StateRecordRenderer for Text {
        fn report_node(&self, _: Node) -> Result<Arc<dyn ReportNode>, RecordError> {
            Err(RecordError::Unsupported("node"))
        }
    }
    #[test]
    fn branch_closures_hide_only_current_path_until_join_and_stalls_report_once() {
        let member = Arc::new(Member::Field(Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: Default::default(),
        })));
        let log = StateReportingMember::new(member, 0);
        let comment = Arc::new(CommentRecord::<()>::new(
            Some("outer\r\nrest".into()),
            None,
            None,
        ));
        comment.set_id(7);
        log.append_data(comment, 1).unwrap();
        log.append_branch(&BranchingRecord::new(2, None, None), 2)
            .unwrap();
        log.close_scope(7, None, 3).unwrap();
        assert!(log.stalled_message(12, 10, &Text).unwrap().is_none());
        let Some(Message::VerifierState { state, .. }) =
            log.stalled_message(13, 10, &Text).unwrap()
        else {
            panic!("missing stall");
        };
        assert!(state.frames[0].steps.is_empty());
        assert!(log.stalled_message(20, 10, &Text).unwrap().is_none());
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        log.next_branch(&factory, 21).unwrap();
        let Some(Message::VerifierState { state, .. }) =
            log.stalled_message(31, 10, &Text).unwrap()
        else {
            panic!("missing stall");
        };
        assert_eq!(state.frames[0].steps[0].description, "outer ...");
        assert!(matches!(
            state.frames[1].branch_condition,
            Some(BranchCondition::Alternative { index: 1, count: 2 })
        ));
        log.end_branch(32).unwrap();
        let Some(Message::VerifierState { state, .. }) =
            log.stalled_message(42, 10, &Text).unwrap()
        else {
            panic!("missing stall");
        };
        assert_eq!(state.frames.len(), 1);
        assert!(state.frames[0].steps.is_empty());
        log.finish().unwrap();
        assert!(log.stalled_message(60, 10, &Text).unwrap().is_none());
    }
}
