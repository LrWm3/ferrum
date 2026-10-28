//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/SymbExLogger.scala
//!
//! Purpose:
//! Manage symbolic execution member logs, scopes and branch events.
//!
//! Planned Rust structure:
//! Port SymbExLogger/ofConfig, SymbExLog/Noop/StateReporting variants, MemberSymbExLogger,
//! MemberSymbExLog and discarding/noop implementations; scope, branch, query, statistics and macro
//! helpers.
//!
//! Behavior to preserve:
//! Select full log for ideModeAdvanced, lightweight stalled-state log for reportStateAfter,
//! otherwise noop; invalid JSON config warns and falls back. Allocate unique IDs, append data then
//! open event, timestamp scope events, route nested branches to current branch and assert matching
//! branch IDs. Filter data and corresponding scope events by blacklist/whitelist; close member at
//! root, track failed SMT query, numeric statistic deltas and macros. Preserve close/race and
//! no-op behavior.
//!
//! Integration:
//! logger::{log_config,state_reporting,records,renderer}, verifier and rules/decider event
//! producers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for worker ownership, ordered events, lifecycle and thread
//! synchronization.
//!
//! Open decisions:
//! Reconcile concurrent branch logging, shutdown semantics and record state snapshots with
//! verifier and state_reporting.
//!
//! Status: member scope/branch recording, filters, query tracking and macro/statistic collection implemented.
//! Recording-run ownership and configuration loading are connected. State reporting,
//! verifier event integration and exact double formatting remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::{
    log_config::LogConfig,
    records::{
        data::{data_record::DataRecord, member_record::MemberRecord},
        scoping::{
            close_scope_record::CloseScopeRecord, open_scope_record::OpenScopeRecord,
            scoping_record::ScopingRecord,
        },
        structural::branching_record::BranchingRecord,
        symbolic_record::{RecordError, RecordRef, RecordRenderer, SymbolicRecord},
    },
};
use crate::{package::Map, state::terms::Term};
use std::{
    collections::HashSet,
    sync::{
        Arc, Mutex,
        atomic::{AtomicI32, Ordering},
    },
    time::{SystemTime, UNIX_EPOCH},
};
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogMode {
    Recording,
    Discarding,
    Disabled,
}
fn time_ms() -> i64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(d) => d.as_millis() as i64,
        Err(e) => -(e.duration().as_millis() as i64),
    }
}
struct MemberLogState {
    closed: bool,
    records: Vec<RecordRef>,
    branches: Vec<Arc<BranchingRecord>>,
    ignored: HashSet<i32>,
    last_statistics: Map<String, String>,
    macros: Map<Term, Term>,
    main: Option<Arc<dyn MemberRecord>>,
}
/// Each member shares the run's UID counter. A mutex serializes complete append
/// operations; branch records retain their identity when returned to readers.
pub struct MemberSymbExLog {
    mode: LogMode,
    config: LogConfig,
    ids: Arc<AtomicI32>,
    state: Mutex<MemberLogState>,
}

/// The source recording root: one shared ID sequence and insertion-ordered
/// member logs for a verification run. State-reporting composition is separate.
pub struct SymbExLog {
    pub log_config: LogConfig,
    ids: Arc<AtomicI32>,
    // Member equality is structural, but the heterogeneous AST has no Hash contract.
    members: Mutex<Vec<(ferrum_silver::ast::program::Member, Arc<MemberSymbExLog>)>>,
}
impl SymbExLog {
    pub fn new(log_config: LogConfig) -> Self {
        Self {
            log_config,
            ids: Arc::new(AtomicI32::new(0)),
            members: Mutex::new(Vec::new()),
        }
    }
    pub fn from_config_file(path: Option<&std::path::Path>, warn: impl FnMut(String)) -> Self {
        Self::new(LogConfig::load_or_default(path, warn))
    }
    pub fn fresh_uid(&self) -> i32 {
        self.ids.fetch_add(1, Ordering::Relaxed)
    }
    pub fn open_member_scope(
        &self,
        member: ferrum_silver::ast::program::Member,
        paths: &crate::decider::path_conditions::LayeredPathConditionStack,
        renderer: &dyn RecordRenderer,
    ) -> Result<Arc<MemberSymbExLog>, RecordError> {
        use super::records::data::{
            function_record::FunctionRecord, method_record::MethodRecord,
            predicate_record::PredicateRecord,
        };
        use ferrum_silver::ast::program::Member;
        let record: Arc<dyn MemberRecord> = match &member {
            Member::Method(value) => Arc::new(MethodRecord::new(Some(value.clone()), Some(paths))),
            Member::Predicate(value) => {
                Arc::new(PredicateRecord::new(Some(value.clone()), Some(paths)))
            }
            Member::Function(value) => {
                Arc::new(FunctionRecord::new(Some(value.clone()), Some(paths)))
            }
            _ => return Err(RecordError::Unsupported("symbolic log member kind")),
        };
        let log = Arc::new(MemberSymbExLog::new(
            LogMode::Recording,
            self.log_config.clone(),
            self.ids.clone(),
        ));
        {
            let mut members = self.members.lock().map_err(|_| RecordError::Poisoned)?;
            if let Some((_, retained)) = members.iter_mut().find(|(old, _)| old == &member) {
                *retained = log.clone();
            } else {
                members.push((member, log.clone()));
            }
        }
        log.open_member_scope(record, renderer)?;
        Ok(log)
    }
    pub fn logs(&self) -> Result<Vec<Arc<MemberSymbExLog>>, RecordError> {
        Ok(self
            .members
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .iter()
            .map(|(_, log)| log.clone())
            .collect())
    }
    /// The pinned source closes retained members without setting its root
    /// `closed` flag. Preserve that behavior: a later member can still be opened.
    pub fn close(&self) -> Result<(), RecordError> {
        for (_, log) in self
            .members
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .iter()
        {
            log.close()?;
        }
        Ok(())
    }
    pub fn to_simple_tree_string(
        &self,
        text: &dyn RecordRenderer,
        factory: &crate::state::terms::TermFactory,
    ) -> Result<String, RecordError> {
        use super::renderer::{renderer::Renderer, simple_tree_renderer::SimpleTreeRenderer};
        let records = self
            .logs()?
            .iter()
            .map(|log| log.records())
            .collect::<Result<Vec<_>, _>>()?;
        SimpleTreeRenderer { text, factory }
            .render(&records.iter().map(Vec::as_slice).collect::<Vec<_>>())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::logger::records::data::comment_record::CommentRecord;
    use crate::logger::renderer::{renderer::Renderer, simple_tree_renderer::SimpleTreeRenderer};
    use crate::state::{
        chunks::Chunk,
        terms::{TermFactory, TermOptions},
    };
    use ferrum_silver::ast::utility::nodes::Node;
    struct Text;
    impl RecordRenderer for Text {
        fn node(&self, _: &Node) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("unexpected node"))
        }
        fn term(&self, _: &Term) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("unexpected term"))
        }
        fn chunk(&self, _: &Chunk) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("unexpected chunk"))
        }
        fn source_line_column(&self, _: &Node) -> Result<String, RecordError> {
            Err(RecordError::Unsupported("unexpected position"))
        }
    }
    #[test]
    fn root_shares_ids_replaces_equal_members_and_closes_retained_logs() {
        use crate::decider::path_conditions::LayeredPathConditionStack;
        use ferrum_silver::ast::program::{Member, Predicate, PredicateData};
        let member = |name: &str| {
            Member::Predicate(Predicate::new(PredicateData {
                name: name.into(),
                formal_args: vec![],
                body: None,
                meta: Default::default(),
            }))
        };
        let root = SymbExLog::new(LogConfig::default());
        let paths = LayeredPathConditionStack::new(false);
        let first = root.open_member_scope(member("p"), &paths, &Text).unwrap();
        assert_eq!(first.records().unwrap()[0].id(), 0);
        assert_eq!(root.fresh_uid(), 2);
        let second = root.open_member_scope(member("q"), &paths, &Text).unwrap();
        assert_eq!(second.records().unwrap()[0].id(), 3);
        let replacement = root.open_member_scope(member("p"), &paths, &Text).unwrap();
        let retained = root.logs().unwrap();
        assert_eq!(retained.len(), 2);
        assert!(Arc::ptr_eq(&retained[0], &replacement));
        assert!(Arc::ptr_eq(&retained[1], &second));
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        assert_eq!(
            root.to_simple_tree_string(&Text, &factory).unwrap(),
            "predicate p\n\npredicate q\n\n"
        );
        root.close().unwrap();
        assert!(replacement.is_closed().unwrap());
        assert!(second.is_closed().unwrap());
        // Source replacement removes the previous member from root ownership.
        assert!(!first.is_closed().unwrap());
        assert!(
            !root
                .open_member_scope(member("r"), &paths, &Text)
                .unwrap()
                .is_closed()
                .unwrap()
        );
    }
    #[test]
    fn nested_branch_scopes_retain_source_tree_indentation() {
        let logger = MemberSymbExLog::new(
            LogMode::Recording,
            LogConfig::default(),
            Arc::new(AtomicI32::new(0)),
        );
        let outer = logger
            .open_scope(
                Arc::new(CommentRecord::<()>::new(Some("outer".into()), None, None)),
                &Text,
            )
            .unwrap();
        let branch = logger.insert_branch_point(2, None, None).unwrap();
        logger.mark_reachable(branch).unwrap();
        let inner = logger
            .open_scope(
                Arc::new(CommentRecord::<()>::new(Some("inner".into()), None, None)),
                &Text,
            )
            .unwrap();
        logger.close_scope(inner).unwrap();
        logger.switch_to_next_branch(branch).unwrap();
        logger.end_branch_point(branch).unwrap();
        logger.close_scope(outer).unwrap();
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let renderer = SimpleTreeRenderer {
            text: &Text,
            factory: &factory,
        };
        assert_eq!(
            renderer.render_member(&logger.records().unwrap()).unwrap(),
            "comment outer\n  Branch 1:\n    comment: Reachable\n    comment inner\n  Branch 2:\n    comment: Unreachable\n"
        );
    }
}
impl MemberSymbExLog {
    pub fn new(mode: LogMode, config: LogConfig, ids: Arc<AtomicI32>) -> Self {
        Self {
            mode,
            config,
            ids,
            state: Mutex::new(MemberLogState {
                closed: false,
                records: vec![],
                branches: vec![],
                ignored: HashSet::new(),
                last_statistics: Map::new(),
                macros: Map::new(),
                main: None,
            }),
        }
    }
    fn fresh_uid(&self) -> i32 {
        self.ids.fetch_add(1, Ordering::Relaxed)
    }
    pub fn when_enabled<T>(&self, action: impl FnOnce() -> T) -> Option<T> {
        (self.mode != LogMode::Disabled).then(action)
    }
    pub fn is_closed(&self) -> Result<bool, RecordError> {
        Ok(self.state.lock().map_err(|_| RecordError::Poisoned)?.closed)
    }
    pub fn close(&self) -> Result<(), RecordError> {
        self.state.lock().map_err(|_| RecordError::Poisoned)?.closed = true;
        Ok(())
    }
    pub fn records(&self) -> Result<Vec<RecordRef>, RecordError> {
        Ok(self
            .state
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .records
            .clone())
    }
    fn append(
        state: &mut MemberLogState,
        record: RecordRef,
        root: bool,
    ) -> Result<(), RecordError> {
        if !root && let Some(branch) = state.branches.last() {
            return branch.append_log(record);
        }
        state.records.push(record);
        Ok(())
    }
    fn insert_scope<R: ScopingRecord>(
        &self,
        record: Arc<R>,
        root: bool,
    ) -> Result<i32, RecordError> {
        record.set_id(self.fresh_uid());
        record.set_time_ms(time_ms());
        let mut state = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        if !state.closed
            && self.mode == LogMode::Recording
            && !state.ignored.contains(&record.ref_id())
        {
            Self::append(&mut state, record.clone(), root)?;
        }
        Ok(record.id())
    }
    pub fn open_member_scope(
        &self,
        member: Arc<dyn MemberRecord>,
        renderer: &dyn RecordRenderer,
    ) -> Result<i32, RecordError> {
        if self.mode == LogMode::Disabled {
            return Ok(0);
        }
        self.state.lock().map_err(|_| RecordError::Poisoned)?.main = Some(member.clone());
        self.open_scope(member, renderer)
    }
    pub fn open_scope(
        &self,
        record: Arc<dyn DataRecord>,
        renderer: &dyn RecordRenderer,
    ) -> Result<i32, RecordError> {
        if self.mode == LogMode::Disabled {
            return Ok(0);
        }
        record.set_id(self.fresh_uid());
        {
            let mut state = self.state.lock().map_err(|_| RecordError::Poisoned)?;
            if !state.closed && self.mode == LogMode::Recording {
                let matched = self
                    .config
                    .get_record_config(record.as_ref(), renderer)?
                    .is_some();
                let ignored = if matched {
                    self.config.is_black_list
                } else {
                    !self.config.is_black_list
                };
                if ignored {
                    state.ignored.insert(record.id());
                } else {
                    Self::append(&mut state, record.clone(), false)?;
                }
            }
        }
        self.insert_scope(Arc::new(OpenScopeRecord::new(record.as_ref())), false)?;
        Ok(record.id())
    }
    pub fn close_scope(&self, id: i32) -> Result<(), RecordError> {
        if self.mode != LogMode::Disabled {
            self.insert_scope(Arc::new(CloseScopeRecord::new(id)), false)?;
        }
        Ok(())
    }
    pub fn close_member_scope(&self) -> Result<(), RecordError> {
        if self.mode == LogMode::Disabled {
            return Ok(());
        }
        let id = self
            .state
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .main
            .as_ref()
            .ok_or(RecordError::Unsupported("missing main member record"))?
            .id();
        self.insert_scope(Arc::new(CloseScopeRecord::new(id)), true)?;
        Ok(())
    }
    pub fn insert_branch_point(
        &self,
        count: i32,
        condition: Option<Term>,
        condition_exp: Option<ferrum_silver::ast::expression::Exp>,
    ) -> Result<i32, RecordError> {
        if self.mode == LogMode::Disabled {
            return Ok(0);
        }
        let branch = Arc::new(BranchingRecord::new(count, condition, condition_exp));
        branch.set_id(self.fresh_uid());
        let mut state = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        if !state.closed && self.mode == LogMode::Recording {
            Self::append(&mut state, branch.clone(), false)?;
            state.branches.push(branch.clone());
        }
        Ok(branch.id())
    }
    fn branch(&self, id: i32) -> Result<Arc<BranchingRecord>, RecordError> {
        let state = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        state
            .branches
            .last()
            .filter(|b| b.id() == id)
            .cloned()
            .ok_or(RecordError::InvalidBranch)
    }
    pub fn switch_to_next_branch(&self, id: i32) -> Result<(), RecordError> {
        if self.mode == LogMode::Recording {
            self.branch(id)?.switch_to_next_branch()?;
        }
        Ok(())
    }
    pub fn mark_reachable(&self, id: i32) -> Result<(), RecordError> {
        if self.mode == LogMode::Recording {
            self.branch(id)?.mark_reachable_at(time_ms())?;
        }
        Ok(())
    }
    pub fn end_branch_point(&self, id: i32) -> Result<(), RecordError> {
        if self.mode == LogMode::Recording {
            let mut state = self.state.lock().map_err(|_| RecordError::Poisoned)?;
            if state.branches.last().is_none_or(|b| b.id() != id) {
                return Err(RecordError::InvalidBranch);
            }
            state.branches.pop();
        }
        Ok(())
    }
    pub fn set_smt_query(&self, query: Option<Term>) -> Result<(), RecordError> {
        if self.mode != LogMode::Disabled
            && let Some(member) = &self.state.lock().map_err(|_| RecordError::Poisoned)?.main
        {
            member.set_last_failed_query(query)?;
        }
        Ok(())
    }
    pub fn add_macro(&self, application: Term, body: Term) -> Result<(), RecordError> {
        if self.mode != LogMode::Disabled {
            self.state
                .lock()
                .map_err(|_| RecordError::Poisoned)?
                .macros
                .insert(application, body);
        }
        Ok(())
    }
    pub fn macros(&self) -> Result<Map<Term, Term>, RecordError> {
        Ok(self
            .state
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .macros
            .clone())
    }
    /// Integer subtraction wraps as Scala Int does. Double text rendering is
    /// injected until the Java-compatible numerical formatter is available.
    pub fn delta_statistics(
        &self,
        current: Map<String, String>,
        render_double: impl Fn(f64) -> String,
    ) -> Result<Map<String, String>, RecordError> {
        let mut state = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        let mut result = current.clone();
        for (key, value) in &current {
            if let Some(old) = state.last_statistics.get(key) {
                let delta = match (value.parse::<i32>(), old.parse::<i32>()) {
                    (Ok(now), Ok(before)) => Some(now.wrapping_sub(before).to_string()),
                    _ => match (value.parse::<f64>(), old.parse::<f64>()) {
                        (Ok(now), Ok(before)) => Some(render_double(now - before)),
                        _ => None,
                    },
                };
                if let Some(delta) = delta {
                    result.insert(format!("{key}-delta"), delta);
                }
            }
        }
        if self.mode != LogMode::Disabled {
            state.last_statistics.extend(current);
        }
        Ok(result)
    }
}
