//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/structural/BranchingRecord.scala
//!
//! Purpose:
//! Track ordered symbolic execution branches and reachability.
//!
//! Planned Rust structure:
//! Port BranchingRecord condition/conditionExp, current index and BranchInfo
//! records/reachable/startTime, plus append, switch and query helpers.
//!
//! Behavior to preserve:
//! Allocate requested number of branches, mark current branch reachable with start time, append in
//! order and assert index bounds; display condition or null.
//!
//! Integration:
//! logger::symb_ex_logger, logger::renderer::simple_tree_renderer and writer; state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered branch records and term identity.
//!
//! Open decisions:
//! Agree on branch ownership and timing with concurrent logger.
//!
//! Status: ordered branch capture, reachability and timestamps implemented; concrete logger scheduling remains.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::structural_record::StructuralRecord;
use crate::logger::records::symbolic_record::{
    RecordError, RecordHeader, RecordRef, RecordRenderer, SymbolicRecord,
};
use crate::state::terms::Term;
use ferrum_silver::ast::expression::Exp;
use std::sync::Mutex;
#[derive(Clone, Default)]
pub struct BranchInfo {
    pub is_reachable: bool,
    pub start_time_ms: i64,
    pub records: Vec<RecordRef>,
}
struct BranchState {
    current: i32,
    branches: Vec<BranchInfo>,
}
pub struct BranchingRecord {
    pub header: RecordHeader,
    pub condition: Option<Term>,
    pub condition_exp: Option<Exp>,
    state: Mutex<BranchState>,
}
impl BranchingRecord {
    pub fn new(
        possible_branches: i32,
        condition: Option<Term>,
        condition_exp: Option<Exp>,
    ) -> Self {
        Self {
            header: RecordHeader::default(),
            condition,
            condition_exp,
            state: Mutex::new(BranchState {
                current: 0,
                branches: vec![BranchInfo::default(); possible_branches.max(0) as usize],
            }),
        }
    }
    pub fn append_log(&self, record: RecordRef) -> Result<(), RecordError> {
        let mut s = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        let i = s.current as usize;
        s.branches
            .get_mut(i)
            .ok_or(RecordError::InvalidBranch)?
            .records
            .push(record);
        Ok(())
    }
    pub fn mark_reachable_at(&self, time_ms: i64) -> Result<(), RecordError> {
        let mut s = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        let i = s.current as usize;
        let branch = s.branches.get_mut(i).ok_or(RecordError::InvalidBranch)?;
        branch.is_reachable = true;
        branch.start_time_ms = time_ms;
        Ok(())
    }
    pub fn switch_to_next_branch(&self) -> Result<(), RecordError> {
        let mut s = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        s.current = s.current.wrapping_add(1);
        Ok(())
    }
    pub fn branch_infos(&self) -> Result<Vec<BranchInfo>, RecordError> {
        Ok(self
            .state
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .branches
            .clone())
    }
    pub fn current_branch(&self) -> Result<BranchInfo, RecordError> {
        let s = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        s.branches
            .get(s.current as usize)
            .cloned()
            .ok_or(RecordError::InvalidBranch)
    }
    pub fn is_reachable(&self, index: i32) -> Result<bool, RecordError> {
        let s = self.state.lock().map_err(|_| RecordError::Poisoned)?;
        Ok(s.branches
            .get(index as usize)
            .ok_or(RecordError::InvalidBranch)?
            .is_reachable)
    }
}
impl SymbolicRecord for BranchingRecord {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "branching"
    }
    fn simple_string(&self, renderer: &dyn RecordRenderer) -> Result<String, RecordError> {
        self.condition
            .as_ref()
            .map(|t| renderer.term(t))
            .unwrap_or_else(|| Ok("null".into()))
    }
}
impl StructuralRecord for BranchingRecord {}
