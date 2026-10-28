//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/CommentRecord.scala
//!
//! Purpose:
//! Record the comment event in symbolic execution.
//!
//! Planned Rust structure:
//! Port CommentRecord containing comment text plus optional state and path assumptions; implement
//! its DataRecord interface and type label comment.
//!
//! Behavior to preserve:
//! Null comment has distinct simple/full rendering. Capture path assumptions when provided and
//! preserve inherited metadata behavior.
//!
//! Integration:
//! logger::symb_ex_logger, logger::records::data::data_record and writer/renderer; corresponding AST
//! and
//! state interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state, term and record ownership.
//!
//! Open decisions:
//! Reconcile event capture and serialization with symb_ex_logger and writer.
//!
//! Status: comment rendering and path/state capture implemented.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::decider::path_conditions::LayeredPathConditionStack;
use crate::logger::records::{
    data::data_record::DataRecord,
    symbolic_record::{RecordError, RecordHeader, RecordRenderer, SymbolicRecord},
};
use crate::state::terms::Term;
use ferrum_silver::ast::utility::nodes::Node;

pub struct CommentRecord<S> {
    pub header: RecordHeader,
    pub state: Option<S>,
    pub pcs: Option<InsertionOrderedSet<Term>>,
    pub comment: Option<String>,
}
impl<S> CommentRecord<S> {
    pub fn new(
        comment: Option<String>,
        state: Option<S>,
        paths: Option<&LayeredPathConditionStack>,
    ) -> Self {
        Self {
            header: RecordHeader::default(),
            state,
            pcs: paths.map(|p| p.assumptions().clone()),
            comment,
        }
    }
}
impl<S: Send + Sync + 'static> SymbolicRecord for CommentRecord<S> {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "comment"
    }
    fn simple_string(&self, _: &dyn RecordRenderer) -> Result<String, RecordError> {
        Ok(self.comment.clone().unwrap_or_else(|| "null".into()))
    }
    fn render(&self, _: &dyn RecordRenderer) -> Result<String, RecordError> {
        Ok(format!(
            "comment {}",
            self.comment.as_deref().unwrap_or("<null>")
        ))
    }
    fn as_data_record(&self) -> Option<&dyn DataRecord> {
        Some(self)
    }
}
impl<S: Send + Sync + 'static> DataRecord for CommentRecord<S> {
    fn value(&self) -> Option<Node> {
        None
    }
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>> {
        self.pcs.as_ref()
    }
}
