//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/DeciderAssertRecord.scala
//!
//! Purpose:
//! Record the decider assert event in symbolic execution.
//!
//! Planned Rust structure:
//! Port DeciderAssertRecord containing symbolic term and optional timeout; implement its
//! DataRecord interface and type label decider assert.
//!
//! Behavior to preserve:
//! State, ast and path conditions are absent; simple display is term or null. Capture path
//! assumptions when provided and preserve inherited metadata behavior.
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
//! Status: query payload and source report data implemented; term renderer remains injected.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::logger::records::{
    data::data_record::DataRecord,
    symbolic_record::{RecordError, RecordHeader, RecordRenderer, SymbolicRecord},
};
use crate::state::terms::Term;
use ferrum_silver::ast::utility::nodes::Node;

pub struct DeciderAssertRecord {
    pub header: RecordHeader,
    pub term: Option<Term>,
    pub timeout: Option<i32>,
}
impl DeciderAssertRecord {
    pub fn new(term: Option<Term>, timeout: Option<i32>) -> Self {
        Self {
            header: RecordHeader::default(),
            term,
            timeout,
        }
    }
}
impl SymbolicRecord for DeciderAssertRecord {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "decider assert"
    }
    fn simple_string(&self, renderer: &dyn RecordRenderer) -> Result<String, RecordError> {
        self.term
            .as_ref()
            .map(|t| renderer.term(t))
            .unwrap_or_else(|| Ok("null".into()))
    }
    fn as_data_record(&self) -> Option<&dyn DataRecord> {
        Some(self)
    }
}
impl DataRecord for DeciderAssertRecord {
    fn value(&self) -> Option<Node> {
        None
    }
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>> {
        None
    }
}
