//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/ProverAssertRecord.scala
//!
//! Purpose:
//! Record the prover assert event in symbolic execution.
//!
//! Planned Rust structure:
//! Port ProverAssertRecord containing term, optional timeout and mutable optional statistics;
//! implement its DataRecord interface and type label prover assert.
//!
//! Behavior to preserve:
//! Getdata marks smt query and includes statistics; display term or null. Capture path assumptions
//! when provided and preserve inherited metadata behavior.
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

pub struct ProverAssertRecord {
    pub header: RecordHeader,
    pub term: Option<Term>,
    pub timeout: Option<i32>,
    pub statistics: std::sync::Mutex<Option<crate::package::Map<String, String>>>,
}
impl ProverAssertRecord {
    pub fn new(term: Option<Term>, timeout: Option<i32>) -> Self {
        Self {
            header: RecordHeader::default(),
            term,
            timeout,
            statistics: std::sync::Mutex::new(None),
        }
    }
}
impl SymbolicRecord for ProverAssertRecord {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "prover assert"
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
    fn get_data(
        &self,
        _: &crate::logger::log_config::LogConfig,
        _: &dyn RecordRenderer,
    ) -> Result<crate::logger::records::record_data::RecordData, RecordError> {
        Ok(crate::logger::records::record_data::RecordData {
            is_smt_query: true,
            smt_statistics: self
                .statistics
                .lock()
                .map_err(|_| RecordError::Poisoned)?
                .clone(),
            ..Default::default()
        })
    }
}
impl DataRecord for ProverAssertRecord {
    fn value(&self) -> Option<Node> {
        None
    }
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>> {
        None
    }
}
