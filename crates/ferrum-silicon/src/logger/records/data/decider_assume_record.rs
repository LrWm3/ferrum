//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/DeciderAssumeRecord.scala
//!
//! Purpose:
//! Record the decider assume event in symbolic execution.
//!
//! Planned Rust structure:
//! Port DeciderAssumeRecord containing sequence of symbolic terms; implement its DataRecord
//! interface and type label decider assume.
//!
//! Behavior to preserve:
//! State, ast and path conditions are absent; display terms space-separated or null. Capture path
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
//! Status: ordered assumption payload and source description implemented; term renderer remains injected.

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

pub struct DeciderAssumeRecord {
    pub header: RecordHeader,
    pub terms: Option<Vec<Term>>,
}
impl DeciderAssumeRecord {
    pub fn new(terms: Option<Vec<Term>>) -> Self {
        Self {
            header: RecordHeader::default(),
            terms,
        }
    }
}
impl SymbolicRecord for DeciderAssumeRecord {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "decider assume"
    }
    fn simple_string(&self, renderer: &dyn RecordRenderer) -> Result<String, RecordError> {
        match &self.terms {
            None => Ok("null".into()),
            Some(terms) => Ok(terms
                .iter()
                .map(|t| renderer.term(t))
                .collect::<Result<Vec<_>, _>>()?
                .join(" ")),
        }
    }
    fn as_data_record(&self) -> Option<&dyn DataRecord> {
        Some(self)
    }
}
impl DataRecord for DeciderAssumeRecord {
    fn value(&self) -> Option<Node> {
        None
    }
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>> {
        None
    }
}
