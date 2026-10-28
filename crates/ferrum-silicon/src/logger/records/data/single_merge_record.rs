//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/SingleMergeRecord.scala
//!
//! Purpose:
//! Record the single merge event in symbolic execution.
//!
//! Planned Rust structure:
//! Port SingleMergeRecord containing destination and new chunk sequences plus path assumptions;
//! implement its DataRecord interface and type label single merge.
//!
//! Behavior to preserve:
//! Preserve sequence order and full display with <= separator and null handling. Capture path
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
//! Status: ordered merge descriptions and null fallback implemented; chunk renderer remains injected.

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

use crate::state::chunks::Chunk;
pub struct SingleMergeRecord {
    pub header: RecordHeader,
    pub dest_chunks: Option<Vec<Chunk>>,
    pub new_chunks: Option<Vec<Chunk>>,
    pub pcs: Option<InsertionOrderedSet<Term>>,
}
impl SingleMergeRecord {
    pub fn new(
        dest_chunks: Option<Vec<Chunk>>,
        new_chunks: Option<Vec<Chunk>>,
        paths: Option<&LayeredPathConditionStack>,
    ) -> Self {
        Self {
            header: RecordHeader::default(),
            dest_chunks,
            new_chunks,
            pcs: paths.map(|p| p.assumptions().clone()),
        }
    }
}
impl SymbolicRecord for SingleMergeRecord {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "single merge"
    }
    fn simple_string(&self, renderer: &dyn RecordRenderer) -> Result<String, RecordError> {
        match (&self.dest_chunks, &self.new_chunks) {
            (Some(a), Some(b)) => Ok(a
                .iter()
                .chain(b)
                .map(|c| renderer.chunk(c))
                .collect::<Result<Vec<_>, _>>()?
                .join(" ")),
            _ => Ok("SingleMerge <null>".into()),
        }
    }
    fn render(&self, renderer: &dyn RecordRenderer) -> Result<String, RecordError> {
        match (&self.dest_chunks, &self.new_chunks) {
            (Some(a), Some(b)) => {
                let a = a
                    .iter()
                    .map(|c| renderer.chunk(c))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(" ");
                let b = b
                    .iter()
                    .map(|c| renderer.chunk(c))
                    .collect::<Result<Vec<_>, _>>()?
                    .join(" ");
                Ok(if b.is_empty() {
                    format!("single merge {a} <=")
                } else {
                    format!("single merge {a} <= {b}")
                })
            }
            _ => Ok("SingleMerge <null>".into()),
        }
    }
    fn as_data_record(&self) -> Option<&dyn DataRecord> {
        Some(self)
    }
}
impl DataRecord for SingleMergeRecord {
    fn value(&self) -> Option<Node> {
        None
    }
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>> {
        self.pcs.as_ref()
    }
}
