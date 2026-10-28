//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/structural/JoiningRecord.scala
//!
//! Purpose:
//! Represent a symbolic execution join event.
//!
//! Planned Rust structure:
//! Port JoiningRecord as DataRecord and StructuralRecord with state and optional path assumptions.
//!
//! Behavior to preserve:
//! Use joining label and null AST value; preserve captured assumption order for metadata.
//!
//! Integration:
//! logger::symb_ex_logger, logger::renderer::simple_tree_renderer and
//! logger::records::data::data_record.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state capture.
//!
//! Open decisions:
//! Agree on record dispatch and state lifetime with logger.
//!
//! Status: joining record with source null description implemented.

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

pub struct JoiningRecord<S> {
    pub header: RecordHeader,
    pub state: Option<S>,
    pub pcs: Option<InsertionOrderedSet<Term>>,
}
impl<S> JoiningRecord<S> {
    pub fn new(state: Option<S>, paths: Option<&LayeredPathConditionStack>) -> Self {
        Self {
            header: RecordHeader::default(),
            state,
            pcs: paths.map(|p| p.assumptions().clone()),
        }
    }
}
impl<S: Send + Sync + 'static> SymbolicRecord for JoiningRecord<S> {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "joining"
    }
    fn simple_string(&self, _: &dyn RecordRenderer) -> Result<String, RecordError> {
        Ok("null".into())
    }
    fn as_data_record(&self) -> Option<&dyn DataRecord> {
        Some(self)
    }
    fn is_joining(&self) -> bool {
        true
    }
}
impl<S: Send + Sync + 'static> DataRecord for JoiningRecord<S> {
    fn value(&self) -> Option<Node> {
        None
    }
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>> {
        self.pcs.as_ref()
    }
}
impl<S: Send + Sync + 'static> super::structural_record::StructuralRecord for JoiningRecord<S> {}
