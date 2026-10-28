//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/WellformednessCheckRecord.scala
//!
//! Purpose:
//! Record the WellformednessCheck event in symbolic execution.
//!
//! Planned Rust structure:
//! Port WellformednessCheckRecord containing condition sequence, state and path assumptions;
//! implement its DataRecord interface and type label WellformednessCheck.
//!
//! Behavior to preserve:
//! Value is null while conditions are separately retained. Capture path assumptions when provided
//! and preserve inherited metadata behavior.
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
//! Status: condition/state/path capture and source null description implemented.

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
use ferrum_silver::ast::{expression::Exp, utility::nodes::Node};

pub struct WellformednessCheckRecord<S> {
    pub header: RecordHeader,
    pub conditions: Vec<Exp>,
    pub state: Option<S>,
    pub pcs: Option<InsertionOrderedSet<Term>>,
}
impl<S> WellformednessCheckRecord<S> {
    pub fn new(
        conditions: Vec<Exp>,
        state: Option<S>,
        paths: Option<&LayeredPathConditionStack>,
    ) -> Self {
        Self {
            header: RecordHeader::default(),
            conditions,
            state,
            pcs: paths.map(|p| p.assumptions().clone()),
        }
    }
}
impl<S: Send + Sync + 'static> SymbolicRecord for WellformednessCheckRecord<S> {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "WellformednessCheck"
    }
    fn simple_string(&self, _: &dyn RecordRenderer) -> Result<String, RecordError> {
        Ok("null".into())
    }
    fn as_data_record(&self) -> Option<&dyn DataRecord> {
        Some(self)
    }
}
impl<S: Send + Sync + 'static> DataRecord for WellformednessCheckRecord<S> {
    fn value(&self) -> Option<Node> {
        None
    }
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>> {
        self.pcs.as_ref()
    }
}
