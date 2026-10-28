//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/MethodRecord.scala
//!
//! Purpose:
//! Record the method event in symbolic execution.
//!
//! Planned Rust structure:
//! Port MethodRecord containing method AST and path assumptions; implement its MemberRecord
//! interface and type label method.
//!
//! Behavior to preserve:
//! Simple display is member name or null. Capture path assumptions when provided and preserve
//! inherited metadata behavior.
//!
//! Integration:
//! logger::symb_ex_logger, logger::records::data::member_record and writer/renderer; corresponding AST
//! and
//! state interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for state, term and record ownership.
//!
//! Open decisions:
//! Reconcile event capture and serialization with symb_ex_logger and writer.
//!
//! Status: member name, path capture and failed-query report implemented; concrete logger calls remain.

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

use crate::logger::{
    log_config::LogConfig,
    records::{
        data::{data_record::data_for, member_record::MemberRecord},
        record_data::RecordData,
    },
};
use ferrum_silver::ast::program::{Member, Method};
use std::sync::Mutex;
pub struct MethodRecord {
    pub header: RecordHeader,
    pub value: Option<Method>,
    pub pcs: Option<InsertionOrderedSet<Term>>,
    pub last_failed_prover_query: Mutex<Option<Term>>,
}
impl MethodRecord {
    pub fn new(value: Option<Method>, paths: Option<&LayeredPathConditionStack>) -> Self {
        Self {
            header: RecordHeader::default(),
            value,
            pcs: paths.map(|p| p.assumptions().clone()),
            last_failed_prover_query: Mutex::new(None),
        }
    }
}
impl SymbolicRecord for MethodRecord {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "method"
    }
    fn simple_string(&self, _: &dyn RecordRenderer) -> Result<String, RecordError> {
        Ok(self
            .value
            .as_ref()
            .map(|v| v.name.clone())
            .unwrap_or_else(|| "null".into()))
    }
    fn as_data_record(&self) -> Option<&dyn DataRecord> {
        Some(self)
    }
    fn get_data(
        &self,
        config: &LogConfig,
        renderer: &dyn RecordRenderer,
    ) -> Result<RecordData, RecordError> {
        let mut data = data_for(self, config, renderer)?;
        data.last_smt_query = self.last_failed_query()?;
        Ok(data)
    }
}
impl DataRecord for MethodRecord {
    fn value(&self) -> Option<Node> {
        self.value.clone().map(|v| Node::Member(Member::Method(v)))
    }
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>> {
        self.pcs.as_ref()
    }
}
impl MemberRecord for MethodRecord {
    fn last_failed_query(&self) -> Result<Option<Term>, RecordError> {
        Ok(self
            .last_failed_prover_query
            .lock()
            .map_err(|_| RecordError::Poisoned)?
            .clone())
    }
    fn set_last_failed_query(&self, query: Option<Term>) -> Result<(), RecordError> {
        *self
            .last_failed_prover_query
            .lock()
            .map_err(|_| RecordError::Poisoned)? = query;
        Ok(())
    }
}
