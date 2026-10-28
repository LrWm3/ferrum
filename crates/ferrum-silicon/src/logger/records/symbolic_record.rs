//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/SymbolicRecord.scala
//!
//! Purpose:
//! Define the shared symbolic log record interface.
//!
//! Planned Rust structure:
//! Port SymbolicRecord id, type/simple string and getData.
//!
//! Behavior to preserve:
//! ID initially -1; default getData produces empty RecordData and string joins type and simple
//! text.
//!
//! Integration:
//! logger::records::{data,scoping,structural}, symb_ex_logger and renderer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for record identity and lifetimes.
//!
//! Open decisions:
//! Agree on enum versus trait dispatch with logger and writer.
//!
//! Status: shared record identity and rendering/data contracts implemented; exact native renderers remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::{data::data_record::DataRecord, record_data::RecordData};
use crate::{
    logger::log_config::LogConfig,
    state::{chunks::Chunk, terms::Term},
};
use ferrum_silver::ast::utility::nodes::Node;
use std::{
    any::Any,
    sync::{
        Arc,
        atomic::{AtomicI32, Ordering},
    },
};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecordError {
    Unsupported(&'static str),
    InvalidBranch,
    Poisoned,
}
/// Source rendering is explicit: Rust Debug text is not an equivalent printer.
pub trait RecordRenderer {
    fn node(&self, node: &Node) -> Result<String, RecordError>;
    fn term(&self, term: &Term) -> Result<String, RecordError>;
    fn chunk(&self, chunk: &Chunk) -> Result<String, RecordError>;
    fn source_line_column(&self, node: &Node) -> Result<String, RecordError>;
}
pub struct RecordHeader {
    id: AtomicI32,
}
impl Default for RecordHeader {
    fn default() -> Self {
        Self {
            id: AtomicI32::new(-1),
        }
    }
}
impl RecordHeader {
    pub fn id(&self) -> i32 {
        self.id.load(Ordering::Relaxed)
    }
    pub fn set_id(&self, id: i32) {
        self.id.store(id, Ordering::Relaxed);
    }
}
pub type RecordRef = Arc<dyn SymbolicRecord>;
pub trait SymbolicRecord: Any + Send + Sync {
    fn as_any(&self) -> &dyn Any;
    fn header(&self) -> &RecordHeader;
    fn id(&self) -> i32 {
        self.header().id()
    }
    fn set_id(&self, id: i32) {
        self.header().set_id(id);
    }
    fn type_string(&self) -> &'static str;
    fn simple_string(&self, renderer: &dyn RecordRenderer) -> Result<String, RecordError>;
    fn render(&self, renderer: &dyn RecordRenderer) -> Result<String, RecordError> {
        Ok(format!(
            "{} {}",
            self.type_string(),
            self.simple_string(renderer)?
        ))
    }
    fn as_data_record(&self) -> Option<&dyn DataRecord> {
        None
    }
    fn is_joining(&self) -> bool {
        false
    }
    fn get_data(
        &self,
        config: &LogConfig,
        renderer: &dyn RecordRenderer,
    ) -> Result<RecordData, RecordError> {
        match self.as_data_record() {
            Some(record) => super::data::data_record::data_for(record, config, renderer),
            None => Ok(RecordData::default()),
        }
    }
}
