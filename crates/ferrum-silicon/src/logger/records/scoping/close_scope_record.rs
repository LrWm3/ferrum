//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/scoping/CloseScopeRecord.scala
//!
//! Purpose:
//! Represent a scope boundary event.
//!
//! Planned Rust structure:
//! Port CloseScopeRecord as ScopingRecord; retain supplied reference ID.
//!
//! Behavior to preserve:
//! Use type label close and display reference ID as decimal; inherit timing metadata.
//!
//! Integration:
//! logger::records::scoping::scoping_record, logger::symb_ex_logger and renderer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for IDs and event ownership.
//!
//! Open decisions:
//! Agree on scope nesting and matching with symb_ex_logger.
//!
//! Status: scope reference, timestamp and report data implemented.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::scoping_record::ScopingRecord;
use crate::logger::{
    log_config::LogConfig,
    records::{
        record_data::RecordData,
        symbolic_record::{RecordError, RecordHeader, RecordRenderer, SymbolicRecord},
    },
};
use std::sync::atomic::{AtomicI64, Ordering};
pub struct CloseScopeRecord {
    pub header: RecordHeader,
    pub ref_id: i32,
    time_ms: AtomicI64,
}
impl CloseScopeRecord {
    pub fn new(ref_id: i32) -> Self {
        Self::from_ref_id(ref_id)
    }
    fn from_ref_id(ref_id: i32) -> Self {
        Self {
            header: RecordHeader::default(),
            ref_id,
            time_ms: AtomicI64::new(0),
        }
    }
}
impl SymbolicRecord for CloseScopeRecord {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn header(&self) -> &RecordHeader {
        &self.header
    }
    fn type_string(&self) -> &'static str {
        "close"
    }
    fn simple_string(&self, _: &dyn RecordRenderer) -> Result<String, RecordError> {
        Ok(self.ref_id.to_string())
    }
    fn get_data(&self, _: &LogConfig, _: &dyn RecordRenderer) -> Result<RecordData, RecordError> {
        Ok(RecordData {
            ref_id: Some(self.ref_id),
            time_ms: Some(self.time_ms()),
            ..Default::default()
        })
    }
}
impl ScopingRecord for CloseScopeRecord {
    fn ref_id(&self) -> i32 {
        self.ref_id
    }
    fn time_ms(&self) -> i64 {
        self.time_ms.load(Ordering::Relaxed)
    }
    fn set_time_ms(&self, time: i64) {
        self.time_ms.store(time, Ordering::Relaxed);
    }
}
