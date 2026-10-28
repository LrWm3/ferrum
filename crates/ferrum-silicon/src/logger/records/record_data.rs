//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/RecordData.scala
//!
//! Purpose:
//! Collect optional metadata for a symbolic execution log record.
//!
//! Planned Rust structure:
//! Port RecordData fields refId, isSmtQuery, smtStatistics, timeMs, pos, lastSMTQuery, store,
//! heap, oldHeap and pcs.
//!
//! Behavior to preserve:
//! Defaults are absent except isSmtQuery=false; retain ordered path conditions and optional
//! state/query details for serialization.
//!
//! Integration:
//! logger::records::{symbolic_record,data,scoping}, logger::writer::symb_ex_log_report_writer and
//! state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for term/state handles and ordered collections.
//!
//! Open decisions:
//! Agree on captured state ownership with logger and writer.
//!
//! Status: optional report fields implemented with native store/heap handles.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::state::{heap::ListBackedHeap, store::MapBackedStore, terms::Term};
use std::sync::Arc;
#[derive(Clone, Debug, Default)]
pub struct RecordData {
    pub ref_id: Option<i32>,
    pub is_smt_query: bool,
    pub smt_statistics: Option<crate::package::Map<String, String>>,
    pub time_ms: Option<i64>,
    pub pos: Option<String>,
    pub last_smt_query: Option<Term>,
    pub store: Option<Arc<MapBackedStore>>,
    pub heap: Option<Arc<ListBackedHeap>>,
    pub old_heap: Option<Arc<ListBackedHeap>>,
    pub pcs: Option<InsertionOrderedSet<Term>>,
}
