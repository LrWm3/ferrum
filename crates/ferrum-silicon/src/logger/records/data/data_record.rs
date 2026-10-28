//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/records/data/DataRecord.scala
//!
//! Purpose:
//! Attach source node and path conditions to symbolic data records.
//!
//! Planned Rust structure:
//! Port DataRecord value, pcs, string rendering and getData.
//!
//! Behavior to preserve:
//! Render null value as null; populate source position for Positioned nodes and include captured
//! ordered assumptions only if includePcs enabled.
//!
//! Integration:
//! logger::records::symbolic_record/record_data and concrete data records; Silver positions and
//! state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for optional data and immutable state capture.
//!
//! Open decisions:
//! Agree on source position serialization and path condition ownership with writer.
//!
//! Status: node and path-condition capture implemented; source-compatible rendering is injected.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::{
    common::collections::immutable::insertion_ordered_set::InsertionOrderedSet,
    logger::{
        log_config::LogConfig,
        records::{
            record_data::RecordData,
            symbolic_record::{RecordError, RecordRenderer, SymbolicRecord},
        },
    },
    state::terms::Term,
};
use ferrum_silver::ast::utility::nodes::Node;
pub trait DataRecord: SymbolicRecord {
    fn value(&self) -> Option<Node>;
    fn pcs(&self) -> Option<&InsertionOrderedSet<Term>>;
}
pub fn data_for(
    record: &dyn DataRecord,
    config: &LogConfig,
    renderer: &dyn RecordRenderer,
) -> Result<RecordData, RecordError> {
    let pos = record
        .value()
        .map(|node| renderer.source_line_column(&node))
        .transpose()?;
    Ok(RecordData {
        pos,
        pcs: if config.include_pcs {
            record.pcs().cloned()
        } else {
            None
        },
        ..RecordData::default()
    })
}
