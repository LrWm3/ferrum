//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/LogConfig.scala
//!
//! Purpose:
//! Configure symbolic log record filtering and optional details.
//!
//! Planned Rust structure:
//! Port LogConfig, RecordConfig, getRecordConfig and JSON protocol.
//!
//! Behavior to preserve:
//! First record config matching kind and optional exact value wins. Default is blacklist with no
//! filters and store/heap/oldHeap/pcs disabled; preserve JSON field names and optional value.
//!
//! Integration:
//! symb_ex_logger, logger::records::data and logger::writer::symb_ex_log_report_writer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for configuration and native JSON.
//!
//! Open decisions:
//! Agree on JSON compatibility and defaults with log consumers.
//!
//! Status: record matching and defaults implemented; JSON configuration decoding remains.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordConfig {
    pub kind: String,
    pub value: Option<String>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogConfig {
    pub is_black_list: bool,
    pub include_store: bool,
    pub include_heap: bool,
    pub include_old_heap: bool,
    pub include_pcs: bool,
    pub record_configs: Vec<RecordConfig>,
}
impl Default for LogConfig {
    fn default() -> Self {
        Self {
            is_black_list: true,
            include_store: false,
            include_heap: false,
            include_old_heap: false,
            include_pcs: false,
            record_configs: vec![],
        }
    }
}
impl LogConfig {
    /// Match in configuration order, evaluating a record's text only when a value is required.
    pub fn get_record_config<'a>(
        &'a self,
        record: &dyn super::records::data::data_record::DataRecord,
        renderer: &dyn super::records::symbolic_record::RecordRenderer,
    ) -> Result<Option<&'a RecordConfig>, super::records::symbolic_record::RecordError> {
        for config in &self.record_configs {
            if config.kind == record.type_string()
                && (config.value.is_none()
                    || config.value.as_ref() == Some(&record.simple_string(renderer)?))
            {
                return Ok(Some(config));
            }
        }
        Ok(None)
    }
}
