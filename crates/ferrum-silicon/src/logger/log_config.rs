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
//! Status: record matching, defaults and source JSON product format implemented.

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogConfigError(pub String);
impl LogConfig {
    /// The JSON product format requires all six fields; `default` is only used
    /// when no configuration file is supplied. Record values may be absent/null.
    pub fn from_json(value: &serde_json::Value) -> Result<Self, LogConfigError> {
        let object = value
            .as_object()
            .ok_or_else(|| LogConfigError("LogConfig must be an object".into()))?;
        let boolean = |key: &str| {
            object
                .get(key)
                .and_then(|v| v.as_bool())
                .ok_or_else(|| LogConfigError(format!("{key} must be a boolean")))
        };
        let records = object
            .get("recordConfigs")
            .and_then(|v| v.as_array())
            .ok_or_else(|| LogConfigError("recordConfigs must be an array".into()))?;
        let mut record_configs = Vec::new();
        for value in records {
            let object = value
                .as_object()
                .ok_or_else(|| LogConfigError("RecordConfig must be an object".into()))?;
            let kind = object
                .get("kind")
                .and_then(|v| v.as_str())
                .ok_or_else(|| LogConfigError("kind must be a string".into()))?
                .into();
            let value = match object.get("value") {
                None | Some(serde_json::Value::Null) => None,
                Some(serde_json::Value::String(value)) => Some(value.clone()),
                _ => return Err(LogConfigError("value must be a string or null".into())),
            };
            record_configs.push(RecordConfig { kind, value });
        }
        Ok(Self {
            is_black_list: boolean("isBlackList")?,
            include_store: boolean("includeStore")?,
            include_heap: boolean("includeHeap")?,
            include_old_heap: boolean("includeOldHeap")?,
            include_pcs: boolean("includePcs")?,
            record_configs,
        })
    }
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({"isBlackList":self.is_black_list,"includeStore":self.include_store,"includeHeap":self.include_heap,"includeOldHeap":self.include_old_heap,"includePcs":self.include_pcs,"recordConfigs":self.record_configs.iter().map(|r| {
            let mut fields = serde_json::Map::new(); fields.insert("kind".into(),serde_json::json!(r.kind));
            if let Some(value) = &r.value { fields.insert("value".into(),serde_json::json!(value)); }
            serde_json::Value::Object(fields)
        }).collect::<Vec<_>>()})
    }
}
