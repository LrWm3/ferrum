//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/MultiRunCountingRecorder.scala
//!
//! Purpose:
//! Count occurrences per source and write totals between runs.
//!
//! Planned Rust structure:
//! Port MultiRunCountingRecorder record, source provider and writeAndClearRecordedData.
//!
//! Behavior to preserve:
//! Detect source changes before increment; emit key: count pairs then clear on source change/stop.
//! Upstream map iteration and recorder are not thread-safe.
//!
//! Integration:
//! reporting::multi_run_recorder and configured sink.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering and IO lifecycle.
//!
//! Open decisions:
//! Agree on map ordering and synchronization with recorder registry.
//!
//! Status: source-boundary counting, buffered output and lifecycle implemented.
//! Native HashMap order does not reproduce Scala's incidental iteration order.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::multi_run_recorder::{
    MultiRunRecorder, SourceProvider, SourceTracker, format_new_source,
};
use std::any::Any;
use std::collections::HashMap;
use std::fmt::Display;
use std::hash::Hash;
use std::io::{self, Write};

pub struct MultiRunCountingRecorder<K, W> {
    pub sink: W,
    source: SourceProvider,
    tracker: SourceTracker,
    data: HashMap<K, i32>,
}
impl<K: Eq + Hash + Display, W: Write> MultiRunCountingRecorder<K, W> {
    pub fn new(sink: W, source: SourceProvider) -> Self {
        Self {
            sink,
            source,
            tracker: SourceTracker::default(),
            data: HashMap::new(),
        }
    }
    pub fn source(&self) -> Option<String> {
        (self.source)()
    }
    pub fn record(&mut self, key: K) -> io::Result<()> {
        let source = self.source();
        if self.tracker.detect_change(source.clone()) {
            self.write_and_clear_recorded_data()?;
            writeln!(self.sink, "{}", format_new_source(source.as_deref()))?;
        }
        let count = self.data.entry(key).or_default();
        *count = count.wrapping_add(1);
        Ok(())
    }
    pub fn write_and_clear_recorded_data(&mut self) -> io::Result<()> {
        for (key, count) in &self.data {
            writeln!(self.sink, "{key}: {count}")?;
        }
        self.data.clear();
        Ok(())
    }
}
impl<K: Eq + Hash + Display + 'static, W: Write + 'static> MultiRunRecorder
    for MultiRunCountingRecorder<K, W>
{
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
    fn reset(&mut self) -> io::Result<()> {
        self.sink.flush()
    }
    fn stop(&mut self) -> io::Result<()> {
        self.write_and_clear_recorded_data()
    }
    fn flush(&mut self) -> io::Result<()> {
        self.sink.flush()
    }
}
