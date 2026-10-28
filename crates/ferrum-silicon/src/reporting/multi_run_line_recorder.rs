//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/MultiRunLineRecorder.scala
//!
//! Purpose:
//! Write recorded lines with source-boundary headers.
//!
//! Planned Rust structure:
//! Port MultiRunLineRecorder source, onSourceChanged and record.
//!
//! Behavior to preserve:
//! Detect source change before writing, print header, then print with optional newline; upstream
//! is not thread-safe.
//!
//! Integration:
//! reporting::multi_run_recorder and configured sink.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for IO and lifecycle.
//!
//! Open decisions:
//! Agree on synchronization and sink ownership with recorder registry.
//!
//! Status: source-boundary headers, line output and lifecycle implemented.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::multi_run_recorder::{
    MultiRunRecorder, SourceProvider, SourceTracker, format_new_source,
};
use std::any::Any;
use std::fmt::Display;
use std::io::{self, Write};

pub struct MultiRunLineRecorder<W> {
    pub sink: W,
    source: SourceProvider,
    tracker: SourceTracker,
}
impl<W: Write> MultiRunLineRecorder<W> {
    pub fn new(sink: W, source: SourceProvider) -> Self {
        Self {
            sink,
            source,
            tracker: SourceTracker::default(),
        }
    }
    pub fn source(&self) -> Option<String> {
        (self.source)()
    }
    pub fn record(&mut self, value: impl Display, newline: bool) -> io::Result<()> {
        let source = self.source();
        if self.tracker.detect_change(source.clone()) {
            writeln!(self.sink, "{}", format_new_source(source.as_deref()))?;
        }
        if newline {
            writeln!(self.sink, "{value}")
        } else {
            write!(self.sink, "{value}")
        }
    }
}
impl<W: Write + 'static> MultiRunRecorder for MultiRunLineRecorder<W> {
    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
    fn reset(&mut self) -> io::Result<()> {
        self.sink.flush()
    }
    fn flush(&mut self) -> io::Result<()> {
        self.sink.flush()
    }
}
