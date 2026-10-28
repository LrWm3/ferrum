//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/MultiRunRecorder.scala
//!
//! Purpose:
//! Manage multi-run recording, source changes, sinks and lifecycle.
//!
//! Planned Rust structure:
//! Port MultiRunRecorder, PrintWriterBasedMultiRunRecorder,
//! BufferingPrintWriterBasedMultiRunRecorder and MultiRunRecorders registry.
//!
//! Behavior to preserve:
//! Detect changes in optional source, emit source headers, flush on reset and write buffered data
//! on change/stop. Registry creates named temp-directory sinks, starts empty, flushes/reset and
//! closes/clears on stop; upstream warns it is not thread-safe.
//!
//! Integration:
//! reporting::{multi_run_counting_recorder,multi_run_line_recorder}, config and verifier
//! lifecycle.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for lifecycle, native factory and IO ownership.
//!
//! Open decisions:
//! Choose typed registry/factory and concurrency policy without changing source-boundary behavior.
//!
//! Status: native source tracking, lifecycle and typed recorder registry implemented.
//! Verifier configuration/lifecycle wiring remains. Rust I/O errors propagate; registry
//! shutdown attempts every recorder before returning its first error.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use std::any::Any;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, BufWriter};
use std::path::PathBuf;
use std::rc::Rc;

/// Recorders deliberately remain local to one verifier thread, as upstream.
pub type SourceProvider = Rc<dyn Fn() -> Option<String>>;

#[derive(Default)]
pub struct SourceTracker {
    last_seen: Option<String>,
}
impl SourceTracker {
    /// Initial None does not count as a change. Update before the change callback,
    /// retaining the source order even if a native writer subsequently fails.
    pub fn detect_change(&mut self, current: Option<String>) -> bool {
        if self.last_seen == current {
            false
        } else {
            self.last_seen = current;
            true
        }
    }
}
pub fn format_new_source(source: Option<&str>) -> String {
    format!(
        "\n---------- {} ----------\n",
        source.unwrap_or("New unnamed source")
    )
}

pub trait MultiRunRecorder: Any {
    fn as_any_mut(&mut self) -> &mut dyn Any;
    fn start(&mut self) -> io::Result<()> {
        Ok(())
    }
    fn reset(&mut self) -> io::Result<()>;
    fn stop(&mut self) -> io::Result<()> {
        Ok(())
    }
    fn flush(&mut self) -> io::Result<()>;
}

/// Explicit factories replace the JVM constructor reflection. One name retains one
/// recorder instance; requesting that name with another concrete type is an error.
pub struct MultiRunRecorders {
    directory: PathBuf,
    source: Rc<RefCell<Option<String>>>,
    recorders: HashMap<String, Box<dyn MultiRunRecorder>>,
}
impl MultiRunRecorders {
    pub fn new(directory: impl Into<PathBuf>) -> Self {
        Self {
            directory: directory.into(),
            source: Rc::new(RefCell::new(None)),
            recorders: HashMap::new(),
        }
    }
    pub fn set_source(&mut self, source: Option<String>) {
        *self.source.borrow_mut() = source;
    }
    pub fn source(&self) -> Option<String> {
        self.source.borrow().clone()
    }
    pub fn start(&self) -> io::Result<()> {
        if self.recorders.is_empty() {
            Ok(())
        } else {
            Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "recorder registry must start empty",
            ))
        }
    }
    pub fn get_or_create<R: MultiRunRecorder>(
        &mut self,
        name: &str,
        factory: impl FnOnce(BufWriter<File>, SourceProvider) -> R,
    ) -> io::Result<&mut R> {
        if !self.recorders.contains_key(name) {
            let path = self.directory.join(format!("{name}.log"));
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent)?;
            }
            let sink = BufWriter::new(File::create(path)?);
            let source = self.source.clone();
            let provider: SourceProvider = Rc::new(move || source.borrow().clone());
            self.recorders
                .insert(name.into(), Box::new(factory(sink, provider)));
        }
        self.recorders
            .get_mut(name)
            .expect("inserted recorder")
            .as_any_mut()
            .downcast_mut()
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "recorder name already has another type",
                )
            })
    }
    pub fn reset(&mut self) -> io::Result<()> {
        for recorder in self.recorders.values_mut() {
            recorder.reset()?;
        }
        for recorder in self.recorders.values_mut() {
            recorder.flush()?;
        }
        Ok(())
    }
    pub fn stop(&mut self) -> io::Result<()> {
        let mut first_error = None;
        for recorder in self.recorders.values_mut() {
            if let Err(error) = recorder.stop() {
                first_error.get_or_insert(error);
            }
        }
        for recorder in self.recorders.values_mut() {
            if let Err(error) = recorder.flush() {
                first_error.get_or_insert(error);
            }
        }
        self.recorders.clear();
        first_error.map_or(Ok(()), Err)
    }
}
