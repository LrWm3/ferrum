//! Port plan: Dispatch structured messages to configured sinks.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/reporter/Reporter.scala
//!
//! Purpose:
//! Dispatch structured messages to configured sinks.
//!
//! Planned Rust structure:
//! Reporter, NoopReporter, ConfigurableReporter, PluginAwareReporter, CSVReporter, StdIOReporter
//! and PollingReporter.
//!
//! Behavior to preserve:
//! Plugin-aware report maps entity successes/failures through plugins before dispatch, but leaves
//! overall results alone. CSV appends and flushes per report, escaping multiline verifier state;
//! stdout has timeInfo and reportPartialResults branches, warning and exception handling. Polling
//! enqueue and pass-through happen under synchronization; dequeue on empty is an error.
//!
//! Integration:
//! reporter::{message,format}, frontend::sil_frontend, plugin manager and verifier results.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile sink lifetimes, synchronized queue and plugin callback ordering with frontend and
//! Silicon reporting.
//!
//! Status: partial; noop, plugin mapping, polling and core CSV cases implemented.
//! StdIO lifecycle output is implemented; remaining CSV and StdIO event renderers are pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::message::Message;
use super::package::Entity;
use crate::verifier::verification_result::{DiagnosticError, VerificationResult};
use std::collections::VecDeque;
use std::io::{self, Write};
use std::sync::{Arc, Mutex, RwLock};

#[derive(Debug)]
pub enum ReportError {
    Io(io::Error),
    Diagnostic(DiagnosticError),
    EmptyQueue,
    Plugin(String),
    Unsupported(&'static str),
}
impl From<io::Error> for ReportError {
    fn from(value: io::Error) -> Self {
        Self::Io(value)
    }
}
impl From<DiagnosticError> for ReportError {
    fn from(value: DiagnosticError) -> Self {
        Self::Diagnostic(value)
    }
}

pub trait Reporter: Send + Sync {
    fn name(&self) -> &str;
    fn report(&self, message: Message) -> Result<(), ReportError>;
}
#[derive(Default)]
pub struct NoopReporter;
impl Reporter for NoopReporter {
    fn name(&self) -> &str {
        "NoopReporter"
    }
    fn report(&self, _: Message) -> Result<(), ReportError> {
        Ok(())
    }
}
/// Plugin result mapping is invoked only for entity success and failure, never overall results.
pub trait EntityResultMapper: Send + Sync {
    fn map_entity_result(
        &self,
        entity: &Entity,
        result: VerificationResult,
    ) -> Result<VerificationResult, ReportError>;
}
pub struct PluginAwareReporter {
    pub name: String,
    pub target: Arc<dyn Reporter>,
    pub mapper: RwLock<Option<Arc<dyn EntityResultMapper>>>,
}
impl Reporter for PluginAwareReporter {
    fn name(&self) -> &str {
        &self.name
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        let mapper = self
            .mapper
            .read()
            .expect("poisoned reporter plugin lock")
            .clone();
        let message = if let Some(mapper) = mapper {
            match message {
                Message::EntitySuccess {
                    verifier,
                    concerning,
                    time,
                    cached,
                } => {
                    let result =
                        mapper.map_entity_result(&concerning, VerificationResult::Success)?;
                    Message::entity_result(verifier, concerning, time, result, cached)
                }
                Message::EntityFailure {
                    verifier,
                    concerning,
                    time,
                    errors,
                    cached,
                } => {
                    let result = mapper
                        .map_entity_result(&concerning, VerificationResult::Failure(errors))?;
                    Message::entity_result(verifier, concerning, time, result, cached)
                }
                other => other,
            }
        } else {
            message
        };
        self.target.report(message)
    }
}
/// Queue insertion and pass-through execute while holding the same lock, matching source ordering.
pub struct PollingReporter {
    pub name: String,
    pub pass_through: Arc<dyn Reporter>,
    messages: Mutex<VecDeque<Message>>,
}
impl PollingReporter {
    pub fn new(pass_through: Arc<dyn Reporter>) -> Self {
        Self {
            name: "polling_reporter".into(),
            pass_through,
            messages: Mutex::new(VecDeque::new()),
        }
    }
    pub fn has_new_message(&self) -> bool {
        !self
            .messages
            .lock()
            .expect("poisoned reporter queue")
            .is_empty()
    }
    pub fn get_new_message(&self) -> Result<Message, ReportError> {
        self.messages
            .lock()
            .expect("poisoned reporter queue")
            .pop_front()
            .ok_or(ReportError::EmptyQueue)
    }
}
impl Reporter for PollingReporter {
    fn name(&self) -> &str {
        &self.name
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        let mut messages = self.messages.lock().expect("poisoned reporter queue");
        messages.push_back(message.clone());
        self.pass_through.report(message)
    }
}
/// Writes the core lifecycle and entity records in source CSV order and flushes each report.
/// Other message families fail explicitly until their source renderers are available.
pub struct CsvReporter<W: Write + Send> {
    pub name: String,
    writer: Mutex<W>,
}
impl<W: Write + Send> CsvReporter<W> {
    pub fn new(writer: W) -> Self {
        Self {
            name: "csv_reporter".into(),
            writer: Mutex::new(writer),
        }
    }
}
impl CsvReporter<std::fs::File> {
    pub fn open(path: impl AsRef<std::path::Path>) -> io::Result<Self> {
        Ok(Self::new(
            std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)?,
        ))
    }
}
impl<W: Write + Send> Reporter for CsvReporter<W> {
    fn name(&self) -> &str {
        &self.name
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        let mut writer = self.writer.lock().expect("poisoned CSV reporter");
        match message {
            Message::AstConstructionFailure { time, .. } => {
                writeln!(writer, "AstConstructionFailureMessage,{time}")?
            }
            Message::AstConstructionSuccess { time } => {
                writeln!(writer, "AstConstructionSuccessMessage,{time}")?
            }
            Message::OverallFailure { time, .. } => {
                writeln!(writer, "OverallFailureMessage,{time}")?
            }
            Message::OverallSuccess { time, .. } => {
                writeln!(writer, "OverallSuccessMessage,{time}")?
            }
            Message::EntitySuccess {
                concerning,
                time,
                cached,
                ..
            } => writeln!(
                writer,
                "EntitySuccessMessage,{},{}, {}",
                concerning.name(),
                time,
                cached
            )?,
            Message::EntityFailure {
                concerning,
                time,
                cached,
                ..
            } => writeln!(
                writer,
                "EntityFailureMessage,{},{}, {}",
                concerning.name(),
                time,
                cached
            )?,
            Message::BranchFailure {
                concerning, cached, ..
            } => writeln!(
                writer,
                "BranchFailureMessage,{},{}",
                concerning.name(),
                cached
            )?,
            Message::WarningsDuringParsing { warnings } => {
                for warning in warnings {
                    writeln!(writer, "WarningsDuringParsing,{warning}")?;
                }
            }
            Message::InvalidArguments { errors, .. } => {
                for error in errors {
                    writeln!(writer, "WarningsDuringParsing,{}", error.render()?)?;
                }
            }
            Message::Simple {
                kind: super::message::SimpleMessageKind::AnnotationWarning,
                text,
            } => writeln!(writer, "AnnotationWarning,{text}")?,
            Message::Simple { .. }
            | Message::BackendSubProcess { .. }
            | Message::Benchmarking { .. } => {}
            _ => {
                return Err(ReportError::Unsupported(
                    "CSV formatting for this message is not yet implemented",
                ));
            }
        }
        writer.flush()?;
        Ok(())
    }
}

/// Console lifecycle and diagnostics reporting; source entity rendering is pending.
pub struct StdIoReporter<W: Write + Send> {
    pub name: String,
    pub time_info: bool,
    pub report_partial_results: bool,
    writer: Mutex<W>,
    counter: std::sync::atomic::AtomicI32,
}
impl<W: Write + Send> StdIoReporter<W> {
    pub fn new(writer: W, time_info: bool) -> Self {
        Self {
            name: "stdout_reporter".into(),
            time_info,
            report_partial_results: false,
            writer: Mutex::new(writer),
            counter: std::sync::atomic::AtomicI32::new(0),
        }
    }
    pub fn counter(&self) -> i32 {
        self.counter.load(std::sync::atomic::Ordering::Relaxed)
    }
    fn time(&self, millis: i64) -> Result<String, ReportError> {
        super::format::package::format_millis_readably(millis)
            .map_err(|_| ReportError::Unsupported("timestamp outside chrono range"))
    }
}
impl<W: Write + Send> Reporter for StdIoReporter<W> {
    fn name(&self) -> &str {
        &self.name
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        use super::message::SimpleMessageKind;
        let mut writer = self.writer.lock().expect("poisoned stdout reporter");
        match message {
            Message::AstConstructionSuccess { time } => {
                if self.time_info {
                    writeln!(
                        writer,
                        "the file represents a consistent Viper program; constructed AST in {}.",
                        self.time(time)?
                    )?;
                } else {
                    writeln!(writer, "the file represents a consistent Viper program.")?;
                }
            }
            Message::AstConstructionFailure { time, errors } => {
                let n = errors.len();
                let suffix = if n == 1 { "" } else { "s" };
                if self.time_info {
                    writeln!(
                        writer,
                        "AST construction resulted in {n} error{suffix} in {}:",
                        self.time(time)?
                    )?;
                } else {
                    writeln!(writer, "AST construction resulted in {n} error{suffix}:")?;
                }
                let width = n.to_string().len();
                for (i, error) in errors.iter().enumerate() {
                    writeln!(writer, "  [{i:>width$}] {}", error.readable_message()?)?;
                }
            }
            Message::OverallSuccess { verifier, time } => {
                if self.time_info {
                    writeln!(
                        writer,
                        "{verifier} finished verification successfully in {}.",
                        self.time(time)?
                    )?;
                } else {
                    writeln!(writer, "{verifier} finished verification successfully.")?;
                }
            }
            Message::OverallFailure {
                verifier,
                time,
                errors,
            } => {
                let n = errors.len();
                let suffix = if n == 1 { "" } else { "s" };
                if self.time_info {
                    writeln!(
                        writer,
                        "{verifier} found {n} error{suffix} in {}:",
                        self.time(time)?
                    )?;
                } else {
                    writeln!(writer, "{verifier} found {n} error{suffix}:")?;
                }
                let width = n.to_string().len();
                for (i, error) in errors.iter().enumerate() {
                    writeln!(writer, "  [{i:>width$}] {}", error.readable_message()?)?;
                }
            }
            Message::WarningsDuringParsing { warnings } => {
                for warning in warnings {
                    writeln!(writer, "{warning}")?;
                }
            }
            Message::InvalidArguments { errors, .. } => {
                for error in errors {
                    writeln!(writer, "  {}", error.readable_message()?)?;
                }
                writeln!(writer, "Run with just --help for usage and options")?;
            }
            Message::Simple {
                kind: SimpleMessageKind::AnnotationWarning,
                text,
            } => writeln!(writer, "Annotation warning: {text}")?,
            Message::Simple {
                kind: SimpleMessageKind::Copyright,
                text,
            } => writeln!(writer, "{text}")?,
            Message::Simple {
                kind: SimpleMessageKind::MissingDependency,
                text,
            } => writeln!(writer, "encountered missing dependency: {text}")?,
            Message::EntitySuccess { .. }
            | Message::EntityFailure { .. }
            | Message::BranchFailure { .. }
                if self.report_partial_results =>
            {
                return Err(ReportError::Unsupported(
                    "entity message source rendering is not yet implemented",
                ));
            }
            Message::EntitySuccess { .. }
            | Message::EntityFailure { .. }
            | Message::BranchFailure { .. }
            | Message::Simple { .. }
            | Message::BackendSubProcess { .. }
            | Message::QuantifierInstantiations { .. }
            | Message::QuantifierChosenTriggers { .. }
            | Message::BlockReached { .. }
            | Message::BlockFailure { .. }
            | Message::PathProcessed { .. }
            | Message::VerificationTermination
            | Message::Benchmarking { .. } => {}
            _ => {
                return Err(ReportError::Unsupported(
                    "stdout formatting for this message is not yet implemented",
                ));
            }
        }
        self.counter
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::message::SimpleMessageKind;
    use super::*;
    #[test]
    fn polling_preserves_order_and_reports_empty_queue() {
        let reporter = PollingReporter::new(Arc::new(NoopReporter));
        for text in ["first", "second"] {
            reporter
                .report(Message::Simple {
                    kind: SimpleMessageKind::Simple,
                    text: text.into(),
                })
                .unwrap();
        }
        for expected in ["first", "second"] {
            let Message::Simple { text, .. } = reporter.get_new_message().unwrap() else {
                panic!("simple event")
            };
            assert_eq!(text, expected);
        }
        assert!(matches!(
            reporter.get_new_message(),
            Err(ReportError::EmptyQueue)
        ));
    }
}
