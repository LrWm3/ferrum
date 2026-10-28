//! Port plan: Create lazily initialized named loggers.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/logger/ViperLogger.scala
//!
//! Purpose:
//! Create lazily initialized named loggers.
//!
//! Planned Rust structure:
//! ViperLogger and file, stdout and silent factories; lazy get, synchronized logger lookup and
//! encoder setup.
//!
//! Behavior to preserve:
//! File logs include date/level/thread/logger/file/line, stdout uses message only; default ERROR,
//! silent OFF, non-additive logger and source level conversion. Initialization uses synchronized
//! lookup and adds an appender.
//!
//! Integration:
//! Silver and Silicon logging clients and configuration.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Choose Rust logging sinks and lifecycle while preserving level, destination and concurrency
//! semantics.
//!
//! Status: partial; lazy shared logger, levels and stdout/file sinks are implemented.
//! Exact Logback abbreviation, internal error handling and integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use chrono::Local;
use std::collections::HashMap;
use std::io::{self, Write};
use std::sync::{Arc, Mutex, OnceLock};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Level {
    All,
    Trace,
    Debug,
    Info,
    Warn,
    Error,
    Off,
}
impl Level {
    pub fn parse(value: &str) -> Self {
        match value.to_ascii_uppercase().as_str() {
            "ALL" => Self::All,
            "TRACE" => Self::Trace,
            "DEBUG" => Self::Debug,
            "INFO" => Self::Info,
            "WARN" => Self::Warn,
            "ERROR" => Self::Error,
            "OFF" => Self::Off,
            _ => Self::Debug,
        }
    }
    fn label(self) -> &'static str {
        match self {
            Self::All => "ALL",
            Self::Trace => "TRACE",
            Self::Debug => "DEBUG",
            Self::Info => "INFO",
            Self::Warn => "WARN",
            Self::Error => "ERROR",
            Self::Off => "OFF",
        }
    }
}
enum Sink {
    Stdout,
    File(std::fs::File),
}
struct LoggerState {
    level: Level,
    sinks: Vec<Sink>,
}
pub struct Logger {
    pub name: String,
    state: Mutex<LoggerState>,
}
impl Logger {
    /// Call-site filename and line are supplied by the logging caller.
    pub fn log(&self, level: Level, message: &str, file: &str, line: u32) -> io::Result<()> {
        let mut state = self.state.lock().expect("poisoned logger");
        if state.level == Level::Off || level < state.level || level == Level::Off {
            return Ok(());
        }
        let date = Local::now().format("%Y-%m-%d %H:%M:%S,%3f");
        let thread = std::thread::current();
        let thread = thread.name().unwrap_or("unnamed");
        let abbreviated = abbreviate_logger(&self.name, 10);
        for sink in &mut state.sinks {
            match sink {
                Sink::Stdout => {
                    let mut out = io::stdout().lock();
                    writeln!(out, "{message}")?;
                }
                Sink::File(out) => writeln!(
                    out,
                    "{date} {} [{thread}] {abbreviated} [{file}:{line}] {message}",
                    level.label()
                )?,
            }
        }
        Ok(())
    }
}
fn abbreviate_logger(name: &str, limit: usize) -> String {
    if name.len() <= limit {
        return name.into();
    }
    let parts: Vec<&str> = name.split('.').collect();
    if parts.len() < 2 {
        return name.into();
    }
    let mut result = name.to_owned();
    let mut reduced = Vec::new();
    for (index, part) in parts.iter().enumerate() {
        if index + 1 < parts.len() && result.len() > limit && part.chars().count() > 1 {
            reduced.push(part.chars().next().unwrap().to_string());
        } else {
            reduced.push((*part).to_owned());
        }
        result = reduced
            .iter()
            .map(String::as_str)
            .chain(parts[index + 1..].iter().copied())
            .collect::<Vec<_>>()
            .join(".");
    }
    result
}
fn registry() -> &'static Mutex<HashMap<String, Arc<Logger>>> {
    static REGISTRY: OnceLock<Mutex<HashMap<String, Arc<Logger>>>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(HashMap::new()))
}
/// Each factory lazily attaches one sink to the process-global logger of the same name.
pub struct ViperLogger {
    pub name: String,
    pub file: Option<String>,
    pub level: String,
    logger: OnceLock<Result<Arc<Logger>, String>>,
}
impl ViperLogger {
    pub fn new(name: impl Into<String>, file: Option<String>, level: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            file,
            level: level.into(),
            logger: OnceLock::new(),
        }
    }
    pub fn file(name: impl Into<String>, file: impl Into<String>) -> Self {
        Self::new(name, Some(file.into()), "ERROR")
    }
    pub fn stdout(name: impl Into<String>, level: impl Into<String>) -> Self {
        Self::new(name, None, level)
    }
    pub fn silent() -> Self {
        Self::new("", None, "OFF")
    }
    pub fn get(&self) -> Result<Arc<Logger>, String> {
        self.logger
            .get_or_init(|| {
                let logger = {
                    let mut entries = registry().lock().expect("poisoned logger registry");
                    entries
                        .entry(self.name.clone())
                        .or_insert_with(|| {
                            Arc::new(Logger {
                                name: self.name.clone(),
                                state: Mutex::new(LoggerState {
                                    level: Level::Debug,
                                    sinks: Vec::new(),
                                }),
                            })
                        })
                        .clone()
                };
                let sink = match &self.file {
                    Some(path) => Sink::File(
                        std::fs::OpenOptions::new()
                            .append(true)
                            .create(true)
                            .open(path)
                            .map_err(|e| e.to_string())?,
                    ),
                    None => Sink::Stdout,
                };
                let mut state = logger.state.lock().expect("poisoned logger");
                state.sinks.push(sink);
                state.level = Level::parse(&self.level);
                drop(state);
                Ok(logger)
            })
            .clone()
    }
}
