//! Ferrum general logger assembly described in PLAN.md.
//! Source: [Silicon.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Silicon.scala) and the pinned Logback configuration.
//! Public log flags remain gated until source event coverage is complete.
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use std::{collections::BTreeMap, sync::Arc};

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
    /// Logback Level.toLevel defaults unknown names to DEBUG.
    pub fn from_source(s: &str) -> Self {
        match s.to_ascii_uppercase().as_str() {
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
}
/// A sink receives one message at a time; the standard source appender writes `%msg%n`.
pub trait Sink: Send + Sync {
    fn write(&self, message: &str);
}
pub struct StdoutSink;
impl Sink for StdoutSink {
    fn write(&self, message: &str) {
        println!("{message}");
    }
}
#[derive(Clone)]
pub struct GeneralLogger {
    levels: BTreeMap<String, Level>,
    sink: Arc<dyn Sink>,
}
impl GeneralLogger {
    pub fn new(
        package_level: Option<&str>,
        named: &BTreeMap<String, String>,
        sink: Arc<dyn Sink>,
    ) -> Self {
        let mut levels = BTreeMap::new();
        levels.insert(String::new(), Level::Info);
        if let Some(level) = package_level {
            let level = Level::from_source(level);
            levels.insert("viper.silicon".into(), level);
            levels.insert("SiliconFrontend".into(), level);
        }
        for (name, level) in named {
            levels.insert(
                if name.eq_ignore_ascii_case("ROOT") {
                    String::new()
                } else {
                    name.clone()
                },
                Level::from_source(level),
            );
        }
        Self { levels, sink }
    }
    pub fn enabled(&self, name: &str, level: Level) -> bool {
        let mut current = name;
        loop {
            if let Some(threshold) = self.levels.get(current) {
                return level >= *threshold && *threshold != Level::Off;
            }
            match current.rsplit_once('.') {
                Some((parent, _)) => current = parent,
                None => current = "",
            }
        }
    }
    pub fn emit(&self, name: &str, level: Level, message: impl FnOnce() -> String) {
        if self.enabled(name, level) {
            self.sink.write(&message());
        }
    }
    /// Source DefaultMainVerifier reports exceptions before rethrowing them.
    pub fn entity_exception(&self, kind: &str, name: Option<&str>) {
        self.emit(
            "viper.silicon.verifier.DefaultMainVerifier-00",
            Level::Error,
            || match name {
                Some(name) => format!("An exception was thrown while verifying {kind} `{name}`."),
                None => "An exception was thrown while verifying a cfg.".into(),
            },
        );
    }
    /// Source DefaultMainVerifier.emitStaticPreamble, called after entering its preamble.
    pub fn configuration_options(&self, options: &BTreeMap<String, String>) {
        if let Some(message) = configuration_message(options) {
            self.emit(
                "viper.silicon.verifier.DefaultMainVerifier-00",
                Level::Info,
                || message,
            );
        }
    }
}
/// The source uses Scala map iteration order; the native parsed config is a BTreeMap.
pub fn configuration_message(options: &BTreeMap<String, String>) -> Option<String> {
    (!options.is_empty()).then(|| {
        format!(
            "Additional prover configuration options are '{}'",
            options
                .iter()
                .map(|(k, v)| format!("({k},{v})"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;
    #[derive(Default)]
    struct Capture(Mutex<Vec<String>>);
    impl Sink for Capture {
        fn write(&self, m: &str) {
            self.0.lock().unwrap().push(m.into());
        }
    }
    #[test]
    fn inherited_named_levels_and_real_preamble_event() {
        let sink = Arc::new(Capture::default());
        let mut named = BTreeMap::new();
        named.insert("viper.silicon.verifier".into(), "OFF".into());
        let logger = GeneralLogger::new(Some("DEBUG"), &named, sink.clone());
        assert!(logger.enabled("viper.silicon.rules.Executor", Level::Debug));
        assert!(!logger.enabled(
            "viper.silicon.verifier.DefaultMainVerifier-00",
            Level::Error
        ));
        logger.configuration_options(&BTreeMap::from([("smt.test".into(), "true".into())]));
        assert!(sink.0.lock().unwrap().is_empty());
        let logger = GeneralLogger::new(Some("INFO"), &BTreeMap::new(), sink.clone());
        logger.configuration_options(&BTreeMap::from([("smt.test".into(), "true".into())]));
        assert_eq!(
            *sink.0.lock().unwrap(),
            ["Additional prover configuration options are '(smt.test,true)'"]
        );
        logger.entity_exception("function", Some("f"));
        assert_eq!(
            sink.0.lock().unwrap().last().unwrap(),
            "An exception was thrown while verifying function `f`."
        );
        assert_eq!(Level::from_source("invalid"), Level::Debug);
    }
}
