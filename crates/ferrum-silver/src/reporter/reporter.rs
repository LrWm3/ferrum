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
//! Status: description only; implementation has not started.
