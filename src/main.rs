//! Upstream:
//! Ferrum-owned CLI assembly described in PLAN.md. Runner behavior is referenced from:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Silicon.scala
//!
//! Purpose:
//! Provide the ferrum executable that configures and runs the native verification pipeline.
//!
//! Planned Rust structure:
//! Keep main as argument capture, reporter/logging setup, facade invocation and exit handling.
//! Model SiliconRunnerInstance.runMain's orchestration through the library session, leaving
//! option definitions in ferrum_silicon::config and frontend phases in Silver.
//!
//! Behavior to preserve:
//! Preserve help/version/configuration handling, diagnostic delivery, source loading and
//! verification result interpretation. Upstream starts with failure exit status and changes it
//! only after reaching verification successfully; keep this distinction from merely parsing
//! input. Ensure cleanup on normal results, failures, exceptions and timeouts. Preserve optional
//! submission/reporting hooks only according to their explicit configuration and native design.
//!
//! Integration:
//! src/lib.rs, ferrum_silicon::{silicon,config}, ferrum_silver::{frontend,reporter,logger},
//! and solver dependency discovery through Silicon's decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for replacing JVM startup and exception handling with native
//! lifecycle/result handling. Exact CLI parsing and logging libraries are not chosen here.
//!
//! Open decisions:
//! Reconcile CLI compatibility, intentional Ferrum naming, signal cancellation and help/version
//! exit behavior with the configuration port; record adopted differences before implementation.
//!
//! Status: description only; implementation has not started.
