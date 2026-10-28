//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Silicon.scala
//!
//! Purpose:
//! Expose the backend lifecycle, frontend adapters and command-line runner.
//!
//! Planned Rust structure:
//! Silicon companion supplies metadata/dependencies and partial argument construction; Silicon
//! implements parseCommandLine/start/reset/stop/verify and failure sorting, logging and exception
//! conversion. SiliconFrontend, SiliconFrontendAPI, MinimalSiliconFrontendAPI, SiliconRunner and
//! SiliconRunnerInstance connect Silver frontend and CLI.
//!
//! Behavior to preserve:
//! Enforce instantiated/configured/started/running lifecycle; repeated verify resets verifier.
//! Always perform Silicon utils.consistency.check on program before backend execution, even when
//! minimal frontend omits its frontend consistency phase. Run verifier in executor with optional
//! seconds timeout; timeout closes log and returns timeout failure, exceptions convert unless
//! disabled, errors rethrow, executor shutdown runs finally. Sort failures by transformed source
//! position. Frontend starts only after valid configuration; runner stops verifier in finally and
//! exits zero only on verified success. Preserve dummy/ignore filename behavior, reporter output
//! and configured logging.
//!
//! Integration:
//! verifier::default_main_verifier, config, utils::consistency, reporting, logger and
//! ferrum_silver::frontend and ferrum_silver::verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Cancellation, verifier reuse and native API/frontend lifecycle.
//!
//! Status: description only; implementation has not started.
