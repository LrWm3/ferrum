//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/SilFrontEndConfig.scala
//!
//! Purpose:
//! Define shared command-line options, validation and counterexample selection.
//!
//! Planned Rust structure:
//! Model SilFrontendConfig and CounterexampleModel variants Native, Variables, Mapped, Resolved
//! and Raw; expose parser, file validation and error handling.
//!
//! Behavior to preserve:
//! Preserve defaults and visibility for parseOnly, dependencies, no-timing, select, ignoreFile,
//! caching, IDE, smoke, plugins, termination/ADT, permission options, submission and partial
//! results. Validate readable file unless ignored; help/version exit and parse errors remain
//! distinct; unsupported model is rejected.
//!
//! Integration:
//! frontend::sil_frontend configures verifier and plugin manager; reporter consumes errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Choose CLI parser and extendable backend configuration with verifier and sil_frontend.
//!
//! Status: description only; implementation has not started.
