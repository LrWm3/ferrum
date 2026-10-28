//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/SilverPluginManager.scala
//!
//! Purpose:
//! Construct ordered plugins and apply their transformations at each pipeline boundary.
//!
//! Planned Rust structure:
//! Represent SilverPluginManager, foldWithError, hook and result mapping methods,
//! resolveAll/resolve and plugin construction errors.
//!
//! Behavior to preserve:
//! foldWithError runs in declaration order and stops at first plugin with errors, appending those
//! errors; result hooks fold all plugins in order. Colon-separated class names retain duplicates
//! and ordering. Upstream reflection tries four-argument constructor then no-argument constructor
//! and distinguishes missing, wrong type and wrong arguments.
//!
//! Integration:
//! plugin::silver_plugin, frontend::sil_frontend, parser::fast_parser and reporter::reporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md; replace JVM reflection with a native registration mechanism
//! while preserving failure distinctions.
//!
//! Open decisions:
//! Agree on native registration and instance/service lifetimes with frontend and bundled plugins.
//!
//! Status: description only; implementation has not started.
