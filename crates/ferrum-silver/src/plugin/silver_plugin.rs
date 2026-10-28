//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/SilverPlugin.scala
//!
//! Purpose:
//! Define the plugin lifecycle hooks and accumulated transformation errors.
//!
//! Planned Rust structure:
//! Represent IOAwarePlugin and SilverPlugin, including beforeParse, beforeResolve,
//! beforeTranslate, beforeMethodFilter, beforeVerify, entity/result mappings, beforeFinish and
//! reportError.
//!
//! Behavior to preserve:
//! Default hooks return input unchanged. Entity and program result mapping occur only after
//! verification; beforeFinish also handles earlier failures. reportError appends unless an equal
//! error at the same position already exists.
//!
//! Integration:
//! plugin::silver_plugin_manager folds hooks; frontend::sil_frontend, parser::fast_parser and
//! reporter::reporter supply lifecycle and data.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, diagnostics and native plugin registration; pass
//! IO services explicitly.
//!
//! Open decisions:
//! Reconcile plugin instance ownership, mutable errors and callbacks with silver_plugin_manager
//! and frontend.
//!
//! Status: description only; implementation has not started.
