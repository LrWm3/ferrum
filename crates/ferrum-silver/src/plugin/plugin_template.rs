//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/PluginTemplate.scala
//!
//! Purpose:
//! Document a skeleton for plugin authors showing all hook contracts.
//!
//! Planned Rust structure:
//! Account for PluginTemplate and each corresponding SilverPlugin hook, including transformation,
//! reporting and result hooks.
//!
//! Behavior to preserve:
//! The source is a copyable example whose methods are unimplemented; default SilverPlugin hooks
//! instead pass through. beforeFinish also runs on failures before verification, whereas result
//! mappings require verification.
//!
//! Integration:
//! plugin::silver_plugin and silver_plugin_manager; frontend::sil_frontend calls the lifecycle.
//!
//! Rust adaptations:
//! Follow porting/conventions.md; express the example as documentation or a native example without
//! executable success placeholders.
//!
//! Open decisions:
//! Decide where the native plugin example belongs once registration and public APIs are settled.
//!
//! Status: description only; implementation has not started.
