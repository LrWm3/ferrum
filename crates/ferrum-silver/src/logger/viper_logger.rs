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
//! Status: description only; implementation has not started.
