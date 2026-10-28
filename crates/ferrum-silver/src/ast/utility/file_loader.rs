//! Port plan: Load textual source content through an injectable loader.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/FileLoader.scala
//!
//! Purpose:
//! Load textual source content through an injectable loader.
//!
//! Planned Rust structure:
//! FileLoader.loadContent and DiskLoader implementation/object.
//!
//! Behavior to preserve:
//! DiskLoader opens the given path, reads its complete text with managed closing, and returns
//! failure in Try rather than a successful empty string.
//!
//! Integration:
//! parser and other source loaders use filesystem paths and the loader abstraction.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Decide Rust text encoding and error type with parser file handling while retaining IO
//! failure and cleanup.
//!
//! Status: description only; implementation has not started.
