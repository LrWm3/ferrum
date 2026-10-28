//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/io/package.scala
//!
//! Purpose:
//! Provide file writing and unique filename utilities.
//!
//! Planned Rust structure:
//! toFile, PrintWriter and makeFilenameUnique create parents, write or append and select a
//! path.
//!
//! Behavior to preserve:
//! Unique naming checks existence and increments a decimal suffix; extension separator
//! remains even for empty extension; target directory must exist and be a directory.
//!
//! Integration:
//! logging, prover and reporting file output.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Native I/O error mapping and race behavior.
//!
//! Status: description only; implementation has not started.
