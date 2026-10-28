//! Port plan: SingleFileSilSuite.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/SingleFileSilSuite.scala
//!
//! Purpose:
//! Port the upstream SingleFileSilSuite.scala test or test-harness component.
//!
//! Planned Rust structure:
//! SingleFileSilSuite frontend overload and buildTestInput.
//!
//! Behavior to preserve:
//! Read the sole input file and call string frontend; reject zero or multiple files. Force input
//! files to one file even when generic grouping would discover several.
//!
//! Integration:
//! sil_suite, test_input and frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Coordinate text decoding and file lifetime with test harness.
//!
//! Status: description only; implementation has not started.
