//! Port plan: IOTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/IOTests.scala
//!
//! Purpose:
//! Port the upstream IOTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! IOTests, runOneCombo and MockIOFrontend/Verifier/Config.
//!
//! Behavior to preserve:
//! Capture stdout for all/basic/let.vpr and missing path; check invalid options,
//! parseOnly/version, dependencies, missing plugin, success and one-error failure. The reuse test
//! invokes several fresh runOneCombo frontends; no-timing assertion is commented out. Mock
//! verifier explicitly supplies Success or Failure.
//!
//! Integration:
//! frontend, reporter, verifier and resource fixtures.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Coordinate output capture and CLI/config behavior with frontend; do not count the disabled
//! no-timing case as coverage.
//!
//! Status: description only; implementation has not started.
