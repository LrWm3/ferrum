//! Port plan: CfgTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/CfgTests.scala
//!
//! Purpose:
//! Port the upstream CfgTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! CfgTests, repeat and ordered helper.
//!
//! Behavior to preserve:
//! Translate cfgtests/determinism/if.vpr and while.vpr 100 times; every branching block must have
//! condition first and its negation second, allowing nested Not pairs; blocks may have one or zero
//! outgoing edges and all other shapes fail.
//!
//! Integration:
//! test_helpers, cfg::silver and cfg::edge.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Preserve ordered edge construction and fixture loading without making determinism test a single
//! run.
//!
//! Status: description only; implementation has not started.
