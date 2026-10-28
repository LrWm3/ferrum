//! Port plan: EntityHashTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/EntityHashTests.scala
//!
//! Purpose:
//! Port the upstream EntityHashTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! EntityHashTests and sameHash helper.
//!
//! Behavior to preserve:
//! Assert domain entity hashes do not change when domain functions and named/anonymous axioms are
//! reordered, including mixed cases. Two anonymous axioms are equal; mixed examples repeat ax1
//! rather than ax0.
//!
//! Integration:
//! utility::caching::CacheHelper and ast::program.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Preserve entity hash behavior separately from ordinary ordered declaration behavior.
//!
//! Status: description only; implementation has not started.
