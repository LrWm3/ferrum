//! Port plan: DomainInstanceTest.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/DomainInstanceTest.scala
//!
//! Purpose:
//! Port the upstream DomainInstanceTest.scala test or test-harness component.
//!
//! Planned Rust structure:
//! DomainInstanceTest and MockSilFrontend fixture translation.
//!
//! Behavior to preserve:
//! Construct basic D[Int] program expecting three ground types; all/domains/domains2.vpr expects
//! no D1, one all-Int D10 and 256 D10 instances; domains_threshold.vpr expects eight. The first
//! fixture silently does nothing on translation failure; other historical assertions are commented
//! out.
//!
//! Integration:
//! ast::utility::domain_instances, ast::program and test_helpers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Decide how to expose source silent failure while retaining actual coverage and threshold
//! assumptions.
//!
//! Status: description only; implementation has not started.
