//! Port plan: PluginTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/PluginTests.scala
//!
//! Purpose:
//! Port the upstream PluginTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! PluginTests, TestPlugin variants, FakeResult and mock frontend/verifier/config.
//!
//! Behavior to preserve:
//! Run plugintests/plugininput.vpr with six plugins: imported vs primary parsing, early reported
//! error, ordered lifecycle hooks, predicate injection before resolve, mapped errors, and abort
//! before translate with beforeFinish. Check loaded plugin count and each plugin test state; mock
//! verifier selects Success or injected failure.
//!
//! Integration:
//! plugin manager, frontend, parser, reporter and verifier errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Replace reflection-based test plugin registration consistently with native plugin design,
//! preserving hook and error order.
//!
//! Status: description only; implementation has not started.
