//! Port plan: RewriterTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/RewriterTests.scala
//!
//! Purpose:
//! Port the upstream RewriterTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! RewriterTests and FileComparisonHelper-based strategies.
//!
//! Behavior to preserve:
//! Test shared-node context and parse binary operator rewrite; compare quantified permission,
//! disjunction, implication, while, assertion merging, constant folding, sibling, method
//! desugaring and copy propagation fixtures. Count additions 3/10/12; verify conditional and
//! repeated strategy composition. Referential-equality regression rewrites both structurally equal
//! assignments without infinite recursion; BinomialHeap is a traversal smoke case.
//!
//! Integration:
//! ast::utility::{viper_strategy,rewriter}, parser and transformations fixtures.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Reconcile reference identity/noRec, context, copy/metadata and expected printed fixture
//! comparisons.
//!
//! Status: description only; implementation has not started.
