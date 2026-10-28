//! Port plan: RegexTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/RegexTests.scala
//!
//! Purpose:
//! Port the upstream RegexTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! RegexTests using tree regex builders and FileComparisonHelper.
//!
//! Behavior to preserve:
//! Check shared node context matching; compare transformation fixtures for
//! disjunction-to-inhale/exhale, complex matching, implication-to-disjunction, while-to-goto,
//! assertion merging, sibling access, method-call desugaring and copy propagation; presentation
//! slide matcher and BinomialHeap traversal also run. Sort variable names in NonDet workaround
//! before comparing reference files.
//!
//! Integration:
//! ast::utility::rewriter::{t_regex,regex_strategy}, viper_strategy, test_helpers and
//! transformations fixtures.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Preserve sharing/context and actual source nondeterminism workaround; investigate
//! child-selector semantics.
//!
//! Status: description only; implementation has not started.
