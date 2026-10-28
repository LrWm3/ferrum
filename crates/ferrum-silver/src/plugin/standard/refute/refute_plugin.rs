//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/refute/RefutePlugin.scala
//!
//! Purpose:
//! Implement refutation by lowering refute to nondeterministically reached assertions and
//! interpreting results.
//!
//! Planned Rust structure:
//! Port RefutePlugin parser, beforeParse/beforeVerify and entity/program result mappings,
//! mapVerificationResultsForNode and NodeWithRefuteInfo.
//!
//! Behavior to preserve:
//! Register keyword and end-statement parser; per method replace each Refute by a fresh local
//! nondeterministic branch containing Assert tagged RefuteInfo then synthesized inhale false.
//! Remove matching AssertFailed errors, preserve others, and add RefuteFailed for contained tagged
//! assertions without errors, matching source refute plus position. Use same mapping for entity
//! and overall results.
//!
//! Integration:
//! plugin::standard::refute::{refute_ast_extension,refute_past_extension,refute_errors}; parser,
//! ast::utility::rewriter, verifier results and reporter entities; smoke runs before refute.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for node identity, error transformations and ordered traversal.
//!
//! Open decisions:
//! Agree on tag identity, traversal and per-entity versus overall result mapping with reporter and
//! smoke.
//!
//! Status: description only; implementation has not started.
