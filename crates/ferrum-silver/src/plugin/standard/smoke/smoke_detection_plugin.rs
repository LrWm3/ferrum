//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/smoke/SmokeDetectionPlugin.scala
//!
//! Purpose:
//! Insert refute-false probes to detect inconsistent specifications, excluding marked unreachable
//! paths.
//!
//! Planned Rust structure:
//! Port SmokeDetectionPlugin parser, beforeParse/beforeVerify, appendRefuteFalse/refuteFalse and
//! CFG reachability collection, plus SmokeDetectionInfo.
//!
//! Behavior to preserve:
//! Add probes at method ends, after nonsynthesized inhales, loop ends, nonempty branches and
//! before nonsynthesized gotos; preserve generated ID behavior and synthesized markers. Build
//! unsimplified CFG, track seen and reachable probe IDs, propagate unreachable through joins only
//! when all branches are unreachable, remove seen-but-unreachable probes and all Unreachable
//! markers. Refute plugin must run afterwards.
//!
//! Integration:
//! plugin::standard::refute::refute_plugin and refute_ast_extension; cfg::silver, parser and
//! ast::utility::rewriter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for node identity, CFG ordering and source metadata.
//!
//! Open decisions:
//! Reconcile CFG traversal/joins and ID reuse for method-end probes with cfg and refute; do not
//! silently repair upstream behavior.
//!
//! Status: description only; implementation has not started.
