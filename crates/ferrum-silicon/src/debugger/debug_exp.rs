//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/DebugExp.scala
//!
//! Purpose:
//! Capture and render expression-level proof context for interactive debugging.
//!
//! Planned Rust structure:
//! Port DebugExp factories/IDs, ImplicationDebugExp, QuantifiedDebugExp,
//! DebugExpPrintConfiguration and DebugAxiom, including recursive term collection and tree
//! editing.
//!
//! Behavior to preserve:
//! Simplify source/final expressions at creation, preserve ordered children and identity-based
//! visited guards; implication combines child terms under antecedent and quantified node combines
//! them under original quantifier/triggers. Printing filters internal nodes, limits depth/children
//! and supports per-ID overrides; retain all config defaults.
//!
//! Integration:
//! debugger::silicon_debugger, decider::path_conditions and evaluator/debug logging.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for stable IDs, term identity and ordered debug trees.
//!
//! Open decisions:
//! Agree on sharing and cycle-safe visitation with path conditions and debugger.
//!
//! Status: description only; implementation has not started.
