//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/TermToSMTLib2Converter.scala
//!
//! Purpose:
//! Render Silicon terms, sorts and declarations to SMT-LIB 2 text.
//!
//! Planned Rust structure:
//! TermToSMTLib2Converter implements TermConverter and StatefulComponent with sort/identifier
//! sanitation cache and render helpers for declarations, literals, quantifiers, applications,
//! arithmetic/permissions, collections, snapshot maps, wand, heap and mask terms.
//!
//! Behavior to preserve:
//! Preserve sanitizer vs raw SMT function/sort names, Unit sort for nullary signatures, negative
//! integer and exact real permission rendering, sort-specific collection equality and argument
//! order. Quantifiers omit empty trigger patterns, include qid/weight, and emit warning plus body
//! for empty binders. Render predicate arguments as snapshot tree, honor HasVarRepr alias and
//! distinct/let order; reject unsupported MagicWandChunkTerm. Reset/stop clears name cache.
//!
//! Integration:
//! state::{terms,identifiers}, decider::smtlib_name_generator, decider::prover_std_io and solver
//! preambles.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Exact serialization, source-level aliases and cache ownership.
//!
//! Status: description only; implementation has not started.
