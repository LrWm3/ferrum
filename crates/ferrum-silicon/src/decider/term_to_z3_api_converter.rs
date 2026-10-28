//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/TermToZ3APIConverter.scala
//!
//! Purpose:
//! Translate Silicon terms into Z3 API objects with context-local caches.
//!
//! Planned Rust structure:
//! TermToZ3APIConverter owns Z3 context, sort/function/SMT-function/term caches, macro map and lazy
//! Snap datatype constructors; convert sorts, declarations, identifiers and term families, plus
//! typed casts and SMT parse workarounds.
//!
//! Behavior to preserve:
//! Create Snap datatype lazily, filter Unit from function arguments; use native
//! arithmetic/permission operations and collection/snapshot-map functions. Expand macros by
//! substitution, translate let by substitution, preserve quantifier patterns/name/weight and use
//! body directly when binders are empty. SMT builtins/sorts use parse-based discovery and cache
//! signatures. Generic convert(decl), Unit sort and SMT sort symbol conversion are upstream
//! unimplemented; source has no mask-heap sort/term dispatch and lacks MagicWandSnapshot case, so
//! track these limitations rather than claiming parity with stdio. Reset clears context references,
//! constructors and all caches; term keys follow configured term identity semantics.
//!
//! Integration:
//! decider::z3_prover_api, decider::term_to_smt_lib2_converter, state::{terms,identifiers} and
//! interfaces::decider::term_converter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Native solver context lifetime, cache identity and explicit missing upstream paths.
//!
//! Status: description only; implementation has not started.
