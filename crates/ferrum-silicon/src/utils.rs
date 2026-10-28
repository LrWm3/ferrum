//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Utils.scala
//!
//! Purpose:
//! Provide shared symbolic, AST, lifecycle and consistency helpers.
//!
//! Planned Rust structure:
//! utils package defines freshSnap/toSf, mapReduceLeft, conflictFreeUnion, append, Counter,
//! NoOpStatefulComponent, MustBeReinitializedAfterReset and NotNothing. Nested ast helpers build
//! boolean/min/quantifier expressions, rewrite range membership, trigger fallback, source
//! positions, flattening, substitution, parser type extraction and ViperEmbedding; consistency
//! checks unsupported permissions and inhale/exhale positions and constructs internal errors.
//!
//! Behavior to preserve:
//! mapReduceLeft preserves left-fold order and empty unit; conflictFreeUnion iterates only first
//! map, excluding second-only keys, an apparent mismatch with its name to reconcile. Counter is
//! non-thread-safe and clone preserves current value. Trigger fallback is not thread-safe; first
//! retain standard triggers then try add/subtract and rewriting. Permission/inhale-exhale errors
//! retain node and metadata; unexpected node errors capture stack.
//!
//! Integration:
//! state::terms, verifier, rules::{evaluator,consumer}, ferrum_silver::ast and ferrum_silver::utility
//! and frontend consistency.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Counter ownership, apparent union omission and native stack traces.
//!
//! Status: description only; implementation has not started.
