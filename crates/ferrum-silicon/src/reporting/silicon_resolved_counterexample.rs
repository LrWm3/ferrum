//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/SiliconResolvedCounterexample.scala
//!
//! Purpose:
//! Build raw and AST-resolved counterexamples from model, store and current/old heaps.
//!
//! Planned Rust structure:
//! Port SiliconRawCounterexample and SiliconResolvedCounterexample plus detBasicVariables,
//! collection seeding/fixpoint operations, heap/quantified extraction, predicate snapshot
//! traversal, function/domain mapping and name resolution helpers.
//!
//! Behavior to preserve:
//! Reconstruct sequences, sets, multisets and maps from model operations and available values;
//! preserve undefined placeholders and type inference. Extract basic and quantified
//! field/predicate/wand resources, evaluate candidate inverse/image or singleton arguments and sum
//! positive permissions per location. Recover predicate fields by walking right-associated
//! snapshot trees and supported equality guards. Resolve store, collection and unique-reference
//! names against Silver resources, retaining old heaps and function/domain interpretations.
//! Preserve partial-model fallbacks and upstream operation-loop behavior.
//!
//! Integration:
//! reporting::converter evaluateTerm, state::{chunks,store,terms}, rules::quantified_chunk_support
//! and consumer snapshots; Silver verifier counterexample/model types.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact permissions, resource identity, ordering and incomplete
//! model outcomes.
//!
//! Open decisions:
//! Reconcile collection fixpoint nontermination on unresolved dependencies, approximate guard
//! evaluation and map iteration with model parser and differential tests before changes.
//!
//! Status: description only; implementation has not started.
