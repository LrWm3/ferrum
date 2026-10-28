//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/Converter.scala
//!
//! Purpose:
//! Extract a legacy mapped model and heap from solver values and symbolic state.
//!
//! Planned Rust structure:
//! Port ExtractedModel/Entry variants, heap entries, DomainEntry, ExtractedFunction and Converter
//! helpers for model function lookup, constant and term evaluation, heap extraction, local/store
//! mapping and domain/function instances.
//!
//! Behavior to preserve:
//! Evaluate literals, variables, applications, snapshot combine/projections/wrappers,
//! field/predicate lookups, Boolean/permission/integer operations and selected collections;
//! preserve Euclidean div/mod and unknown/partial model fallbacks. Extract basic
//! fields/predicates, legacy quantified-field approximation and unresolved chunks; recursively map
//! references/sequences with cycle detection and derive set values. Preserve model-name lookup
//! order, exact rational operations after source decimal parsing, function partial application and
//! type errors.
//!
//! Integration:
//! reporting::{domain_interpreter,silicon_resolved_counterexample}, state::{terms,heap,store},
//! decider::term_to_smt_lib2_converter and Silver verifier model.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact numeric representation, error distinctions, cycles and
//! collection order.
//!
//! Open decisions:
//! Reconcile approximate decimal parsing, legacy quantified extraction and model name matching
//! with resolved counterexample and solver formats; document any correction.
//!
//! Status: description only; implementation has not started.
