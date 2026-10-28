//! Port plan: ConsistencyTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/ConsistencyTests.scala
//!
//! Purpose:
//! Port the upstream ConsistencyTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! ConsistencyTests using directly constructed Silver ASTs.
//!
//! Behavior to preserve:
//! Check exact ordered ConsistencyError sequences for non-Boolean while,
//! missing/duplicate/type-mismatched names, conditional and assignment types, method arity,
//! function/predicate/domain calls, quantified permission shape and trigger coverage, and
//! DomainType/BackendType reference/interpretation errors.
//!
//! Integration:
//! ast::{ast,expression,statement,program,type}, ast::utility::consistency and verifier results.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Keep diagnostics, positions and check order; tests construct ASTs that frontend typechecking
//! could reject earlier.
//!
//! Status: description only; implementation has not started.
