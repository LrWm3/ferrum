//! Port plan: ChopperTests.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/ChopperTests.scala
//!
//! Purpose:
//! Port the upstream ChopperTests.scala test or test-harness component.
//!
//! Planned Rust structure:
//! ChopperTests and SCC component/DAG comparison helpers.
//!
//! Behavior to preserve:
//! Assert single and independent functions/methods/predicates, shared domain and field
//! dependencies, dependent function merge, method/predicate bodyless stubs, and unfolding
//! requiring predicate body. SCC cases cover singleton, two/three cycles, X graph and inverse
//! mapping/DAG edges. Uses DefaultWithoutForcedMerge and explicit bounds.
//!
//! Integration:
//! ast::utility::chopper and ast::program.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Reconcile deterministic vector expectations with source graph/set iteration and compare SCCs as
//! sets.
//!
//! Status: description only; implementation has not started.
