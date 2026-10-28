//! Port plan: ExpectedCounterexampleAnnotation.scala
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/test/scala/ExpectedCounterexampleAnnotation.scala
//!
//! Purpose:
//! Port the upstream ExpectedCounterexampleAnnotation.scala test or test-harness component.
//!
//! Planned Rust structure:
//! ExpectedCounterexampleAnnotation, CounterexampleTestInput, CounterexampleParser and
//! ExpectedCounterexample.
//!
//! Behavior to preserve:
//! Match ID and location plus resolved failure-context counterexample. Expected expressions
//! include equality, access predicates and magic wands; resolve store variables, fields including
//! folded predicates, sequence/map lookups, predicate permissions and function table/default
//! values. Wand matching accepts resolved values or variable names, and wand grammar is tried
//! before access/equality.
//!
//! Integration:
//! counterexample_variables_tests, test_annotations, parser,
//! verifier::{counterexample,verification_error}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, diagnostics and provisional ownership.
//! Reuse upstream fixtures and retain source test distinctions.
//!
//! Open decisions:
//! Agree on literal equality, heap names, partial values and backend-specific model conversion.
//!
//! Status: description only; implementation has not started.
