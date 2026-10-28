//! Port plan: Shared verification suite for interpreted backend types.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/testing/BackendTypeTest.scala
//!
//! Purpose:
//! Shared verification suite for interpreted backend types.
//!
//! Planned Rust structure:
//! BackendTypeTest program generators, wrapInProgram and verifier lifecycle hooks; named tests for
//! type/field combinations, float quantified permissions, bitvectors, floats, function and
//! predicate behavior.
//!
//! Behavior to preserve:
//! Start verifier once after parsing dummy.vpr and stop after all cases. Verify bitvector XOR 1
//! xor 2 = 3 and broad bitwise/arithmetic/shift operations; float 3.75 + 25.5 = 29.25, min/max and
//! function postconditions, float field quantified permissions and predicate fold/exhale. Negative
//! variants require exactly AssertFailed at the original assert or PostconditionViolated with
//! original expression/function.
//!
//! Integration:
//! ast::utility::backend_type_factories,
//! verifier::{verifier,verification_result,verification_error}, concrete backend harness.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile test registration and solver/backend availability with Silicon while preserving
//! failure node identity and lifecycle.
//!
//! Status: description only; implementation has not started.
