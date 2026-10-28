//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/PermissionSupporter.scala
//!
//! Purpose:
//! Check permission signs with verification errors and continuations.
//!
//! Planned Rust structure:
//! permissionSupporter.assertNotNegative and assertPositive take state, permission, error and
//! verifier, then invoke Q after a successful check.
//!
//! Behavior to preserve:
//! A constrainable ARP variable bypasses the sign assertion; otherwise assert nonnegative or
//! positive and attach NegativePermission or NonPositivePermission on failure. Debug expression
//! uses source position and metadata.
//!
//! Integration:
//! rules::symbolic_execution_rules, rules::evaluator, state::terms, decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Continuation and verifier context ownership.
//!
//! Status: description only; implementation has not started.
