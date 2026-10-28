//! Port plan: Define the Silver verifier lifecycle and dependencies.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/Verifier.scala
//!
//! Purpose:
//! Define the Silver verifier lifecycle and dependencies.
//!
//! Planned Rust structure:
//! Verifier extends LifetimeComponent with name/version/buildVersion/copyright/signature,
//! debugInfo, dependencies, parseCommandLine, start, verify, stop and reporter; Dependency,
//! DefaultDependency and test-only NoVerifier.
//!
//! Behavior to preserve:
//! Arguments and debug information are each set at most once; parse arguments precedes start,
//! verify follows start and stop ends use. NoVerifier.verify is deliberately unimplemented rather
//! than success. Preserve dependency information and reporter access.
//!
//! Integration:
//! components::lifetime_component, ast::program, reporter::reporter, verifier::verification_result
//! and Silicon verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Agree on lifecycle errors and object ownership with frontend and Silicon; do not turn
//! NoVerifier into a success-producing placeholder.
//!
//! Status: description only; implementation has not started.
