//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/predicateinstance/PredicateInstanceErrors.scala
//!
//! Purpose:
//! Define verification errors for inaccessible predicate instances.
//!
//! Planned Rust structure:
//! Port PredicateInstanceError and PredicateInstanceNoAccess, including id, text, cached flag and
//! withNode/withReason.
//!
//! Behavior to preserve:
//! Preserve predicateinstance.no.access identity and offending-node provenance. Upstream
//! withReason ignores its new reason, a potential bug needing explicit reconciliation.
//!
//! Integration:
//! predicate_instance_plugin maps precondition errors; verifier error/reason interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for error and reason mapping.
//!
//! Open decisions:
//! Resolve withReason behavior with verifier error contract and differential tests.
//!
//! Status: description only; implementation has not started.
