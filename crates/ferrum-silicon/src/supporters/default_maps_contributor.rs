//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/DefaultMapsContributor.scala
//!
//! Purpose:
//! Instantiate the builtin map domain for used map sorts.
//!
//! Planned Rust structure:
//! Port DefaultMapsContributor specialization of BuiltinDomainsContributor.
//!
//! Behavior to preserve:
//! Use $Map and /dafny_axioms/maps.vpr unless configured file overrides; require two sort
//! arguments in key/value order.
//!
//! Integration:
//! supporters::{builtin_domains_contributor,domains}, state::terms and config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for resource loading; preserve .vpr source format.
//!
//! Open decisions:
//! Agree on resource embedding and override handling with builtin_domains_contributor.
//!
//! Status: description only; implementation has not started.
