//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/DefaultMultisetsContributor.scala
//!
//! Purpose:
//! Instantiate builtin multiset axioms.
//!
//! Planned Rust structure:
//! Port DefaultMultisetsContributor specialization and unary sort factory.
//!
//! Behavior to preserve:
//! Choose multisets_old.vpr under useOldAxiomatization, otherwise multisets.vpr, with configured
//! file override; use $Multiset.
//!
//! Integration:
//! supporters::{builtin_domains_contributor,domains}, config and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for configuration and native resources; retain .vpr formats.
//!
//! Open decisions:
//! Reconcile configuration access with verifier and builtin_domains_contributor.
//!
//! Status: description only; implementation has not started.
