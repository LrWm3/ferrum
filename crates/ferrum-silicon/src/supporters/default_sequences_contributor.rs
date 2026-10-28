//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/DefaultSequencesContributor.scala
//!
//! Purpose:
//! Instantiate builtin sequence axioms, including integer ranges.
//!
//! Planned Rust structure:
//! Port DefaultSequencesContributor specialization and transformSourceDomainInstance.
//!
//! Behavior to preserve:
//! Select sequences_old.vpr or sequences.vpr and configured override; use $Seq unary sort. Retain
//! Seq_range function and named Seq_range_ axioms only for Seq[Int] to avoid duplicate
//! declarations.
//!
//! Integration:
//! supporters::{builtin_domains_contributor,domains}, config and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered declarations and .vpr resources.
//!
//! Open decisions:
//! Agree on resource selection and type-instantiation ordering with builtin_domains_contributor.
//!
//! Status: description only; implementation has not started.
