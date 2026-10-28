//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/DefaultSetsContributor.scala
//!
//! Purpose:
//! Instantiate builtin set axioms including sets needed indirectly.
//!
//! Planned Rust structure:
//! Port DefaultSetsContributor specialization and computeGroundTypeInstances.
//!
//! Behavior to preserve:
//! Select sets_old.vpr or sets.vpr and user override. In quantified-permission cases add set types
//! of every field, Ref and embedded Snap; add sets of map key/value types for map domains.
//! Preserve insertion order and unary sort.
//!
//! Integration:
//! supporters::builtin_domains_contributor and qps contributors, state::terms, Silver AST and
//! config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered ground instances and .vpr resources.
//!
//! Open decisions:
//! Reconcile indirect set-type contributions with quantified contributors and type embedding.
//!
//! Status: description only; implementation has not started.
