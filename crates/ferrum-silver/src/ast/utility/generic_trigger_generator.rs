//! Port plan: Find and rank trigger sets covering quantified variables.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/GenericTriggerGenerator.scala
//!
//! Purpose:
//! Find and rank trigger sets covering quantified variables.
//!
//! Planned Rust structure:
//! GenericTriggerGenerator and TriggerSet, customizable possible/forbidden predicates,
//! candidate traversal hooks, buildTriggersCovering and group/first/strictest entry points.
//!
//! Behavior to preserve:
//! Exclude applications involving nested bound variables; replace forbidden arguments with
//! fresh variables; include relevant variables from hooks. Enumerate covering subsets, discard
//! redundant and subsumed candidates, group by extra variables and sort by count. First-group
//! searches expressions individually, not combinations; strictest unions terms via a set.
//! Mutable filters make shared generator non-thread-safe.
//!
//! Integration:
//! ast::utility::{triggers,expressions,generic_axiom_rewriter}, AST visitors and extension
//! expressions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile fresh counter, ordered collection and per-worker filter ownership with triggers
//! and quantifier consumers.
//!
//! Status: description only; implementation has not started.
