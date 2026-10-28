//! Port plan: Expression purity, heap dependence, fragments, variables and proof obligations.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Expressions.scala
//!
//! Purpose:
//! Expression purity, heap dependence, fragments, variables and proof obligations.
//!
//! Planned Rust structure:
//! Expressions.isPure/isHeapDependent/dependsOnCurrentHeap, asBooleanExp and pure/access
//! fragments, inhale/exhale projections, free/contained variables, rename/instantiate,
//! subExps, well-definedness/proof obligations, trigger and conjunct helpers.
//!
//! Behavior to preserve:
//! Distinguish old and old[lhs] heap state with the wand-state flag; purity follows specific
//! expression families and extension hooks. Let binding scopes only its body for free-variable
//! analysis, and unused let values do not contribute contained variables. Instantiate
//! capture-avoiding through Sanitizer. Proof obligations visit children first and guard lazy
//! branches; forall trigger selection prefers no extra variables and disallows adding extras
//! to impure quantifiers.
//!
//! Integration:
//! ast::{ast,expression,program}, ast::utility::{nodes,visitor,triggers,rewriter},
//! utility::sanitizer and Silicon.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Coordinate binder substitution, heap-state interpretation, and trigger identity with
//! sanitizer, quantified_permissions and Silicon.
//!
//! Status: description only; implementation has not started.
