//! Port plan: Identify, collect and desugar quantified resource permissions.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/QuantifiedPermissions.scala
//!
//! Purpose:
//! Identify, collect and desugar quantified resource permissions.
//!
//! Planned Rust structure:
//! QuantifiedPermissionAssertion and SourceQuantifiedPermissionAssertion extractors;
//! quantifiedFields, quantifiedPredicates, resourceTriggers, quantifiedMagicWands, dependency
//! traversal and desugar helpers.
//!
//! Behavior to preserve:
//! Implicit condition becomes true. Traverse dependencies, but only specifications of non-root
//! methods/functions; ordered sets retain resource discovery order. Desugar impure forall RHS
//! conjunction, nested implications, conditionals, nested quantifiers and let; combine nested
//! triggers by cross product and preserve metadata. Split distinct inhale/exhale views into
//! paired wrappers; pure/unmatched forms stay unchanged.
//!
//! Integration:
//! ast::{expression,program}, ast::utility::{nodes,expressions,triggers,inverse_functions};
//! Silicon quantified permissions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Agree on dependency closure, metadata and trigger ordering with inverse_functions and
//! Silicon consumers.
//!
//! Status: description only; implementation has not started.
