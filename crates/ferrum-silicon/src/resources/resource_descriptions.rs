//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/ResourceDescriptions.scala
//!
//! Purpose:
//! Define assumptions for field, predicate and wand chunks.
//!
//! Planned Rust structure:
//! Port ResourceDescription, BasicDescription, PredicateDescription, FieldDescription and
//! MagicWandDescription, including named property constructors.
//!
//! Behavior to preserve:
//! All require nonnegative permissions; fields additionally require positive permission implies
//! non-null receiver. Configured upper bounds add at-most-one instance property and delayed
//! pairwise permission-sum disequality. Basic delayed property checks positive permissions and
//! distinct values imply distinct arguments; wand has no delayed properties. Preserve property
//! order and Check semantics.
//!
//! Integration:
//! resources::{resources,property,property_expressions}, property interpreters and
//! rules::state_consolidator.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact permission terms, ordering and delayed assumptions.
//!
//! Open decisions:
//! Agree on upper-bound configuration and heap consolidation boundaries with rules and state.
//!
//! Status: description only; implementation has not started.
