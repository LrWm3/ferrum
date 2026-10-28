//! Port plan: Compute needed ground generic-type instances and instantiate domain members.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/DomainInstances.scala
//!
//! Purpose:
//! Compute needed ground generic-type instances and instantiate domain members.
//!
//! Planned Rust structure:
//! DomainInstances.TypeSubstitution, GroundTypeInstance/TypeInstance/AtomicTypeInstance,
//! DomainParameter and coordinates (atomic, collection, map, domain); getInstanceMembers,
//! collectGroundTypes, findNecessaryTypeInstances, substitute, type closure and type-variable
//! depth helpers, plus diagnostic and Tarjan data structures.
//!
//! Behavior to preserve:
//! Collect direct ground types and concrete domain applications; unify axiom applications with
//! default Int for unmatched variables. Traverse type coordinates bottom-up with
//! depth/inflation luggage and default threshold 1; filter instantiated members to those whose
//! ground types are necessary, then distinct. Preserve type substitution, downClosure behavior
//! and errors on non-ground coordinates; commented-out SCC code is not active.
//!
//! Integration:
//! ast::{type,program,expression}, ast::utility::{nodes,visitor}; Program.groundTypeInstances
//! and downstream domain encoding.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Agree on type coordinate equality, bounded expansion and unordered-set effects with type
//! and Silicon domain encoders.
//!
//! Status: description only; implementation has not started.
