//! Port plan: Collect type variables and constituents.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Types.scala
//!
//! Purpose:
//! Collect type variables and constituents.
//!
//! Planned Rust structure:
//! Types.typeVariables, freeTypeVariables and typeConstituents overloads for types and domain
//! members.
//!
//! Behavior to preserve:
//! Recurse through domain mappings, collection element and map key/value; domain function
//! signatures and typed nodes in axioms determine free variables. Constituents omit the outer
//! type; domain arguments are returned directly while collection and map paths recurse.
//!
//! Integration:
//! ast::{type,program,ast}, ast::utility::{nodes,visitor,domain_instances}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile domain parameter mappings and set/order semantics with ast::type and
//! domain_instances.
//!
//! Status: description only; implementation has not started.
