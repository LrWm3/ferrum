//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/predicateinstance/PredicateInstanceASTExtension.scala
//!
//! Purpose:
//! Represent predicate instance expressions before lowering.
//!
//! Planned Rust structure:
//! Port PredicateInstance with predicate name, arguments, pure extension type, subnodes, pretty
//! printer and purity consistency checks; expose PredicateInstance domain type helper.
//!
//! Behavior to preserve:
//! Type is the nullary PredicateInstance domain; each argument must be pure. verifyExtExp is
//! unimplemented upstream, so lowering is required before backend verification.
//!
//! Integration:
//! predicate_instance_plugin lowers nodes; parser extension translates them; ast consistency and
//! pretty printing.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for extension nodes, type and metadata.
//!
//! Open decisions:
//! Agree on domain lookup/type representation and unsupported unlowered extension handling with
//! ast and verifier.
//!
//! Status: description only; implementation has not started.
