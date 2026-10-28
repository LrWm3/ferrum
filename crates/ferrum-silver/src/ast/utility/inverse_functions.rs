//! Port plan: Generate inverse domains and axioms for quantified resource permissions.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/InverseFunctions.scala
//!
//! Purpose:
//! Generate inverse domains and axioms for quantified resource permissions.
//!
//! Planned Rust structure:
//! InverseFunctions.getFreshInverse, its global counter and field, predicate and magic-wand
//! generation branches.
//!
//! Behavior to preserve:
//! A non-QP is returned unchanged with no generated artifacts. Field inverse has a Ref
//! parameter per quantified variable; predicate and wand use resource arguments or evaluable
//! wand holes. Generate both inverse axioms, triggers and rewritten forall with metadata and
//! substitutions in source order; unsupported resource fails. Some branches assume nonempty
//! conjunction inputs.
//!
//! Integration:
//! ast::{expression,program}, ast::utility::{quantified_permissions,impure_assume_rewriter}
//! and downstream quantified permission processing.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile counter lifecycle/concurrency, fresh names, zero-argument cases and substitution
//! with trigger and verifier owners.
//!
//! Status: description only; implementation has not started.
