//! Port plan: Rewrite forbidden trigger terms by solving for quantified variables.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/GenericAxiomRewriter.scala
//!
//! Purpose:
//! Rewrite forbidden trigger terms by solving for quantified variables.
//!
//! Planned Rust structure:
//! GenericAxiomRewriter adapters, extractInvalidTermsInTriggerSets, partitionInvalidTerms,
//! solve and rewrite with TriggerSet.
//!
//! Behavior to preserve:
//! Shallow-collect forbidden terms; reject terms with zero or multiple quantified variables
//! and abort if any equation cannot be solved. Replace each term by a fresh variable in
//! triggers and body, replace no-longer-triggered old variables by a solution, add equality
//! constraints as implication antecedent, and reconstruct quantifier and triggers. Preserve
//! source iteration and all-or-nothing result.
//!
//! Integration:
//! ast::utility::{generic_arithmetic_solver,generic_trigger_generator,triggers}; concrete
//! adapter uses ast expressions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Agree on freshness, ordered sets, metadata and quantifier reconstruction with triggers and
//! consumers; inspect equality construction across multiple variables.
//!
//! Status: description only; implementation has not started.
