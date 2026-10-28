//! Port plan: Split a Silver program into dependency-closed verification subprograms and merge them.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/chopper/Chopper.scala
//!
//! Purpose:
//! Split a Silver program into dependency-closed verification subprograms and merge them.
//!
//! Planned Rust structure:
//! Chopper/PluginAwareChopper, ChopperLike and Metrics; Cut, Penalty and default
//! configurations; ViperGraph/ViperGraphs, Vertices/Edges and SCC/Component including
//! plugin-aware dependencies.
//!
//! Behavior to preserve:
//! Select methods/functions/predicates by default; model definitions versus specs/signatures,
//! fields, domain types/functions/axioms and Always. Compute dependency reachability, SCC
//! condensation for more than two important nodes, smallest cuts and greedy priority-queue
//! merges with nonpositive penalty or positive bound pressure. Reconstruct bodyless stubs only
//! when definition absent. Domain axiom edges depend on outside-quantifier uses and triggers;
//! opaque/reveal and termination well-founded domains modify dependencies. Reject plugin AST
//! nodes and invalid bounds; require trigger-bearing quantifiers. Preserve safety checks and
//! timing metrics.
//!
//! Integration:
//! ast::{program,expression,statement,type}, ast::utility::{nodes,visitor},
//! plugin::standard::termination and frontend verification/chopping callers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile node/vertex identity, set and queue ordering, plugin preprocessing and output
//! program ordering with frontend and verifier; do not silently normalize source unordered
//! iteration.
//!
//! Status: description only; implementation has not started.
