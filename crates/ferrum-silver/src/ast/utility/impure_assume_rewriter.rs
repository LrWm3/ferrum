//! Port plan: Translate impure assumes into pure permission comparisons and generated domains.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/ImpureAssumeRewriter.scala
//!
//! Purpose:
//! Translate impure assumes into pure permission comparisons and generated domains.
//!
//! Planned Rust structure:
//! ImpureAssumeRewriter.rewriteAssumes, rewriteQPs, rewrite, rewriteInhale/split,
//! generatePermUsingFunc and generateFunc; helper and inverse/domain accumulators.
//!
//! Behavior to preserve:
//! Reset mutable accumulators per program; first rewrite quantified permissions via inverses,
//! then transform assumes into inhale sequences and add synthetic domains only when needed.
//! Track preceding resource occurrences and implication conditions to encode aliasing with
//! conditional permission sums; avoid rewriting accesses within wands and predicate access
//! directly under unfolding. Preserve helper reuse, generation order and metadata.
//!
//! Integration:
//! ast::{program,statement,expression},
//! ast::utility::{inverse_functions,simplifier,viper_strategy}; frontend transformations.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Move mutable global generator state to an agreed per-run context without changing
//! name/order, and reconcile transformation metadata with viper_strategy.
//!
//! Status: description only; implementation has not started.
