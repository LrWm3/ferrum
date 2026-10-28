//! Port plan: Prune unreachable CFG nodes and contract eligible empty statement blocks.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/utility/CfgSimplifier.scala
//!
//! Purpose:
//! Prune unreachable CFG nodes and contract eligible empty statement blocks.
//!
//! Planned Rust structure:
//! Port pruneUnreachable and simplify using queue traversal and insertion-ordered block/edge sets.
//!
//! Behavior to preserve:
//! Pruning starts at entry and removes exit if unreachable. Simplification assumes exit has no outgoing
//! edges; contract only an empty statement block with exactly one incoming and outgoing edge when at
//! least one edge is normal and at most one is conditional, preserving the non-normal kind and
//! condition. Keep traversal and deduplication order.
//!
//! Integration:
//! Operates on cfg::{cfg,block,edge}; called by cfg::silver::cfg_generator.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Agree on generic copy/factory, ordered sets and block identity with cfg::cfg; retain all
//! uncontracted cases.
//!
//! Status: description only; implementation has not started.
