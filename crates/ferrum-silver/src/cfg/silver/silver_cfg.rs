//! Port plan: Silver-specialized CFG analyses and aliases.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/silver/SilverCfg.scala
//!
//! Purpose:
//! Silver-specialized CFG analyses and aliases.
//!
//! Planned Rust structure:
//! Represent SilverCfg, SilverBlock/SilverLoopHeadBlock/SilverEdge aliases, copy, cached writtenVars
//! and joinPoints/findJoinPoint.
//!
//! Behavior to preserve:
//! writtenVars breadth-first traverses from loop head with In/Out depth changes, stops below zero,
//! visits each block once and caches distinct variables in discovery order. Join-point BFS recursively
//! handles two-way branches, avoids revisiting loop heads, rejects more than two successors and asserts
//! no top-level join.
//!
//! Integration:
//! Implements cfg::cfg over ast::{statement,expression}; used by cfg::silver::cfg_generator, loop
//! analysis and Silicon.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Reconcile identity-keyed cache and branch/join semantics with cfg::block and Silicon execution;
//! copied graphs get fresh caches.
//!
//! Status: description only; implementation has not started.
