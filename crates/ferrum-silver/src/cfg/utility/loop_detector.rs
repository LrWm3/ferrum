//! Port plan: Detect natural loops, annotate CFG boundaries and optionally project loop information
//! back to AST.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/utility/LoopDetector.scala
//!
//! Purpose:
//! Detect natural loops, annotate CFG boundaries and optionally project loop information back to AST.
//!
//! Planned Rust structure:
//! Port IdInfo, LoopInfo, detect overloads, naturalLoops, writtenVariables, augment, isReducible and
//! collectBlocks; use Dominators and AST traversal/metadata rewriting.
//!
//! Behavior to preserve:
//! Reject irreducible graphs; merge provided syntactic loop membership with natural loops from
//! backedges. CFG augmentation uses insertion-ordered BFS, replaces loop-head statement blocks and
//! splits multi-boundary edges, attaching original condition only to first edge. AST path adds
//! temporary IDs, computes ignored invariant labels and optional distinct written variables, contracts
//! empty paths, attaches loop info at transitions, and removes IDs unless requested. Preserve source's
//! exact intermediate edge-kind expression and its discarded fold result for separate investigation,
//! not silent repair.
//!
//! Integration:
//! Uses cfg::{cfg,block,edge,silver::{cfg_generator,silver_cfg},utility::dominators} and
//! ast::{ast,statement,expression,utility::rewriter}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Reconcile AST IDs, loop-head/block identity, edge-splitting quirks and ignored-label reporting with
//! CFG generator and consumers.
//!
//! Status: description only; implementation has not started.
