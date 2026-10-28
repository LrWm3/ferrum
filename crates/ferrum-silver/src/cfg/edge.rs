//! Port plan: Generic CFG edges and loop-boundary classification.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/Edge.scala
//!
//! Purpose:
//! Generic CFG edges and loop-boundary classification.
//!
//! Planned Rust structure:
//! Represent Kind Normal/In/Out/Unknown and Edge with UnconditionalEdge and ConditionalEdge, source,
//! target, optional condition, isIn/isOut.
//!
//! Behavior to preserve:
//! Constructors default to Unknown; preserve edge equality, endpoint identity, condition and kind
//! through graph transformations.
//!
//! Integration:
//! Used by cfg::{block,cfg,silver::cfg_generator,utility::{cfg_simplifier,loop_detector,dominators}}
//! and Silicon.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Reconcile edge equality and endpoint handles with cfg::block and ordered graph sets.
//!
//! Status: description only; implementation has not started.
