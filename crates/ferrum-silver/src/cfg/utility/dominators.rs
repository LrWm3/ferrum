//! Port plan: Compute immediate dominators and identify natural-loop backedges.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/utility/Dominators.scala
//!
//! Purpose:
//! Compute immediate dominators and identify natural-loop backedges.
//!
//! Planned Rust structure:
//! Represent Dominators with DFS indices and immediate-dominator map, dominator/dominates/isBackedge
//! and Lengauer-Tarjan DFS, link, evaluate and bucket helpers.
//!
//! Behavior to preserve:
//! Assume a connected graph; entry dominates itself and backedges require DFS target index no greater
//! than source plus domination. Preserve DFS successor order, semi-dominator/bucket passes and path
//! compression. Upstream evaluate uses equality comparison `label(index) == ancestorLabel` rather than
//! assignment; preserve this observable quirk until separately investigated.
//!
//! Integration:
//! Consumes cfg::{cfg,block,edge}; cfg::utility::loop_detector relies on its relation.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Reconcile block identity and handling of the apparent comparison bug with loop_detector and
//! differential tests; any correction is a recorded separate difference.
//!
//! Status: description only; implementation has not started.
