//! Port plan: Generic basic blocks with stable identities and ordered contents.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/Block.scala
//!
//! Purpose:
//! Generic basic blocks with stable identities and ordered contents.
//!
//! Planned Rust structure:
//! Represent Block, StatementBlock, PreconditionBlock, PostconditionBlock and LoopHeadBlock, with fresh
//! atomic IDs, constructors and elements projection.
//!
//! Behavior to preserve:
//! Preserve block object identity even for identical contents; elements put loop invariants before
//! statements. StatementBlock distinguishes no invariant data from present invariants and optional loop
//! ID, including nested option distinction. Fresh IDs increase globally.
//!
//! Integration:
//! Used by cfg::{cfg,edge,silver,utility} and Silicon CFG consumers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Agree on block handles and ID allocation with cfg::cfg and graph transforms; do not replace identity
//! with structural content equality.
//!
//! Status: description only; implementation has not started.
