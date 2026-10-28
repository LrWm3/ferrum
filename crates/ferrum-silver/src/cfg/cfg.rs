//! Port plan: Immutable generic CFG and graph queries, mapping and DOT output.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/Cfg.scala
//!
//! Purpose:
//! Immutable generic CFG and graph queries, mapping and DOT output.
//!
//! Planned Rust structure:
//! Represent Cfg with blocks, edges, entry, optional exit and incoming/outgoing indexes by block ID;
//! expose predecessors/successors, map/copy and toDot.
//!
//! Behavior to preserve:
//! Preserve edge list order in indexes, duplicate successors, fresh mapped blocks and mapped edge
//! kinds/conditions; statements flat-map and expressions map. Map builds blocks from map values, whose
//! upstream iteration order is not guaranteed. DOT emits record labels, loop markers, source-specific
//! escaping and entry/exit styling.
//!
//! Integration:
//! Uses cfg::{block,edge}; implemented by cfg::silver::silver_cfg and transformed by cfg::utility.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ownership, identity, ordering and errors; proposed interfaces
//! remain provisional.
//!
//! Open decisions:
//! Agree on generic factory/copy and block identity with SilverCfg and mapping; preserve observable
//! ordering without silently sorting unordered source collections.
//!
//! Status: description only; implementation has not started.
