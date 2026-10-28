//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/MoreCompleteExhaleSupporter.scala
//!
//! Purpose:
//! Summarise and consume permissions across potentially aliasing nonquantified chunks.
//!
//! Planned Rust structure:
//! moreCompleteExhaleSupporter defines TaggedSummarisingSnapshot, FreshSummarisingSnapshot,
//! ReusedSummarisingSnapshot, permSummariseOnly, summariseOnly/summarise, lookupComplete,
//! consumeComplete, read-only and exact/constrainable consumption helpers, and
//! assumeFieldPermissionUpperBounds.
//!
//! Behavior to preserve:
//! Cache summaries by resource, ordered chunks and arguments; reuse known or provable snapshot,
//! otherwise fresh quantified snapshot and definitions, recording fresh map. One-chunk shortcut is
//! disabled for counterexamples. Lookup checks positive summed permission and handles
//! smoke-dead/package paths distinctly. Read-only asserts access without modifying heap; exact
//! consumption prioritizes definite/syntactic aliases, subtracts conditional minima, drops provably
//! nonpositive chunks and checks remaining amount; empty heap requires zero. Constrainable
//! consumption creates bounded fresh taken permissions, asserts positive availability and assumes
//! requested amount equals total. Fresh permission macros are avoided for literal terms, function
//! recording, flyweight or counterexample; packaging snapshot variables are excluded from
//! permission arguments. Preserve timeout checks, field upper bound assumptions, error and snapshot
//! conditions.
//!
//! Integration:
//! rules::chunk_supporter, state_consolidator, state::package, resources and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Summarising cache identity, fresh symbols and continuation context.
//!
//! Status: tagged summarising snapshot data implemented; execution rules remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::state::terms::Term;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TaggedSummarisingSnapshot {
    Fresh(Term),
    Reused(Term),
}
impl TaggedSummarisingSnapshot {
    pub fn snapshot(&self) -> &Term {
        match self {
            Self::Fresh(t) | Self::Reused(t) => t,
        }
    }
}
