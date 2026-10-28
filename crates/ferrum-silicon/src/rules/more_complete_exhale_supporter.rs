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
//! Status: tagged snapshot data and symbolic permission summation live here; native context
//! implements lookup, snapshot summaries and consumption. Mode admission remains gated.

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

/// Sum permission at the requested arguments over all source-ordered chunks.
/// This is the symbolic expression used by both complete lookup and consumption;
/// a chunk contributes only when each argument equals the requested one.
pub fn permission_sum(
    factory: &crate::state::terms::TermFactory,
    chunks: &[crate::state::package::NonQuantifiedChunkKey],
    arguments: &[Term],
) -> Term {
    use crate::interfaces::state::chunks::{GeneralChunk, NonQuantifiedChunk};
    use crate::state::package::NonQuantifiedChunkKey;
    let mut sum = factory.no_perm();
    for chunk in chunks {
        let (args, permission) = match chunk {
            NonQuantifiedChunkKey::Basic(chunk) => (chunk.args(), chunk.permission(factory)),
            NonQuantifiedChunkKey::Wand(chunk) => (chunk.args(), chunk.permission(factory)),
        };
        let equal = factory.and(
            args.iter()
                .zip(arguments)
                .map(|(a, b)| factory.equals(a.clone(), b.clone())),
        );
        sum = factory.perm_plus(sum, factory.ite(equal, permission, factory.no_perm()));
    }
    sum
}
