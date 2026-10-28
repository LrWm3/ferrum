//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/MaskHeapSnapshotSupporter.scala
//!
//! Purpose:
//! Adapt snapshot handling to per-resource mask/heap encoding.
//!
//! Planned Rust structure:
//! Port MaskHeapSnapshotSupporter overrides for unit/combine/finalize, produce adaptation, empty
//! constraint and snapshot pairing.
//!
//! Behavior to preserve:
//! Consume snapshots as ordered resource masks, merge preserving first order and fill absent
//! resource masks with zero; finalize against the evaluation heap into heap-restricted snapshot
//! tree. Produce converts snapshot tree leaves to aliased per-resource heaps when needed. Empty
//! constraint is absent and both conjuncts receive the same snapshot function rather than
//! splitting.
//!
//! Integration:
//! supporters::snapshot_supporter, rules::{mask_heap_supporter,magic_wand_supporter},
//! state::{terms,heap} and decider::decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for branch state, ordering, solver aliasing and snapshot
//! identity.
//!
//! Open decisions:
//! Agree on resource-key identity, heap lifetime and alias ownership with mask_heap_supporter and
//! producer/consumer.
//!
//! Status: partial; mask snapshot combination, unit and shared producer functions implemented.
//! Resource discovery, completed-consume conversion and produce adaptation remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.
use crate::state::terms::{ResourceKey, Term, TermFactory, TermKind};

pub struct MaskHeapSnapshotSupporter<'a> {
    pub factory: &'a TermFactory,
}
impl MaskHeapSnapshotSupporter<'_> {
    pub fn unit_snapshot(&self) -> Term {
        self.factory.mask_map_term([])
    }
    /// Unlike the default encoding, do not even evaluate the by-name snapshot.
    pub fn empty_snapshot_constraint(&self, _snapshot: impl FnOnce() -> Term) -> Option<Term> {
        None
    }
    /// The mask encoding shares a single producer snapshot function between conjuncts.
    pub fn create_snapshot_pair<F: Clone>(&self, snapshot_function: F) -> (F, F) {
        (snapshot_function.clone(), snapshot_function)
    }
    pub fn to_mask_map<E>(
        &self,
        snapshot: &Term,
        fallback: impl FnOnce(&Term) -> Result<Vec<(ResourceKey, Term)>, E>,
    ) -> Result<Vec<(ResourceKey, Term)>, E> {
        match snapshot.kind() {
            TermKind::MaskMapTerm(map) => Ok(map.iter().cloned().collect()),
            TermKind::HeapToSnap(_, mask, resource) => Ok(vec![(resource.clone(), mask.clone())]),
            _ => fallback(snapshot),
        }
    }
    pub fn combine_snapshots<E>(
        &self,
        first: &Term,
        second: &Term,
        first_fallback: impl FnOnce(&Term) -> Result<Vec<(ResourceKey, Term)>, E>,
        second_fallback: impl FnOnce(&Term) -> Result<Vec<(ResourceKey, Term)>, E>,
    ) -> Result<Term, E> {
        let mut result = self.to_mask_map(first, first_fallback)?;
        for (key, mask) in self.to_mask_map(second, second_fallback)? {
            if let Some((_, previous)) = result.iter_mut().find(|(old, _)| old == &key) {
                *previous = self.factory.mask_sum(previous.clone(), mask);
            } else {
                result.push((key, mask));
            }
        }
        Ok(self.factory.mask_map_term(result))
    }
}
