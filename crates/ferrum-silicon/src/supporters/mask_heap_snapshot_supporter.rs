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
//! Status: partial; mask snapshot combination, finalization and producer adaptation are implemented.
//! Runtime state/continuation integration remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.
use crate::rules::mask_heap_supporter::{
    MaskHeapError, masks_from_snapshot, merge_preserving_first_order, snapshot_from_masks,
};
use crate::state::heap::ListBackedHeap;
use crate::state::symbol_converter::DefaultSymbolConverter;
use crate::state::terms::{ResourceKey, Sort, Term, TermFactory, TermKind};

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

    /// `heap` must be the source evaluation heap selected for the current exhale state.
    pub fn finalize_consumed_snapshot<E>(
        &self,
        snapshot: &Term,
        resources: &[ResourceKey],
        heap: &ListBackedHeap,
        alias: impl FnMut(Term) -> Result<Term, E>,
    ) -> Result<Term, MaskHeapError<E>> {
        let zeros: Vec<_> = resources
            .iter()
            .cloned()
            .map(|resource| {
                let zero = if matches!(resource, ResourceKey::Field(_)) {
                    self.factory.zero_mask()
                } else {
                    self.factory.pred_zero_mask()
                };
                (resource, zero)
            })
            .collect();
        let masks = self.to_mask_map(snapshot, |term| {
            Ok::<_, MaskHeapError<E>>(masks_from_snapshot(self.factory, term.clone(), resources))
        })?;
        let merged = merge_preserving_first_order(self.factory, &zeros, &masks);
        snapshot_from_masks(self.factory, &merged, resources, heap, alias)
    }

    /// Return the single heap-map term shared by both producer conjuncts.
    pub fn adapt_produce_snapshot<E>(
        &self,
        snapshot: Term,
        resources: &[ResourceKey],
        converter: &DefaultSymbolConverter,
        mut alias: impl FnMut(Term) -> Result<Term, E>,
    ) -> Result<Term, MaskHeapError<E>> {
        if matches!(snapshot.kind(), TermKind::HeapMapTerm(_)) {
            return Ok(snapshot);
        }
        let parts = self.factory.from_snap_tree(
            snapshot,
            i32::try_from(resources.len()).expect("too many resources"),
        );
        let mut heaps = Vec::with_capacity(resources.len());
        for (resource, part) in resources.iter().cloned().zip(parts) {
            let sort = match &resource {
                ResourceKey::Field(field) => Sort::Heap(Box::new(
                    converter.to_sort(&field.typ).map_err(MaskHeapError::Sort)?,
                )),
                ResourceKey::Predicate(_) => Sort::PredHeap,
                ResourceKey::Wand(_) => Sort::WandHeap,
            };
            if let TermKind::HeapToSnap(_, _, source) = part.kind() {
                if source != &resource {
                    return Err(MaskHeapError::MissingResource);
                }
            }
            let heap = self.factory.snap_to_heap(part, resource.clone(), sort);
            heaps.push((resource, alias(heap).map_err(MaskHeapError::Service)?));
        }
        Ok(self.factory.heap_map_term(heaps))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rules::mask_heap_supporter::empty_heap;
    use crate::state::terms::TermOptions;
    use ferrum_silver::ast::{
        ast::Metadata,
        program::{Field, FieldData, Predicate, PredicateData, Program},
        r#type::Type,
    };
    use std::sync::Arc;

    #[test]
    fn empty_heap_and_snapshot_preserve_resource_order() {
        let meta = Metadata::default();
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let predicate = Predicate::new(PredicateData {
            name: "p".into(),
            formal_args: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![],
            vec![field.clone()],
            vec![],
            vec![predicate.clone()],
            vec![],
            vec![],
            meta,
        );
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let heap = empty_heap(
            &program,
            &factory,
            &converter,
            false,
            |_, _| -> Result<Term, ()> { panic!("dummy heap must not allocate") },
        )
        .unwrap();
        let resources = vec![
            ResourceKey::Field(Arc::new(field)),
            ResourceKey::Predicate(Arc::new(predicate)),
        ];
        let supporter = MaskHeapSnapshotSupporter { factory: &factory };
        let masks = masks_from_snapshot(&factory, factory.unit(), &resources);
        assert_eq!(masks.len(), 2);
        assert!(matches!(masks[0].1.kind(), TermKind::ZeroMask));
        assert!(matches!(masks[1].1.kind(), TermKind::PredZeroMask));
        let snapshot = supporter
            .finalize_consumed_snapshot(&factory.mask_map_term(masks), &resources, &heap, |t| {
                Ok::<_, ()>(t)
            })
            .unwrap();
        let heap_map = supporter
            .adapt_produce_snapshot(snapshot, &resources, &converter, |t| Ok::<_, ()>(t))
            .unwrap();
        assert!(
            matches!(heap_map.kind(), TermKind::HeapMapTerm(entries) if entries.iter().map(|(key,_)|key).eq(resources.iter()))
        );
    }
}
