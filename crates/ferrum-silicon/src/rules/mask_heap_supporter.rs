//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/MaskHeapSupporter.scala
//!
//! Purpose:
//! Implement alternative mask-and-heap symbolic resource encoding.
//!
//! Planned Rust structure:
//! maskHeapSupporter implements HeapSupportRules and StatefulComponent: resource sequence
//! cache/lifecycle, ordered map merge, mask heap lookup/creation, wand heap merge and snapshot
//! conversions; mask subtraction/single-add simplification and bounds; single/quantified consume
//! and produce; field, current permission, havoc, forperm, function/predicate snapshots, resource
//! triggers and wand operations.
//!
//! Behavior to preserve:
//! Cache ordered resource sequences and clear on reset; resources sorted by name and first-map
//! ordering retained during map merge. Wand heap merge sums overlapping masks and merges heaps,
//! retaining resources appearing on just one side. Consume checks exact or constrainable permissions
//! and read-only access, uses reserve transfer during packaging and sums consumed masks; otherwise
//! subtract mask
//! and optionally freshen heap constrained to agree on known locations. simplifyOnConsume selects
//! solver-assisted cancellation. Quantified paths assume auxiliary and inverse definitions, assert
//! nonnegative permission and injectivity, build mask definitions and report appropriate failures;
//! inhale injectivity may be configured as assumed. Produce merges masks and heaps, assumes
//! good-mask and field bounds/non-nullness. Empty heaps use zero masks with fresh or dummy heaps.
//! Field reads/assignments assert permission, havoc frames untouched locations, trigger variants
//! offer heap and mask lookups, and function triggers use frame encoding. Preserve resource
//! snapshot conversion, predicate and wand-specific layouts and reserve merging.
//!
//! Integration:
//! rules::heap_supporter, quantified_chunk_support, magic_wand_supporter, evaluator, state::terms,
//! supporters::functions::mask_heap_function_encoding and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Mask/snapshot representation, ordered resource identity and solver/continuation ownership.
//!
//! Status: partial; cached shallow resource discovery and ordered mask merging implemented.
//! Heap manipulation, snapshots, quantified permissions and verifier rules remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2025 ETH Zurich.
use crate::state::chunks::MagicWandIdentifier;
use crate::state::terms::{ResourceKey, Term, TermFactory};
use ferrum_silver::ast::{
    expression::{Exp, ExpKind},
    program::Program,
    utility::{
        expressions::MagicWandError,
        nodes::{Node, TraversalError, subnodes},
        visitor::shallow_collect,
    },
};
use std::sync::Arc;

#[derive(Debug)]
pub enum ResourceDiscoveryError {
    Traversal(TraversalError),
    Wand(MagicWandError),
    MissingPredicate(String),
}
#[derive(Default)]
pub struct ResourceSequenceCache {
    entries: Vec<(Vec<Exp>, Vec<ResourceKey>)>,
}
impl ResourceSequenceCache {
    pub fn reset(&mut self) {
        self.entries.clear();
    }
    /// As upstream, the cache key is the ordered expression sequence, not the program identity.
    pub fn resources(
        &mut self,
        expressions: &[Exp],
        program: &Program,
    ) -> Result<Vec<ResourceKey>, ResourceDiscoveryError> {
        if let Some((_, resources)) = self.entries.iter().find(|(key, _)| key == expressions) {
            return Ok(resources.clone());
        }
        let mut resources = Vec::new();
        for expression in expressions {
            let nodes = shallow_collect(&[Node::Exp(expression.clone())], &subnodes, &mut |node| {
                if let Node::Exp(e) = node {
                    match e.kind() {
                        ExpKind::FieldAccessPredicate(..)
                        | ExpKind::PredicateAccessPredicate(..)
                        | ExpKind::MagicWand(..) => return Some(e.clone()),
                        _ => {}
                    }
                }
                None
            })
            .map_err(ResourceDiscoveryError::Traversal)?;
            for expression in nodes {
                let resource = match expression.kind() {
                    ExpKind::FieldAccessPredicate(access, _) => {
                        ResourceKey::Field(Arc::new(access.field.clone()))
                    }
                    ExpKind::PredicateAccessPredicate(access) => {
                        let name = &access.location.predicate_name;
                        let predicate = program
                            .predicates
                            .iter()
                            .find(|p| &p.name == name)
                            .ok_or_else(|| {
                                ResourceDiscoveryError::MissingPredicate(name.clone())
                            })?;
                        ResourceKey::Predicate(Arc::new(predicate.clone()))
                    }
                    ExpKind::MagicWand(..) => ResourceKey::Wand(
                        MagicWandIdentifier::new(expression.clone(), program)
                            .map_err(ResourceDiscoveryError::Wand)?,
                    ),
                    _ => unreachable!(),
                };
                if !resources.contains(&resource) {
                    resources.push(resource);
                }
            }
        }
        resources.sort_by_key(|r| match r {
            ResourceKey::Field(f) => f.name.clone(),
            ResourceKey::Predicate(p) => p.name.clone(),
            ResourceKey::Wand(w) => w.to_string(),
        });
        self.entries.push((expressions.to_vec(), resources.clone()));
        Ok(resources)
    }
}
/// Combine resource masks while preserving the first map's key order.
pub fn merge_preserving_first_order(
    factory: &TermFactory,
    first: &[(ResourceKey, Term)],
    second: &[(ResourceKey, Term)],
) -> Vec<(ResourceKey, Term)> {
    let mut result = first.to_vec();
    for (key, mask) in second {
        if let Some((_, value)) = result.iter_mut().find(|(old, _)| old == key) {
            *value = factory.mask_sum(value.clone(), mask.clone());
        } else {
            result.push((key.clone(), mask.clone()));
        }
    }
    result
}
