// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Snapshot-map cache from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/SnapshotMapCache.scala
//! Status: immutable cache operations and domain-condition compatibility implemented.

use super::chunks::{QuantifiedFieldChunk, QuantifiedMagicWandChunk, QuantifiedPredicateChunk};
use super::terms::{Term, TermKind};
use crate::rules::quantified_chunk_support::{SnapshotMapDefinition, SnapshotResource};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuantifiedBasicChunk {
    Field(QuantifiedFieldChunk),
    Predicate(QuantifiedPredicateChunk),
    Wand(QuantifiedMagicWandChunk),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CacheKey {
    pub resource: SnapshotResource,
    pub relevant_chunks: Vec<QuantifiedBasicChunk>,
}
#[derive(Clone, Debug)]
struct CacheValue {
    definition: SnapshotMapDefinition,
    permissions: Term,
    domain_condition: Option<Term>,
}
/// Vector-backed immutable map keeps source structural key equality without relying
/// on incomplete AST structural hashing; iteration is not exposed by upstream.
#[derive(Clone, Debug, Default)]
pub struct SnapshotMapCache {
    entries: Vec<(CacheKey, CacheValue)>,
}
impl SnapshotMapCache {
    pub fn empty() -> Self {
        Self::default()
    }
    pub fn get(
        &self,
        key: &CacheKey,
        requested: Option<&Term>,
    ) -> Option<(&SnapshotMapDefinition, &Term)> {
        let (_, value) = self.entries.iter().find(|(k, _)| k == key)?;
        if value.domain_condition.as_ref() == requested
            || (requested.is_none()
                && value
                    .domain_condition
                    .as_ref()
                    .is_some_and(|t| matches!(t.kind(), TermKind::True)))
        {
            Some((&value.definition, &value.permissions))
        } else {
            None
        }
    }
    #[must_use]
    pub fn with_entry(
        &self,
        key: CacheKey,
        definition: SnapshotMapDefinition,
        permissions: Term,
        domain_condition: Option<Term>,
    ) -> Self {
        let mut result = self.clone();
        let value = CacheValue {
            definition,
            permissions,
            domain_condition,
        };
        if let Some((old_key, old)) = result.entries.iter_mut().find(|(k, _)| k == &key) {
            *old_key = key;
            *old = value;
        } else {
            result.entries.push((key, value));
        }
        result
    }
    #[must_use]
    pub fn union(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (key, value) in &other.entries {
            if let Some((old_key, old)) = result.entries.iter_mut().find(|(k, _)| k == key) {
                *old_key = key.clone();
                *old = value.clone();
            } else {
                result.entries.push((key.clone(), value.clone()));
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::{TermFactory, TermOptions};
    use ferrum_silver::ast::{ast::Metadata, program::Field, r#type::Type};
    use std::sync::Arc;
    #[test]
    fn cached_true_covers_no_domain_but_not_other_conditions() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let resource = SnapshotResource::Field(Arc::new(Field::new(
            ferrum_silver::ast::program::FieldData {
                name: "f".into(),
                typ: Type::Int,
                meta: Metadata::default(),
            },
        )));
        let key = CacheKey {
            resource: resource.clone(),
            relevant_chunks: vec![],
        };
        let definition = SnapshotMapDefinition {
            resource,
            snapshot_map: f.unit(),
            value_definitions: vec![],
            domain_definitions: vec![],
        };
        let cache = SnapshotMapCache::empty().with_entry(
            key.clone(),
            definition,
            f.full_perm(),
            Some(f.boolean(true)),
        );
        assert!(cache.get(&key, None).is_some());
        assert!(cache.get(&key, Some(&f.boolean(true))).is_some());
        assert!(cache.get(&key, Some(&f.boolean(false))).is_none());
    }
}
