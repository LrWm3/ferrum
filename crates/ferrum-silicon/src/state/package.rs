// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! State cache types from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/package.scala
//! Status: permission and summarizing-snapshot cache shapes implemented; the
//! latter uses the concrete tagged snapshot type from its rule owner.

use super::chunks::{BasicChunk, MagicWandChunk};
use super::snapshot_map_cache::CacheKey;
use super::terms::Term;
use crate::rules::more_complete_exhale_supporter::TaggedSummarisingSnapshot;
use crate::rules::quantified_chunk_support::{PermMapDefinition, SnapshotResource};
use ferrum_silver::ast::expression::Exp;

/// TreeSeqMap-like insertion ordering with structural map equality. Vector
/// storage avoids requiring AST nodes to implement Hash before that port lands.
#[derive(Clone, Debug)]
pub struct OrderedMap<K, V>(Vec<(K, V)>);
impl<K, V> Default for OrderedMap<K, V> {
    fn default() -> Self {
        Self(Vec::new())
    }
}
impl<K: Eq, V> OrderedMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn iter(&self) -> impl Iterator<Item = &(K, V)> {
        self.0.iter()
    }
    pub fn get(&self, key: &K) -> Option<&V> {
        self.0.iter().find(|(k, _)| k == key).map(|(_, v)| v)
    }
    pub fn insert(&mut self, key: K, value: V) {
        if let Some((old_key, old)) = self.0.iter_mut().find(|(k, _)| k == &key) {
            *old_key = key;
            *old = value;
        } else {
            self.0.push((key, value));
        }
    }
}
impl<K: Eq + Clone, V: Clone> OrderedMap<K, V> {
    pub fn union(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (k, v) in other.iter() {
            result.insert(k.clone(), v.clone());
        }
        result
    }
}
impl<K: Eq, V: Eq> PartialEq for OrderedMap<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len() && self.0.iter().all(|(k, v)| other.get(k) == Some(v))
    }
}
impl<K: Eq, V: Eq> Eq for OrderedMap<K, V> {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NonQuantifiedChunkKey {
    Basic(BasicChunk),
    Wand(MagicWandChunk),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotSummaryKey {
    pub resource: SnapshotResource,
    pub chunks: Vec<NonQuantifiedChunkKey>,
    pub arguments: Vec<Term>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotSummary<S> {
    pub tagged_snapshot: Option<S>,
    pub definitions: Option<Vec<Term>>,
    pub permission: Term,
    pub permission_exp: Option<Exp>,
}
pub type PmCache = OrderedMap<CacheKey, PermMapDefinition>;
pub type SsCache = OrderedMap<SnapshotSummaryKey, SnapshotSummary<TaggedSummarisingSnapshot>>;
