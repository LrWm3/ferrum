//! Mutable insertion-ordered map of insertion-ordered sets.
//!
//! Port of [`MultiMap.scala`](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/collections/mutable/MultiMap.scala).
//! Status: implemented; integration with callers remains pending.
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use indexmap::{IndexMap, IndexSet};
use std::hash::Hash;

#[derive(Clone, Debug)]
pub struct MMultiMap<K, V> {
    entries: IndexMap<K, IndexSet<V>>,
}

impl<K: Eq + Hash, V: Eq + Hash> Default for MMultiMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Eq + Hash, V: Eq + Hash> MMultiMap<K, V> {
    pub fn new() -> Self {
        Self {
            entries: IndexMap::new(),
        }
    }
    pub fn add_binding(&mut self, key: K, value: V) -> &mut Self {
        self.entries.entry(key).or_default().insert(value);
        self
    }
    pub fn remove_binding(&mut self, key: &K, value: &V) -> &mut Self {
        if let Some(values) = self.entries.get_mut(key) {
            values.shift_remove(value);
            if values.is_empty() {
                self.entries.shift_remove(key);
            }
        }
        self
    }
    pub fn entry_exists(&self, key: &K, predicate: impl FnMut(&V) -> bool) -> bool {
        self.entries
            .get(key)
            .is_some_and(|values| values.iter().any(predicate))
    }
    pub fn get(&self, key: &K) -> Option<&IndexSet<V>> {
        self.entries.get(key)
    }
    pub fn iter(&self) -> impl Iterator<Item = (&K, &IndexSet<V>)> {
        self.entries.iter()
    }
}
