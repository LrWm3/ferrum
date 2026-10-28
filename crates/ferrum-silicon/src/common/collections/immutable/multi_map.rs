//! Immutable map-of-sets helpers.
//!
//! Port of [`MultiMap.scala`](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/collections/immutable/MultiMap.scala).
//! Status: implemented; integration with callers remains pending.
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use std::collections::{HashMap, HashSet};
use std::hash::Hash;

pub type MultiMap<K, V> = HashMap<K, HashSet<V>>;

/// Return a new map with a binding added.
pub fn add_binding<K: Eq + Hash + Clone, V: Eq + Hash + Clone>(
    map: &MultiMap<K, V>,
    key: K,
    value: V,
) -> MultiMap<K, V> {
    let mut result = map.clone();
    result.entry(key).or_default().insert(value);
    result
}

/// Remove a binding, retaining the key even when its set becomes empty.
pub fn remove_binding<K: Eq + Hash + Clone, V: Eq + Hash + Clone>(
    map: &MultiMap<K, V>,
    key: &K,
    value: &V,
) -> MultiMap<K, V> {
    let mut result = map.clone();
    if let Some(values) = result.get_mut(key) {
        values.remove(value);
    }
    result
}
