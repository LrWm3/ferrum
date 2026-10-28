//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/package.scala
//!
//! Purpose:
//! Provide deterministic collection and trigger aliases for Silicon.
//!
//! Planned Rust structure:
//! TriggerSet/TriggerSets, immutable Map/toMap, Stack, MList, MSet, MMap, MStack and predefMapToMap
//! conversion.
//!
//! Behavior to preserve:
//! Immutable map uses TreeSeqMap insertion order; mutable sets/maps are linked, stack is
//! sequence/list. Preserve order and duplicate-key behavior rather than random hash iteration.
//!
//! Integration:
//! state, rules, decider and verifier collections.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Native ordered collections and aliases.
//!
//! Status: implemented; integration and broad differential checks remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use indexmap::{IndexMap, IndexSet};
use std::hash::Hash;

pub type TriggerSet<T> = Vec<T>;
pub type TriggerSets<T> = Vec<TriggerSet<T>>;
pub type Map<K, V> = IndexMap<K, V>;
pub type MMap<K, V> = IndexMap<K, V>;
pub type MSet<T> = IndexSet<T>;
pub type MList<T> = Vec<T>;
/// Stack entries are kept in source list order (head at index zero).
pub type Stack<T> = Vec<T>;
pub type MStack<T> = Vec<T>;

/// TreeSeqMap overwrites both the key object and value, without moving its position.
pub fn to_map<K: Eq + Hash, V>(items: impl IntoIterator<Item = (K, V)>) -> Map<K, V> {
    let mut result = Map::new();
    for (key, value) in items {
        if let Some(index) = result.get_index_of(&key) {
            result.shift_remove_index(index);
            result.shift_insert(index, key, value);
        } else {
            result.insert(key, value);
        }
    }
    result
}
