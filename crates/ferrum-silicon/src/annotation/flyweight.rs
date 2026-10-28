//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/annotation/src/main/scala/flyweight.scala
//!
//! Purpose:
//! Generate the historical annotation-driven flyweight classes.
//!
//! Planned Rust structure:
//! flyweight and flyweightMacro.impl inspect class and optional companion; generate private
//! constructor, pool, apply, optional copy and unapply, preserving companion definitions.
//!
//! Behavior to preserve:
//! Reject invalid annottees and explicit custom apply without return type; matching apply
//! is renamed _apply. Pool lookup and insertion are separate, and identity hash is used.
//! This annotation is dormant in the current build; Terms uses ConditionalFlyweight
//! factories.
//!
//! Integration:
//! state::terms factories and annotation build configuration.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Whether any native macro is needed once term factories are ported.
//!
//! Status: native strong-pool substitute implemented. Scala annotation expansion remains
//! dormant in the pinned upstream build; source-generation features are not activated.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{Arc, Mutex};

/// Native substitute for the dormant Scala annotation's strong companion pool.
/// The factory runs outside the lock, allowing recursive construction. Concurrent
/// creators may both run, but only the canonical stored `Arc` is returned.
pub struct FlyweightPool<K, V> {
    values: Mutex<HashMap<K, Arc<V>>>,
}
impl<K, V> Default for FlyweightPool<K, V> {
    fn default() -> Self {
        Self {
            values: Mutex::new(HashMap::new()),
        }
    }
}
impl<K: Eq + Hash, V> FlyweightPool<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn get_or_intern(&self, key: K, create: impl FnOnce(&K) -> V) -> Arc<V> {
        if let Some(value) = self
            .values
            .lock()
            .expect("flyweight pool poisoned")
            .get(&key)
            .cloned()
        {
            return value;
        }
        let candidate = Arc::new(create(&key));
        self.values
            .lock()
            .expect("flyweight pool poisoned")
            .entry(key)
            .or_insert(candidate)
            .clone()
    }
    pub fn len(&self) -> usize {
        self.values.lock().expect("flyweight pool poisoned").len()
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn clear(&self) {
        self.values.lock().expect("flyweight pool poisoned").clear();
    }
}
