//! Immutable insertion-ordered set.
//!
//! Port of [`InsertionOrderedSet.scala`](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/collections/immutable/InsertionOrderedSet.scala).
//! Reinsertion leaves an element in place; removal followed by insertion appends it.
//!
//! Status: implemented; integration with term and state users remains pending.
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.

use indexmap::IndexSet;
use std::hash::Hash;

/// A value-style set whose iterator follows insertion order.
#[derive(Clone, Debug)]
pub struct InsertionOrderedSet<E> {
    elements: IndexSet<E>,
}

impl<E: Eq + Hash> Default for InsertionOrderedSet<E> {
    fn default() -> Self {
        Self::new()
    }
}

/// Mutable construction helper; `finish` produces the immutable value.
pub struct InsertionOrderedSetBuilder<E> {
    elements: IndexSet<E>,
}
impl<E: Eq + Hash> InsertionOrderedSetBuilder<E> {
    pub fn new() -> Self {
        Self {
            elements: IndexSet::new(),
        }
    }
    pub fn add(&mut self, element: E) -> &mut Self {
        self.elements.insert(element);
        self
    }
    pub fn clear(&mut self) {
        self.elements.clear();
    }
    pub fn finish(self) -> InsertionOrderedSet<E> {
        InsertionOrderedSet {
            elements: self.elements,
        }
    }
}
impl<E: Eq + Hash> Default for InsertionOrderedSetBuilder<E> {
    fn default() -> Self {
        Self::new()
    }
}

impl<E: Eq + Hash> InsertionOrderedSet<E> {
    pub fn new() -> Self {
        Self {
            elements: IndexSet::new(),
        }
    }
    pub fn contains(&self, element: &E) -> bool {
        self.elements.contains(element)
    }
    pub fn len(&self) -> usize {
        self.elements.len()
    }
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &E> {
        self.elements.iter()
    }
    /// Update an exclusively borrowed set without cloning its accumulated elements.
    /// Previously cloned values keep their independent backing storage.
    pub(crate) fn insert(&mut self, element: E) {
        self.elements.insert(element);
    }
    pub(crate) fn remove(&mut self, element: &E) {
        self.elements.shift_remove(element);
    }
}

impl<E: Eq + Hash + Clone> InsertionOrderedSet<E> {
    #[must_use]
    pub fn incl(&self, element: E) -> Self {
        let mut result = self.clone();
        result.elements.insert(element);
        result
    }
    #[must_use]
    pub fn excl(&self, element: &E) -> Self {
        let mut result = self.clone();
        result.elements.shift_remove(element);
        result
    }
}

impl<E: Eq + Hash> FromIterator<E> for InsertionOrderedSet<E> {
    fn from_iter<T: IntoIterator<Item = E>>(iter: T) -> Self {
        Self {
            elements: iter.into_iter().collect(),
        }
    }
}
impl<E: Eq + Hash> PartialEq for InsertionOrderedSet<E> {
    fn eq(&self, other: &Self) -> bool {
        self.elements == other.elements
    }
}
impl<E: Eq + Hash> Eq for InsertionOrderedSet<E> {}
impl<'a, E> IntoIterator for &'a InsertionOrderedSet<E> {
    type Item = &'a E;
    type IntoIter = indexmap::set::Iter<'a, E>;
    fn into_iter(self) -> Self::IntoIter {
        self.elements.iter()
    }
}

impl<E> IntoIterator for InsertionOrderedSet<E> {
    type Item = E;
    type IntoIter = indexmap::set::IntoIter<E>;
    fn into_iter(self) -> Self::IntoIter {
        self.elements.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::Cell, rc::Rc};

    #[derive(Debug)]
    struct Counted {
        value: usize,
        clones: Rc<Cell<usize>>,
    }
    impl Clone for Counted {
        fn clone(&self) -> Self {
            self.clones.set(self.clones.get() + 1);
            Self {
                value: self.value,
                clones: self.clones.clone(),
            }
        }
    }
    impl PartialEq for Counted {
        fn eq(&self, other: &Self) -> bool {
            self.value == other.value
        }
    }
    impl Eq for Counted {}
    impl Hash for Counted {
        fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
            self.value.hash(state);
        }
    }

    #[test]
    fn owned_updates_preserve_order_and_snapshots_without_cloning_elements() {
        let clones = Rc::new(Cell::new(0));
        let value = |value| Counted {
            value,
            clones: clones.clone(),
        };
        let mut set = InsertionOrderedSet::new();
        for i in 0..128 {
            set.insert(value(i));
        }
        assert_eq!(clones.get(), 0, "growth must not copy the accumulated set");
        let snapshot = set.clone();
        clones.set(0);
        set.insert(value(4)); // Reinsertion must leave the original entry in place.
        set.remove(&value(5));
        set.remove(&value(999));
        set.insert(value(5));
        assert_eq!(clones.get(), 0, "updates must not copy stored elements");
        assert_eq!(
            snapshot.iter().map(|v| v.value).collect::<Vec<_>>(),
            (0..128).collect::<Vec<_>>()
        );
        assert_eq!(
            set.iter().map(|v| v.value).collect::<Vec<_>>(),
            (0..128).filter(|i| *i != 5).chain([5]).collect::<Vec<_>>()
        );
        assert_eq!(
            set, snapshot,
            "set equality remains independent of insertion order"
        );
    }
}
