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
