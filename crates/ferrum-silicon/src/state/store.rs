// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Persistent, insertion-ordered symbolic stores.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Store.scala
//! Status: map-backed store and its factory operations implemented.

use super::terms::Term;
use ferrum_silver::ast::expression::{Exp, ExpKind};

/// A Silver AbstractLocalVar, preserving its complete structural equality and metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbstractLocalVar(Exp);
impl AbstractLocalVar {
    pub fn new(expression: Exp) -> Self {
        assert!(
            matches!(
                expression.kind(),
                ExpKind::LocalVar(_) | ExpKind::Result(_) | ExpKind::LocalVarWithVersion(..)
            ),
            "store keys must be abstract local variables"
        );
        Self(expression)
    }
    pub fn expression(&self) -> &Exp {
        &self.0
    }
}

pub type StoreValue = (Term, Option<Exp>);

pub trait Store {
    fn values(&self) -> &[(AbstractLocalVar, StoreValue)];
    fn get(&self, key: &AbstractLocalVar) -> Option<&Term>;
    fn get_exp(&self, key: &AbstractLocalVar) -> Option<&Exp>;
    fn at(&self, key: &AbstractLocalVar) -> &Term {
        self.get(key).expect("store key is absent")
    }
}

/// Source uses TreeSeqMap in insertion order. Overwriting a key keeps its position.
#[derive(Clone, Debug, Default)]
pub struct MapBackedStore {
    entries: Vec<(AbstractLocalVar, StoreValue)>,
}
impl MapBackedStore {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn from_bindings(
        bindings: impl IntoIterator<Item = (AbstractLocalVar, StoreValue)>,
    ) -> Self {
        let mut result = Self::new();
        for (key, value) in bindings {
            result.insert(key, value);
        }
        result
    }
    fn insert(&mut self, key: AbstractLocalVar, value: StoreValue) {
        if let Some((old_key, old)) = self.entries.iter_mut().find(|(k, _)| k == &key) {
            *old_key = key;
            *old = value;
        } else {
            self.entries.push((key, value));
        }
    }
    #[must_use]
    pub fn with_binding(&self, key: AbstractLocalVar, value: StoreValue) -> Self {
        let mut result = self.clone();
        result.insert(key, value);
        result
    }
    #[must_use]
    pub fn with_store(&self, other: &impl Store) -> Self {
        let mut result = self.clone();
        for (key, value) in other.values() {
            result.insert(key.clone(), value.clone());
        }
        result
    }
    pub fn term_values(&self) -> impl Iterator<Item = (&AbstractLocalVar, &Term)> {
        self.entries.iter().map(|(key, (term, _))| (key, term))
    }
    pub fn exp_values(&self) -> impl Iterator<Item = (&AbstractLocalVar, Option<&Exp>)> {
        self.entries
            .iter()
            .map(|(key, (_, exp))| (key, exp.as_ref()))
    }
}
impl Store for MapBackedStore {
    fn values(&self) -> &[(AbstractLocalVar, StoreValue)] {
        &self.entries
    }
    fn get(&self, key: &AbstractLocalVar) -> Option<&Term> {
        self.entries
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, (term, _))| term)
    }
    fn get_exp(&self, key: &AbstractLocalVar) -> Option<&Exp> {
        self.entries
            .iter()
            .find(|(k, _)| k == key)
            .and_then(|(_, (_, exp))| exp.as_ref())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::{TermFactory, TermOptions};
    use ferrum_silver::ast::expression::LocalVar;
    use ferrum_silver::ast::{ast::Metadata, r#type::Type};
    #[test]
    fn overwriting_keeps_first_key_order_and_new_value() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let var = |name: &str| {
            AbstractLocalVar::new(Exp::new(
                ExpKind::LocalVar(LocalVar::new(name.into(), Type::Int, Metadata::default())),
                Metadata::default(),
            ))
        };
        let x = var("x");
        let y = var("y");
        let store = MapBackedStore::from_bindings([
            (x.clone(), (f.int_literal(1), None)),
            (y.clone(), (f.int_literal(2), None)),
            (x.clone(), (f.int_literal(3), None)),
        ]);
        assert_eq!(
            store.values().iter().map(|(k, _)| k).collect::<Vec<_>>(),
            vec![&x, &y]
        );
        assert_eq!(store.at(&x), &f.int_literal(3));
        assert!(store.get_exp(&x).is_none());
    }
}
