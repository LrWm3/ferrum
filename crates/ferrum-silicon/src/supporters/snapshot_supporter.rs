//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/SnapshotSupporter.scala
//!
//! Purpose:
//! Choose snapshot sorts and split/combine snapshots for assertion production and consumption.
//!
//! Planned Rust structure:
//! Port SnapshotSupporter and DefaultSnapshotSupporter optimalSnapshotSort, unit/combine/finalize,
//! empty constraint, production adaptation and createSnapshotPair.
//!
//! Behavior to preserve:
//! Default uses Unit and Combine, finalization is identity and empty constraint lazily requires
//! snapshot = Unit. Choose field sort, recursively inspect predicate body with cycle guard,
//! quantified field-value function sort or Snap fallback; preserve purity and conditional cases.
//! Split non-Unit snapshot via First/Second and assume its reconstruction equality; Unit cannot be
//! decomposed.
//!
//! Integration:
//! rules::{producer,consumer}, supporters::qps::predicate_snap_generator and
//! mask_heap_snapshot_supporter; state::terms and decider::decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for lazy snapshot effects, metadata and ownership.
//!
//! Open decisions:
//! Reconcile snapshot function/continuation signatures and optimal-sort recursion with producer,
//! consumer and mask heap alternative.
//!
//! Status: partial; default snapshot sorting, combination, constraints and decomposition implemented.
//! Concrete verifier/debug integration and paired snapshot-function callbacks remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::symbol_converter::{DefaultSymbolConverter, SymbolConversionError};
use crate::state::terms::{Sort, Term, TermFactory, TermKind};
use ferrum_silver::ast::{
    expression::{Exp, ExpKind},
    program::{Field, Predicate, Program},
    utility::quantified_permissions::quantified_permission_assertion,
};

#[derive(Debug)]
pub enum SnapshotError<E> {
    Sort(SymbolConversionError),
    MissingPredicate(String),
    UnitDecomposition,
    Assume(E),
}
pub struct DefaultSnapshotSupporter<'a> {
    pub symbols: &'a DefaultSymbolConverter,
    pub factory: &'a TermFactory,
}
impl DefaultSnapshotSupporter<'_> {
    pub fn wand_sort(&self) -> Sort {
        Sort::MagicWandSnapFunction
    }
    pub fn adapt_produce_snapshot_function<F>(&self, snapshot_function: F) -> F {
        snapshot_function
    }
    /// Projection snapshot functions convert their fixed term to the requested sort.
    pub fn convert_projection(&self, snapshot: Term, sort: Sort) -> Term {
        self.factory.sort_wrapper(snapshot, sort)
    }
    pub fn unit_snapshot(&self) -> Term {
        self.factory.unit()
    }
    pub fn combine_snapshots(&self, left: Term, right: Term) -> Term {
        self.factory.combine(left, right)
    }
    pub fn finalize_consumed_snapshot(&self, snapshot: Term) -> Term {
        snapshot
    }
    pub fn empty_snapshot_constraint(&self, snapshot: impl FnOnce() -> Term) -> Term {
        self.factory.equals(snapshot(), self.factory.unit())
    }
    /// Decomposition must assume equality before handing either projection to a caller.
    pub fn create_snapshot_pair<E>(
        &self,
        snapshot: Term,
        mut assume: impl FnMut(Term) -> Result<(), E>,
    ) -> Result<(Term, Term), SnapshotError<E>> {
        if matches!(snapshot.kind(), TermKind::Unit) {
            return Err(SnapshotError::UnitDecomposition);
        }
        let left = self.factory.first(snapshot.clone());
        let right = self.factory.second(snapshot.clone());
        assume(
            self.factory
                .equals(snapshot, self.factory.combine(left.clone(), right.clone())),
        )
        .map_err(SnapshotError::Assume)?;
        Ok((left, right))
    }
    pub fn field_sort<E>(&self, field: &Field) -> Result<Sort, SnapshotError<E>> {
        self.symbols
            .to_sort(&field.typ)
            .map_err(SnapshotError::Sort)
    }
    pub fn predicate_sort<E>(
        &self,
        predicate: &Predicate,
        program: &Program,
        known: &crate::package::Map<String, Sort>,
    ) -> Result<Sort, SnapshotError<E>> {
        if let Some(sort) = known.get(&predicate.name) {
            return Ok(sort.clone());
        }
        match &predicate.body {
            Some(body) => self.optimal_snapshot_sort(body, program).map(|v| v.0),
            None => Ok(Sort::Snap),
        }
    }
    pub fn optimal_snapshot_sort<E>(
        &self,
        assertion: &Exp,
        program: &Program,
    ) -> Result<(Sort, bool), SnapshotError<E>> {
        self.optimal(assertion, program, &[])
    }
    fn optimal<E>(
        &self,
        assertion: &Exp,
        program: &Program,
        visited: &[String],
    ) -> Result<(Sort, bool), SnapshotError<E>> {
        if assertion.is_pure() {
            return Ok((Sort::Snap, !matches!(assertion.kind(), ExpKind::And(..))));
        }
        match assertion.kind() {
            ExpKind::FieldAccessPredicate(access, _) => {
                Ok((self.field_sort(&access.field)?, false))
            }
            ExpKind::PredicateAccessPredicate(access) => {
                let name = &access.location.predicate_name;
                if visited.contains(name) {
                    return Ok((Sort::Snap, false));
                }
                let predicate = program
                    .predicates
                    .iter()
                    .find(|p| &p.name == name)
                    .ok_or_else(|| SnapshotError::MissingPredicate(name.clone()))?;
                if let Some(body) = &predicate.body {
                    let mut visited = visited.to_vec();
                    visited.push(name.clone());
                    self.optimal(body, program, &visited)
                } else {
                    Ok((Sort::Snap, false))
                }
            }
            ExpKind::Implies(_, body) => self.optimal(body, program, visited),
            ExpKind::And(_, _) => Ok((Sort::Snap, false)),
            ExpKind::CondExp(_, left, right) if left.is_pure() && right.is_pure() => {
                let a = self.optimal(left, program, visited)?;
                let b = self.optimal(right, program, visited)?;
                let pure = a.1 && b.1;
                assert!(!pure, "impure conditional produced pure snapshot branches");
                Ok((if a.0 == b.0 { a.0 } else { Sort::Snap }, pure))
            }
            _ => {
                if let Some((_, _, access)) = quantified_permission_assertion(assertion) {
                    if let ExpKind::FieldAccessPredicate(field, _) = access.kind() {
                        return Ok((
                            Sort::FieldValueFunction {
                                codomain: Box::new(self.field_sort(&field.field)?),
                                field_name: field.field.name.clone(),
                            },
                            false,
                        ));
                    }
                }
                Ok((Sort::Snap, false))
            }
        }
    }
}
