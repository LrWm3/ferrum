//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Triggers.scala
//!
//! Purpose:
//! Generate and rewrite term-level quantifier triggers.
//!
//! Planned Rust structure:
//! Trigger, TriggerGenerator, AxiomRewriter and SimpleArithmeticSolver adapt Silver generic
//! trigger and arithmetic machinery to Silicon terms.
//!
//! Behavior to preserve:
//! First trigger group may introduce extra variables; assemble then attempt rewrite,
//! falling back to original. Custom trigger predicates override defaults;
//! arithmetic/boolean operations are forbidden except advanced plus/minus; reconstruction
//! checks arity. Fresh rewrite variables use @rw counter.
//!
//! Search-based assembly installs the advanced filter temporarily and clears it
//! after search; the mutable generator is explicitly not thread-safe.
//!
//! Integration:
//! state::terms, state::utils and ferrum_silver::ast::utility trigger machinery.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Generic trigger extension points and counter ownership.
//!
//! Status: partial; trigger classification, overrides and argument reconstruction implemented.
//! Generic trigger search, axiom rewriting and quantification assembly remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::{
    ApplicableKind, ApplicationTarget, Term, TermFactory, TermKind, UnsupportedSubterms,
    UnsupportedTriggerTransform,
};
use std::collections::HashMap;

/// Filters are mutable per generator, as in the source; use one instance per worker.
#[derive(Default)]
pub struct TriggerGenerator {
    pub custom_possible: Option<Box<dyn Fn(&Term) -> Option<bool>>>,
    pub custom_forbidden: Option<Box<dyn Fn(&Term) -> Option<bool>>>,
}
#[derive(Debug)]
pub enum TriggerError {
    Traversal(UnsupportedSubterms),
    Transform(UnsupportedTriggerTransform),
    Arity { expected: usize, actual: usize },
}
impl TriggerGenerator {
    pub fn default_is_possible_trigger(term: &Term) -> bool {
        match term.kind() {
            TermKind::App {
                applicable: ApplicationTarget::Function(f),
                ..
            } => f.data().kind != ApplicableKind::Macro,
            TermKind::App {
                applicable: ApplicationTarget::Variable(_),
                ..
            } => true,
            TermKind::CustomEquals(..)
            | TermKind::PermMin(..)
            | TermKind::SeqRanged(..)
            | TermKind::SeqNil(..)
            | TermKind::SeqSingleton(..)
            | TermKind::SeqAppend(..)
            | TermKind::SeqDrop(..)
            | TermKind::SeqTake(..)
            | TermKind::SeqUpdate(..)
            | TermKind::SeqLength(..)
            | TermKind::SeqAt(..)
            | TermKind::SeqIn(..)
            | TermKind::EmptySet(..)
            | TermKind::SingletonSet(..)
            | TermKind::SetAdd(..)
            | TermKind::SetUnion(..)
            | TermKind::SetIntersection(..)
            | TermKind::SetDifference(..)
            | TermKind::SetIn(..)
            | TermKind::SetCardinality(..)
            | TermKind::EmptyMultiset(..)
            | TermKind::SingletonMultiset(..)
            | TermKind::MultisetAdd(..)
            | TermKind::MultisetUnion(..)
            | TermKind::MultisetIntersection(..)
            | TermKind::MultisetDifference(..)
            | TermKind::MultisetCardinality(..)
            | TermKind::MultisetCount(..)
            | TermKind::MapLookup(..)
            | TermKind::MapCardinality(..)
            | TermKind::MapDomain(..)
            | TermKind::MapRange(..)
            | TermKind::MapUpdate(..)
            | TermKind::MwsfLookup(..)
            | TermKind::Unit
            | TermKind::Combine(..)
            | TermKind::First(..)
            | TermKind::Second(..)
            | TermKind::Domain(..)
            | TermKind::PredicateDomain(..)
            | TermKind::Lookup(..)
            | TermKind::PredicateLookup(..) => true,
            _ => false,
        }
    }

    pub fn is_possible_trigger(&self, term: &Term) -> bool {
        self.custom_possible
            .as_ref()
            .and_then(|f| f(term))
            .unwrap_or_else(|| Self::default_is_possible_trigger(term))
    }
    pub fn default_is_forbidden(term: &Term) -> bool {
        matches!(
            term.kind(),
            TermKind::Plus(..)
                | TermKind::Minus(..)
                | TermKind::Times(..)
                | TermKind::Div(..)
                | TermKind::Mod(..)
                | TermKind::Not(..)
                | TermKind::Or(..)
                | TermKind::And(..)
                | TermKind::Implies(..)
                | TermKind::Iff(..)
                | TermKind::Ite(..)
                | TermKind::BuiltinEquals(..)
                | TermKind::Less(..)
                | TermKind::AtMost(..)
                | TermKind::Greater(..)
                | TermKind::AtLeast(..)
                | TermKind::PermTimes(..)
                | TermKind::IntPermTimes(..)
                | TermKind::PermIntDiv(..)
                | TermKind::PermPermDiv(..)
                | TermKind::PermPlus(..)
                | TermKind::PermMinus(..)
                | TermKind::PermLess(..)
                | TermKind::PermAtMost(..)
                | TermKind::Distinct(..)
        )
    }
    pub fn is_forbidden(&self, term: &Term) -> bool {
        self.custom_forbidden
            .as_ref()
            .and_then(|f| f(term))
            .unwrap_or_else(|| Self::default_is_forbidden(term))
    }
    pub fn advanced_forbidden(term: &Term) -> Option<bool> {
        if matches!(term.kind(), TermKind::Plus(..) | TermKind::Minus(..)) {
            Some(false)
        } else {
            None
        }
    }
    /// Sequential replacement matches the source even when children are repeated.
    pub fn with_args(
        factory: &TermFactory,
        term: &Term,
        args: &[Term],
    ) -> Result<Term, TriggerError> {
        let children = term.subterms().map_err(TriggerError::Traversal)?;
        if children.len() != args.len() {
            return Err(TriggerError::Arity {
                expected: children.len(),
                actual: args.len(),
            });
        }
        let mut result = term.clone();
        for (old, new) in children.into_iter().zip(args) {
            if old != *new {
                result = factory
                    .replace(&result, &HashMap::from([(old, new.clone())]))
                    .map_err(TriggerError::Transform)?;
            }
        }
        Ok(result)
    }
}

/// Native adapter for Silver's generic arithmetic isolation algorithm.
/// Source rendering is supplied explicitly until Silicon term display is complete.
pub struct SimpleArithmeticSolver<'a, R, T> {
    pub factory: &'a TermFactory,
    pub render: R,
    pub render_sort: T,
}
impl<R, T, E> ferrum_silver::ast::utility::generic_arithmetic_solver::ArithmeticAdapter
    for SimpleArithmeticSolver<'_, R, T>
where
    R: Fn(&Term) -> Result<String, E>,
    T: Fn(&crate::state::terms::Sort) -> Result<String, E>,
    E: From<UnsupportedSubterms>,
{
    type Exp = Term;
    type Var = Term;
    type Type = crate::state::terms::Sort;
    type Error = E;
    fn render_exp(&self, exp: &Term) -> Result<String, E> {
        (self.render)(exp)
    }
    fn render_var(&self, var: &Term) -> Result<String, E> {
        (self.render)(var)
    }
    fn render_type(&self, typ: &Self::Type) -> Result<String, E> {
        (self.render_sort)(typ)
    }
    fn var_exp(&self, var: &Term) -> Term {
        var.clone()
    }
    fn typ(&self, exp: &Term) -> Result<Self::Type, E> {
        Ok(exp.sort().clone())
    }
    fn is_int(&self, typ: &Self::Type) -> bool {
        *typ == crate::state::terms::Sort::Int
    }
    fn occurrences(&self, node: &Term, target: &Term) -> Result<usize, E> {
        let mut count = usize::from(node == target);
        for child in node.subterms().map_err(E::from)? {
            count += self.occurrences(&child, target)?;
        }
        Ok(count)
    }
    fn contains(&self, node: &Term, target: &Term) -> Result<bool, E> {
        if node == target {
            return Ok(true);
        }
        for child in node.subterms().map_err(E::from)? {
            if self.contains(&child, target)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    fn plus(&self, left: Term, right: Term) -> Term {
        self.factory.plus(left, right)
    }
    fn minus(&self, left: Term, right: Term) -> Term {
        self.factory.minus(left, right)
    }
    fn as_plus(&self, exp: &Term) -> Option<(Term, Term)> {
        if let TermKind::Plus(a, b) = exp.kind() {
            Some((a.clone(), b.clone()))
        } else {
            None
        }
    }
    fn as_minus(&self, exp: &Term) -> Option<(Term, Term)> {
        if let TermKind::Minus(a, b) = exp.kind() {
            Some((a.clone(), b.clone()))
        } else {
            None
        }
    }
}
