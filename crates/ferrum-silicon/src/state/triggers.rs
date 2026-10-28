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
//! Status: partial; source generic trigger search and arithmetic axiom rewriting are connected.
//! Forbidden trigger subterms are rewritten per occurrence, including equal subterms.

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
    next_unique: std::cell::Cell<u64>,
    next_rewrite: std::cell::Cell<u64>,
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
            } => false,
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

/// Errors from source generic trigger search and arithmetic axiom rewriting.
#[derive(Debug)]
pub enum NativeTriggerSearchError {
    Traversal(UnsupportedSubterms),
    Transform(UnsupportedTriggerTransform),
    Trigger(TriggerError),
    RequiresAxiomRewrite,
    UnsupportedLet,
}
struct NativeTriggerAdapter<'a> {
    factory: &'a TermFactory,
    generator: &'a TriggerGenerator,
    advanced: bool,
}
impl ferrum_silver::ast::utility::generic_trigger_generator::TriggerAdapter
    for NativeTriggerAdapter<'_>
{
    type Node = Term;
    type Exp = Term;
    type Var = Term;
    type Error = NativeTriggerSearchError;
    fn root(&self, exp: &Term) -> Term {
        exp.clone()
    }
    fn children(&self, node: &Term) -> Result<Vec<Term>, Self::Error> {
        node.subterms().map_err(NativeTriggerSearchError::Traversal)
    }
    fn expression(&self, node: &Term) -> Option<Term> {
        Some(node.clone())
    }
    fn quantified_vars(&self, node: &Term) -> Option<Vec<Term>> {
        match node.kind() {
            TermKind::Quantification { vars, .. } => Some(vars.clone()),
            _ => None,
        }
    }
    fn possible_trigger(&self, exp: &Term) -> Result<bool, Self::Error> {
        Ok(self.generator.is_possible_trigger(exp))
    }
    fn arguments(&self, exp: &Term) -> Result<Vec<Term>, Self::Error> {
        exp.subterms().map_err(NativeTriggerSearchError::Traversal)
    }
    fn with_arguments(&self, exp: &Term, args: Vec<Term>) -> Result<Term, Self::Error> {
        TriggerGenerator::with_args(self.factory, exp, &args)
            .map_err(NativeTriggerSearchError::Trigger)
    }
    fn variables_in(&self, exp: &Term) -> Result<Vec<Term>, Self::Error> {
        let variables = exp
            .deep_collect(&mut |term| matches!(term.kind(), TermKind::Var(_)).then(|| term.clone()))
            .map_err(NativeTriggerSearchError::Traversal)?;
        let mut unique = Vec::new();
        for variable in variables {
            if !unique.contains(&variable) {
                unique.push(variable);
            }
        }
        Ok(unique)
    }
    fn rewrite_forbidden(&mut self, exp: &Term) -> Result<(Term, Vec<Term>), Self::Error> {
        let fresh = std::cell::RefCell::new(Vec::new());
        let result = self
            .factory
            .transform_preorder(exp, &|term| {
                if !self.generator.is_forbidden(term)
                    || (self.advanced
                        && matches!(term.kind(), TermKind::Plus(..) | TermKind::Minus(..)))
                {
                    return None;
                }
                let id = self.generator.next_unique.get();
                self.generator.next_unique.set(id.wrapping_add(1));
                let var = self.factory.var(
                    crate::state::identifiers::Identifier::new(format!("fresh__{id}")),
                    term.sort().clone(),
                    false,
                );
                fresh.borrow_mut().push(var.clone());
                Some(var)
            })
            .map_err(NativeTriggerSearchError::Transform)?;
        Ok((result, fresh.into_inner()))
    }
    fn additional_relevant(
        &self,
        _: &Term,
        _: &[Term],
        _: &[Term],
    ) -> Result<Vec<Term>, Self::Error> {
        Ok(vec![])
    }
    fn modify(
        &self,
        _: &Term,
        _: &[Term],
        _: &[Vec<ferrum_silver::ast::utility::generic_trigger_generator::Candidate<Term, Term>>],
    ) -> Result<
        Option<Vec<ferrum_silver::ast::utility::generic_trigger_generator::Candidate<Term, Term>>>,
        Self::Error,
    > {
        Ok(None)
    }
    fn has_subnode(&self, parent: &Term, child: &Term) -> Result<bool, Self::Error> {
        parent
            .has_subterm(child)
            .map_err(NativeTriggerSearchError::Traversal)
    }
}
impl TriggerGenerator {
    /// Try each search term in source order and return its first nonempty trigger group.
    pub fn generate_group(
        &self,
        factory: &TermFactory,
        variables: &[Term],
        search: &[Term],
        advanced: bool,
    ) -> Result<(Vec<crate::state::terms::Trigger>, Vec<Term>), NativeTriggerSearchError> {
        use ferrum_silver::ast::utility::generic_trigger_generator::generate_trigger_set_groups;
        let mut adapter = NativeTriggerAdapter {
            factory,
            generator: self,
            advanced,
        };
        for term in search {
            if let Some((sets, extra)) = generate_trigger_set_groups(&mut adapter, variables, term)?
                .into_iter()
                .next()
            {
                return Ok((
                    sets.into_iter()
                        .map(|set| crate::state::terms::Trigger { terms: set.exps })
                        .collect(),
                    extra,
                ));
            }
        }
        Ok((vec![], vec![]))
    }
}

impl From<UnsupportedSubterms> for NativeTriggerSearchError {
    fn from(error: UnsupportedSubterms) -> Self {
        Self::Traversal(error)
    }
}
struct NativeAxiomAdapter<'a> {
    factory: &'a TermFactory,
    generator: &'a TriggerGenerator,
}
impl ferrum_silver::ast::utility::generic_axiom_rewriter::AxiomAdapter for NativeAxiomAdapter<'_> {
    type Exp = Term;
    type Var = Term;
    type Quantifier = Term;
    type Trigger = crate::state::terms::Trigger;
    type Error = NativeTriggerSearchError;
    fn invalid_terms(&self, expression: &Term) -> Result<Vec<Term>, Self::Error> {
        expression
            .shallow_collect(&mut |term| self.generator.is_forbidden(term).then(|| term.clone()))
            .map_err(NativeTriggerSearchError::Traversal)
    }
    fn variables(&self, q: &Term) -> Vec<Term> {
        match q.kind() {
            TermKind::Quantification { vars, .. } => vars.clone(),
            _ => vec![],
        }
    }
    fn body(&self, q: &Term) -> Term {
        match q.kind() {
            TermKind::Quantification { body, .. } => body.clone(),
            _ => q.clone(),
        }
    }
    fn var_exp(&self, v: &Term) -> Term {
        v.clone()
    }
    fn contains(&self, expression: &Term, value: &Term) -> Result<bool, Self::Error> {
        expression
            .contains(value)
            .map_err(NativeTriggerSearchError::Traversal)
    }
    fn replace(
        &self,
        expression: &Term,
        original: &Term,
        replacement: &Term,
    ) -> Result<Term, Self::Error> {
        self.factory
            .replace(
                expression,
                &HashMap::from([(original.clone(), replacement.clone())]),
            )
            .map_err(NativeTriggerSearchError::Transform)
    }
    fn fresh_for(&mut self, var: &Term, _: &Term) -> Result<Term, Self::Error> {
        let TermKind::Var(value) = var.kind() else {
            return Err(NativeTriggerSearchError::RequiresAxiomRewrite);
        };
        let id = self.generator.next_rewrite.get();
        self.generator.next_rewrite.set(id.wrapping_add(1));
        Ok(self.factory.var(
            crate::state::identifiers::Identifier::new(format!("{}@rw{id}", value.id.name())),
            var.sort().clone(),
            false,
        ))
    }
    fn solve(&self, lhs: &Term, rhs: &Term, variable: &Term) -> Result<Option<Term>, Self::Error> {
        let solver = SimpleArithmeticSolver {
            factory: self.factory,
            render: |t: &Term| Ok::<_, NativeTriggerSearchError>(format!("{:?}", t.kind())),
            render_sort: |sort: &crate::state::terms::Sort| {
                Ok::<_, NativeTriggerSearchError>(sort.to_string())
            },
        };
        match ferrum_silver::ast::utility::generic_arithmetic_solver::solve(&solver, lhs.clone(), rhs.clone(), variable.clone())? {
            ferrum_silver::ast::utility::generic_arithmetic_solver::SolverResult::SolvingSuccess { rhs, .. } => Ok(Some(rhs)),
            _ => Ok(None),
        }
    }
    fn equal(&self, a: Term, b: Term) -> Term {
        self.factory.equals(a, b)
    }
    fn and(&self, terms: Vec<Term>) -> Term {
        self.factory.and(terms)
    }
    fn implies(&self, a: Term, b: Term) -> Term {
        self.factory.implies(a, b)
    }
    fn trigger(&self, exps: Vec<Term>) -> Self::Trigger {
        crate::state::terms::Trigger { terms: exps }
    }
    fn copy_quantifier(
        &self,
        q: &Term,
        vars: Vec<Term>,
        body: Term,
        triggers: Vec<Self::Trigger>,
    ) -> Result<Term, Self::Error> {
        let TermKind::Quantification {
            quantifier,
            name,
            is_global,
            weight,
            ..
        } = q.kind()
        else {
            return Err(NativeTriggerSearchError::RequiresAxiomRewrite);
        };
        self.factory
            .quantification(
                *quantifier,
                vars,
                body,
                triggers,
                name.clone(),
                *is_global,
                *weight,
            )
            .map_err(NativeTriggerSearchError::Transform)
    }
}
impl TriggerGenerator {
    /// Apply the source arithmetic trigger rewrite, retaining the original quantifier
    /// when isolation cannot solve every invalid trigger term.
    pub fn rewrite_axiom(
        &self,
        factory: &TermFactory,
        quantifier: &Term,
    ) -> Result<Term, NativeTriggerSearchError> {
        let TermKind::Quantification { triggers, .. } = quantifier.kind() else {
            return Err(NativeTriggerSearchError::RequiresAxiomRewrite);
        };
        let sets = triggers
            .iter()
            .map(
                |trigger| ferrum_silver::ast::utility::generic_trigger_generator::TriggerSet {
                    exps: trigger.terms.clone(),
                },
            )
            .collect::<Vec<_>>();
        let mut adapter = NativeAxiomAdapter {
            factory,
            generator: self,
        };
        Ok(
            ferrum_silver::ast::utility::generic_axiom_rewriter::rewrite(
                &mut adapter,
                quantifier,
                &sets,
            )?
            .unwrap_or_else(|| quantifier.clone()),
        )
    }
}

#[cfg(test)]
mod native_rewrite_tests {
    use super::*;
    use crate::state::{
        identifiers::Identifier,
        terms::{ApplicableData, ApplicableKind, Quantifier, Sort, TermOptions, Trigger},
    };
    #[test]
    fn equal_forbidden_occurrences_get_distinct_fresh_variables() {
        use ferrum_silver::ast::utility::generic_trigger_generator::TriggerAdapter;
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let x = factory.var(Identifier::new("x"), Sort::Int, false);
        let f = factory.applicable(ApplicableData {
            kind: ApplicableKind::Fun,
            id: Identifier::new("f"),
            arg_sorts: vec![Sort::Int, Sort::Int],
            result_sort: Sort::Int,
        });
        let forbidden = factory.plus(x, factory.int_literal(1));
        let input = factory.app(f, vec![forbidden.clone(), forbidden]);
        let generator = TriggerGenerator::default();
        let mut adapter = NativeTriggerAdapter {
            factory: &factory,
            generator: &generator,
            advanced: false,
        };
        let (result, fresh) = adapter.rewrite_forbidden(&input).unwrap();
        assert_eq!(fresh.len(), 2);
        assert_ne!(fresh[0], fresh[1]);
        let TermKind::App { args, .. } = result.kind() else {
            panic!("expected application")
        };
        assert_eq!(args, &fresh);
    }
    #[test]
    fn arithmetic_trigger_isolated_into_a_fresh_quantified_variable() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let x = factory.var(Identifier::new("x"), Sort::Int, false);
        let f = factory.applicable(ApplicableData {
            kind: ApplicableKind::Fun,
            id: Identifier::new("f"),
            arg_sorts: vec![Sort::Int],
            result_sort: Sort::Int,
        });
        let application = factory.app(f, vec![factory.plus(x.clone(), factory.int_literal(1))]);
        let q = factory
            .quantification(
                Quantifier::Forall,
                vec![x.clone()],
                factory.equals(application.clone(), x.clone()),
                vec![Trigger {
                    terms: vec![application],
                }],
                "test".into(),
                false,
                None,
            )
            .unwrap();
        let result = TriggerGenerator::default()
            .rewrite_axiom(&factory, &q)
            .unwrap();
        let TermKind::Quantification {
            vars,
            triggers,
            body,
            ..
        } = result.kind()
        else {
            panic!("expected quantifier")
        };
        assert_eq!(vars.len(), 1);
        assert_ne!(vars[0], x);
        assert!(vars[0].free_variables().unwrap().contains(&vars[0]));
        assert!(!triggers[0].terms[0].contains(&x).unwrap());
        assert!(body.contains(&vars[0]).unwrap());
    }
}
