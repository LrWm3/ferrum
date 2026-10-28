//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/QuantifierSupporter.scala
//!
//! Purpose:
//! Generate and validate triggers and eliminate heap-dependent trigger terms.
//!
//! Planned Rust structure:
//! Port QuantifierSupporter and DefaultQuantifierSupporter autoTrigger,
//! makeTriggersHeapIndependent and detectQuantificationProblems.
//!
//! Behavior to preserve:
//! Keep explicit triggers; otherwise append generator extra variables. Split each distinct trigger
//! into a quantification with fresh projection variables replacing field/predicate snapshot
//! function applications. For forall report missing triggers, missing bound variables, invalid and
//! forbidden terms in source check order; exists has no checks.
//!
//! Integration:
//! state::triggers trigger generator, rules::evaluator and verifier; Silver parser debug types.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for quantifier identity, variable freshness and trigger order.
//!
//! Open decisions:
//! Agree on fresh declaration/quantifier metadata and mapping iteration with evaluator and term
//! factories.
//!
//! Status: partial; trigger generation dispatch, heap-independent trigger splitting
//! and source quantifier checks implemented. Trigger search/render/fresh services remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::{
    ApplicableKind, ApplicationTarget, Quantifier, Sort, Term, TermFactory, TermKind, Trigger,
    UnsupportedSubterms, UnsupportedTriggerTransform,
};
use crate::state::triggers::TriggerGenerator;

#[derive(Debug)]
pub enum QuantifierSupportError<E> {
    NotQuantifier,
    MissingDependency,
    Traversal(UnsupportedSubterms),
    Transform(UnsupportedTriggerTransform),
    Service(E),
}
pub trait QuantifierTriggerServices {
    type Error;
    fn generate_trigger_sets(
        &mut self,
        variables: &[Term],
        body: &Term,
    ) -> Result<Option<(Vec<Trigger>, Vec<Term>)>, Self::Error>;
    fn fresh_projection(&mut self, sort: &Sort) -> Result<Term, Self::Error>;
    fn render_term(&mut self, term: &Term) -> Result<String, Self::Error>;
    fn render_trigger(&mut self, trigger: &Trigger) -> Result<String, Self::Error>;
}
/// Preserve explicit triggers; otherwise install generated sets and extra binders.
pub fn auto_trigger<S: QuantifierTriggerServices>(
    factory: &TermFactory,
    services: &mut S,
    q: &Term,
) -> Result<Term, QuantifierSupportError<S::Error>> {
    let TermKind::Quantification {
        quantifier,
        vars,
        body,
        triggers,
        name,
        ..
    } = q.kind()
    else {
        return Err(QuantifierSupportError::NotQuantifier);
    };
    if !triggers.is_empty() {
        return Ok(q.clone());
    }
    let Some((triggers, extra)) = services
        .generate_trigger_sets(vars, body)
        .map_err(QuantifierSupportError::Service)?
    else {
        return Ok(q.clone());
    };
    let variables = vars.iter().cloned().chain(extra).collect();
    factory
        .quantification(
            *quantifier,
            variables,
            body.clone(),
            triggers,
            name.clone(),
            false,
            None,
        )
        .map_err(QuantifierSupportError::Transform)
}
/// Split a quantifier by trigger set and replace source-recognized heap dependencies
/// with fresh binders. Freshness is requested for every occurrence before map deduplication.
pub fn make_triggers_heap_independent<S: QuantifierTriggerServices>(
    factory: &TermFactory,
    services: &mut S,
    q: &Term,
) -> Result<Vec<Term>, QuantifierSupportError<S::Error>> {
    let TermKind::Quantification {
        quantifier,
        vars,
        body,
        triggers,
        name,
        is_global,
        ..
    } = q.kind()
    else {
        return Err(QuantifierSupportError::NotQuantifier);
    };
    fn deps(term: &Term, out: &mut Vec<Term>) {
        match term.kind() {
            TermKind::App {
                applicable: ApplicationTarget::Function(fun),
                args,
            } if fun.data().kind == ApplicableKind::HeapDepFun => {
                for arg in args {
                    deps(arg, out);
                }
            }
            TermKind::Var(_) | TermKind::App { .. }
                if matches!(
                    term.sort(),
                    Sort::FieldValueFunction { .. } | Sort::PredicateSnapFunction { .. }
                ) =>
            {
                out.push(term.clone())
            }
            _ => {}
        }
    }
    fn replace<E>(
        factory: &TermFactory,
        term: &Term,
        map: &[(Term, Term)],
    ) -> Result<Term, QuantifierSupportError<E>> {
        match term.kind() {
            TermKind::App { applicable, args } => {
                let args = args
                    .iter()
                    .map(|arg| replace(factory, arg, map))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(match applicable {
                    ApplicationTarget::Function(fun) => factory.app(fun.clone(), args),
                    ApplicationTarget::Variable(var) => factory.app_var(var.clone(), args),
                })
            }
            TermKind::Var(_)
                if matches!(
                    term.sort(),
                    Sort::FieldValueFunction { .. } | Sort::PredicateSnapFunction { .. }
                ) =>
            {
                map.iter()
                    .find(|(from, _)| from == term)
                    .map(|(_, to)| to.clone())
                    .ok_or(QuantifierSupportError::MissingDependency)
            }
            _ => Ok(term.clone()),
        }
    }
    let mut seen: Vec<(Vec<Term>, Vec<Term>)> = Vec::new();
    let mut output = Vec::new();
    for trigger in triggers {
        let mut dependencies = Vec::new();
        for term in &trigger.terms {
            deps(term, &mut dependencies);
        }
        let pair = (trigger.terms.clone(), dependencies);
        if seen.contains(&pair) {
            continue;
        }
        seen.push(pair.clone());
        let mut substitutions: Vec<(Term, Term)> = Vec::new();
        for dependency in &pair.1 {
            let fresh = services
                .fresh_projection(dependency.sort())
                .map_err(QuantifierSupportError::Service)?;
            if let Some((_, value)) = substitutions.iter_mut().find(|(key, _)| key == dependency) {
                *value = fresh;
            } else {
                substitutions.push((dependency.clone(), fresh));
            }
        }
        let terms = pair
            .0
            .iter()
            .map(|term| replace(factory, term, &substitutions))
            .collect::<Result<Vec<_>, _>>()?;
        let variables = vars
            .iter()
            .cloned()
            .chain(substitutions.into_iter().map(|(_, var)| var))
            .collect();
        output.push(
            factory
                .quantification(
                    *quantifier,
                    variables,
                    body.clone(),
                    vec![Trigger { terms }],
                    name.clone(),
                    *is_global,
                    None,
                )
                .map_err(QuantifierSupportError::Transform)?,
        );
    }
    Ok(output)
}
/// Validate forall trigger coverage and possible/forbidden trigger terms in source order.
pub fn detect_quantification_problems<S: QuantifierTriggerServices>(
    generator: &TriggerGenerator,
    services: &mut S,
    q: &Term,
) -> Result<Vec<String>, QuantifierSupportError<S::Error>> {
    let TermKind::Quantification {
        quantifier,
        vars,
        triggers,
        ..
    } = q.kind()
    else {
        return Err(QuantifierSupportError::NotQuantifier);
    };
    if *quantifier == Quantifier::Exists {
        return Ok(vec![]);
    }
    let mut problems = Vec::new();
    if triggers.is_empty() {
        problems.push("No triggers given".into());
    }
    for trigger in triggers {
        let mut found = Vec::new();
        for term in &trigger.terms {
            found.extend(
                term.deep_collect(&mut |t| {
                    matches!(t.kind(), TermKind::Var(_)).then_some(t.clone())
                })
                .map_err(QuantifierSupportError::Traversal)?,
            );
        }
        if !vars.iter().all(|var| found.contains(var)) {
            problems.push(format!(
                "Trigger set {} does not contain all quantified variables",
                services
                    .render_trigger(trigger)
                    .map_err(QuantifierSupportError::Service)?
            ));
        }
    }
    for trigger in triggers {
        for term in &trigger.terms {
            if !generator.is_possible_trigger(term) {
                problems.push(format!(
                    "Trigger {} is not a possible trigger",
                    services
                        .render_term(term)
                        .map_err(QuantifierSupportError::Service)?
                ));
            }
            for forbidden in term
                .deep_collect(&mut |term| generator.is_forbidden(term).then_some(term.clone()))
                .map_err(QuantifierSupportError::Traversal)?
            {
                problems.push(format!(
                    "Term {} may not occur in triggers",
                    services
                        .render_term(&forbidden)
                        .map_err(QuantifierSupportError::Service)?
                ));
            }
        }
    }
    Ok(problems)
}
