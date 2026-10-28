//! Generic quantifier trigger repair using arithmetic isolation.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/GenericAxiomRewriter.scala
//! Status: generic rewrite algorithm implemented through fallible language-specific adapters;
//! concrete Silver and Silicon adapters remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::generic_trigger_generator::TriggerSet;

pub trait AxiomAdapter {
    type Exp: Clone + Eq;
    type Var: Clone + Eq;
    type Quantifier: Clone;
    type Trigger;
    type Error;
    /// Source shallow collection stops below each forbidden term.
    fn invalid_terms(&self, expression: &Self::Exp) -> Result<Vec<Self::Exp>, Self::Error>;
    fn variables(&self, q: &Self::Quantifier) -> Vec<Self::Var>;
    fn body(&self, q: &Self::Quantifier) -> Self::Exp;
    fn var_exp(&self, v: &Self::Var) -> Self::Exp;
    fn contains(&self, expression: &Self::Exp, value: &Self::Exp) -> Result<bool, Self::Error>;
    fn replace(
        &self,
        expression: &Self::Exp,
        original: &Self::Exp,
        replacement: &Self::Exp,
    ) -> Result<Self::Exp, Self::Error>;
    fn fresh_for(&mut self, var: &Self::Var, term: &Self::Exp) -> Result<Self::Var, Self::Error>;
    /// Return None for a pre-solving error or an unsolved equation.
    fn solve(
        &self,
        lhs: &Self::Var,
        rhs: &Self::Exp,
        variable: &Self::Var,
    ) -> Result<Option<Self::Exp>, Self::Error>;
    fn equal(&self, a: Self::Exp, b: Self::Exp) -> Self::Exp;
    fn and(&self, terms: Vec<Self::Exp>) -> Self::Exp;
    fn implies(&self, a: Self::Exp, b: Self::Exp) -> Self::Exp;
    fn trigger(&self, exps: Vec<Self::Exp>) -> Self::Trigger;
    fn copy_quantifier(
        &self,
        q: &Self::Quantifier,
        vars: Vec<Self::Var>,
        body: Self::Exp,
        triggers: Vec<Self::Trigger>,
    ) -> Result<Self::Quantifier, Self::Error>;
}
pub fn extract_invalid_terms<A: AxiomAdapter>(
    adapter: &A,
    triggers: &[TriggerSet<A::Exp>],
) -> Result<Vec<Vec<A::Exp>>, A::Error> {
    let mut result = Vec::new();
    for trigger in triggers {
        for exp in &trigger.exps {
            result.push(adapter.invalid_terms(exp)?);
        }
    }
    Ok(result)
}
#[derive(Clone, Debug)]
struct Solved<E, V> {
    variable: V,
    entries: Vec<(E, V, E)>,
}
/// Returns None when any invalid term has zero/multiple quantified variables or
/// cannot be solved; no partial rewritten quantifier is returned.
pub fn rewrite<A: AxiomAdapter>(
    adapter: &mut A,
    q: &A::Quantifier,
    triggers: &[TriggerSet<A::Exp>],
) -> Result<Option<A::Quantifier>, A::Error> {
    let mut invalid = Vec::new();
    for term in extract_invalid_terms(adapter, triggers)?
        .into_iter()
        .flatten()
    {
        if !invalid.contains(&term) {
            invalid.push(term);
        }
    }
    if invalid.is_empty() {
        return Ok(Some(q.clone()));
    }
    let qvars = adapter.variables(q);
    let mut partitions: Vec<(A::Var, Vec<A::Exp>)> = Vec::new();
    let mut invalid_partition = false;
    for term in invalid {
        let mut contained = Vec::new();
        for var in &qvars {
            if adapter.contains(&term, &adapter.var_exp(var))? {
                contained.push(var.clone());
            }
        }
        if contained.len() != 1 {
            invalid_partition = true;
            continue;
        }
        let variable = contained.pop().expect("length checked");
        if let Some((_, terms)) = partitions.iter_mut().find(|(v, _)| *v == variable) {
            terms.push(term);
        } else {
            partitions.push((variable, vec![term]));
        }
    }
    if invalid_partition {
        return Ok(None);
    }
    let mut solved: Vec<Solved<A::Exp, A::Var>> = Vec::new();
    let mut failed = false;
    for (variable, terms) in partitions {
        let mut entries = Vec::new();
        for term in terms {
            let fresh = adapter.fresh_for(&variable, &term)?;
            if let Some(solution) = adapter.solve(&fresh, &term, &variable)? {
                entries.push((term, fresh, solution));
            } else {
                failed = true;
            }
        }
        if !entries.is_empty() {
            solved.push(Solved { variable, entries });
        }
    }
    if failed {
        return Ok(None);
    }
    let mut rewritten_triggers = triggers.to_vec();
    let mut body = adapter.body(q);
    for group in &solved {
        for (invalid, fresh, _) in &group.entries {
            let replacement = adapter.var_exp(fresh);
            for trigger in &mut rewritten_triggers {
                for expression in &mut trigger.exps {
                    *expression = adapter.replace(expression, invalid, &replacement)?;
                }
            }
            body = adapter.replace(&body, invalid, &replacement)?;
        }
    }
    let mut unused = Vec::new();
    for group in &solved {
        let variable = adapter.var_exp(&group.variable);
        let mut used = false;
        for trigger in &rewritten_triggers {
            for expression in &trigger.exps {
                if adapter.contains(expression, &variable)? {
                    used = true;
                    break;
                }
            }
            if used {
                break;
            }
        }
        if !used {
            unused.push(group.variable.clone());
            body = adapter.replace(&body, &variable, &group.entries[0].2)?;
        }
    }
    // Upstream flattens every group into one sequence before pairing neighbors.
    let mut components = Vec::new();
    for group in &solved {
        if !unused.contains(&group.variable) {
            components.push(adapter.var_exp(&group.variable));
        }
        components.extend(
            group
                .entries
                .iter()
                .map(|(_, _, solution)| solution.clone()),
        );
    }
    let equalities = components
        .windows(2)
        .map(|p| adapter.equal(p[0].clone(), p[1].clone()))
        .collect();
    body = adapter.implies(adapter.and(equalities), body);
    let mut new_vars: Vec<_> = qvars.into_iter().filter(|v| !unused.contains(v)).collect();
    for group in solved {
        new_vars.extend(group.entries.into_iter().map(|(_, fresh, _)| fresh));
    }
    let triggers = rewritten_triggers
        .into_iter()
        .map(|t| adapter.trigger(t.exps))
        .collect();
    Ok(Some(adapter.copy_quantifier(q, new_vars, body, triggers)?))
}
