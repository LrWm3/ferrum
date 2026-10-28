//! Generic candidate combination and minimization for quantified triggers.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/GenericTriggerGenerator.scala
//! Status: partial; candidate discovery, covering and grouping are implemented through
//! explicit language-specific traversal, forbidden-term rewriting and modification hooks.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TriggerSet<E> {
    pub exps: Vec<E>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Candidate<E, V> {
    pub exp: E,
    pub covered: Vec<V>,
    pub extra: Vec<V>,
}
fn distinct<V: Clone + Eq>(items: impl IntoIterator<Item = V>) -> Vec<V> {
    let mut result = Vec::new();
    for item in items {
        if !result.contains(&item) {
            result.push(item);
        }
    }
    result
}
/// Source Seq.diff removes one occurrence per element, retaining order and multiplicity.
fn difference<V: Clone + Eq>(items: &[V], remove: &[V]) -> Vec<V> {
    let mut result = items.to_vec();
    for x in remove {
        if let Some(i) = result.iter().position(|a| a == x) {
            result.remove(i);
        }
    }
    result
}
pub fn build_triggers_covering<E: Clone, V: Clone + Eq>(
    vars: &[V],
    candidates: &[Candidate<E, V>],
    current: &[E],
    extra: &[V],
) -> Vec<(TriggerSet<E>, Vec<V>)> {
    if vars.is_empty() {
        return vec![(
            TriggerSet {
                exps: current.to_vec(),
            },
            extra.to_vec(),
        )];
    }
    let Some((first, rest)) = candidates.split_first() else {
        return Vec::new();
    };
    let needed = difference(vars, &first.covered);
    let relevant: Vec<_> = rest
        .iter()
        .filter(|c| c.covered.iter().any(|v| needed.contains(v)))
        .cloned()
        .collect();
    let mut extended = current.to_vec();
    extended.push(first.exp.clone());
    let new_extra = distinct(extra.iter().chain(&first.extra).cloned());
    let mut result = build_triggers_covering(&needed, &relevant, &extended, &new_extra);
    result.extend(build_triggers_covering(vars, rest, current, extra));
    result
}
/// Applies the source strict-subterm filtering and grouping to discovered candidates.
pub fn group_candidates<E: Clone + Eq, V: Clone + Eq, Err>(
    vars: &[V],
    candidates: &[Candidate<E, V>],
    has_subnode: &impl Fn(&E, &E) -> Result<bool, Err>,
) -> Result<Vec<(Vec<TriggerSet<E>>, Vec<V>)>, Err> {
    if candidates.is_empty() {
        return Ok(Vec::new());
    }
    let all = build_triggers_covering(vars, candidates, &[], &[]);
    let mut filtered = Vec::new();
    for candidate in all {
        let mut redundant = false;
        for a in &candidate.0.exps {
            for b in &candidate.0.exps {
                if has_subnode(a, b)? {
                    redundant = true;
                    break;
                }
            }
            if redundant {
                break;
            }
        }
        if !redundant {
            filtered.push(candidate);
        }
    }
    let mut unique = Vec::new();
    for c in &filtered {
        if !unique.contains(c) {
            unique.push(c.clone());
        }
    }
    let mut kept = Vec::new();
    for c in &unique {
        let mut subsumed = false;
        for other in &filtered {
            if c == other
                || !c.1.iter().all(|x| other.1.contains(x))
                || !other.1.iter().all(|x| c.1.contains(x))
            {
                continue;
            }
            let mut all_found = true;
            for x in &c.0.exps {
                let mut found = false;
                for y in &other.0.exps {
                    if has_subnode(y, x)? {
                        found = true;
                        break;
                    }
                }
                if !found {
                    all_found = false;
                    break;
                }
            }
            if all_found {
                subsumed = true;
                break;
            }
        }
        if !subsumed {
            kept.push(c.clone());
        }
    }
    let mut groups: Vec<(Vec<TriggerSet<E>>, Vec<V>)> = Vec::new();
    while !kept.is_empty() {
        let key = kept[0].1.clone();
        let mut matching = Vec::new();
        let mut rest = Vec::new();
        for (trigger, extra) in kept {
            if extra == key {
                matching.push(trigger);
            } else {
                rest.push((trigger, extra));
            }
        }
        groups.insert(0, (matching, key));
        kept = rest;
    }
    groups.sort_by_key(|(_, extra)| extra.len());
    Ok(groups)
}

/// Language-specific traversal and rebuilding required by the source algorithm.
/// `rewrite_forbidden` must use the language's innermost transform and invoke
/// `fresh` for each forbidden expression in source traversal order.
pub trait TriggerAdapter {
    type Node: Clone;
    type Exp: Clone + Eq;
    type Var: Clone + Eq;
    type Error;
    fn root(&self, exp: &Self::Exp) -> Self::Node;
    fn children(&self, node: &Self::Node) -> Result<Vec<Self::Node>, Self::Error>;
    fn expression(&self, node: &Self::Node) -> Option<Self::Exp>;
    fn quantified_vars(&self, node: &Self::Node) -> Option<Vec<Self::Var>>;
    fn possible_trigger(&self, exp: &Self::Exp) -> Result<bool, Self::Error>;
    fn arguments(&self, exp: &Self::Exp) -> Result<Vec<Self::Exp>, Self::Error>;
    fn with_arguments(
        &self,
        exp: &Self::Exp,
        args: Vec<Self::Exp>,
    ) -> Result<Self::Exp, Self::Error>;
    fn variables_in(&self, exp: &Self::Exp) -> Result<Vec<Self::Var>, Self::Error>;
    /// Return fresh variables in creation order.
    fn rewrite_forbidden(
        &mut self,
        exp: &Self::Exp,
    ) -> Result<(Self::Exp, Vec<Self::Var>), Self::Error>;
    fn additional_relevant(
        &self,
        node: &Self::Node,
        relevant: &[Self::Var],
        avoid: &[Self::Var],
    ) -> Result<Vec<Self::Var>, Self::Error>;
    /// `None` means no hook matched; `Some` replaces the flattened child results.
    fn modify(
        &self,
        node: &Self::Node,
        relevant: &[Self::Var],
        children: &[Vec<Candidate<Self::Exp, Self::Var>>],
    ) -> Result<Option<Vec<Candidate<Self::Exp, Self::Var>>>, Self::Error>;
    fn has_subnode(&self, parent: &Self::Exp, child: &Self::Exp) -> Result<bool, Self::Error>;
}
/// Discover candidate terms and their required extra variables in source reduction order.
pub fn get_function_apps_containing<A: TriggerAdapter>(
    adapter: &mut A,
    vars: &[A::Var],
    search: &A::Exp,
) -> Result<Vec<Candidate<A::Exp, A::Var>>, A::Error> {
    fn bounds<A: TriggerAdapter>(
        adapter: &A,
        node: &A::Node,
        out: &mut Vec<A::Var>,
    ) -> Result<(), A::Error> {
        if let Some(vars) = adapter.quantified_vars(node) {
            out.extend(vars);
        }
        for child in adapter.children(node)? {
            bounds(adapter, &child, out)?;
        }
        Ok(())
    }
    fn relevant<A: TriggerAdapter>(
        adapter: &A,
        node: &A::Node,
        vars: &mut Vec<A::Var>,
        avoid: &[A::Var],
    ) -> Result<(), A::Error> {
        let new_vars = adapter.additional_relevant(node, vars, avoid)?;
        *vars = distinct(vars.iter().cloned().chain(new_vars));
        for child in adapter.children(node)? {
            relevant(adapter, &child, vars, avoid)?;
        }
        Ok(())
    }
    fn reduce<A: TriggerAdapter>(
        adapter: &mut A,
        node: &A::Node,
        vars: &[A::Var],
        avoid: &[A::Var],
    ) -> Result<Vec<Candidate<A::Exp, A::Var>>, A::Error> {
        let mut children = Vec::new();
        for child in adapter.children(node)? {
            children.push(reduce(adapter, &child, vars, avoid)?);
        }
        if let Some(exp) = adapter.expression(node) {
            if adapter.possible_trigger(&exp)? {
                let mut extra = Vec::new();
                let mut covered = Vec::new();
                let mut nested = false;
                let mut args = Vec::new();
                for arg in adapter.arguments(&exp)? {
                    let (arg, new_vars) = adapter.rewrite_forbidden(&arg)?;
                    // Scala prepends each freshly generated variable; adapters return the
                    // same per-argument sequence and later arguments prepend earlier ones.
                    for v in new_vars {
                        extra.insert(0, v);
                    }
                    args.push(arg);
                }
                // Complete all argument rewrites before variable inspection, as upstream does.
                for arg in &args {
                    for v in adapter.variables_in(arg)? {
                        if avoid.contains(&v) {
                            nested = true;
                        }
                        if vars.contains(&v) {
                            covered.insert(0, v);
                        }
                    }
                }
                let mut out: Vec<_> = children.into_iter().flatten().collect();
                if !nested && !covered.is_empty() {
                    out.push(Candidate {
                        exp: adapter.with_arguments(&exp, args)?,
                        covered,
                        extra,
                    });
                }
                return Ok(out);
            }
        }
        if let Some(modified) = adapter.modify(node, vars, &children)? {
            return Ok(modified);
        }
        Ok(children.into_iter().flatten().collect())
    }
    let root = adapter.root(search);
    let mut avoid = Vec::new();
    bounds(adapter, &root, &mut avoid)?;
    let mut all_vars = vars.to_vec();
    relevant(adapter, &root, &mut all_vars, &avoid)?;
    let all_vars = distinct(vars.iter().cloned().chain(all_vars));
    reduce(adapter, &root, &all_vars, &avoid)
}
pub fn generate_trigger_set_groups<A: TriggerAdapter>(
    adapter: &mut A,
    vars: &[A::Var],
    search: &A::Exp,
) -> Result<Vec<(Vec<TriggerSet<A::Exp>>, Vec<A::Var>)>, A::Error> {
    let candidates = get_function_apps_containing(adapter, vars, search)?;
    group_candidates(vars, &candidates, &|a, b| adapter.has_subnode(a, b))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn covering_uses_source_multiset_diff_and_distinct_extras() {
        let candidates = vec![
            Candidate {
                exp: "a",
                covered: vec!["x"],
                extra: vec!["z"],
            },
            Candidate {
                exp: "b",
                covered: vec!["x"],
                extra: vec!["z"],
            },
        ];
        let found = build_triggers_covering(&["x", "x"], &candidates, &[], &[]);
        assert_eq!(
            found,
            vec![(
                TriggerSet {
                    exps: vec!["a", "b"]
                },
                vec!["z"]
            )]
        );
    }
}
