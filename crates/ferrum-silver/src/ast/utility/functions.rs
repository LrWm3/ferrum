//! Function call graphs and recursion analyses.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Functions.scala
//! Status: partial; unfolding-aware expressions, call graphs, SCC heights and cycle queries are
//! implemented; extensions rely on their traversal hooks. Call-graph tie ordering can vary.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::nodes::{Node, TraversalError, subnodes};
use crate::ast::{
    expression::{Exp, ExpKind},
    program::{Function, Program},
};
use indexmap::IndexMap;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FunctionAnalysisError {
    Traversal(TraversalError),
    MissingFunction(String),
    MissingPredicate(String),
    InvalidUnfolding,
}
impl From<TraversalError> for FunctionAnalysisError {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Edge<T> {
    pub source: T,
    pub target: T,
}
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CallGraph {
    pub vertices: Vec<String>,
    pub edges: Vec<Edge<String>>,
}
pub fn all_subexpressions(f: &Function) -> Vec<Exp> {
    f.pres
        .iter()
        .chain(&f.posts)
        .chain(f.body.iter())
        .cloned()
        .collect()
}
fn visit(
    node: &Node,
    f: &mut impl FnMut(&Node) -> Result<(), FunctionAnalysisError>,
) -> Result<(), FunctionAnalysisError> {
    f(node)?;
    for child in subnodes(node)? {
        visit(&child, f)?;
    }
    Ok(())
}
pub fn all_subexpressions_including_unfoldings(
    program: &Program,
    f: &Function,
) -> Result<Vec<Exp>, FunctionAnalysisError> {
    fn add_unfoldings(e: &Exp, out: &mut Vec<Exp>) -> Result<(), FunctionAnalysisError> {
        visit(&Node::Exp(e.clone()), &mut |n| {
            if let Node::Exp(e) = n {
                if matches!(e.kind(), ExpKind::Unfolding(..)) {
                    out.push(e.clone());
                }
            }
            Ok(())
        })
    }
    let mut subexpressions = all_subexpressions(f);
    let mut unfoldings = Vec::new();
    for exp in &subexpressions {
        add_unfoldings(exp, &mut unfoldings)?;
    }
    let mut visited = HashSet::new();
    let mut i = 0;
    while i < unfoldings.len() {
        let ExpKind::Unfolding(access, _) = unfoldings[i].kind() else {
            unreachable!()
        };
        let ExpKind::PredicateAccessPredicate(p) = access.kind() else {
            return Err(FunctionAnalysisError::InvalidUnfolding);
        };
        let name = &p.location.predicate_name;
        if visited.insert(name.clone()) {
            let pred = program
                .find_predicate_optionally(name)
                .ok_or_else(|| FunctionAnalysisError::MissingPredicate(name.clone()))?;
            if let Some(body) = &pred.body {
                subexpressions.push(body.clone());
                add_unfoldings(body, &mut unfoldings)?;
            }
        }
        i += 1;
    }
    Ok(subexpressions)
}
pub fn get_function_callgraph(
    program: &Program,
    mut subs: impl FnMut(&Function) -> Result<Vec<Exp>, FunctionAnalysisError>,
) -> Result<CallGraph, FunctionAnalysisError> {
    let mut graph = CallGraph::default();
    for f in &program.functions {
        if !graph.vertices.contains(&f.name) {
            graph.vertices.push(f.name.clone());
        }
    }
    for f in &program.functions {
        for exp in subs(f)? {
            visit(&Node::Exp(exp), &mut |node| {
                if let Node::Exp(e) = node {
                    if let ExpKind::FuncApp(name, _) = e.kind() {
                        if !graph.vertices.contains(name) {
                            return Err(FunctionAnalysisError::MissingFunction(name.clone()));
                        }
                        let edge = Edge {
                            source: f.name.clone(),
                            target: name.clone(),
                        };
                        if !graph.edges.contains(&edge) {
                            graph.edges.push(edge);
                        }
                    }
                }
                Ok(())
            })?;
        }
    }
    Ok(graph)
}
impl CallGraph {
    /// Traverse a root's cycle in the order used by JGraphT's rooted DFS.
    fn cycle_probe_order(&self, root: &str, cycle: &HashSet<String>) -> Vec<String> {
        let mut visited = HashSet::new();
        let mut stack = vec![root.to_owned()];
        let mut result = Vec::new();
        while let Some(vertex) = stack.pop() {
            if !visited.insert(vertex.clone()) {
                continue;
            }
            if cycle.contains(&vertex) {
                result.push(vertex.clone());
            }
            for edge in self.edges.iter().filter(|edge| edge.source == vertex) {
                if !visited.contains(&edge.target) {
                    stack.push(edge.target.clone());
                }
            }
        }
        result
    }
    fn reachable(&self, source: &str) -> HashSet<String> {
        let mut seen = HashSet::new();
        let mut queue = VecDeque::from([source.to_owned()]);
        while let Some(name) = queue.pop_front() {
            for e in self.edges.iter().filter(|e| e.source == name) {
                if seen.insert(e.target.clone()) {
                    queue.push_back(e.target.clone());
                }
            }
        }
        seen
    }
    pub fn cycles_containing(&self, name: &str) -> HashSet<String> {
        let reachable = self.reachable(name);
        if !reachable.contains(name) {
            return HashSet::new();
        }
        reachable
            .into_iter()
            .filter(|other| other == name || self.reachable(other).contains(name))
            .collect()
    }
    /// SCC numbering follows one valid source topological order; ties are not promised by JGraphT.
    pub fn heights(&self) -> HashMap<String, usize> {
        let mut components: Vec<Vec<String>> = Vec::new();
        for name in &self.vertices {
            if components.iter().flatten().any(|n| n == name) {
                continue;
            }
            let reachable = self.reachable(name);
            components.push(
                self.vertices
                    .iter()
                    .filter(|other| {
                        *other == name
                            || (reachable.contains(*other) && self.reachable(other).contains(name))
                    })
                    .cloned()
                    .collect(),
            );
        }
        let index = |n: &String| {
            components
                .iter()
                .position(|c| c.contains(n))
                .expect("edge vertex")
        };
        let mut successors = vec![HashSet::new(); components.len()];
        let mut indegree = vec![0usize; components.len()];
        for edge in &self.edges {
            let a = index(&edge.source);
            let b = index(&edge.target);
            if a != b && successors[a].insert(b) {
                indegree[b] += 1;
            }
        }
        let mut queue: VecDeque<_> = indegree
            .iter()
            .enumerate()
            .filter_map(|(i, d)| (*d == 0).then_some(i))
            .collect();
        let mut result = HashMap::new();
        let mut height = 0;
        while let Some(i) = queue.pop_front() {
            for name in &components[i] {
                result.insert(name.clone(), height);
            }
            height += 1;
            for target in &successors[i] {
                indegree[*target] -= 1;
                if indegree[*target] == 0 {
                    queue.push_back(*target);
                }
            }
        }
        result
    }
}
pub fn heights(
    program: &Program,
    consider_unfoldings: bool,
) -> Result<HashMap<String, usize>, FunctionAnalysisError> {
    Ok(get_function_callgraph(program, |f| {
        if consider_unfoldings {
            all_subexpressions_including_unfoldings(program, f)
        } else {
            Ok(all_subexpressions(f))
        }
    })?
    .heights())
}
pub fn find_function_cycles_via(
    program: &Program,
    via: impl Fn(&Function) -> Vec<Exp>,
    subs: impl Fn(&Function) -> Vec<Exp>,
) -> Result<IndexMap<String, HashSet<String>>, FunctionAnalysisError> {
    let mut result = IndexMap::new();
    for entry in &program.functions {
        let graph =
            get_function_callgraph(program, |f| Ok(if f == entry { via(f) } else { subs(f) }))?;
        let cycle = graph.cycles_containing(&entry.name);
        if !cycle.is_empty() {
            result.insert(entry.name.clone(), cycle);
        }
    }
    Ok(result)
}
pub fn find_function_cycles_via_optimized(
    program: &Program,
    via: impl Fn(&Function) -> Vec<Exp>,
) -> Result<IndexMap<String, HashSet<String>>, FunctionAnalysisError> {
    let graph = get_function_callgraph(program, |f| Ok(via(f)))?;
    let mut result = IndexMap::new();
    for f in &program.functions {
        let cycle = graph.cycles_containing(&f.name);
        if !cycle.is_empty() {
            result.insert(f.name.clone(), cycle);
        }
    }
    Ok(result)
}
pub fn find_function_cycles_via_preconditions(
    program: &Program,
) -> Result<IndexMap<String, HashSet<String>>, FunctionAnalysisError> {
    find_function_cycles_via(program, |f| f.pres.clone(), all_subexpressions)
}

/// Source cycle diagnostics retain the rooted traversal order for Scala's
/// small immutable sets; the underlying cycle query remains a set-valued API.
pub fn find_ordered_function_cycles_via_preconditions(
    program: &Program,
) -> Result<IndexMap<String, Vec<String>>, FunctionAnalysisError> {
    let mut result = IndexMap::new();
    for entry in &program.functions {
        let graph = get_function_callgraph(program, |f| {
            Ok(if f == entry {
                f.pres.clone()
            } else {
                all_subexpressions(f)
            })
        })?;
        let cycle = graph.cycles_containing(&entry.name);
        if !cycle.is_empty() {
            result.insert(
                entry.name.clone(),
                graph.cycle_probe_order(&entry.name, &cycle),
            );
        }
    }
    Ok(result)
}

/// Calls in the body are returned in reverse discovery order with outermost-first unfoldings.
pub fn recursive_calls_and_surrounding_unfoldings(
    f: &Function,
) -> Result<Vec<(Exp, Vec<Exp>)>, FunctionAnalysisError> {
    fn walk(
        node: &Node,
        name: &str,
        unfoldings: &[Exp],
        out: &mut Vec<(Exp, Vec<Exp>)>,
    ) -> Result<(), FunctionAnalysisError> {
        if let Node::Exp(e) = node {
            match e.kind() {
                // Upstream calls e.replace(e, body), i.e. replaces the entire RHS root with
                // the let body; it does not substitute the bound variable into that body.
                ExpKind::Let(_, _, body) => {
                    return walk(&Node::Exp(body.clone()), name, unfoldings, out);
                }
                ExpKind::Unfolding(_, body) => {
                    let mut nested = unfoldings.to_vec();
                    nested.push(e.clone());
                    return walk(&Node::Exp(body.clone()), name, &nested, out);
                }
                ExpKind::FuncApp(called, args) => {
                    if called == name {
                        out.insert(0, (e.clone(), unfoldings.to_vec()));
                    }
                    for arg in args {
                        walk(&Node::Exp(arg.clone()), name, unfoldings, out)?;
                    }
                    return Ok(());
                }
                _ => {}
            }
        }
        for child in subnodes(node)? {
            walk(&child, name, unfoldings, out)?;
        }
        Ok(())
    }
    let mut out = Vec::new();
    if let Some(body) = &f.body {
        walk(&Node::Exp(body.clone()), &f.name, &[], &mut out)?;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ast::Metadata, program::LocalVarDecl, r#type::Type};
    #[test]
    fn let_walk_matches_source_root_replacement_and_prepends_calls() {
        let m = Metadata::default();
        let call = |name: &str| Exp::new(ExpKind::FuncApp(name.into(), vec![]), m.clone());
        let rhs = call("f");
        let body = Exp::new(ExpKind::And(call("f"), call("f")), m.clone());
        let let_exp = Exp::new(
            ExpKind::Let(
                LocalVarDecl::new("x".into(), Type::Int, m.clone()),
                rhs,
                body,
            ),
            m.clone(),
        );
        let function = Function::new(crate::ast::program::FunctionData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(let_exp),
            meta: m,
        });
        let calls = recursive_calls_and_surrounding_unfoldings(&function).unwrap();
        assert_eq!(calls.len(), 2);
    }
}
