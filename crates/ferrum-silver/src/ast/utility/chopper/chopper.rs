//! Dependency graph components and merge penalties for program chopping.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/chopper/Chopper.scala
//! Status: partial; vertex families, default penalties and ordered Tarjan SCC/condensation
//! are implemented. Viper dependency construction, bounded cuts and program reconstruction
//! are not yet implemented and cannot be used to chop a program.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    program::{Domain, DomainAxiom},
    r#type::DomainType,
};
use std::collections::BTreeSet;
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Vertex {
    MethodSpec(String),
    Method(String),
    FunctionSpec(String),
    Function(String),
    PredicateSig(String),
    PredicateBody(String),
    Field(String),
    DomainFunction(String),
    DomainAxiom(DomainAxiom, Domain),
    DomainType(DomainType),
    Always,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PenaltyConfig {
    pub method: i32,
    pub method_spec: i32,
    pub function: i32,
    pub function_sig: i32,
    pub predicate: i32,
    pub predicate_sig: i32,
    pub field: i32,
    pub domain_type: i32,
    pub domain_function: i32,
    pub domain_axiom: i32,
    pub shared_threshold: i32,
}
impl Default for PenaltyConfig {
    fn default() -> Self {
        Self {
            method: 0,
            method_spec: 0,
            function: 20,
            function_sig: 5,
            predicate: 10,
            predicate_sig: 2,
            field: 1,
            domain_type: 1,
            domain_function: 1,
            domain_axiom: 5,
            shared_threshold: 50,
        }
    }
}
pub trait Penalty<T> {
    fn penalty(&self, node: &T) -> i32;
    fn merge_penalty(&self, lhs: i32, rhs: i32, shared: i32) -> i32;
}
impl Penalty<Vertex> for PenaltyConfig {
    fn penalty(&self, node: &Vertex) -> i32 {
        match node {
            Vertex::Method(_) => self.method,
            Vertex::MethodSpec(_) => self.method_spec,
            Vertex::Function(_) => self.function,
            Vertex::FunctionSpec(_) => self.function_sig,
            Vertex::PredicateBody(_) => self.predicate,
            Vertex::PredicateSig(_) => self.predicate_sig,
            Vertex::Field(_) => self.field,
            Vertex::DomainType(_) => self.domain_type,
            Vertex::DomainFunction(_) => self.domain_function,
            Vertex::DomainAxiom(..) => self.domain_axiom,
            Vertex::Always => 0,
        }
    }
    fn merge_penalty(&self, lhs: i32, rhs: i32, shared: i32) -> i32 {
        let ratio = (self.shared_threshold.wrapping_add(shared) as f32
            / self.shared_threshold as f32) as i32;
        lhs.wrapping_add(rhs).wrapping_mul(ratio)
    }
}
#[derive(Clone, Copy, Debug, Default)]
pub struct DefaultWithoutForcedMerge(pub PenaltyConfig);
impl Penalty<Vertex> for DefaultWithoutForcedMerge {
    fn penalty(&self, node: &Vertex) -> i32 {
        self.0.penalty(node)
    }
    fn merge_penalty(&self, lhs: i32, rhs: i32, shared: i32) -> i32 {
        self.0.merge_penalty(lhs, rhs, shared).max(1)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Component<T> {
    pub nodes: Vec<T>,
}
impl<T> Component<T> {
    pub fn proxy(&self) -> &T {
        &self.nodes[0]
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GraphError {
    WrongAdjacencyLength,
    InvalidVertex(usize),
}
/// SCC order and member order follow source sorted successor traversal and list prepend.
pub fn fast_components(
    n: usize,
    edges: &[BTreeSet<usize>],
) -> Result<Vec<Component<usize>>, GraphError> {
    if edges.len() != n {
        return Err(GraphError::WrongAdjacencyLength);
    }
    if let Some(v) = edges.iter().flat_map(|e| e.iter()).find(|v| **v >= n) {
        return Err(GraphError::InvalidVertex(*v));
    }
    struct State<'a> {
        edges: &'a [BTreeSet<usize>],
        index: usize,
        indices: Vec<Option<usize>>,
        low: Vec<usize>,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        components: Vec<Component<usize>>,
    }
    fn visit(v: usize, s: &mut State<'_>) {
        let index = s.index;
        s.index += 1;
        s.indices[v] = Some(index);
        s.low[v] = index;
        s.stack.push(v);
        s.on_stack[v] = true;
        for &w in &s.edges[v] {
            if s.indices[w].is_none() {
                visit(w, s);
                s.low[v] = s.low[v].min(s.low[w]);
            } else if s.on_stack[w] {
                s.low[v] = s.low[v].min(s.indices[w].unwrap());
            }
        }
        if s.low[v] == index {
            let mut component = Vec::new();
            loop {
                let w = s.stack.pop().expect("Tarjan stack");
                s.on_stack[w] = false;
                component.insert(0, w);
                if w == v {
                    break;
                }
            }
            s.components.insert(0, Component { nodes: component });
        }
    }
    let mut s = State {
        edges,
        index: 0,
        indices: vec![None; n],
        low: vec![0; n],
        stack: Vec::new(),
        on_stack: vec![false; n],
        components: Vec::new(),
    };
    for v in 0..n {
        if s.indices[v].is_none() {
            visit(v, &mut s);
        }
    }
    Ok(s.components)
}
/// Source component-edge array has `n` slots indexed by component proxy.
pub fn fast_compute(
    n: usize,
    edges: &[BTreeSet<usize>],
) -> Result<(Vec<Component<usize>>, Vec<usize>, Vec<BTreeSet<usize>>), GraphError> {
    let components = fast_components(n, edges)?;
    let mut owner = vec![0; n];
    for (i, c) in components.iter().enumerate() {
        for &v in &c.nodes {
            owner[v] = i;
        }
    }
    let mut result = vec![BTreeSet::new(); n];
    for (source, targets) in edges.iter().enumerate() {
        for &target in targets {
            let a = &components[owner[source]];
            let b = &components[owner[target]];
            if a.proxy() != b.proxy() {
                result[*a.proxy()].insert(*b.proxy());
            }
        }
    }
    Ok((components, owner, result))
}
/// Inputs omit duplicate nodes, and endpoints absent from nodes are still inserted,
/// as in toFastGraph. Edges are returned between component indices in input order.
pub fn compute<T: Clone + Eq>(
    nodes: &[T],
    edges: &[(T, T)],
) -> Result<(Vec<Component<T>>, Vec<(T, usize)>, Vec<(usize, usize)>), GraphError> {
    let mut values = Vec::<T>::new();
    fn id<T: Clone + Eq>(values: &mut Vec<T>, value: &T) -> usize {
        if let Some(i) = values.iter().position(|v| v == value) {
            i
        } else {
            values.push(value.clone());
            values.len() - 1
        }
    }
    for node in nodes {
        id(&mut values, node);
    }
    let indexed: Vec<_> = edges
        .iter()
        .map(|(a, b)| (id(&mut values, a), id(&mut values, b)))
        .collect();
    let mut adjacency = vec![BTreeSet::new(); values.len()];
    for (a, b) in &indexed {
        adjacency[*a].insert(*b);
    }
    let (components, owners, _) = fast_compute(values.len(), &adjacency)?;
    let typed = components
        .iter()
        .map(|c| Component {
            nodes: c.nodes.iter().map(|v| values[*v].clone()).collect(),
        })
        .collect();
    let mapping = values.into_iter().zip(owners.iter().copied()).collect();
    let mut graph = Vec::new();
    for (a, b) in indexed {
        let edge = (owners[a], owners[b]);
        if edge.0 != edge.1 && !graph.contains(&edge) {
            graph.push(edge);
        }
    }
    Ok((typed, mapping, graph))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn scc_order_and_proxy_follow_sorted_traversal() {
        let edges = vec![BTreeSet::from([1]), BTreeSet::from([0, 2]), BTreeSet::new()];
        let (components, owner, graph) = fast_compute(3, &edges).unwrap();
        assert_eq!(
            components,
            vec![
                Component { nodes: vec![0, 1] },
                Component { nodes: vec![2] }
            ]
        );
        assert_eq!(owner, vec![0, 0, 1]);
        assert_eq!(graph[0], BTreeSet::from([2]));
    }
}
