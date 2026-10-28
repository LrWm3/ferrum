//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/CallGraph.scala
//!
//! Purpose:
//! Classify recursive dependencies in directed call graphs.
//!
//! Planned Rust structure:
//! Port CallGraph mutuallyRecursiveVertices and clearlyNonRecursiveVertices.
//!
//! Behavior to preserve:
//! Compute strongly connected components; nonrecursive routine destructively removes incoming
//! edges starting at leaves, enqueueing predecessors once outdegree reaches zero. Preserve
//! iteration consequences where observable.
//!
//! Integration:
//! function_check, method_check and termination_plugin build graphs of Silver members.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for graph ordering and native graph algorithms.
//!
//! Open decisions:
//! Agree on graph ownership and iteration order with callers.
//!
//! Status: implemented generic SCC and destructive non-recursive leaf peeling;
//! callers still construct graph vertices and edges from the program.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

/// Directed call graph. Vertices and edges retain insertion order; duplicate edges collapse.
#[derive(Clone, Debug, Default)]
pub struct DirectedGraph<V> {
    pub vertices: Vec<V>,
    pub edges: Vec<(V, V)>,
}
impl<V: Clone + Eq> DirectedGraph<V> {
    pub fn new() -> Self {
        Self {
            vertices: Vec::new(),
            edges: Vec::new(),
        }
    }
    pub fn add_vertex(&mut self, vertex: V) {
        if !self.vertices.contains(&vertex) {
            self.vertices.push(vertex);
        }
    }
    pub fn add_edge(&mut self, from: V, to: V) {
        self.add_vertex(from.clone());
        self.add_vertex(to.clone());
        if !self.edges.contains(&(from.clone(), to.clone())) {
            self.edges.push((from, to));
        }
    }
}
/// Kosaraju's algorithm returns all strongly connected components, including singletons.
pub fn mutually_recursive_vertices<V: Clone + Eq>(graph: &DirectedGraph<V>) -> Vec<Vec<V>> {
    fn visit<V: Clone + Eq>(
        v: &V,
        edges: &[(V, V)],
        visited: &mut Vec<V>,
        order: &mut Vec<V>,
        reverse: bool,
    ) {
        if visited.contains(v) {
            return;
        }
        visited.push(v.clone());
        for (from, to) in edges {
            let (a, b) = if reverse { (to, from) } else { (from, to) };
            if a == v {
                visit(b, edges, visited, order, reverse);
            }
        }
        order.push(v.clone());
    }
    let mut visited = Vec::new();
    let mut order = Vec::new();
    for vertex in &graph.vertices {
        visit(vertex, &graph.edges, &mut visited, &mut order, false);
    }
    visited.clear();
    let mut components = Vec::new();
    for vertex in order.into_iter().rev() {
        if !visited.contains(&vertex) {
            let mut component = Vec::new();
            visit(&vertex, &graph.edges, &mut visited, &mut component, true);
            components.push(component);
        }
    }
    components
}
/// Remove incoming edges while peeling leaves, exactly as the source mutates its graph.
pub fn clearly_non_recursive_vertices<V: Clone + Eq>(graph: &mut DirectedGraph<V>) -> Vec<V> {
    let mut border: std::collections::VecDeque<_> = graph
        .vertices
        .iter()
        .filter(|v| !graph.edges.iter().any(|(from, _)| from == *v))
        .cloned()
        .collect();
    let mut result = Vec::new();
    while let Some(vertex) = border.pop_front() {
        let incoming: Vec<_> = graph
            .edges
            .iter()
            .filter(|(_, to)| to == &vertex)
            .cloned()
            .collect();
        for edge in incoming {
            if let Some(index) = graph.edges.iter().position(|e| e == &edge) {
                graph.edges.remove(index);
            }
            if !graph.edges.iter().any(|(from, _)| from == &edge.0) {
                border.push_back(edge.0);
            }
        }
        if !result.contains(&vertex) {
            result.push(vertex);
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn retains_cycles_and_vertices_that_reach_them() {
        let mut graph = DirectedGraph::new();
        for (from, to) in [("a", "b"), ("b", "a"), ("c", "a"), ("d", "e")] {
            graph.add_edge(from, to);
        }
        let components = mutually_recursive_vertices(&graph);
        assert!(components.iter().any(|component| component.len() == 2
            && component.contains(&"a")
            && component.contains(&"b")));
        let nonrecursive = clearly_non_recursive_vertices(&mut graph);
        assert_eq!(nonrecursive, vec!["e", "d"]);
        assert_eq!(graph.edges.len(), 3);
    }
}
