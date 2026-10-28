//! Dependency graph components and merge penalties for program chopping.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/chopper/Chopper.scala
//! Status: single-program plugin-aware selection, graph primitives and program reconstruction
//! are implemented. The general bounded multi-program chopping entry point remains pending.

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
    CycleInAcyclicCut,
}
/// Merge two sorted scored lists, using the left score for shared nodes as upstream.
pub fn penalty_and_merge<T: Ord + Clone>(
    left: &[(T, i32)],
    right: &[(T, i32)],
    penalty: &impl Penalty<T>,
) -> (i32, Vec<(T, i32)>) {
    use std::cmp::Ordering;
    let (mut a, mut b, mut shared) = (0i32, 0i32, 0i32);
    let (mut i, mut j) = (0, 0);
    let mut merged = Vec::with_capacity(left.len() + right.len());
    while i < left.len() && j < right.len() {
        match left[i].0.cmp(&right[j].0) {
            Ordering::Less => {
                a = a.wrapping_add(left[i].1);
                merged.push(left[i].clone());
                i += 1;
            }
            Ordering::Greater => {
                b = b.wrapping_add(right[j].1);
                merged.push(right[j].clone());
                j += 1;
            }
            Ordering::Equal => {
                shared = shared.wrapping_add(left[i].1);
                merged.push(left[i].clone());
                i += 1;
                j += 1;
            }
        }
    }
    for entry in &left[i..] {
        a = a.wrapping_add(entry.1);
        merged.push(entry.clone());
    }
    for entry in &right[j..] {
        b = b.wrapping_add(entry.1);
        merged.push(entry.clone());
    }
    (penalty.merge_penalty(a, b, shared), merged)
}

/// Source greedy merge over a min-penalty priority queue. Equal-penalty ties and
/// output order follow the host heap/hash-map iteration order, as in the source
/// they are not semantically ordered; callers must not rely on a stable tie order.
pub fn merge_programs<T: Ord + Clone>(
    programs: &[Vec<T>],
    bound: Option<usize>,
    penalty: &impl Penalty<T>,
) -> Vec<Vec<T>> {
    use std::collections::{BinaryHeap, HashMap};
    struct Merge<T> {
        rank: i32,
        cost: i32,
        left: usize,
        right: usize,
        merged: Vec<(T, i32)>,
    }
    impl<T> PartialEq for Merge<T> {
        fn eq(&self, other: &Self) -> bool {
            self.rank == other.rank
        }
    }
    impl<T> Eq for Merge<T> {}
    impl<T> PartialOrd for Merge<T> {
        fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
            Some(self.cmp(other))
        }
    }
    impl<T> Ord for Merge<T> {
        fn cmp(&self, other: &Self) -> std::cmp::Ordering {
            self.rank.cmp(&other.rank)
        }
    }
    let initial: Vec<Vec<(T, i32)>> = programs
        .iter()
        .map(|program| {
            program
                .iter()
                .map(|v| (v.clone(), penalty.penalty(v)))
                .collect()
        })
        .collect();
    let mut sets: HashMap<usize, Vec<(T, i32)>> = initial.iter().cloned().enumerate().collect();
    let mut queue = BinaryHeap::new();
    for left in 0..initial.len() {
        for right in left + 1..initial.len() {
            let (cost, merged) = penalty_and_merge(&initial[left], &initial[right], penalty);
            queue.push(Merge {
                rank: cost.wrapping_neg(),
                cost,
                left,
                right,
                merged,
            });
        }
    }
    let mut next = initial.len();
    while let Some(head) = queue.peek() {
        if head.cost > 0 && !bound.is_some_and(|n| sets.len() > n) {
            break;
        }
        let mut candidate = queue.pop().expect("peeked queue");
        while !(sets.contains_key(&candidate.left) && sets.contains_key(&candidate.right)) {
            let Some(next_candidate) = queue.pop() else {
                return sets
                    .into_values()
                    .map(|p| p.into_iter().map(|(v, _)| v).collect())
                    .collect();
            };
            candidate = next_candidate;
        }
        if candidate.cost <= 0 || bound.is_some_and(|n| sets.len() > n) {
            sets.remove(&candidate.left);
            sets.remove(&candidate.right);
            for (&index, existing) in &sets {
                let (cost, merged) = penalty_and_merge(existing, &candidate.merged, penalty);
                queue.push(Merge {
                    rank: cost.wrapping_neg(),
                    cost,
                    left: index,
                    right: next,
                    merged,
                });
            }
            sets.insert(next, candidate.merged);
            next += 1;
        }
    }
    sets.into_values()
        .map(|p| p.into_iter().map(|(v, _)| v).collect())
        .collect()
}

fn validate_cut_graph(
    n: usize,
    selected: &[usize],
    edges: &[BTreeSet<usize>],
) -> Result<(), GraphError> {
    if edges.len() != n {
        return Err(GraphError::WrongAdjacencyLength);
    }
    for &v in selected.iter().chain(edges.iter().flat_map(|e| e.iter())) {
        if v >= n {
            return Err(GraphError::InvalidVertex(v));
        }
    }
    Ok(())
}

/// Source cyclic cut: preserve selected-node order and duplicate-selected behavior.
pub fn smallest_cut_with_cycles(
    n: usize,
    selected: &[usize],
    edges: &[BTreeSet<usize>],
) -> Result<Vec<Vec<usize>>, GraphError> {
    validate_cut_graph(n, selected, edges)?;
    let mut global = vec![false; n];
    let mut not_root = vec![false; n];
    let mut reachable = vec![BTreeSet::new(); n];
    for &start in selected {
        let mut stack = vec![start];
        let mut local = vec![false; n];
        let mut result = BTreeSet::new();
        while let Some(node) = stack.pop() {
            if !local[node] {
                local[node] = true;
                if global[node] {
                    not_root[node] = true;
                }
                global[node] = true;
                result.insert(node);
                stack.extend(edges[node].iter().copied());
            }
        }
        reachable[start] = result;
    }
    Ok(selected
        .iter()
        .filter(|&&node| !not_root[node])
        .map(|&node| reachable[node].iter().copied().collect())
        .collect())
}

/// Source DAG cut using shared reachability memoization and source root ordering.
pub fn smallest_cut_without_cycles(
    n: usize,
    selected: &[usize],
    edges: &[BTreeSet<usize>],
) -> Result<Vec<Vec<usize>>, GraphError> {
    validate_cut_graph(n, selected, edges)?;
    #[derive(Clone, Copy)]
    enum State {
        Unvisited,
        Active,
        Finalized(usize),
    }
    let mut state = vec![State::Unvisited; n];
    let mut not_root = vec![false; n];
    let mut reachable = vec![BTreeSet::new(); n];
    for &start in selected {
        let mut stack = vec![(start, false)];
        while let Some((node, finish)) = stack.pop() {
            match state[node] {
                State::Unvisited => {
                    state[node] = State::Active;
                    stack.push((node, true));
                    stack.extend(edges[node].iter().copied().map(|v| (v, false)));
                }
                State::Active if finish => {
                    let mut result = BTreeSet::from([node]);
                    for &child in &edges[node] {
                        if !matches!(state[child], State::Finalized(_)) {
                            return Err(GraphError::CycleInAcyclicCut);
                        }
                        result.extend(reachable[child].iter().copied());
                    }
                    reachable[node] = result;
                    state[node] = State::Finalized(start);
                }
                State::Active => return Err(GraphError::CycleInAcyclicCut),
                State::Finalized(previous) if previous != start => not_root[node] = true,
                State::Finalized(_) => {}
            }
        }
    }
    Ok(selected
        .iter()
        .filter(|&&node| !not_root[node])
        .map(|&node| reachable[node].iter().copied().collect())
        .collect())
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

#[cfg(test)]
mod cut_tests {
    use super::*;
    #[test]
    fn positive_cost_merges_only_when_bound_forces_them() {
        struct P;
        impl Penalty<i32> for P {
            fn penalty(&self, _: &i32) -> i32 {
                1
            }
            fn merge_penalty(&self, lhs: i32, rhs: i32, _: i32) -> i32 {
                lhs + rhs
            }
        }
        let input = vec![vec![1], vec![2], vec![3]];
        assert_eq!(merge_programs(&input, None, &P).len(), 3);
        let result = merge_programs(&input, Some(1), &P);
        assert_eq!(result, vec![vec![1, 2, 3]]);
    }
    #[test]
    fn cyclic_and_dag_cuts_keep_source_duplicate_selection_behavior() {
        let edges = vec![BTreeSet::from([1]), BTreeSet::new()];
        assert_eq!(
            smallest_cut_with_cycles(2, &[0, 0], &edges).unwrap(),
            Vec::<Vec<usize>>::new()
        );
        assert_eq!(
            smallest_cut_without_cycles(2, &[0, 0], &edges).unwrap(),
            vec![vec![0, 1], vec![0, 1]]
        );
        assert_eq!(
            smallest_cut_without_cycles(2, &[1, 0], &edges).unwrap(),
            vec![vec![0, 1]]
        );
    }
}

/// Error boundaries for the source plugin-aware single-part chopper.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SelectionError {
    Traversal(crate::ast::utility::nodes::TraversalError),
    ExtensionMember,
    ExtensionType,
    InvalidUnfolding,
    MissingVertex,
}
impl From<crate::ast::utility::nodes::TraversalError> for SelectionError {
    fn from(value: crate::ast::utility::nodes::TraversalError) -> Self {
        Self::Traversal(value)
    }
}

fn definition(
    member: &crate::ast::program::Member,
    use_site: bool,
) -> Result<Vertex, SelectionError> {
    use crate::ast::program::Member;
    Ok(match member {
        Member::Method(m) => {
            if use_site {
                Vertex::MethodSpec(m.name.clone())
            } else {
                Vertex::Method(m.name.clone())
            }
        }
        Member::Function(f) => {
            if use_site {
                Vertex::FunctionSpec(f.name.clone())
            } else {
                Vertex::Function(f.name.clone())
            }
        }
        Member::Predicate(p) => {
            if use_site {
                Vertex::PredicateSig(p.name.clone())
            } else {
                Vertex::PredicateBody(p.name.clone())
            }
        }
        Member::Field(f) => Vertex::Field(f.name.clone()),
        Member::Domain(d) => Vertex::DomainType(DomainType::new(
            &d.name,
            d.type_vars
                .iter()
                .map(|v| (v.clone(), crate::ast::r#type::Type::Var(v.clone())))
                .collect(),
            d.type_vars.clone(),
        )),
        Member::Extension(_) => return Err(SelectionError::ExtensionMember),
    })
}
fn type_uses(typ: &crate::ast::r#type::Type, out: &mut Vec<Vertex>) -> Result<(), SelectionError> {
    use crate::ast::r#type::Type;
    match typ {
        Type::Domain(d) => {
            out.push(Vertex::DomainType(d.clone()));
            for t in d.type_arguments() {
                type_uses(&t, out)?;
            }
        }
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => type_uses(t, out)?,
        Type::Map(pair) => {
            type_uses(&pair.0, out)?;
            type_uses(&pair.1, out)?;
        }
        Type::Extension(_) => return Err(SelectionError::ExtensionType),
        _ => {}
    }
    Ok(())
}
fn direct_uses(node: &crate::ast::utility::nodes::Node) -> Result<Vec<Vertex>, SelectionError> {
    use crate::ast::{ast::Info, expression::ExpKind, statement::StmtKind, utility::nodes::Node};
    let mut result = Vec::new();
    match node {
        Node::Stmt(s) => match s.kind() {
            StmtKind::MethodCall { method_name, .. } => {
                result.push(Vertex::MethodSpec(method_name.clone()))
            }
            StmtKind::Fold(p) | StmtKind::Unfold(p) => {
                result.push(Vertex::PredicateBody(p.location.predicate_name.clone()))
            }
            _ => {}
        },
        Node::Exp(e) => match e.kind() {
            ExpKind::FuncApp(name, _) => {
                let reveal = e
                    .metadata()
                    .info
                    .find(&|i| matches!(i, Info::Annotation(_)))
                    .is_some_and(|i| matches!(i, Info::Annotation(a) if a.contains_key("reveal")));
                result.push(if reveal {
                    Vertex::Function(name.clone())
                } else {
                    Vertex::FunctionSpec(name.clone())
                });
            }
            ExpKind::DomainFuncApp(name, ..) | ExpKind::BackendFuncApp(name, ..) => {
                result.push(Vertex::DomainFunction(name.clone()))
            }
            ExpKind::FieldAccess(f) => result.push(Vertex::Field(f.field.name.clone())),
            ExpKind::PredicateAccess(p) => {
                result.push(Vertex::PredicateSig(p.predicate_name.clone()))
            }
            ExpKind::Unfolding(acc, _) => {
                let ExpKind::PredicateAccessPredicate(p) = acc.kind() else {
                    return Err(SelectionError::InvalidUnfolding);
                };
                result.push(Vertex::PredicateBody(p.location.predicate_name.clone()));
            }
            _ => {}
        },
        Node::FieldAccess(f) => result.push(Vertex::Field(f.field.name.clone())),
        Node::PredicateAccess(p) => result.push(Vertex::PredicateSig(p.predicate_name.clone())),
        Node::Type(t) => type_uses(t, &mut result)?,
        _ => {}
    }
    Ok(result)
}
fn usages(
    node: &crate::ast::utility::nodes::Node,
    stop_at_quantifiers: bool,
) -> Result<Vec<Vertex>, SelectionError> {
    use crate::ast::{
        expression::ExpKind,
        utility::nodes::{Node, subnodes},
    };
    let mut out = direct_uses(node)?;
    if stop_at_quantifiers
        && matches!(node, Node::Exp(e) if matches!(e.kind(), ExpKind::Forall(..) | ExpKind::Exists(..) | ExpKind::ForPerm(..)))
    {
        return Ok(out);
    }
    for child in subnodes(node)? {
        out.extend(usages(&child, stop_at_quantifiers)?);
    }
    Ok(out)
}
fn quantifier_uses(
    node: &crate::ast::utility::nodes::Node,
    out: &mut Vec<Vertex>,
) -> Result<(), SelectionError> {
    use crate::ast::{
        expression::ExpKind,
        utility::nodes::{Node, subnodes},
    };
    if let Node::Exp(e) = node {
        if let ExpKind::Forall(_, triggers, _) | ExpKind::Exists(_, triggers, _) = e.kind() {
            let groups = triggers
                .iter()
                .map(|t| usages(&Node::Trigger(t.clone()), false))
                .collect::<Result<Vec<_>, _>>()?;
            if groups.iter().any(Vec::is_empty) {
                out.extend(usages(node, false)?);
            } else {
                out.extend(groups.into_iter().flatten());
            }
        }
    }
    for child in subnodes(node)? {
        quantifier_uses(&child, out)?;
    }
    Ok(())
}
fn dependencies(
    member: &crate::ast::program::Member,
) -> Result<Vec<(Vertex, Vertex)>, SelectionError> {
    use crate::ast::{ast::Info, program::Member, utility::nodes::Node};
    let def = definition(member, false)?;
    let use_v = definition(member, true)?;
    let mut edges = Vec::new();
    let mut add = |origin: &Vertex, node: Node| -> Result<(), SelectionError> {
        edges.extend(
            usages(&node, false)?
                .into_iter()
                .map(|target| (origin.clone(), target)),
        );
        Ok(())
    };
    match member {
        Member::Method(m) => {
            add(&def, Node::Member(member.clone()))?;
            for n in m.pres.iter().chain(&m.posts).cloned().map(Node::Exp).chain(
                m.formal_args
                    .iter()
                    .chain(&m.formal_returns)
                    .cloned()
                    .map(Node::LocalDecl),
            ) {
                add(&use_v, n)?;
            }
        }
        Member::Predicate(p) => {
            add(&def, Node::Member(member.clone()))?;
            for v in &p.formal_args {
                add(&use_v, Node::LocalDecl(v.clone()))?;
            }
        }
        Member::Function(f) => {
            add(&def, Node::Member(member.clone()))?;
            for n in f
                .pres
                .iter()
                .chain(&f.posts)
                .cloned()
                .map(Node::Exp)
                .chain(f.formal_args.iter().cloned().map(Node::LocalDecl))
                .chain(std::iter::once(Node::Exp(f.result())))
            {
                add(&use_v, n)?;
            }
            let opaque = f
                .meta
                .info
                .find(&|i| matches!(i, Info::Annotation(_)))
                .is_some_and(|i| matches!(i, Info::Annotation(a) if a.contains_key("opaque")));
            if !opaque {
                edges.push((use_v.clone(), def.clone()));
            }
        }
        Member::Field(_) => add(&def, Node::Member(member.clone()))?,
        Member::Domain(d) => {
            let special = d.name.ends_with("WellFoundedOrder");
            if special {
                edges.push((Vertex::Always, def.clone()));
            }
            for ax in &d.axioms {
                let ax_v = Vertex::DomainAxiom(ax.clone(), d.clone());
                let exp = Node::Exp(ax.exp().clone());
                edges.extend(usages(&exp, false)?.into_iter().map(|v| (ax_v.clone(), v)));
                if special {
                    edges.push((def.clone(), ax_v.clone()));
                } else {
                    let mut to_ax = usages(&exp, true)?;
                    quantifier_uses(&exp, &mut to_ax)?;
                    edges.extend(
                        to_ax
                            .into_iter()
                            .filter(
                                |v| !matches!(v, Vertex::DomainType(t) if t.domain_name == d.name),
                            )
                            .map(|v| (v, ax_v.clone())),
                    );
                }
            }
            for f in &d.functions {
                let f_v = Vertex::DomainFunction(f.name.clone());
                edges.extend(
                    usages(&Node::DomainFunc(f.clone()), false)?
                        .into_iter()
                        .map(|v| (f_v.clone(), v)),
                );
                if special {
                    edges.push((def.clone(), f_v));
                }
            }
        }
        Member::Extension(_) => return Err(SelectionError::ExtensionMember),
    }
    edges.push((def, Vertex::Always));
    edges.push((use_v, Vertex::Always));
    Ok(edges)
}

/// Source `PluginAwareChopper.chop(program, selection)` for the frontend's bound
/// of one program. The union of reachability closures is the single merged cut;
/// `None` means no member was selected. Unavailable extension traversal is an error.
pub fn chop_selected(
    program: &crate::ast::program::Program,
    selection: &std::collections::HashSet<String>,
) -> Result<Option<crate::ast::program::Program>, SelectionError> {
    use crate::ast::program::Member;
    let members = program.members();
    let edges = members
        .iter()
        .map(dependencies)
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let mut pending = members
        .iter()
        .filter(|member| selection.contains(member.name()))
        .map(|member| definition(member, false))
        .collect::<Result<Vec<_>, _>>()?;
    if pending.is_empty() {
        return Ok(None);
    }
    let mut included = Vec::new();
    while let Some(current) = pending.pop() {
        if included.contains(&current) {
            continue;
        }
        for (origin, target) in &edges {
            if *origin == current {
                pending.push(target.clone());
            }
        }
        included.push(current);
    }
    let mut methods = Vec::new();
    let mut functions = Vec::new();
    let mut predicates = Vec::new();
    let mut fields = Vec::new();
    let mut domains = Vec::new();
    for vertex in &included {
        match vertex {
            Vertex::Method(name) | Vertex::MethodSpec(name)
                if program.find_method_optionally(name).is_none() =>
            {
                return Err(SelectionError::MissingVertex);
            }
            Vertex::Function(name) | Vertex::FunctionSpec(name)
                if program.find_function_optionally(name).is_none() =>
            {
                return Err(SelectionError::MissingVertex);
            }
            Vertex::PredicateSig(name) | Vertex::PredicateBody(name)
                if program.find_predicate_optionally(name).is_none() =>
            {
                return Err(SelectionError::MissingVertex);
            }
            Vertex::Field(name) if program.find_field_optionally(name).is_none() => {
                return Err(SelectionError::MissingVertex);
            }
            Vertex::DomainFunction(name)
                if program.find_domain_function_optionally(name).is_none() =>
            {
                return Err(SelectionError::MissingVertex);
            }
            Vertex::DomainType(t) if program.find_domain_optionally(&t.domain_name).is_none() => {
                return Err(SelectionError::MissingVertex);
            }
            _ => {}
        }
    }
    for member in &members {
        match member {
            Member::Method(m) => {
                if included.contains(&Vertex::Method(m.name.clone())) {
                    methods.push(m.clone());
                } else if included.contains(&Vertex::MethodSpec(m.name.clone())) {
                    methods.push(m.copy_with(|x| x.body = None));
                }
            }
            Member::Function(f) => {
                if included.contains(&Vertex::Function(f.name.clone())) {
                    functions.push(f.clone());
                } else if included.contains(&Vertex::FunctionSpec(f.name.clone())) {
                    functions.push(f.copy_with(|x| x.body = None));
                }
            }
            Member::Predicate(p) => {
                if included.contains(&Vertex::PredicateBody(p.name.clone())) {
                    predicates.push(p.clone());
                } else if included.contains(&Vertex::PredicateSig(p.name.clone())) {
                    predicates.push(p.copy_with(|x| x.body = None));
                }
            }
            Member::Field(f) if included.contains(&Vertex::Field(f.name.clone())) => {
                fields.push(f.clone())
            }
            Member::Domain(d) => {
                let fs = d
                    .functions
                    .iter()
                    .filter(|f| included.contains(&Vertex::DomainFunction(f.name.clone())))
                    .cloned()
                    .collect::<Vec<_>>();
                let axioms = d
                    .axioms
                    .iter()
                    .filter(|a| included.contains(&Vertex::DomainAxiom((*a).clone(), d.clone())))
                    .cloned()
                    .collect::<Vec<_>>();
                let used = included
                    .iter()
                    .any(|v| matches!(v, Vertex::DomainType(t) if t.domain_name == d.name));
                if used || !fs.is_empty() || !axioms.is_empty() {
                    domains.push(d.copy_with(|v| {
                        v.functions = fs;
                        v.axioms = axioms;
                    }));
                }
            }
            _ => {}
        }
    }
    Ok(Some(program.copy_with(|p| {
        p.methods = methods;
        p.functions = functions;
        p.predicates = predicates;
        p.fields = fields;
        p.domains = domains;
    })))
}

#[cfg(test)]
mod selection_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        program::{Method, MethodData, Program},
        statement::{Stmt, StmtKind},
    };
    #[test]
    fn used_domain_function_reaches_its_axiom() {
        use crate::ast::{
            expression::{Exp, ExpExtra, ExpKind},
            program::{
                Domain, DomainAxiom, DomainAxiomKind, DomainData, DomainFunc, DomainFuncData,
            },
            r#type::Type,
        };
        let meta = Metadata::default();
        let app = Exp::with_extra(
            ExpKind::DomainFuncApp("f".into(), vec![], Default::default()),
            meta.clone(),
            ExpExtra {
                typ: Some(Type::Bool),
                domain_name: Some("D".into()),
                ..Default::default()
            },
        );
        let function = DomainFunc::new(DomainFuncData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let axiom = DomainAxiom::new(DomainAxiomKind::Anonymous {
            exp: app.clone(),
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![function],
            axioms: vec![axiom],
            type_vars: vec![],
            interpretations: None,
            meta: meta.clone(),
        });
        let body = Stmt::new(StmtKind::Assert(app), meta.clone());
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: meta.clone(),
        });
        let p = Program::new(
            vec![domain],
            vec![],
            vec![],
            vec![],
            vec![method],
            vec![],
            meta,
        );
        let result = chop_selected(&p, &std::collections::HashSet::from(["m".into()]))
            .unwrap()
            .unwrap();
        assert_eq!(result.domains[0].functions.len(), 1);
        assert_eq!(result.domains[0].axioms.len(), 1);
    }
    #[test]
    fn plugin_well_founded_domain_is_always_retained() {
        use crate::ast::program::{Domain, DomainData};
        let meta = Metadata::default();
        let domain = Domain::new(DomainData {
            name: "IntWellFoundedOrder".into(),
            functions: vec![],
            axioms: vec![],
            type_vars: vec![],
            interpretations: None,
            meta: meta.clone(),
        });
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![],
                declarations: vec![],
            },
            meta.clone(),
        );
        let method = Method::new(MethodData {
            name: "selected".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: meta.clone(),
        });
        let p = Program::new(
            vec![domain],
            vec![],
            vec![],
            vec![],
            vec![method],
            vec![],
            meta,
        );
        let selected = chop_selected(&p, &std::collections::HashSet::from(["selected".into()]))
            .unwrap()
            .unwrap();
        assert_eq!(selected.domains[0].name, "IntWellFoundedOrder");
    }
    #[test]
    fn selected_method_keeps_called_specification_without_body() {
        let m = Metadata::default();
        let method = |name: &str, body: Stmt| {
            Method::new(MethodData {
                name: name.into(),
                formal_args: vec![],
                formal_returns: vec![],
                pres: vec![],
                posts: vec![],
                body: Some(body),
                meta: m.clone(),
            })
        };
        let empty = Stmt::new(
            StmtKind::Seqn {
                statements: vec![],
                declarations: vec![],
            },
            m.clone(),
        );
        let call = Stmt::new(
            StmtKind::MethodCall {
                method_name: "callee".into(),
                args: vec![],
                targets: vec![],
            },
            m.clone(),
        );
        let p = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![
                method("caller", call),
                method("callee", empty.clone()),
                method("unused", empty),
            ],
            vec![],
            m,
        );
        let result = chop_selected(&p, &std::collections::HashSet::from(["caller".into()]))
            .unwrap()
            .unwrap();
        assert_eq!(result.methods.len(), 2);
        assert!(result.find_method("caller").unwrap().body.is_some());
        assert!(result.find_method("callee").unwrap().body.is_none());
        assert!(
            chop_selected(&p, &std::collections::HashSet::from(["missing".into()]))
                .unwrap()
                .is_none()
        );
    }
}
