//! Dependency collection for verifier cache keys.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/Caching.scala
//! Status: partial; dependency collection is implemented. MD5 and pretty-printed normalized
//! entity hashing remain pending until the source printer and digest interface are available.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    expression::ExpKind,
    program::{Member, Method, Program},
    statement::StmtKind,
    utility::nodes::{Node, TraversalError, subnodes},
};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DependencyError {
    Traversal(TraversalError),
    MissingFunction(String),
    MissingPredicate(String),
    MissingMethod(String),
}
impl From<TraversalError> for DependencyError {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
fn is_hashable(n: &Node) -> bool {
    !matches!(n, Node::Program(_) | Node::Trigger(_))
}
fn mark_subtree(root: &Node, marker: &mut Vec<Node>) -> Result<(), DependencyError> {
    for child in subnodes(root)? {
        mark_subtree(&child, marker)?;
    }
    if is_hashable(root) && !marker.contains(root) {
        marker.push(root.clone());
    }
    Ok(())
}
/// Emulate deepCollect: children are evaluated before the callback, while returned
/// callback results precede the collected child results.
fn collect(
    root: &Node,
    callback: &mut impl FnMut(&Node) -> Result<Vec<Node>, DependencyError>,
) -> Result<Vec<Node>, DependencyError> {
    let mut children = Vec::new();
    for child in subnodes(root)? {
        children.extend(collect(&child, callback)?);
    }
    let mut own = callback(root)?;
    own.extend(children);
    Ok(own)
}
fn recursive_dependencies(
    program: &Program,
    roots: &[Node],
    marker: &mut Vec<Node>,
) -> Result<Vec<Node>, DependencyError> {
    let mut result = Vec::new();
    for root in roots {
        let mut callback = |node: &Node| -> Result<Vec<Node>, DependencyError> {
            match node {
                Node::Exp(exp) if matches!(exp.kind(), ExpKind::FuncApp(..)) => {
                    let ExpKind::FuncApp(name, _) = exp.kind() else {
                        unreachable!()
                    };
                    let f = program
                        .find_function_optionally(name)
                        .ok_or_else(|| DependencyError::MissingFunction(name.clone()))?;
                    let member = Node::Member(Member::Function(f.clone()));
                    if marker.contains(&member) {
                        return Ok(Vec::new());
                    }
                    mark_subtree(&member, marker)?;
                    let children = f
                        .pres
                        .iter()
                        .chain(&f.posts)
                        .chain(f.body.iter())
                        .cloned()
                        .map(Node::Exp)
                        .collect::<Vec<_>>();
                    let mut out = vec![member];
                    out.extend(recursive_dependencies(program, &children, marker)?);
                    Ok(out)
                }
                Node::PredicateAccess(p) => {
                    let pred = program
                        .find_predicate_optionally(&p.predicate_name)
                        .ok_or_else(|| {
                            DependencyError::MissingPredicate(p.predicate_name.clone())
                        })?;
                    let member = Node::Member(Member::Predicate(pred.clone()));
                    if marker.contains(&member) {
                        return Ok(Vec::new());
                    }
                    mark_subtree(&member, marker)?;
                    let children = pred.body.iter().cloned().map(Node::Exp).collect::<Vec<_>>();
                    let mut out = vec![member];
                    out.extend(recursive_dependencies(program, &children, marker)?);
                    Ok(out)
                }
                Node::Exp(exp) if matches!(exp.kind(), ExpKind::PredicateAccess(..)) => {
                    let ExpKind::PredicateAccess(p) = exp.kind() else {
                        unreachable!()
                    };
                    let pred = program
                        .find_predicate_optionally(&p.predicate_name)
                        .ok_or_else(|| {
                            DependencyError::MissingPredicate(p.predicate_name.clone())
                        })?;
                    let member = Node::Member(Member::Predicate(pred.clone()));
                    if marker.contains(&member) {
                        return Ok(Vec::new());
                    }
                    mark_subtree(&member, marker)?;
                    let children = pred.body.iter().cloned().map(Node::Exp).collect::<Vec<_>>();
                    let mut out = vec![member];
                    out.extend(recursive_dependencies(program, &children, marker)?);
                    Ok(out)
                }
                _ => Ok(Vec::new()),
            }
        };
        result.extend(collect(root, &mut callback)?);
    }
    Ok(result)
}
/// The source marks the initial method and function/predicate subtrees, but deliberately
/// does not mark a called method when it visits its specification.
pub fn get_dependencies(program: &Program, method: &Method) -> Result<Vec<Node>, DependencyError> {
    let root = Node::Member(Member::Method(method.clone()));
    let mut marker = Vec::new();
    mark_subtree(&root, &mut marker)?;
    let mut out = vec![root];
    out.extend(
        program
            .domains
            .iter()
            .cloned()
            .map(|v| Node::Member(Member::Domain(v))),
    );
    out.extend(
        program
            .fields
            .iter()
            .cloned()
            .map(|v| Node::Member(Member::Field(v))),
    );
    let roots: Vec<Node> = method
        .pres
        .iter()
        .chain(&method.posts)
        .cloned()
        .map(Node::Exp)
        .chain(method.body.iter().cloned().map(Node::Stmt))
        .collect();
    for root in roots {
        let mut callback = |node: &Node| -> Result<Vec<Node>, DependencyError> {
            match node {
                Node::Stmt(s) if matches!(s.kind(), StmtKind::MethodCall { .. }) => {
                    let StmtKind::MethodCall { method_name, .. } = s.kind() else {
                        unreachable!()
                    };
                    let m = program
                        .find_method_optionally(method_name)
                        .ok_or_else(|| DependencyError::MissingMethod(method_name.clone()))?;
                    if marker.contains(&Node::Member(Member::Method(m.clone()))) {
                        return Ok(Vec::new());
                    }
                    let spec: Vec<_> = m
                        .formal_args
                        .iter()
                        .chain(&m.formal_returns)
                        .cloned()
                        .map(Node::LocalDecl)
                        .chain(m.pres.iter().chain(&m.posts).cloned().map(Node::Exp))
                        .collect();
                    let mut result = spec.clone();
                    result.extend(recursive_dependencies(program, &spec, &mut marker)?);
                    Ok(result)
                }
                Node::Exp(e)
                    if matches!(
                        e.kind(),
                        ExpKind::FuncApp(..) | ExpKind::PredicateAccess(..)
                    ) =>
                {
                    recursive_dependencies(program, std::slice::from_ref(node), &mut marker)
                }
                Node::PredicateAccess(_) => {
                    recursive_dependencies(program, std::slice::from_ref(node), &mut marker)
                }
                _ => Ok(Vec::new()),
            }
        };
        out.extend(collect(&root, &mut callback)?);
    }
    Ok(out)
}
