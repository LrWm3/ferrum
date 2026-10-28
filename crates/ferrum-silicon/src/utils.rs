//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Utils.scala
//!
//! Purpose:
//! Provide shared symbolic, AST, lifecycle and consistency helpers.
//!
//! Planned Rust structure:
//! utils package defines freshSnap/toSf, mapReduceLeft, conflictFreeUnion, append, Counter,
//! NoOpStatefulComponent, MustBeReinitializedAfterReset and NotNothing. Nested ast helpers build
//! boolean/min/quantifier expressions, rewrite range membership, trigger fallback, source
//! positions, flattening, substitution, parser type extraction and ViperEmbedding; consistency
//! checks unsupported permissions and inhale/exhale positions and constructs internal errors.
//!
//! Behavior to preserve:
//! mapReduceLeft preserves left-fold order and empty unit; conflictFreeUnion iterates only first
//! map, excluding second-only keys, an apparent mismatch with its name to reconcile. Counter is
//! non-thread-safe and clone preserves current value. Trigger fallback is not thread-safe; first
//! retain standard triggers then try add/subtract and rewriting. Permission/inhale-exhale errors
//! retain node and metadata; unexpected node errors capture stack.
//!
//! Integration:
//! state::terms, verifier, rules::{evaluator,consumer}, ferrum_silver::ast and ferrum_silver::utility
//! and frontend consistency.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Counter ownership, apparent union omission and native stack traces.
//!
//! Status: map/counter, AST construction/substitution, range rewriting and backend consistency
//! helpers implemented. Parser type extraction, advanced trigger/fresh adapters and native
//! sort embedding remain. Unexpected-node helpers accept a caller-captured native stack.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::package::Map;
use crate::state::terms::{Sort, Term, TermFactory};
use std::hash::Hash;

/// Evaluate mapped values before reducing, preserving strict source collection effects.
pub fn map_reduce_left<E>(
    values: impl IntoIterator<Item = E>,
    map: impl FnMut(E) -> E,
    reduce: impl FnMut(E, E) -> E,
    unit: E,
) -> E {
    values
        .into_iter()
        .map(map)
        .collect::<Vec<_>>()
        .into_iter()
        .reduce(reduce)
        .unwrap_or(unit)
}
/// The source intentionally iterates only m1: keys present solely in m2 are omitted.
pub fn conflict_free_union<K: Eq + Hash + Clone, V: Eq + Clone>(
    first: &Map<K, V>,
    second: &Map<K, V>,
) -> (Map<K, V>, Map<K, (V, V)>) {
    let mut union = Map::new();
    let mut conflicts = Map::new();
    for (key, value) in first {
        match second.get(key) {
            Some(other) if other != value => {
                conflicts.insert(key.clone(), (value.clone(), other.clone()));
            }
            _ => {
                union.insert(key.clone(), value.clone());
            }
        }
    }
    (union, conflicts)
}
pub fn append<K: Eq + Hash + Clone, C: Clone>(
    first: &Map<K, C>,
    second: &Map<K, C>,
    mut combine: impl FnMut(&C, &C) -> C,
) -> Map<K, C> {
    let mut result = first.clone();
    for (key, value) in second {
        let value = result
            .get(key)
            .map(|old| combine(old, value))
            .unwrap_or_else(|| value.clone());
        result.insert(key.clone(), value);
    }
    result
}
#[derive(Clone, Debug)]
pub struct Counter {
    first: i32,
    next: i32,
}
impl Default for Counter {
    fn default() -> Self {
        Self::new(0)
    }
}
impl Counter {
    pub fn new(first: i32) -> Self {
        Self { first, next: first }
    }
    pub fn next(&mut self) -> i32 {
        let value = self.next;
        self.next = self.next.wrapping_add(1);
        value
    }
}
impl ferrum_silver::components::components::LifetimeComponent for Counter {
    fn start(&mut self) {}
    fn stop(&mut self) {}
}
impl ferrum_silver::components::components::StatefulComponent for Counter {
    fn reset(&mut self) {
        self.next = self.first;
    }
}
#[derive(Default)]
pub struct NoOpStatefulComponent;
impl ferrum_silver::components::components::LifetimeComponent for NoOpStatefulComponent {
    fn start(&mut self) {}
    fn stop(&mut self) {}
}
impl ferrum_silver::components::components::StatefulComponent for NoOpStatefulComponent {
    fn reset(&mut self) {}
}
pub trait MustBeReinitializedAfterReset:
    ferrum_silver::components::components::StatefulComponent
{
}
pub fn to_snapshot_function(factory: &TermFactory, term: Term) -> impl Fn(Sort) -> Term + '_ {
    move |sort| factory.sort_wrapper(term.clone(), sort)
}

pub mod ast {
    use super::*;
    use ferrum_silver::ast::{
        ast::Metadata,
        expression::{Exp, ExpKind, Trigger},
        position::Position,
        program::{LocalVarDecl, Program},
        utility::nodes::{self, Node},
    };
    use ferrum_silver::verifier::verification_result::DiagnosticError;
    fn inherited_metadata(expression: &Exp) -> Metadata {
        Metadata {
            position: expression.metadata().position.clone(),
            info: expression.metadata().info.clone(),
            error_trafo: Default::default(),
        }
    }
    pub fn big_and(
        expressions: impl IntoIterator<Item = Exp>,
        map: impl FnMut(Exp) -> Exp,
        empty_position: Position,
    ) -> Exp {
        map_reduce_left(
            expressions,
            map,
            |a, b| {
                let meta = inherited_metadata(&a);
                Exp::new(ExpKind::And(a, b), meta)
            },
            Exp::new(
                ExpKind::TrueLit,
                Metadata {
                    position: empty_position,
                    ..Default::default()
                },
            ),
        )
    }
    pub fn big_or(
        expressions: impl IntoIterator<Item = Exp>,
        map: impl FnMut(Exp) -> Exp,
        empty_position: Position,
    ) -> Exp {
        map_reduce_left(
            expressions,
            map,
            |a, b| {
                let meta = inherited_metadata(&a);
                Exp::new(ExpKind::Or(a, b), meta)
            },
            Exp::new(
                ExpKind::FalseLit,
                Metadata {
                    position: empty_position,
                    ..Default::default()
                },
            ),
        )
    }
    pub fn remove_known_to_be_true(expressions: &[Exp], terms: &[Term]) -> Vec<Exp> {
        expressions
            .iter()
            .zip(terms)
            .filter(|(_, term)| !matches!(term.kind(), crate::state::terms::TermKind::True))
            .map(|(exp, _)| exp.clone())
            .collect()
    }
    pub fn simplify_variable_name(name: &str) -> Result<&str, &'static str> {
        name.rfind('@')
            .map(|at| &name[..at])
            .ok_or("variable name has no version delimiter")
    }
    pub fn replace_vars_in_exp(
        expression: &Exp,
        names: &[String],
        replacements: &[Exp],
    ) -> Result<Exp, ferrum_silver::utility::sanitizer::SanitizeError> {
        let substitutions = names
            .iter()
            .cloned()
            .zip(replacements.iter().cloned())
            .collect();
        ferrum_silver::utility::sanitizer::replace_free_variables_in_expression(
            expression,
            substitutions,
            Default::default(),
        )
    }
    pub fn build_min_exp(expressions: &[Exp]) -> Result<Exp, &'static str> {
        let Some((first, rest)) = expressions.split_first() else {
            return Err("empty minimum expression");
        };
        if rest.is_empty() {
            Ok(first.clone())
        } else {
            Ok(Exp::new(
                ExpKind::DebugPermMin(first.clone(), build_min_exp(rest)?),
                inherited_metadata(first),
            ))
        }
    }
    pub fn build_quant_exp(
        quantifier: crate::state::terms::Quantifier,
        variables: Vec<LocalVarDecl>,
        body: Exp,
        triggers: Vec<Trigger>,
    ) -> Exp {
        let metadata = body.metadata().clone();
        Exp::new(
            match quantifier {
                crate::state::terms::Quantifier::Forall => {
                    ExpKind::Forall(variables, triggers, body)
                }
                crate::state::terms::Quantifier::Exists => {
                    ExpKind::Exists(variables, triggers, body)
                }
            },
            metadata,
        )
    }
    pub fn source_line(position: &Position) -> String {
        position
            .line_column()
            .map(|p| p.line().to_string())
            .unwrap_or_else(|| position.to_string())
    }
    pub fn source_line_column(position: &Position) -> String {
        position
            .line_column()
            .map(|p| format!("{}:{}", p.line(), p.column()))
            .unwrap_or_else(|| position.to_string())
    }
    pub fn flatten_operator(
        expression: &Exp,
        args: &impl Fn(&Exp) -> Option<Vec<Exp>>,
    ) -> Vec<Exp> {
        match args(expression) {
            Some(children) => children
                .iter()
                .flat_map(|child| flatten_operator(child, args))
                .collect(),
            None => vec![expression.clone()],
        }
    }
    pub fn rewrite_range_contains(program: &Program) -> Result<Program, DiagnosticError> {
        let mapped = nodes::map_node_tree(&Node::Program(program.clone()), &|node| {
            if let Node::Exp(exp) = node
                && let ExpKind::SeqContains(value, range) = exp.kind()
                && let ExpKind::RangeSeq(a, b) = range.kind()
            {
                let meta = Metadata {
                    position: exp.metadata().position.clone(),
                    ..Default::default()
                };
                let changed = Exp::new(
                    ExpKind::And(
                        Exp::new(ExpKind::LeCmp(a.clone(), value.clone()), meta.clone()),
                        Exp::new(ExpKind::LtCmp(value.clone(), b.clone()), meta.clone()),
                    ),
                    meta,
                );
                return ferrum_silver::ast::utility::viper_strategy::preserve_metadata(
                    node,
                    &Node::Exp(changed),
                    true,
                )
                .map_err(|_| DiagnosticError::Unsupported("range membership rewrite metadata"));
            }
            Ok(node.clone())
        })?;
        match mapped {
            Node::Program(program) => Ok(program),
            _ => Err(DiagnosticError::InvalidNode("rewritten program")),
        }
    }
}

pub mod consistency {
    use ferrum_silver::ast::{
        expression::ExpKind,
        program::{Member, Program},
        utility::nodes::{Node, TraversalError, subnodes},
    };
    use ferrum_silver::verifier::verification_error::{
        ErrorReason, VerificationError, VerificationErrorKind,
    };
    pub fn unsupported_permission(
        node: Node,
        render: &impl Fn(&Node) -> Result<String, TraversalError>,
    ) -> Result<VerificationError, TraversalError> {
        let explanation = format!(
            "Silicon doesn't support the permission expression {}.",
            render(&node)?
        );
        Ok(VerificationError::new(
            VerificationErrorKind::Internal(Some(node.clone())),
            ErrorReason::FeatureUnsupported { node, explanation },
        ))
    }
    pub fn unsupported_inhale_exhale(node: Node) -> VerificationError {
        VerificationError::new(VerificationErrorKind::Internal(Some(node.clone())),ErrorReason::FeatureUnsupported {node,explanation:"Silicon currently doesn't support inhale-exhale assertions in certain positions. See Silicon issue #271 for further details.".into()})
    }
    pub fn check_permissions(
        root: &Node,
        render: &impl Fn(&Node) -> Result<String, TraversalError>,
    ) -> Result<Vec<VerificationError>, TraversalError> {
        let mut result = Vec::new();
        if matches!(root,Node::Exp(exp) if matches!(exp.kind(),ExpKind::EpsilonPerm)) {
            result.push(unsupported_permission(root.clone(), render)?);
        }
        for child in subnodes(root)? {
            result.extend(check_permissions(&child, render)?);
        }
        Ok(result)
    }
    fn collect_impure(root: &Node) -> Result<Vec<VerificationError>, TraversalError> {
        let mut result = Vec::new();
        if matches!(root,Node::Exp(exp) if matches!(exp.kind(),ExpKind::InhaleExhaleExp(..)) && !exp.is_pure())
        {
            result.push(unsupported_inhale_exhale(root.clone()));
        }
        for child in subnodes(root)? {
            result.extend(collect_impure(&child)?);
        }
        Ok(result)
    }
    pub fn check_inhale_exhale_assertions(
        root: &Node,
    ) -> Result<Vec<VerificationError>, TraversalError> {
        let mut result = Vec::new();
        match root {
            Node::Member(Member::Function(function)) => {
                for pre in &function.pres {
                    result.extend(collect_impure(&Node::Exp(pre.clone()))?);
                }
            }
            Node::Member(Member::Predicate(predicate)) => {
                if let Some(body) = &predicate.body {
                    result.extend(collect_impure(&Node::Exp(body.clone()))?);
                }
            }
            _ => {}
        }
        for child in subnodes(root)? {
            result.extend(check_inhale_exhale_assertions(&child)?);
        }
        Ok(result)
    }
    pub fn check(
        program: &Program,
        render: &impl Fn(&Node) -> Result<String, TraversalError>,
    ) -> Result<Vec<VerificationError>, TraversalError> {
        let root = Node::Program(program.clone());
        let mut result = check_permissions(&root, render)?;
        result.extend(check_inhale_exhale_assertions(&root)?);
        Ok(result)
    }
    pub fn unexpected_node(
        node: Node,
        explanation: String,
        stack_trace: Vec<String>,
    ) -> VerificationError {
        VerificationError::new(
            VerificationErrorKind::Internal(Some(node.clone())),
            ErrorReason::UnexpectedNode {
                node,
                explanation,
                stack_trace,
            },
        )
    }
    pub fn unexpected_inhale_exhale(node: Node, stack_trace: Vec<String>) -> VerificationError {
        unexpected_node(node,"InhaleExhale-expressions should have been eliminated by calling expr.whenInhaling/Exhaling.".into(),stack_trace)
    }
    pub fn unexpected_domain_node(node: Node, stack_trace: Vec<String>) -> VerificationError {
        unexpected_node(
            node,
            "The expression should not occur in domain expressions.".into(),
            stack_trace,
        )
    }
}
