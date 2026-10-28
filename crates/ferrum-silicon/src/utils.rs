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
//! Status: map/counter, AST construction/substitution, range rewriting, trigger preprocessing
//! and backend consistency helpers are implemented. Parser type extraction and native sort
//! embedding remain. Unexpected-node helpers accept a caller-captured native stack.

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
    /// One source-ordered quantifier trigger report, before and after preprocessing.
    #[derive(Clone, Debug)]
    pub struct QuantifierTriggerEvent {
        pub original: Exp,
        pub rewritten: Exp,
        pub old_triggers: Vec<Trigger>,
        pub triggers: Vec<Trigger>,
    }
    #[derive(Clone, Debug)]
    pub struct AutoTriggeredProgram {
        pub program: Program,
        pub events: Vec<QuantifierTriggerEvent>,
    }
    #[derive(Debug)]
    pub enum AutoTriggerProgramError {
        Trigger(String),
        Traversal(DiagnosticError),
    }
    #[derive(Debug)]
    pub enum AutoTriggerWithCallbackError<E> {
        Preprocessing(AutoTriggerProgramError),
        Callback(E),
    }

    /// Compute triggers bottom-up, as Silicon does before parallel verification.
    /// CFGs are deliberately not transformed, matching the source TODO.
    pub fn auto_trigger_program(
        program: &Program,
    ) -> Result<AutoTriggeredProgram, AutoTriggerProgramError> {
        let mut events = Vec::new();
        let program = auto_trigger_program_with_callback(program, |event| {
            events.push(event.clone());
            Ok::<_, std::convert::Infallible>(())
        })
        .map_err(|error| match error {
            AutoTriggerWithCallbackError::Preprocessing(error) => error,
            AutoTriggerWithCallbackError::Callback(never) => match never {},
        })?;
        Ok(AutoTriggeredProgram { program, events })
    }

    /// Report each quantifier immediately in traversal order; a callback failure stops traversal.
    pub fn auto_trigger_program_with_callback<E>(
        program: &Program,
        callback: impl FnMut(&QuantifierTriggerEvent) -> Result<(), E>,
    ) -> Result<Program, AutoTriggerWithCallbackError<E>> {
        use ferrum_silver::ast::utility::{
            generic_axiom_rewriter,
            triggers::{self, AxiomRewriter, SilverQuantifier, TriggerGeneration},
        };
        static ADVANCED: std::sync::OnceLock<std::sync::Mutex<TriggerGeneration>> =
            std::sync::OnceLock::new();
        let callback = std::cell::RefCell::new(callback);
        let failure = std::cell::RefCell::new(None);
        let callback_failure = std::cell::RefCell::new(None);
        let transformed = nodes::map_node_tree_bottom_up(
            &Node::Program(program.clone()),
            &|node| {
                let Node::Exp(expression) = node else {
                    return Ok(node.clone());
                };
                let old = match expression.kind() {
                    ExpKind::Forall(_, triggers, _) if expression.is_pure() => triggers.clone(),
                    ExpKind::Exists(_, triggers, _) => triggers.clone(),
                    _ => return Ok(node.clone()),
                };
                let compute = || -> Result<Exp, String> {
                    let standard = triggers::auto_trigger(expression)
                        .map_err(|e| format!("standard trigger generation: {e:?}"))?;
                    let present = match standard.kind() {
                        ExpKind::Forall(_, t, _) | ExpKind::Exists(_, t, _) => t,
                        _ => unreachable!(),
                    };
                    if !present.is_empty() {
                        return Ok(standard);
                    }
                    let quantifier = SilverQuantifier::new(expression.clone())
                        .map_err(|_| "invalid quantifier".to_owned())?;
                    let mut generator = ADVANCED
                        .get_or_init(|| std::sync::Mutex::new(TriggerGeneration::new(true)))
                        .lock()
                        .expect("advanced trigger generator poisoned");
                    let candidate = triggers::generate_trigger_set(&quantifier, &mut generator)
                        .map_err(|e| format!("advanced trigger generation: {e:?}"))?;
                    drop(generator);
                    let Some((variables, sets)) = candidate else {
                        return Ok(expression.clone());
                    };
                    let body = match expression.kind() {
                        ExpKind::Forall(_, _, body) | ExpKind::Exists(_, _, body) => body.clone(),
                        _ => unreachable!(),
                    };
                    let kind = match expression.kind() {
                        ExpKind::Forall(..) => ExpKind::Forall(variables, vec![], body),
                        ExpKind::Exists(..) => ExpKind::Exists(variables, vec![], body),
                        _ => unreachable!(),
                    };
                    let intermediate = Exp::new(kind, inherited_metadata(expression));
                    let intermediate = SilverQuantifier::new(intermediate)
                        .map_err(|_| "invalid quantifier".to_owned())?;
                    let mut adapter = AxiomRewriter {
                        render: ferrum_silver::ast::pretty::pretty_printer::pretty_node,
                    };
                    Ok(
                        generic_axiom_rewriter::rewrite(&mut adapter, &intermediate, &sets)
                            .map_err(|e| format!("advanced trigger rewrite: {e:?}"))?
                            .map(SilverQuantifier::into_expression)
                            .unwrap_or_else(|| expression.clone()),
                    )
                };
                let rewritten = compute().map_err(|error| {
                    *failure.borrow_mut() = Some(error);
                    DiagnosticError::Unsupported("quantifier trigger preprocessing")
                })?;
                let triggers = match rewritten.kind() {
                    ExpKind::Forall(_, t, _) | ExpKind::Exists(_, t, _) => t.clone(),
                    _ => unreachable!(),
                };
                let event = QuantifierTriggerEvent {
                    original: expression.clone(),
                    rewritten: rewritten.clone(),
                    old_triggers: old,
                    triggers,
                };
                callback.borrow_mut()(&event).map_err(|error| {
                    *callback_failure.borrow_mut() = Some(error);
                    DiagnosticError::Unsupported("quantifier trigger reporter")
                })?;
                Ok(Node::Exp(rewritten))
            },
            false,
        );
        if let Some(error) = callback_failure.into_inner() {
            return Err(AutoTriggerWithCallbackError::Callback(error));
        }
        if let Some(error) = failure.into_inner() {
            return Err(AutoTriggerWithCallbackError::Preprocessing(
                AutoTriggerProgramError::Trigger(error),
            ));
        }
        let Node::Program(program) = transformed.map_err(|error| {
            AutoTriggerWithCallbackError::Preprocessing(AutoTriggerProgramError::Traversal(error))
        })?
        else {
            return Err(AutoTriggerWithCallbackError::Preprocessing(
                AutoTriggerProgramError::Traversal(DiagnosticError::InvalidNode(
                    "triggered program",
                )),
            ));
        };
        Ok(program)
    }

    #[cfg(test)]
    mod trigger_preprocessing_tests {
        use super::*;
        use ferrum_silver::parser::{
            fast_parser::parse_program,
            parse_ast::init_properties,
            resolver::{NameAnalyser, check_program_core},
            translator::translate_program_core,
        };
        #[test]
        fn callback_failure_stops_at_first_quantifier() {
            let parsed = parse_program("function f(x: Int): Int function p(): Bool { (forall i: Int :: f(i) == f(i)) && (exists j: Int :: f(j) == f(j)) }", "test.vpr").unwrap();
            init_properties(parsed.node()).unwrap();
            assert!(NameAnalyser::default().run(parsed.node()).unwrap());
            check_program_core(&parsed, &mut |_, _| {}).unwrap();
            let program = translate_program_core(&parsed).unwrap();
            let mut calls = 0;
            let error = auto_trigger_program_with_callback(&program, |event| {
                calls += 1;
                assert!(matches!(event.original.kind(), ExpKind::Forall(..)));
                Err("report failed")
            })
            .unwrap_err();
            assert!(matches!(
                error,
                AutoTriggerWithCallbackError::Callback("report failed")
            ));
            assert_eq!(calls, 1);
        }

        #[test]
        fn impure_forall_is_not_triggered_at_this_stage() {
            let parsed = parse_program(
                "field f: Int method m() { inhale forall r: Ref :: acc(r.f) }",
                "test.vpr",
            )
            .unwrap();
            init_properties(parsed.node()).unwrap();
            assert!(NameAnalyser::default().run(parsed.node()).unwrap());
            check_program_core(&parsed, &mut |_, _| {}).unwrap();
            let program = translate_program_core(&parsed).unwrap();
            let result = auto_trigger_program(&program).unwrap();
            assert!(result.events.is_empty());
        }

        #[test]
        fn nested_quantifiers_are_processed_bottom_up() {
            let parsed = parse_program("function f(x: Int, y: Int): Int function p(): Bool { forall x: Int :: exists y: Int :: f(x, y) == f(x, y) }", "test.vpr").unwrap();
            init_properties(parsed.node()).unwrap();
            assert!(NameAnalyser::default().run(parsed.node()).unwrap());
            check_program_core(&parsed, &mut |_, _| {}).unwrap();
            let program = translate_program_core(&parsed).unwrap();
            let result = auto_trigger_program(&program).unwrap();
            assert_eq!(result.events.len(), 2);
            assert!(matches!(
                result.events[0].rewritten.kind(),
                ExpKind::Exists(..)
            ));
            assert!(matches!(
                result.events[1].rewritten.kind(),
                ExpKind::Forall(..)
            ));
        }

        #[test]
        fn arithmetic_fallback_rewrites_trigger_variable() {
            let parsed = parse_program("function f(x: Int): Int function p(): Bool { forall i: Int :: f(i + 1) == f(i + 1) }", "test.vpr").unwrap();
            init_properties(parsed.node()).unwrap();
            assert!(NameAnalyser::default().run(parsed.node()).unwrap());
            check_program_core(&parsed, &mut |_, _| {}).unwrap();
            let program = translate_program_core(&parsed).unwrap();
            let result = auto_trigger_program(&program).unwrap();
            assert_eq!(result.events.len(), 1);
            assert!(!result.events[0].triggers.is_empty());
            assert!(
                matches!(result.events[0].rewritten.kind(), ExpKind::Forall(vars, _, _) if vars.iter().any(|v| v.name.starts_with("__rw_")))
            );
        }

        #[test]
        fn handles_forall_exists_and_reports_missing_in_source_order() {
            let parsed = parse_program("function f(x: Int): Int function p(): Bool { (forall i: Int :: f(i) == f(i)) && (exists j: Int :: f(j) == f(j)) && (forall k: Int :: k == k) }", "test.vpr").unwrap();
            init_properties(parsed.node()).unwrap();
            assert!(NameAnalyser::default().run(parsed.node()).unwrap());
            check_program_core(&parsed, &mut |_, _| {}).unwrap();
            let program = translate_program_core(&parsed).unwrap();
            let result = auto_trigger_program(&program).unwrap();
            assert_eq!(result.events.len(), 3);
            assert!(matches!(
                result.events[0].rewritten.kind(),
                ExpKind::Forall(..)
            ));
            assert!(matches!(
                result.events[1].rewritten.kind(),
                ExpKind::Exists(..)
            ));
            assert!(!result.events[0].triggers.is_empty());
            assert!(!result.events[1].triggers.is_empty());
            assert!(result.events[2].triggers.is_empty());
        }
    }

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
