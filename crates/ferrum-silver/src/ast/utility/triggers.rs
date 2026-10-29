//! Silver trigger-generation adapters and integer isolation.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Triggers.scala
//! Status: partial; arithmetic solver, axiom rewriting and built-in trigger generation are implemented.
//! Extension trigger reconstruction and configurable custom classification remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::{
    generic_arithmetic_solver::ArithmeticAdapter,
    nodes::{Node, TraversalError, subnodes},
};
use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpKind, ExpressionTypeError, LocalVar},
    r#type::Type,
};
#[derive(Debug)]
pub enum ArithmeticError<E> {
    Traversal(TraversalError),
    Type(ExpressionTypeError),
    Renderer(E),
}

/// The renderer supplies source AST formatting without requiring Display on Exp.
pub struct SimpleArithmeticSolver<R> {
    pub render: R,
}
impl<R, E> ArithmeticAdapter for SimpleArithmeticSolver<R>
where
    R: Fn(&Node) -> Result<String, E>,
{
    type Exp = Exp;
    type Var = LocalVar;
    type Type = Type;
    type Error = ArithmeticError<E>;
    fn render_exp(&self, e: &Exp) -> Result<String, Self::Error> {
        (self.render)(&Node::Exp(e.clone())).map_err(ArithmeticError::Renderer)
    }
    fn render_var(&self, v: &LocalVar) -> Result<String, Self::Error> {
        (self.render)(&Node::LocalVar(v.clone())).map_err(ArithmeticError::Renderer)
    }
    fn render_type(&self, t: &Type) -> Result<String, Self::Error> {
        (self.render)(&Node::Type(t.clone())).map_err(ArithmeticError::Renderer)
    }
    fn var_exp(&self, v: &LocalVar) -> Exp {
        Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone())
    }
    fn typ(&self, e: &Exp) -> Result<Type, Self::Error> {
        e.typ().map_err(ArithmeticError::Type)
    }
    fn is_int(&self, t: &Type) -> bool {
        *t == Type::Int
    }
    fn occurrences(&self, node: &Exp, target: &Exp) -> Result<usize, Self::Error> {
        fn count<E>(node: &Node, target: &Node) -> Result<usize, ArithmeticError<E>> {
            let mut n = usize::from(node == target);
            for child in subnodes(node).map_err(ArithmeticError::Traversal)? {
                // Expressions.subExps recurses through direct expression children only.
                let child = match child {
                    Node::Exp(e) => Some(Node::Exp(e)),
                    Node::LocalVar(v) => Some(Node::LocalVar(v)),
                    Node::FieldAccess(v) => Some(Node::FieldAccess(v)),
                    Node::PredicateAccess(v) => Some(Node::PredicateAccess(v)),
                    Node::PredicateAccessPredicate(v) => Some(Node::PredicateAccessPredicate(v)),
                    _ => None,
                };
                if let Some(child) = child {
                    n += count(&child, target)?;
                }
            }
            Ok(n)
        }
        count(&Node::Exp(node.clone()), &Node::Exp(target.clone()))
    }
    fn contains(&self, node: &Exp, target: &Exp) -> Result<bool, Self::Error> {
        fn search<E>(n: &Node, target: &Node) -> Result<bool, ArithmeticError<E>> {
            if n == target {
                return Ok(true);
            }
            for c in subnodes(n).map_err(ArithmeticError::Traversal)? {
                if search(&c, target)? {
                    return Ok(true);
                }
            }
            Ok(false)
        }
        search(&Node::Exp(node.clone()), &Node::Exp(target.clone()))
    }
    fn plus(&self, a: Exp, b: Exp) -> Exp {
        Exp::new(ExpKind::Add(a, b), Metadata::default())
    }
    fn minus(&self, a: Exp, b: Exp) -> Exp {
        Exp::new(ExpKind::Sub(a, b), Metadata::default())
    }
    fn as_plus(&self, e: &Exp) -> Option<(Exp, Exp)> {
        if let ExpKind::Add(a, b) = e.kind() {
            Some((a.clone(), b.clone()))
        } else {
            None
        }
    }
    fn as_minus(&self, e: &Exp) -> Option<(Exp, Exp)> {
        if let ExpKind::Sub(a, b) = e.kind() {
            Some((a.clone(), b.clone()))
        } else {
            None
        }
    }
}

/// Silver instantiation of the generic axiom-trigger arithmetic rewriter.
#[derive(Debug)]
pub enum AxiomRewriteError<E> {
    Traversal(TraversalError),
    Arithmetic(ArithmeticError<E>),
    Replacement(super::rewriter::strategy::ExpressionReplacementError),
    InvalidQuantifier,
    ExtensionForbiddenClassification,
}
/// Quantifier validated once, before the infallible adapter accessors are used.
#[derive(Clone, Debug)]
pub struct SilverQuantifier(Exp);
impl SilverQuantifier {
    pub fn new(exp: Exp) -> Result<Self, Exp> {
        if matches!(
            exp.kind(),
            ExpKind::Forall(..) | ExpKind::Exists(..) | ExpKind::ForPerm(..)
        ) {
            Ok(Self(exp))
        } else {
            Err(exp)
        }
    }
    pub fn expression(&self) -> &Exp {
        &self.0
    }
    pub fn into_expression(self) -> Exp {
        self.0
    }
}
pub struct AxiomRewriter<R> {
    pub render: R,
}
static NEXT_REWRITE_ID: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(0);
impl<R, E> super::generic_axiom_rewriter::AxiomAdapter for AxiomRewriter<R>
where
    R: Fn(&Node) -> Result<String, E>,
{
    type Exp = Exp;
    type Var = LocalVar;
    type Quantifier = SilverQuantifier;
    type Trigger = crate::ast::expression::Trigger;
    type Error = AxiomRewriteError<E>;
    fn invalid_terms(&self, expression: &Exp) -> Result<Vec<Exp>, Self::Error> {
        fn visit<E>(e: &Exp, out: &mut Vec<Exp>) -> Result<(), AxiomRewriteError<E>> {
            if matches!(e.kind(), ExpKind::Extension(_)) {
                return Err(AxiomRewriteError::ExtensionForbiddenClassification);
            }
            if super::consistency::is_forbidden_in_trigger(e) {
                out.push(e.clone());
                return Ok(());
            }
            for n in subnodes(&Node::Exp(e.clone())).map_err(AxiomRewriteError::Traversal)? {
                let child = match n {
                    Node::Exp(e) => Some(e),
                    Node::LocalVar(v) => {
                        Some(Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone()))
                    }
                    Node::FieldAccess(v) => {
                        Some(Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone()))
                    }
                    Node::PredicateAccess(v) => Some(Exp::new(
                        ExpKind::PredicateAccess(v.clone()),
                        v.meta.clone(),
                    )),
                    Node::PredicateAccessPredicate(v) => Some(Exp::new(
                        ExpKind::PredicateAccessPredicate(v.clone()),
                        v.meta.clone(),
                    )),
                    _ => None,
                };
                if let Some(child) = child {
                    visit(&child, out)?;
                }
            }
            Ok(())
        }
        let mut result = Vec::new();
        visit(expression, &mut result)?;
        Ok(result)
    }
    fn variables(&self, q: &SilverQuantifier) -> Vec<LocalVar> {
        match q.0.kind() {
            ExpKind::Forall(vars, ..) | ExpKind::Exists(vars, ..) | ExpKind::ForPerm(vars, ..) => {
                vars.iter().map(|v| v.local_var()).collect()
            }
            _ => unreachable!("validated quantifier"),
        }
    }
    fn body(&self, q: &SilverQuantifier) -> Exp {
        match q.0.kind() {
            ExpKind::Forall(_, _, body)
            | ExpKind::Exists(_, _, body)
            | ExpKind::ForPerm(_, _, body) => body.clone(),
            _ => unreachable!("validated quantifier"),
        }
    }
    fn var_exp(&self, v: &LocalVar) -> Exp {
        Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone())
    }
    fn contains(&self, expression: &Exp, value: &Exp) -> Result<bool, Self::Error> {
        SimpleArithmeticSolver {
            render: &self.render,
        }
        .contains(expression, value)
        .map_err(AxiomRewriteError::Arithmetic)
    }
    fn replace(
        &self,
        expression: &Exp,
        original: &Exp,
        replacement: &Exp,
    ) -> Result<Exp, Self::Error> {
        super::rewriter::strategy::replace_expressions(
            expression,
            &[(original.clone(), replacement.clone())],
        )
        .map_err(AxiomRewriteError::Replacement)
    }
    fn fresh_for(&mut self, var: &LocalVar, term: &Exp) -> Result<LocalVar, Self::Error> {
        let typ = term
            .typ()
            .map_err(|e| AxiomRewriteError::Arithmetic(ArithmeticError::Type(e)))?;
        let id = NEXT_REWRITE_ID
            .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
            .wrapping_add(1);
        Ok(LocalVar::new(
            format!("__rw_{}{id}", var.name),
            typ,
            Metadata::default(),
        ))
    }
    fn solve(
        &self,
        lhs: &LocalVar,
        rhs: &Exp,
        variable: &LocalVar,
    ) -> Result<Option<Exp>, Self::Error> {
        use super::generic_arithmetic_solver::{SolverResult, solve};
        let solver = SimpleArithmeticSolver {
            render: &self.render,
        };
        Ok(
            match solve(&solver, lhs.clone(), rhs.clone(), variable.clone())
                .map_err(AxiomRewriteError::Arithmetic)?
            {
                SolverResult::SolvingSuccess { rhs, .. } => Some(rhs),
                _ => None,
            },
        )
    }
    fn equal(&self, a: Exp, b: Exp) -> Exp {
        Exp::new(ExpKind::EqCmp(a, b), Metadata::default())
    }
    fn and(&self, terms: Vec<Exp>) -> Exp {
        terms
            .into_iter()
            .fold(Exp::new(ExpKind::TrueLit, Metadata::default()), |a, b| {
                Exp::new(ExpKind::And(a, b), Metadata::default())
            })
    }
    fn implies(&self, a: Exp, b: Exp) -> Exp {
        Exp::new(ExpKind::Implies(a, b), Metadata::default())
    }
    fn trigger(&self, exps: Vec<Exp>) -> Self::Trigger {
        crate::ast::expression::Trigger::new(exps, Metadata::default())
    }
    fn copy_quantifier(
        &self,
        q: &SilverQuantifier,
        vars: Vec<LocalVar>,
        body: Exp,
        triggers: Vec<Self::Trigger>,
    ) -> Result<SilverQuantifier, Self::Error> {
        let declarations = vars
            .into_iter()
            .map(|v| {
                crate::ast::program::LocalVarDecl::new(
                    v.name.clone(),
                    v.typ.clone(),
                    v.meta.clone(),
                )
            })
            .collect();
        let kind = match q.0.kind() {
            ExpKind::Forall(..) => ExpKind::Forall(declarations, triggers, body),
            ExpKind::Exists(..) => ExpKind::Exists(declarations, triggers, body),
            _ => return Err(AxiomRewriteError::InvalidQuantifier),
        };
        Ok(SilverQuantifier(Exp::with_extra(
            kind,
            q.0.metadata().clone(),
            q.0.0.extra.clone(),
        )))
    }
}

#[cfg(test)]
mod axiom_rewriter_tests {
    use super::*;
    use crate::ast::utility::{generic_axiom_rewriter, generic_trigger_generator::TriggerSet};
    use crate::ast::{expression::ExpExtra, program::LocalVarDecl};
    #[test]
    fn rewrites_arithmetic_trigger_and_quantifier() {
        let m = Metadata::default();
        let decl = LocalVarDecl::new("x".into(), Type::Int, m.clone());
        let x = Exp::new(ExpKind::LocalVar(decl.local_var()), m.clone());
        let sum = Exp::new(
            ExpKind::Add(x, Exp::new(ExpKind::IntLit(1.into()), m.clone())),
            m.clone(),
        );
        let app = Exp::with_extra(
            ExpKind::FuncApp("f".into(), vec![sum]),
            m.clone(),
            ExpExtra {
                typ: Some(Type::Int),
                ..ExpExtra::default()
            },
        );
        let quantifier = SilverQuantifier::new(Exp::new(
            ExpKind::Forall(vec![decl], vec![], Exp::new(ExpKind::TrueLit, m.clone())),
            m,
        ))
        .unwrap();
        let mut adapter = AxiomRewriter {
            render: |_: &Node| -> Result<String, ()> { Ok("expression".into()) },
        };
        let result = generic_axiom_rewriter::rewrite(
            &mut adapter,
            &quantifier,
            &[TriggerSet { exps: vec![app] }],
        )
        .unwrap()
        .unwrap()
        .into_expression();
        assert!(
            matches!(result.kind(), ExpKind::Forall(vars, triggers, _) if vars[0].name.starts_with("__rw_x") && triggers.len() == 1)
        );
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TriggerGenerationError {
    Traversal(TraversalError),
    Type(ExpressionTypeError),
    Replacement(super::rewriter::strategy::ExpressionReplacementError),
    UnsupportedExtension,
    InvalidArguments,
}
/// One independent source TriggerGeneration instance, including its fresh counter.
pub struct TriggerGeneration {
    next_id: std::sync::atomic::AtomicI32,
    pub allow_add_and_subtract: bool,
}
impl TriggerGeneration {
    pub fn new(allow_add_and_subtract: bool) -> Self {
        Self {
            next_id: std::sync::atomic::AtomicI32::new(0),
            allow_add_and_subtract,
        }
    }
    fn forbidden(&self, e: &Exp) -> bool {
        if self.allow_add_and_subtract && matches!(e.kind(), ExpKind::Add(..) | ExpKind::Sub(..)) {
            false
        } else {
            super::consistency::is_forbidden_in_trigger(e)
        }
    }
}
impl Default for TriggerGeneration {
    fn default() -> Self {
        Self::new(false)
    }
}
fn trigger_possible(e: &Exp) -> Result<bool, TraversalError> {
    use ExpKind::*;
    Ok(match e.kind() {
        FuncApp(..)
        | DomainFuncApp(..)
        | EmptySeq(..)
        | ExplicitSeq(..)
        | RangeSeq(..)
        | SeqAppend(..)
        | SeqIndex(..)
        | SeqTake(..)
        | SeqDrop(..)
        | SeqContains(..)
        | SeqUpdate(..)
        | SeqLength(..)
        | EmptySet(..)
        | ExplicitSet(..)
        | EmptyMultiset(..)
        | ExplicitMultiset(..)
        | AnySetUnion(..)
        | AnySetIntersection(..)
        | AnySetSubset(..)
        | AnySetMinus(..)
        | AnySetContains(..)
        | AnySetCardinality(..)
        | EmptyMap(..)
        | ExplicitMap(..)
        | Maplet(..)
        | MapUpdate(..)
        | MapLookup(..)
        | MapContains(..)
        | MapCardinality(..)
        | MapDomain(..)
        | MapRange(..) => true,
        Extension(ext) => ext.0.is_valid_trigger()?,
        Old(inner) | LabelledOld(inner, _) => {
            !matches!(
                inner.kind(),
                Extension(_) | FieldAccess(_) | PredicateAccess(_) | Old(_) | LabelledOld(_, _)
            ) && trigger_possible(inner)?
        }
        _ => false,
    })
}
fn trigger_contains(
    root: &Node,
    target: &Node,
    strict: bool,
) -> Result<bool, TriggerGenerationError> {
    fn go(
        n: &Node,
        root: &Node,
        target: &Node,
        strict: bool,
    ) -> Result<bool, TriggerGenerationError> {
        if n == target && (!strict || n != root) {
            return Ok(true);
        }
        for child in subnodes(n).map_err(TriggerGenerationError::Traversal)? {
            if go(&child, root, target, strict)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    go(root, root, target, strict)
}
impl super::generic_trigger_generator::TriggerAdapter for TriggerGeneration {
    type Node = Node;
    type Exp = Exp;
    type Var = LocalVar;
    type Error = TriggerGenerationError;
    fn root(&self, e: &Exp) -> Node {
        Node::Exp(e.clone())
    }
    fn children(&self, n: &Node) -> Result<Vec<Node>, Self::Error> {
        subnodes(n).map_err(TriggerGenerationError::Traversal)
    }
    fn expression(&self, n: &Node) -> Option<Exp> {
        match n {
            Node::Exp(e) => Some(e.clone()),
            Node::LocalVar(v) => Some(Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone())),
            Node::FieldAccess(v) => Some(Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone())),
            Node::PredicateAccess(v) => Some(Exp::new(
                ExpKind::PredicateAccess(v.clone()),
                v.meta.clone(),
            )),
            Node::PredicateAccessPredicate(v) => Some(Exp::new(
                ExpKind::PredicateAccessPredicate(v.clone()),
                v.meta.clone(),
            )),
            _ => None,
        }
    }
    fn quantified_vars(&self, n: &Node) -> Option<Vec<LocalVar>> {
        match n {
            Node::Exp(e) => match e.kind() {
                ExpKind::Forall(vars, ..)
                | ExpKind::Exists(vars, ..)
                | ExpKind::ForPerm(vars, ..) => Some(vars.iter().map(|v| v.local_var()).collect()),
                _ => None,
            },
            _ => None,
        }
    }
    fn possible_trigger(&self, e: &Exp) -> Result<bool, Self::Error> {
        trigger_possible(e).map_err(TriggerGenerationError::Traversal)
    }
    fn arguments(&self, e: &Exp) -> Result<Vec<Exp>, Self::Error> {
        match e.kind() {
            ExpKind::Old(inner) | ExpKind::LabelledOld(inner, _) => self.arguments(inner),
            ExpKind::Extension(_) => Err(TriggerGenerationError::UnsupportedExtension),
            _ => super::expressions::sub_expressions(e).map_err(TriggerGenerationError::Traversal),
        }
    }
    fn with_arguments(&self, e: &Exp, args: Vec<Exp>) -> Result<Exp, Self::Error> {
        match e.kind() {
            ExpKind::Old(inner) => {
                return Ok(Exp::new(
                    ExpKind::Old(self.with_arguments(inner, args)?),
                    e.metadata().clone(),
                ));
            }
            ExpKind::LabelledOld(inner, label) => {
                return Ok(Exp::new(
                    ExpKind::LabelledOld(self.with_arguments(inner, args)?, label.clone()),
                    e.metadata().clone(),
                ));
            }
            ExpKind::Extension(_) => return Err(TriggerGenerationError::UnsupportedExtension),
            ExpKind::EmptySeq(_)
            | ExpKind::EmptySet(_)
            | ExpKind::EmptyMultiset(_)
            | ExpKind::EmptyMap(..) => {
                return if args.is_empty() {
                    Ok(e.clone())
                } else {
                    Err(TriggerGenerationError::InvalidArguments)
                };
            }
            _ => {}
        }
        let mut next = args.into_iter();
        let rebuilt = e.map_expression_children(
            &mut |_| next.next().ok_or(TriggerGenerationError::InvalidArguments),
            &mut |_| Err(TriggerGenerationError::UnsupportedExtension),
            &mut |_| Err(TriggerGenerationError::InvalidArguments),
            &mut |_| Err(TriggerGenerationError::InvalidArguments),
            &mut |_| Err(TriggerGenerationError::InvalidArguments),
        )?;
        if next.next().is_some() {
            return Err(TriggerGenerationError::InvalidArguments);
        }
        Ok(Exp::with_extra(
            rebuilt.kind().clone(),
            e.metadata().clone(),
            e.0.extra.clone(),
        ))
    }
    fn variables_in(&self, e: &Exp) -> Result<Vec<LocalVar>, Self::Error> {
        super::expressions::contained_variables_excluding_let(&Node::Exp(e.clone()))
            .map_err(TriggerGenerationError::Traversal)
    }
    fn rewrite_forbidden(&mut self, e: &Exp) -> Result<(Exp, Vec<LocalVar>), Self::Error> {
        fn go(
            this: &TriggerGeneration,
            e: &Exp,
            fresh: &std::cell::RefCell<Vec<LocalVar>>,
        ) -> Result<Exp, TriggerGenerationError> {
            if this.forbidden(e) {
                let id = this
                    .next_id
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                let typ = e.typ().map_err(TriggerGenerationError::Type)?;
                let var = LocalVar::new(format!("fresh__{id}"), typ, Metadata::default());
                fresh.borrow_mut().push(var.clone());
                return Ok(Exp::new(ExpKind::LocalVar(var), Metadata::default()));
            }
            e.map_expression_children(
                &mut |x| go(this, x, fresh),
                &mut |_| Err(TriggerGenerationError::UnsupportedExtension),
                &mut |field| {
                    let receiver = go(this, &field.receiver, fresh)?;
                    Ok(if receiver == field.receiver {
                        field.clone()
                    } else {
                        crate::ast::expression::FieldAccess::new(
                            receiver,
                            field.field.clone(),
                            field.meta.clone(),
                        )
                    })
                },
                &mut |pred| {
                    let args = pred
                        .args
                        .iter()
                        .map(|x| go(this, x, fresh))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(if args == pred.args {
                        pred.clone()
                    } else {
                        crate::ast::expression::PredicateAccess::new(
                            args,
                            pred.predicate_name.clone(),
                            pred.meta.clone(),
                        )
                    })
                },
                &mut |trigger| {
                    let exps = trigger
                        .exps
                        .iter()
                        .map(|x| go(this, x, fresh))
                        .collect::<Result<Vec<_>, _>>()?;
                    Ok(if exps == trigger.exps {
                        trigger.clone()
                    } else {
                        crate::ast::expression::Trigger::new(exps, trigger.meta.clone())
                    })
                },
            )
        }
        let fresh = std::cell::RefCell::new(Vec::new());
        let result = go(self, e, &fresh)?;
        Ok((result, fresh.into_inner()))
    }
    fn additional_relevant(
        &self,
        node: &Node,
        relevant: &[LocalVar],
        avoid: &[LocalVar],
    ) -> Result<Vec<LocalVar>, Self::Error> {
        if let Node::Exp(e) = node {
            if let ExpKind::Let(var, value, body) = e.kind() {
                let local = var.local_var();
                let local_node = Node::LocalVar(local.clone());
                if trigger_contains(&Node::Exp(body.clone()), &local_node, false)? {
                    let mut has_relevant = false;
                    for v in relevant {
                        if trigger_contains(
                            &Node::Exp(value.clone()),
                            &Node::LocalVar(v.clone()),
                            false,
                        )? {
                            has_relevant = true;
                            break;
                        }
                    }
                    let mut has_avoid = false;
                    for v in avoid {
                        if trigger_contains(
                            &Node::Exp(value.clone()),
                            &Node::LocalVar(v.clone()),
                            false,
                        )? {
                            has_avoid = true;
                            break;
                        }
                    }
                    if has_relevant && !has_avoid {
                        return Ok(vec![local]);
                    }
                }
            }
        }
        Ok(vec![])
    }
    fn modify(
        &self,
        node: &Node,
        relevant: &[LocalVar],
        children: &[Vec<super::generic_trigger_generator::Candidate<Exp, LocalVar>>],
    ) -> Result<Option<Vec<super::generic_trigger_generator::Candidate<Exp, LocalVar>>>, Self::Error>
    {
        use super::generic_trigger_generator::Candidate;
        let Node::Exp(e) = node else { return Ok(None) };
        let mut out = Vec::new();
        match e.kind() {
            ExpKind::Old(_) | ExpKind::LabelledOld(_, _) => {
                for child in children.iter().flatten() {
                    let exp = match e.kind() {
                        ExpKind::Old(_) => Exp::new(
                            ExpKind::Old(child.exp.clone()),
                            child.exp.metadata().clone(),
                        ),
                        ExpKind::LabelledOld(_, label) => Exp::new(
                            ExpKind::LabelledOld(child.exp.clone(), label.clone()),
                            child.exp.metadata().clone(),
                        ),
                        _ => unreachable!(),
                    };
                    out.push(Candidate {
                        exp,
                        covered: child.covered.clone(),
                        extra: child.extra.clone(),
                    });
                }
            }
            ExpKind::Let(var, value, body) => {
                let local = var.local_var();
                let used = trigger_contains(
                    &Node::Exp(body.clone()),
                    &Node::LocalVar(local.clone()),
                    false,
                )?;
                for child in children.iter().flatten() {
                    if used && self.forbidden(value) {
                        continue;
                    }
                    let mut covered: Vec<_> = child
                        .covered
                        .iter()
                        .filter(|v| *v != &local)
                        .cloned()
                        .collect();
                    if used {
                        for v in relevant {
                            if trigger_contains(
                                &Node::Exp(value.clone()),
                                &Node::LocalVar(v.clone()),
                                false,
                            )? {
                                covered.push(v.clone());
                            }
                        }
                    }
                    let source = Exp::new(ExpKind::LocalVar(local.clone()), local.meta.clone());
                    let exp = super::rewriter::strategy::replace_expressions(
                        &child.exp,
                        &[(source, value.clone())],
                    )
                    .map_err(TriggerGenerationError::Replacement)?;
                    out.push(Candidate {
                        exp,
                        covered,
                        extra: child.extra.clone(),
                    });
                }
            }
            _ => return Ok(None),
        }
        Ok(Some(out))
    }
    fn has_subnode(&self, parent: &Exp, child: &Exp) -> Result<bool, Self::Error> {
        trigger_contains(&Node::Exp(parent.clone()), &Node::Exp(child.clone()), true)
    }
}

#[cfg(test)]
mod trigger_generation_tests {
    use super::*;
    use crate::ast::utility::generic_trigger_generator::generate_trigger_set_groups;
    use crate::ast::{expression::ExpExtra, program::LocalVarDecl};
    #[test]
    fn discovers_function_trigger_for_quantified_variable() {
        let m = Metadata::default();
        let decl = LocalVarDecl::new("x".into(), Type::Int, m.clone());
        let x = decl.local_var();
        let arg = Exp::new(ExpKind::LocalVar(x.clone()), m.clone());
        let app = Exp::with_extra(
            ExpKind::FuncApp("f".into(), vec![arg]),
            m,
            ExpExtra {
                typ: Some(Type::Int),
                ..ExpExtra::default()
            },
        );
        let mut generator = TriggerGeneration::default();
        let groups = generate_trigger_set_groups(&mut generator, &[x], &app).unwrap();
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].0.len(), 1);
        assert_eq!(groups[0].0[0].exps, vec![app]);
        assert!(groups[0].1.is_empty());
    }
}

/// Generate source trigger groups, using the supplied generator's persistent fresh counter.
pub fn generate_trigger_set(
    quantifier: &SilverQuantifier,
    generator: &mut TriggerGeneration,
) -> Result<
    Option<(
        Vec<crate::ast::program::LocalVarDecl>,
        Vec<super::generic_trigger_generator::TriggerSet<Exp>>,
    )>,
    TriggerGenerationError,
> {
    use super::generic_trigger_generator::generate_trigger_set_groups;
    let q = quantifier.expression();
    let (vars, body) = match q.kind() {
        ExpKind::Forall(vars, _, body)
        | ExpKind::Exists(vars, _, body)
        | ExpKind::ForPerm(vars, _, body) => (vars, body),
        _ => unreachable!("validated quantifier"),
    };
    let locals: Vec<_> = vars.iter().map(|v| v.local_var()).collect();
    let groups = generate_trigger_set_groups(generator, &locals, body)?;
    if let Some((triggers, _)) = groups.iter().find(|(_, extra)| extra.is_empty()) {
        return Ok(Some((vars.clone(), triggers.clone())));
    }
    if q.is_pure() {
        if let Some((triggers, extra)) = groups.into_iter().next() {
            let mut all = vars.clone();
            all.extend(extra.into_iter().map(|v| {
                crate::ast::program::LocalVarDecl::new(
                    v.name.clone(),
                    v.typ.clone(),
                    Metadata::default(),
                )
            }));
            return Ok(Some((all, triggers)));
        }
    }
    Ok(None)
}

/// Forall and Exists per-instance source autoTrigger lazy value. Failed generation is not cached.
pub fn auto_trigger(forall: &Exp) -> Result<Exp, TriggerGenerationError> {
    use crate::ast::{ast::Info, expression::SimplifiedExp};
    static DEFAULT: std::sync::OnceLock<std::sync::Mutex<TriggerGeneration>> =
        std::sync::OnceLock::new();
    let (triggers, body, is_exists) = match forall.kind() {
        ExpKind::Forall(_, triggers, body) => (triggers, body, false),
        ExpKind::Exists(_, triggers, body) => (triggers, body, true),
        _ => return Err(TriggerGenerationError::InvalidArguments),
    };
    let mut cached = forall
        .0
        .auto_triggered
        .lock()
        .expect("auto trigger cache poisoned");
    if let Some(existing) = &*cached {
        return Ok(match existing {
            SimplifiedExp::Same => forall.clone(),
            SimplifiedExp::Other(e) => e.clone(),
        });
    }
    let result = if triggers.is_empty() {
        let q = SilverQuantifier::new(forall.clone())
            .map_err(|_| TriggerGenerationError::InvalidArguments)?;
        let mut generator = DEFAULT
            .get_or_init(|| std::sync::Mutex::new(TriggerGeneration::default()))
            .lock()
            .expect("trigger generator poisoned");
        if let Some((vars, sets)) = generate_trigger_set(&q, &mut generator)? {
            let triggers = sets
                .into_iter()
                .map(|s| crate::ast::expression::Trigger::new(s.exps, Metadata::default()))
                .collect();
            Exp::new(
                if is_exists {
                    ExpKind::Exists(vars, triggers, body.clone())
                } else {
                    ExpKind::Forall(vars, triggers, body.clone())
                },
                Metadata {
                    position: forall.metadata().position.clone(),
                    info: Info::pair(Info::AutoTriggered, forall.metadata().info.clone()),
                    ..Metadata::default()
                },
            )
        } else {
            forall.clone()
        }
    } else {
        forall.clone()
    };
    *cached = Some(if result.same_node(forall) {
        SimplifiedExp::Same
    } else {
        SimplifiedExp::Other(result.clone())
    });
    Ok(result)
}

#[cfg(test)]
mod auto_trigger_tests {
    use super::*;
    use crate::ast::{expression::ExpExtra, program::LocalVarDecl};
    #[test]
    fn generated_forall_is_cached_by_source_identity() {
        let m = Metadata::default();
        let decl = LocalVarDecl::new("x".into(), Type::Int, m.clone());
        let var = Exp::new(ExpKind::LocalVar(decl.local_var()), m.clone());
        let app = Exp::with_extra(
            ExpKind::FuncApp("f".into(), vec![var]),
            m.clone(),
            ExpExtra {
                typ: Some(Type::Bool),
                ..ExpExtra::default()
            },
        );
        let q = Exp::new(ExpKind::Forall(vec![decl], vec![], app), m);
        let first = auto_trigger(&q).unwrap();
        let second = auto_trigger(&q).unwrap();
        assert!(first.same_node(&second));
        assert!(matches!(first.kind(), ExpKind::Forall(_, triggers, _) if triggers.len() == 1));
        assert!(!q.same_node(&first));
    }
    #[test]
    fn generated_exists_is_cached_and_preserves_quantifier_kind() {
        let m = Metadata::default();
        let decl = LocalVarDecl::new("x".into(), Type::Int, m.clone());
        let arg = Exp::new(ExpKind::LocalVar(decl.local_var()), m.clone());
        let app = Exp::with_extra(
            ExpKind::FuncApp("f".into(), vec![arg]),
            m.clone(),
            ExpExtra {
                typ: Some(Type::Bool),
                ..ExpExtra::default()
            },
        );
        let q = Exp::new(ExpKind::Exists(vec![decl], vec![], app), m);
        let first = auto_trigger(&q).unwrap();
        assert!(first.same_node(&auto_trigger(&q).unwrap()));
        assert!(matches!(first.kind(), ExpKind::Exists(_, triggers, _) if triggers.len() == 1));
        assert!(!q.same_node(&first));
    }
}
