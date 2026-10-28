//! Silver trigger-generation adapters and integer isolation.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Triggers.scala
//! Status: partial; SimpleArithmeticSolver is implemented. Trigger generation, axiom rewriting,
//! extension trigger classification and let-sensitive substitution remain pending.

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
