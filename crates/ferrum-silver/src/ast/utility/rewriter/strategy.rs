//! Generic context-aware tree rewrite strategies.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/Strategy.scala
//! Status: partial. Product traversal, top-down/bottom-up/innermost strategies,
//! contexts, identity-based no-recursion, child selection and repetition are
//! implemented; regex strategies, rule composition and concrete adapters remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::rewritable::{ProductValue, Rewritable, with_children};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Traverse {
    TopDown,
    BottomUp,
    Innermost,
    Outermost,
}
#[derive(Clone, Debug)]
pub struct Context<N, C> {
    pub ancestors: Vec<N>,
    pub custom: C,
    no_recursion: Vec<N>,
}
impl<N, C> Context<N, C> {
    /// Mark a node to be excluded from recursion for the lifetime of the strategy.
    pub fn no_rec(&mut self, node: N) {
        self.no_recursion.push(node);
    }
    pub fn node(&self) -> Option<&N> {
        self.ancestors.last()
    }
    pub fn parent(&self) -> Option<&N> {
        self.ancestors.iter().rev().nth(1)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StrategyError<E> {
    Adapter(E),
    OutermostUnsupported,
    IterationLimit,
}
impl<E> From<E> for StrategyError<E> {
    fn from(e: E) -> Self {
        Self::Adapter(e)
    }
}

/// A strategy owns its no-recursion list, as in the source. Node identity, not
/// structural equality, controls no-recursion and the changed flag.
pub struct Strategy<R: Rewritable, C, F> {
    pub adapter: R,
    pub mode: Traverse,
    pub force_copy: bool,
    pub rule: F,
    no_recursion: Vec<R::Node>,
    pub changed: bool,
    pub select:
        Option<Box<dyn Fn(&R::Node, &ProductValue<R::Node, R::Atom>) -> bool + Send + Sync>>,
    _context: std::marker::PhantomData<C>,
}
impl<R: Rewritable, C: Clone, F> Strategy<R, C, F>
where
    F: FnMut(&R::Node, &mut Context<R::Node, C>) -> Result<Option<(R::Node, C)>, R::Error>,
{
    pub fn new(adapter: R, mode: Traverse, rule: F) -> Self {
        Self {
            adapter,
            mode,
            force_copy: false,
            rule,
            no_recursion: Vec::new(),
            changed: false,
            select: None,
            _context: std::marker::PhantomData,
        }
    }
    pub fn no_rec(&mut self, node: R::Node) {
        self.no_recursion.push(node);
    }
    fn blocked(&self, node: &R::Node) -> bool {
        self.no_recursion
            .iter()
            .any(|n| self.adapter.same_node(n, node))
    }
    pub fn execute(
        &mut self,
        node: &R::Node,
        context: C,
    ) -> Result<R::Node, StrategyError<R::Error>> {
        if self.mode == Traverse::Outermost {
            return Err(StrategyError::OutermostUnsupported);
        }
        self.changed = false;
        let result = self.rewrite_node(
            node,
            &Context {
                ancestors: Vec::new(),
                custom: context,
                no_recursion: Vec::new(),
            },
        )?;
        self.changed = !self.adapter.same_node(&result, node);
        self.adapter.init_properties(&result)?;
        Ok(result)
    }
    pub fn repeat(
        &mut self,
        node: &R::Node,
        context: C,
    ) -> Result<R::Node, StrategyError<R::Error>> {
        let mut current = self.execute(node, context.clone())?;
        let mut n = 1;
        while self.changed {
            current = self.execute(&current, context.clone())?;
            n += 1;
            if n >= 10000 {
                return Err(StrategyError::IterationLimit);
            }
        }
        Ok(current)
    }
    pub fn repeat_times(
        &mut self,
        node: &R::Node,
        context: C,
        limit: usize,
    ) -> Result<R::Node, StrategyError<R::Error>> {
        if limit == 0 {
            return Ok(node.clone());
        }
        let mut current = self.execute(node, context.clone())?;
        let mut n = 1;
        while self.changed && n < limit {
            current = self.execute(&current, context.clone())?;
            n += 1;
        }
        Ok(current)
    }
    #[inline(never)]
    fn rewrite_node(
        &mut self,
        node: &R::Node,
        context: &Context<R::Node, C>,
    ) -> Result<R::Node, StrategyError<R::Error>> {
        crate::utility::stack::with_stack(|| self.rewrite_node_inner(node, context))
    }
    #[inline(never)]
    fn rewrite_node_inner(
        &mut self,
        node: &R::Node,
        context: &Context<R::Node, C>,
    ) -> Result<R::Node, StrategyError<R::Error>> {
        if self.blocked(node) {
            return Ok(node.clone());
        }
        let mut c = context.clone();
        c.ancestors.push(node.clone());
        match self.mode {
            Traverse::TopDown | Traverse::Innermost => {
                let outcome = (self.rule)(node, &mut c)?;
                self.no_recursion.append(&mut c.no_recursion);
                let (current, custom) = match outcome {
                    Some(pair) => pair,
                    None => (node.clone(), c.custom.clone()),
                };
                c.custom = custom;
                *c.ancestors.last_mut().expect("current node") = current.clone();
                if (self.mode == Traverse::Innermost && !self.adapter.same_node(node, &current))
                    || (self.mode == Traverse::TopDown && self.blocked(&current))
                {
                    return Ok(current);
                }
                self.rewrite_children(&current, &c)
            }
            Traverse::BottomUp => {
                let current = self.rewrite_children(node, &c)?;
                *c.ancestors.last_mut().expect("current node") = current.clone();
                let outcome = (self.rule)(&current, &mut c)?;
                self.no_recursion.append(&mut c.no_recursion);
                Ok(outcome.map(|(n, _)| n).unwrap_or(current))
            }
            Traverse::Outermost => Err(StrategyError::OutermostUnsupported),
        }
    }
    fn rewrite_children(
        &mut self,
        node: &R::Node,
        context: &Context<R::Node, C>,
    ) -> Result<R::Node, StrategyError<R::Error>> {
        let children = self.adapter.children(node)?;
        let mut transformed = Vec::with_capacity(children.len());
        for child in children {
            let allowed = self
                .select
                .as_ref()
                .is_none_or(|select| select(node, &child));
            transformed.push(if allowed {
                self.rewrite_value(child, context)?
            } else {
                child
            });
        }
        Ok(with_children(
            &self.adapter,
            node,
            transformed,
            self.force_copy,
        )?)
    }
    #[inline(never)]
    fn rewrite_value(
        &mut self,
        value: ProductValue<R::Node, R::Atom>,
        context: &Context<R::Node, C>,
    ) -> Result<ProductValue<R::Node, R::Atom>, StrategyError<R::Error>> {
        crate::utility::stack::with_stack(|| self.rewrite_value_inner(value, context))
    }
    #[inline(never)]
    fn rewrite_value_inner(
        &mut self,
        value: ProductValue<R::Node, R::Atom>,
        context: &Context<R::Node, C>,
    ) -> Result<ProductValue<R::Node, R::Atom>, StrategyError<R::Error>> {
        use ProductValue::*;
        Ok(match value {
            Node(n) => Node(self.rewrite_node(&n, context)?),
            Sequence(xs) => Sequence(
                xs.into_iter()
                    .map(|x| self.rewrite_value(x, context))
                    .collect::<Result<_, _>>()?,
            ),
            Optional(x) => Optional(
                x.map(|x| self.rewrite_value(*x, context).map(Box::new))
                    .transpose()?,
            ),
            Left(x) => Left(Box::new(self.rewrite_value(*x, context)?)),
            Right(x) => Right(Box::new(self.rewrite_value(*x, context)?)),
            Tuple(xs) => Tuple(
                xs.into_iter()
                    .map(|x| self.rewrite_value(x, context))
                    .collect::<Result<_, _>>()?,
            ),
            Map(xs) => {
                let mut mapped: Vec<(
                    ProductValue<R::Node, R::Atom>,
                    ProductValue<R::Node, R::Atom>,
                )> = Vec::new();
                for (key, value) in xs {
                    let key = self.rewrite_value(key, context)?;
                    let value = self.rewrite_value(value, context)?;
                    if let Some(existing) = mapped.iter_mut().find(|(k, _)| k == &key) {
                        *existing = (key, value);
                    } else {
                        mapped.push((key, value));
                    }
                }
                Map(mapped)
            }
            Atom(x) => Atom(x),
        })
    }
}

#[cfg(test)]
mod review_tests {
    use super::*;
    use std::sync::{Arc, Mutex};
    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Node {
        value: u8,
        child: Option<Arc<Node>>,
    }
    struct Adapter;
    impl Rewritable for Adapter {
        type Node = Arc<Node>;
        type Atom = ();
        type Error = ();
        fn children(
            &self,
            n: &Self::Node,
        ) -> Result<Vec<ProductValue<Self::Node, Self::Atom>>, ()> {
            Ok(vec![ProductValue::Optional(
                n.child.clone().map(|c| Box::new(ProductValue::Node(c))),
            )])
        }
        fn rebuild(
            &self,
            n: &Self::Node,
            c: Vec<ProductValue<Self::Node, Self::Atom>>,
        ) -> Result<Self::Node, ()> {
            let ProductValue::Optional(child) = c.into_iter().next().unwrap() else {
                panic!()
            };
            let child = child.map(|c| match *c {
                ProductValue::Node(n) => n,
                _ => panic!(),
            });
            Ok(Arc::new(Node {
                value: n.value,
                child,
            }))
        }
        fn same_node(&self, a: &Self::Node, b: &Self::Node) -> bool {
            Arc::ptr_eq(a, b)
        }
    }
    #[test]
    fn rewritten_top_down_node_is_parent_in_child_context() {
        let root = Arc::new(Node {
            value: 1,
            child: Some(Arc::new(Node {
                value: 2,
                child: None,
            })),
        });
        let observed = Arc::new(Mutex::new(None));
        let captured = observed.clone();
        let mut strategy = Strategy::new(
            Adapter,
            Traverse::TopDown,
            move |n: &Arc<Node>, c: &mut Context<Arc<Node>, ()>| {
                if n.value == 1 {
                    Ok(Some((
                        Arc::new(Node {
                            value: 3,
                            child: n.child.clone(),
                        }),
                        (),
                    )))
                } else {
                    *captured.lock().unwrap() = c.parent().map(|p| p.value);
                    Ok(None)
                }
            },
        );
        strategy.execute(&root, ()).unwrap();
        assert_eq!(*observed.lock().unwrap(), Some(3));
    }
    #[test]
    fn innermost_no_rec_mark_on_unchanged_node_does_not_stop_its_children() {
        let root = Arc::new(Node {
            value: 1,
            child: Some(Arc::new(Node {
                value: 2,
                child: None,
            })),
        });
        let visits = Arc::new(Mutex::new(Vec::new()));
        let captured = visits.clone();
        let mut strategy = Strategy::new(
            Adapter,
            Traverse::Innermost,
            move |n: &Arc<Node>, c: &mut Context<Arc<Node>, ()>| {
                captured.lock().unwrap().push(n.value);
                if n.value == 1 {
                    c.no_rec(n.clone());
                }
                Ok(None)
            },
        );
        strategy.execute(&root, ()).unwrap();
        assert_eq!(*visits.lock().unwrap(), vec![1, 2]);
    }
}

/// Failure while replacing expressions inside a more specific source AST slot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpressionReplacementError {
    Extension,
    InvalidFieldAccess,
    InvalidPredicateAccess,
}
/// Source `Exp.replace` uses structural map keys and an innermost strategy:
/// a changed node is replaced once and its replacement is not traversed; an
/// identity-preserving rule result continues into that node's children.
/// Declaration and type replacement is a separate generic Node operation.
pub fn replace_expressions(
    expression: &crate::ast::expression::Exp,
    replacements: &[(crate::ast::expression::Exp, crate::ast::expression::Exp)],
) -> Result<crate::ast::expression::Exp, ExpressionReplacementError> {
    use crate::ast::expression::{Exp, ExpKind, Trigger};
    #[inline(never)]
    fn go(e: &Exp, replacements: &[(Exp, Exp)]) -> Result<Exp, ExpressionReplacementError> {
        crate::utility::stack::with_stack(|| go_inner(e, replacements))
    }
    #[inline(never)]
    fn go_inner(e: &Exp, replacements: &[(Exp, Exp)]) -> Result<Exp, ExpressionReplacementError> {
        if let Some((_, replacement)) = replacements.iter().find(|(original, _)| original == e) {
            if !replacement.same_node(e) {
                return Ok(replacement.clone());
            }
        }
        e.map_expression_children(
            &mut |x| go(x, replacements),
            &mut |extension| {
                let failure = std::cell::RefCell::new(None);
                let mapped = extension.0.map_expressions(&|child| {
                    go(child, replacements).map_err(|error| {
                        *failure.borrow_mut() = Some(error);
                        crate::verifier::verification_result::DiagnosticError::Unsupported(
                            "extension expression replacement",
                        )
                    })
                });
                match mapped {
                    Ok(value) => Ok(value),
                    Err(_) => Err(failure
                        .into_inner()
                        .unwrap_or(ExpressionReplacementError::Extension)),
                }
            },
            &mut |field| {
                let node = Exp::new(ExpKind::FieldAccess(field.clone()), field.meta.clone());
                let result = go(&node, replacements)?;
                let ExpKind::FieldAccess(field) = result.kind() else {
                    return Err(ExpressionReplacementError::InvalidFieldAccess);
                };
                Ok(field.clone())
            },
            &mut |predicate| {
                let node = Exp::new(
                    ExpKind::PredicateAccess(predicate.clone()),
                    predicate.meta.clone(),
                );
                let result = go(&node, replacements)?;
                let ExpKind::PredicateAccess(predicate) = result.kind() else {
                    return Err(ExpressionReplacementError::InvalidPredicateAccess);
                };
                Ok(predicate.clone())
            },
            &mut |trigger: &Trigger| {
                let exps = trigger
                    .exps
                    .iter()
                    .map(|x| go(x, replacements))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(if exps == trigger.exps {
                    trigger.clone()
                } else {
                    Trigger::new(exps, trigger.meta.clone())
                })
            },
        )
    }
    if replacements.is_empty() {
        return Ok(expression.clone());
    }
    go(expression, replacements)
}

/// Failure in a bottom-up, per-occurrence expression rewrite.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpressionRewriteError<E> {
    Callback(E),
    InvalidFieldAccess,
    InvalidPredicateAccess,
}

/// Rewrite each built-in expression occurrence bottom-up. Extension reconstruction
/// is delegated to `extension`, which can rewrite its children via the supplied continuation.
/// As with upstream product reconstruction, structurally equal children reuse
/// their original parent, even if their metadata differs.
pub fn rewrite_expression_bottom_up<E>(
    expression: &crate::ast::expression::Exp,
    rule: &mut impl FnMut(&crate::ast::expression::Exp) -> Result<crate::ast::expression::Exp, E>,
    extension: &impl Fn(
        &crate::ast::expression::ExtensionExpHandle,
        &mut dyn FnMut(
            &crate::ast::expression::Exp,
        ) -> Result<crate::ast::expression::Exp, ExpressionRewriteError<E>>,
    )
        -> Result<crate::ast::expression::ExtensionExpHandle, ExpressionRewriteError<E>>,
) -> Result<crate::ast::expression::Exp, ExpressionRewriteError<E>> {
    use crate::ast::expression::{Exp, ExpKind, ExtensionExpHandle, Trigger};
    fn go<E>(
        e: &Exp,
        rule: &std::cell::RefCell<&mut impl FnMut(&Exp) -> Result<Exp, E>>,
        extension: &impl Fn(
            &ExtensionExpHandle,
            &mut dyn FnMut(&Exp) -> Result<Exp, ExpressionRewriteError<E>>,
        ) -> Result<ExtensionExpHandle, ExpressionRewriteError<E>>,
    ) -> Result<Exp, ExpressionRewriteError<E>> {
        let rebuilt = e.map_expression_children(
            &mut |x| go(x, rule, extension),
            &mut |x| extension(x, &mut |child| go(child, rule, extension)),
            &mut |field| {
                let view = Exp::new(ExpKind::FieldAccess(field.clone()), field.meta.clone());
                let result = go(&view, rule, extension)?;
                match result.kind() {
                    ExpKind::FieldAccess(v) => Ok(v.clone()),
                    _ => Err(ExpressionRewriteError::InvalidFieldAccess),
                }
            },
            &mut |predicate| {
                let view = Exp::new(
                    ExpKind::PredicateAccess(predicate.clone()),
                    predicate.meta.clone(),
                );
                let result = go(&view, rule, extension)?;
                match result.kind() {
                    ExpKind::PredicateAccess(v) => Ok(v.clone()),
                    _ => Err(ExpressionRewriteError::InvalidPredicateAccess),
                }
            },
            &mut |trigger: &Trigger| {
                let exps = trigger
                    .exps
                    .iter()
                    .map(|x| go(x, rule, extension))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(if exps == trigger.exps {
                    trigger.clone()
                } else {
                    Trigger::new(exps, trigger.meta.clone())
                })
            },
        )?;
        rule.borrow_mut()(&rebuilt).map_err(ExpressionRewriteError::Callback)
    }
    go(expression, &std::cell::RefCell::new(rule), extension)
}

#[cfg(test)]
mod expression_replacement_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        expression::{Exp, ExpKind, FieldAccess, LocalVar},
        program::Field,
        r#type::Type,
    };
    #[test]
    fn bottom_up_callback_visits_equal_occurrences_independently() {
        let m = Metadata::default();
        let left = Exp::new(ExpKind::TrueLit, m.clone());
        let right = Exp::new(ExpKind::TrueLit, m.clone());
        let root = Exp::new(ExpKind::And(left, right), m.clone());
        let mut count = 0;
        let result = rewrite_expression_bottom_up(
            &root,
            &mut |e| -> Result<Exp, ()> {
                if matches!(e.kind(), ExpKind::TrueLit) {
                    count += 1;
                    Ok(if count == 1 {
                        Exp::new(ExpKind::FalseLit, e.metadata().clone())
                    } else {
                        e.clone()
                    })
                } else {
                    Ok(e.clone())
                }
            },
            &|_, _| Err(ExpressionRewriteError::Callback(())),
        )
        .unwrap();
        assert_eq!(count, 2);
        assert!(
            matches!(result.kind(), ExpKind::And(a, b) if matches!(a.kind(), ExpKind::FalseLit) && matches!(b.kind(), ExpKind::TrueLit))
        );
    }
    #[test]
    fn replacement_is_simultaneous_and_checks_narrow_location_slot() {
        let m = Metadata::default();
        let var = |name: &str| {
            Exp::new(
                ExpKind::LocalVar(LocalVar::new(name.into(), Type::Int, m.clone())),
                m.clone(),
            )
        };
        let x = var("x");
        let y = var("y");
        let z = var("z");
        let pair = Exp::new(ExpKind::Add(x.clone(), y.clone()), m.clone());
        let result =
            replace_expressions(&pair, &[(x.clone(), y.clone()), (y.clone(), z.clone())]).unwrap();
        assert!(matches!(result.kind(),ExpKind::Add(a,b) if a == &y && b == &z));
        let identity = replace_expressions(
            &pair,
            &[(pair.clone(), pair.clone()), (x.clone(), z.clone())],
        )
        .unwrap();
        assert!(matches!(identity.kind(),ExpKind::Add(a,b) if a == &z && b == &y));
        let receiver = Exp::new(
            ExpKind::LocalVar(LocalVar::new("r".into(), Type::Ref, m.clone())),
            m.clone(),
        );
        let field = FieldAccess::new(
            receiver,
            Field::new(crate::ast::program::FieldData {
                name: "f".into(),
                typ: Type::Int,
                meta: m.clone(),
            }),
            m.clone(),
        );
        let access = Exp::new(ExpKind::FieldAccess(field.clone()), m.clone());
        let predicate = Exp::new(ExpKind::FieldAccessPredicate(field, None), m);
        assert_eq!(
            replace_expressions(&predicate, &[(access, x)]),
            Err(ExpressionReplacementError::InvalidFieldAccess)
        );
    }
}

#[cfg(test)]
mod extension_replacement_tests {
    use super::*;
    use crate::{
        ast::{
            ast::Metadata,
            expression::{Exp, ExpKind, LocalVar},
            r#type::Type,
        },
        plugin::standard::predicateinstance::predicate_instance_ast_extension::PredicateInstance,
    };
    #[test]
    fn structural_replacement_rebuilds_predicate_instance_arguments() {
        let meta = Metadata::default();
        let original = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Int, meta.clone())),
            meta.clone(),
        );
        let replacement = Exp::new(ExpKind::IntLit(7.into()), meta.clone());
        let expression = PredicateInstance {
            predicate: "p".into(),
            args: vec![original.clone()],
            meta,
        }
        .expression();
        let result = replace_expressions(&expression, &[(original, replacement.clone())]).unwrap();
        let ExpKind::Extension(extension) = result.kind() else {
            panic!("predicate instance")
        };
        let instance = extension
            .0
            .as_any()
            .downcast_ref::<PredicateInstance>()
            .unwrap();
        assert!(instance.args[0].same_node(&replacement));
    }
}

#[cfg(test)]
mod stack_depth_regression_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        expression::{Exp, ExpKind},
        position::Position,
        utility::nodes::{Node, replace_expressions},
    };
    use std::sync::Arc;

    #[derive(Clone)]
    struct TestNode(Option<Arc<TestNode>>);
    impl PartialEq for TestNode {
        fn eq(&self, other: &Self) -> bool {
            match (&self.0, &other.0) {
                (None, None) => true,
                (Some(a), Some(b)) => Arc::ptr_eq(a, b),
                _ => false,
            }
        }
    }
    struct Adapter;
    impl Rewritable for Adapter {
        type Node = Arc<TestNode>;
        type Atom = ();
        type Error = ();
        fn children(
            &self,
            n: &Self::Node,
        ) -> Result<Vec<ProductValue<Self::Node, Self::Atom>>, ()> {
            Ok(vec![ProductValue::Optional(
                n.0.clone().map(|c| Box::new(ProductValue::Node(c))),
            )])
        }
        fn rebuild(
            &self,
            n: &Self::Node,
            _: Vec<ProductValue<Self::Node, Self::Atom>>,
        ) -> Result<Self::Node, ()> {
            Ok(n.clone())
        }
        fn same_node(&self, a: &Self::Node, b: &Self::Node) -> bool {
            Arc::ptr_eq(a, b)
        }
    }
    #[test]
    fn deep_generic_strategy_uses_a_grown_same_thread_stack() {
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                let thread = std::thread::current().id();
                let mut node = Arc::new(TestNode(None));
                for _ in 0..2000 {
                    node = Arc::new(TestNode(Some(node)));
                }
                let mut visited = 0;
                let mut strategy = Strategy::new(
                    Adapter,
                    Traverse::TopDown,
                    |_: &Arc<TestNode>, _: &mut Context<Arc<TestNode>, ()>| {
                        assert_eq!(std::thread::current().id(), thread);
                        assert!(stacker::remaining_stack().is_some_and(|n| n > 2 * 1024 * 1024));
                        visited += 1;
                        Ok::<_, ()>(None)
                    },
                );
                let out = strategy.execute(&node, ()).unwrap();
                assert!(Arc::ptr_eq(&node, &out));
                drop(strategy);
                assert_eq!(visited, 2001);
                // Independently exercise the walker, not recursive Arc destruction.
                std::mem::forget(node);
                std::mem::forget(out);
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn deep_expression_replacement_preserves_identity_and_metadata() {
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                let meta = Metadata {
                    position: Position::Virtual("deep".into()),
                    ..Default::default()
                };
                let mut exp = Exp::new(ExpKind::TrueLit, meta.clone());
                for _ in 0..2000 {
                    exp = Exp::new(ExpKind::Not(exp), meta.clone());
                }
                let root = Node::Exp(exp.clone());
                let from = Exp::new(ExpKind::FalseLit, Metadata::default());
                let to = Exp::new(ExpKind::TrueLit, Metadata::default());
                let Node::Exp(out) = replace_expressions(&root, &[(from, to)]).unwrap() else {
                    panic!("expected expression")
                };
                assert!(out.same_node(&exp));
                assert_eq!(out.metadata().position, Position::Virtual("deep".into()));
                // Independently exercise the walker, not recursive Arc destruction.
                std::mem::forget(root);
                std::mem::forget(exp);
                std::mem::forget(out);
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn deep_expression_rewrite_keeps_metadata_and_changes_only_the_leaf() {
        std::thread::Builder::new()
            .stack_size(512 * 1024)
            .spawn(|| {
                let meta = Metadata {
                    position: Position::Virtual("deep".into()),
                    ..Default::default()
                };
                let from = Exp::new(ExpKind::FalseLit, meta.clone());
                let to = Exp::new(ExpKind::TrueLit, meta.clone());
                let mut exp = from.clone();
                for _ in 0..2000 {
                    exp = Exp::new(ExpKind::Not(exp), meta.clone());
                }
                let root = Node::Exp(exp.clone());
                let Node::Exp(out) =
                    replace_expressions(&root, &[(from.clone(), to.clone())]).unwrap()
                else {
                    panic!("expected expression")
                };
                assert!(!out.same_node(&exp));
                let mut cursor = &out;
                for _ in 0..2000 {
                    assert_eq!(cursor.metadata().position, Position::Virtual("deep".into()));
                    let ExpKind::Not(next) = cursor.kind() else {
                        panic!("wrong rewritten shape")
                    };
                    cursor = next;
                }
                assert!(cursor.same_node(&to));
                assert_eq!(cursor.metadata().position, Position::Virtual("deep".into()));
                // These long chains would exercise recursive Arc drop, a separate problem.
                std::mem::forget(root);
                std::mem::forget(exp);
                std::mem::forget(out);
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
