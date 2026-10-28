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
    fn rewrite_node(
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
    fn rewrite_value(
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
