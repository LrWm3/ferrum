//! Tree-regex matching and top-down rewriting.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/RegexStrategy.scala
//! Status: partial. Matching, context combination and reconstruction are generic;
//! concrete AST/parser adapters and callback-driven noRec remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::rewritable::{ProductValue, Rewritable, with_children};
use super::t_regex_automaton::{
    Automaton, AutomatonError, StateId, TRegexAutomaton, TransitionInfo,
};
use std::collections::HashSet;

#[derive(Clone, Debug)]
pub struct RegexContext<N, C> {
    pub ancestors: Vec<N>,
    pub custom: C,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RegexError<E> {
    Adapter(E),
    Automaton(AutomatonError),
    DuplicateMatch,
}
impl<E> From<AutomatonError> for RegexError<E> {
    fn from(e: AutomatonError) -> Self {
        Self::Automaton(e)
    }
}
struct Entry<N, C> {
    node: N,
    context: RegexContext<N, C>,
    index: usize,
}

pub struct RegexStrategy<R: Rewritable, C, F, U, B> {
    pub adapter: R,
    pub automaton: Automaton<R::Node, C>,
    pub pattern: TRegexAutomaton,
    pub rule: F,
    pub accumulate: U,
    pub combine: B,
    pub default: C,
    pub changed: bool,
    no_recursion: Vec<R::Node>,
    pub select:
        Option<Box<dyn Fn(&R::Node, &ProductValue<R::Node, R::Atom>) -> bool + Send + Sync>>,
}
impl<R: Rewritable, C: Clone, F, U, B> RegexStrategy<R, C, F, U, B>
where
    F: FnMut(&R::Node, &RegexContext<R::Node, C>) -> Result<Option<R::Node>, R::Error>,
    U: Fn(&C, &C) -> C,
    B: Fn(&C, &C) -> C,
{
    pub fn new(
        adapter: R,
        automaton: Automaton<R::Node, C>,
        pattern: TRegexAutomaton,
        rule: F,
        accumulate: U,
        combine: B,
        default: C,
    ) -> Self {
        Self {
            adapter,
            automaton,
            pattern,
            rule,
            accumulate,
            combine,
            default,
            changed: false,
            no_recursion: Vec::new(),
            select: None,
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
    fn children(&self, node: &R::Node) -> Result<Vec<R::Node>, RegexError<R::Error>> {
        fn add<N: Clone, A>(value: ProductValue<N, A>, out: &mut Vec<N>) {
            match value {
                ProductValue::Node(n) => out.push(n),
                ProductValue::Sequence(xs) => {
                    for x in xs {
                        if let ProductValue::Node(n) = x {
                            out.push(n);
                        }
                    }
                }
                ProductValue::Optional(Some(x)) => {
                    if let ProductValue::Node(n) = *x {
                        out.push(n)
                    }
                }
                _ => {}
            }
        }
        let mut result = Vec::new();
        for child in self.adapter.children(node).map_err(RegexError::Adapter)? {
            add(child, &mut result);
        }
        Ok(result)
    }
    fn insert_match(
        &self,
        entries: &mut Vec<Entry<R::Node, C>>,
        node: R::Node,
        context: RegexContext<R::Node, C>,
    ) -> Result<(), RegexError<R::Error>> {
        let matches: Vec<usize> = entries
            .iter()
            .enumerate()
            .filter_map(|(i, e)| self.adapter.same_node(&e.node, &node).then_some(i))
            .collect();
        let exact: Vec<usize> = matches
            .iter()
            .copied()
            .filter(|i| {
                entries[*i]
                    .context
                    .ancestors
                    .iter()
                    .zip(&context.ancestors)
                    .all(|(a, b)| self.adapter.same_node(a, b))
            })
            .collect();
        match exact.len() {
            0 => entries.push(Entry {
                node,
                context,
                index: matches.len(),
            }),
            1 => {
                let old = entries.remove(exact[0]);
                entries.push(Entry {
                    node,
                    context: RegexContext {
                        ancestors: old.context.ancestors,
                        custom: (self.combine)(&old.context.custom, &context.custom),
                    },
                    index: old.index,
                });
            }
            _ => return Err(RegexError::DuplicateMatch),
        }
        Ok(())
    }
    fn descend_match(
        &mut self,
        node: &R::Node,
        state: StateId,
        context: RegexContext<R::Node, C>,
        marked: Vec<(R::Node, RegexContext<R::Node, C>)>,
        entries: &mut Vec<Entry<R::Node, C>>,
    ) -> Result<(), RegexError<R::Error>> {
        let (states, actions) = self.automaton.transition(state, node)?;
        let children = self.children(node)?;
        let mut marked = marked;
        let mut context = context;
        context.ancestors.push(node.clone());
        for action in actions {
            match action {
                TransitionInfo::MarkedForRewrite => marked.push((node.clone(), context.clone())),
                TransitionInfo::Context(c) => {
                    context.custom = (self.accumulate)(&context.custom, &c)
                }
                // Source computes `newChildren.filter(...)` and discards the result.
                TransitionInfo::ChildSelect(_) => {}
            }
        }
        let mut accepting = false;
        for state in &states {
            accepting |= self.automaton.is_accepting(*state)?;
        }
        if accepting {
            for (node, context) in &marked {
                self.insert_match(entries, node.clone(), context.clone())?;
            }
        }
        for child in children {
            for state in &states {
                if !self.automaton.is_accepting(*state)? {
                    self.descend_match(&child, *state, context.clone(), marked.clone(), entries)?;
                }
            }
        }
        Ok(())
    }
    fn scan_value(
        &mut self,
        value: ProductValue<R::Node, R::Atom>,
        ancestors: &[R::Node],
        starts: &HashSet<StateId>,
        entries: &mut Vec<Entry<R::Node, C>>,
    ) -> Result<(), RegexError<R::Error>> {
        use ProductValue::*;
        match value {
            Node(n) => self.scan_node(&n, ancestors, starts, entries)?,
            Sequence(xs) | Tuple(xs) => {
                for x in xs {
                    self.scan_value(x, ancestors, starts, entries)?
                }
            }
            Optional(Some(x)) | Left(x) | Right(x) => {
                self.scan_value(*x, ancestors, starts, entries)?
            }
            Map(xs) => {
                for (k, v) in xs {
                    self.scan_value(k, ancestors, starts, entries)?;
                    self.scan_value(v, ancestors, starts, entries)?
                }
            }
            Optional(None) | Atom(_) => {}
        }
        Ok(())
    }
    fn scan_node(
        &mut self,
        node: &R::Node,
        ancestors: &[R::Node],
        starts: &HashSet<StateId>,
        entries: &mut Vec<Entry<R::Node, C>>,
    ) -> Result<(), RegexError<R::Error>> {
        for state in starts {
            if self.automaton.valid_input(*state, node)? {
                self.descend_match(
                    node,
                    *state,
                    RegexContext {
                        ancestors: ancestors.to_vec(),
                        custom: self.default.clone(),
                    },
                    Vec::new(),
                    entries,
                )?;
            }
        }
        let mut path = ancestors.to_vec();
        path.push(node.clone());
        for child in self.adapter.children(node).map_err(RegexError::Adapter)? {
            self.scan_value(child, &path, starts, entries)?;
        }
        Ok(())
    }
    fn replace_node(
        &mut self,
        node: &R::Node,
        entries: &mut Vec<Entry<R::Node, C>>,
    ) -> Result<R::Node, RegexError<R::Error>> {
        if self.blocked(node) {
            return Ok(node.clone());
        }
        let match_index = entries
            .iter()
            .enumerate()
            .filter(|(_, e)| self.adapter.same_node(&e.node, node))
            .min_by_key(|(_, e)| e.index)
            .map(|(i, _)| i);
        let current = if let Some(i) = match_index {
            let entry = entries.remove(i);
            (self.rule)(node, &entry.context)
                .map_err(RegexError::Adapter)?
                .unwrap_or_else(|| node.clone())
        } else {
            node.clone()
        };
        if self.blocked(&current) {
            return Ok(current);
        }
        let children = self
            .adapter
            .children(&current)
            .map_err(RegexError::Adapter)?;
        let mut updated = Vec::new();
        for child in children {
            let allowed = self.select.as_ref().is_none_or(|f| f(&current, &child));
            updated.push(if allowed {
                self.replace_value(child, entries)?
            } else {
                child
            });
        }
        with_children(&self.adapter, &current, updated, false).map_err(RegexError::Adapter)
    }
    fn replace_value(
        &mut self,
        value: ProductValue<R::Node, R::Atom>,
        entries: &mut Vec<Entry<R::Node, C>>,
    ) -> Result<ProductValue<R::Node, R::Atom>, RegexError<R::Error>> {
        use ProductValue::*;
        Ok(match value {
            Node(n) => Node(self.replace_node(&n, entries)?),
            Sequence(xs) => Sequence(
                xs.into_iter()
                    .map(|x| self.replace_value(x, entries))
                    .collect::<Result<_, _>>()?,
            ),
            Optional(x) => Optional(
                x.map(|x| self.replace_value(*x, entries).map(Box::new))
                    .transpose()?,
            ),
            Map(xs) => {
                let mut result: Vec<(
                    ProductValue<R::Node, R::Atom>,
                    ProductValue<R::Node, R::Atom>,
                )> = Vec::new();
                for (k, v) in xs {
                    let k = self.replace_value(k, entries)?;
                    let v = self.replace_value(v, entries)?;
                    if let Some(entry) = result.iter_mut().find(|(old, _)| old == &k) {
                        *entry = (k, v)
                    } else {
                        result.push((k, v))
                    }
                }
                Map(result)
            }
            // The source replaceTopDown does not dispatch tuples or Either.
            other => other,
        })
    }
    pub fn execute(&mut self, node: &R::Node) -> Result<R::Node, RegexError<R::Error>> {
        self.changed = false;
        let starts = self.automaton.effective(self.pattern.start)?;
        let mut entries = Vec::new();
        self.scan_node(node, &[], &starts, &mut entries)?;
        self.adapter
            .init_properties(node)
            .map_err(RegexError::Adapter)?;
        let result = self.replace_node(node, &mut entries)?;
        self.changed = result != *node;
        Ok(result)
    }
}
