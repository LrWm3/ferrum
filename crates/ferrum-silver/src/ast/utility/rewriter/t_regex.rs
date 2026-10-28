//! Tree-path regular expression combinators.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/rewriter/TRegex.scala
//! Status: partial. Match predicates, actions and automaton combinators are implemented;
//! context builders and integration with RegexStrategy remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::t_regex_automaton::{Automaton, Matcher, TRegexAutomaton, TransitionInfo};
use std::sync::Arc;

pub enum TreeRegex<N, C> {
    Match(Matcher<N, C>),
    Nested(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Star(Box<Self>),
    Optional(Box<Self>),
}
impl<N, C> Clone for TreeRegex<N, C> {
    fn clone(&self) -> Self {
        match self {
            Self::Match(m) => Self::Match(Matcher {
                predicate: m.predicate.clone(),
                actions: m.actions.clone(),
            }),
            Self::Nested(a, b) => Self::Nested(a.clone(), b.clone()),
            Self::Or(a, b) => Self::Or(a.clone(), b.clone()),
            Self::Star(a) => Self::Star(a.clone()),
            Self::Optional(a) => Self::Optional(a.clone()),
        }
    }
}
impl<N: 'static, C: 'static> TreeRegex<N, C> {
    pub fn node(predicate: impl Fn(&N) -> bool + Send + Sync + 'static, rewrite: bool) -> Self {
        Self::Match(Matcher {
            predicate: Arc::new(predicate),
            actions: Arc::new(move |_| {
                if rewrite {
                    vec![TransitionInfo::MarkedForRewrite]
                } else {
                    vec![]
                }
            }),
        })
    }
    pub fn context(
        predicate: impl Fn(&N) -> bool + Send + Sync + 'static,
        extract: impl Fn(&N) -> C + Send + Sync + 'static,
        rewrite: bool,
    ) -> Self {
        Self::Match(Matcher {
            predicate: Arc::new(predicate),
            actions: Arc::new(move |n| {
                let mut result = vec![TransitionInfo::Context(extract(n))];
                if rewrite {
                    result.push(TransitionInfo::MarkedForRewrite);
                }
                result
            }),
        })
    }
    pub fn child(
        predicate: impl Fn(&N) -> bool + Send + Sync + 'static,
        extract: impl Fn(&N) -> N + Send + Sync + 'static,
        rewrite: bool,
    ) -> Self {
        Self::Match(Matcher {
            predicate: Arc::new(predicate),
            actions: Arc::new(move |n| {
                let mut result = vec![TransitionInfo::ChildSelect(extract(n))];
                if rewrite {
                    result.push(TransitionInfo::MarkedForRewrite);
                }
                result
            }),
        })
    }
    pub fn nested(self, next: Self) -> Self {
        Self::Nested(Box::new(self), Box::new(next))
    }
    pub fn or(self, other: Self) -> Self {
        Self::Or(Box::new(self), Box::new(other))
    }
    pub fn star(self) -> Self {
        Self::Star(Box::new(self))
    }
    pub fn optional(self) -> Self {
        Self::Optional(Box::new(self))
    }
    pub fn wildcard() -> Self {
        Self::node(|_| true, false)
    }
    pub fn plus(self) -> Self {
        self.clone().nested(self.star())
    }
    pub fn descendant(self, next: Self) -> Self {
        self.nested(Self::wildcard().star()).nested(next)
    }
    pub fn non_consecutive_star(self) -> Self {
        self.star().nested(Self::wildcard().star()).star()
    }
    pub fn compile(&self, machine: &mut Automaton<N, C>) -> TRegexAutomaton {
        match self {
            Self::Match(m) => {
                let start = machine.new_state();
                let end = machine.new_state();
                machine
                    .set_match(
                        start,
                        end,
                        Matcher {
                            predicate: m.predicate.clone(),
                            actions: m.actions.clone(),
                        },
                    )
                    .expect("new states");
                TRegexAutomaton { start, end }
            }
            Self::Nested(a, b) => {
                let a = a.compile(machine);
                let b = b.compile(machine);
                machine.add_epsilon(a.end, b.start).expect("new states");
                TRegexAutomaton {
                    start: a.start,
                    end: b.end,
                }
            }
            Self::Or(a, b) => {
                let a = a.compile(machine);
                let b = b.compile(machine);
                let start = machine.new_state();
                let end = machine.new_state();
                for (x, y) in [
                    (start, a.start),
                    (start, b.start),
                    (a.end, end),
                    (b.end, end),
                ] {
                    machine.add_epsilon(x, y).expect("new states");
                }
                TRegexAutomaton { start, end }
            }
            Self::Star(a) => {
                let a = a.compile(machine);
                let end = machine.new_state();
                machine.add_epsilon(a.start, end).expect("new states");
                machine.add_epsilon(a.end, a.start).expect("new states");
                TRegexAutomaton {
                    start: a.start,
                    end,
                }
            }
            Self::Optional(a) => {
                let a = a.compile(machine);
                machine.add_epsilon(a.start, a.end).expect("new states");
                a
            }
        }
    }
}
