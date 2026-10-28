//! Generic CFG edges and loop-boundary kinds.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/Edge.scala
//! Status: implemented; integration with Silver CFG remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::block::Block;
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub enum Kind {
    Normal,
    In,
    Out,
    #[default]
    Unknown,
}
impl std::fmt::Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Normal => "normal",
            Self::In => "in",
            Self::Out => "out",
            Self::Unknown => "unknown",
        })
    }
}
#[derive(Debug)]
pub enum Edge<S, E> {
    Unconditional {
        source: Block<S, E>,
        target: Block<S, E>,
        kind: Kind,
    },
    Conditional {
        condition: E,
        source: Block<S, E>,
        target: Block<S, E>,
        kind: Kind,
    },
}
impl<S, E: Clone> Clone for Edge<S, E> {
    fn clone(&self) -> Self {
        match self {
            Self::Unconditional {
                source,
                target,
                kind,
            } => Self::Unconditional {
                source: source.clone(),
                target: target.clone(),
                kind: *kind,
            },
            Self::Conditional {
                condition,
                source,
                target,
                kind,
            } => Self::Conditional {
                condition: condition.clone(),
                source: source.clone(),
                target: target.clone(),
                kind: *kind,
            },
        }
    }
}
impl<S, E: PartialEq> PartialEq for Edge<S, E> {
    fn eq(&self, o: &Self) -> bool {
        match (self, o) {
            (
                Self::Unconditional {
                    source: a,
                    target: b,
                    kind: c,
                },
                Self::Unconditional {
                    source: x,
                    target: y,
                    kind: z,
                },
            ) => a == x && b == y && c == z,
            (
                Self::Conditional {
                    condition: a,
                    source: b,
                    target: c,
                    kind: d,
                },
                Self::Conditional {
                    condition: w,
                    source: x,
                    target: y,
                    kind: z,
                },
            ) => a == w && b == x && c == y && d == z,
            _ => false,
        }
    }
}
impl<S, E: Eq> Eq for Edge<S, E> {}
impl<S, E> Edge<S, E> {
    pub fn unconditional_default(source: Block<S, E>, target: Block<S, E>) -> Self {
        Self::unconditional(source, target, Kind::Unknown)
    }
    pub fn conditional_default(condition: E, source: Block<S, E>, target: Block<S, E>) -> Self {
        Self::conditional(condition, source, target, Kind::Unknown)
    }
    pub fn unconditional(source: Block<S, E>, target: Block<S, E>, kind: Kind) -> Self {
        Self::Unconditional {
            source,
            target,
            kind,
        }
    }
    pub fn conditional(condition: E, source: Block<S, E>, target: Block<S, E>, kind: Kind) -> Self {
        Self::Conditional {
            condition,
            source,
            target,
            kind,
        }
    }
    pub fn source(&self) -> &Block<S, E> {
        match self {
            Self::Unconditional { source, .. } | Self::Conditional { source, .. } => source,
        }
    }
    pub fn target(&self) -> &Block<S, E> {
        match self {
            Self::Unconditional { target, .. } | Self::Conditional { target, .. } => target,
        }
    }
    pub fn kind(&self) -> Kind {
        match self {
            Self::Unconditional { kind, .. } | Self::Conditional { kind, .. } => *kind,
        }
    }
    pub fn is_in(&self) -> bool {
        self.kind() == Kind::In
    }
    pub fn is_out(&self) -> bool {
        self.kind() == Kind::Out
    }
}
