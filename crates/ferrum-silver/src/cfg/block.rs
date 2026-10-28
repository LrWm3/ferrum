//! Generic identity-bearing CFG blocks.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/Block.scala
//! Status: implemented; integration with Silver CFG remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::{
    Arc,
    atomic::{AtomicI32, Ordering},
};

static NEXT_ID: AtomicI32 = AtomicI32::new(0);

#[derive(Debug)]
pub enum BlockKind<S, E> {
    Statement {
        statements: Vec<S>,
        invariants: Option<Vec<E>>,
        loop_id: Option<Option<i32>>,
    },
    Precondition(Vec<E>),
    Postcondition(Vec<E>),
    LoopHead {
        invariants: Vec<E>,
        statements: Vec<S>,
        loop_id: Option<i32>,
    },
}
#[derive(Debug)]
pub struct BlockData<S, E> {
    pub id: i32,
    pub kind: BlockKind<S, E>,
}
#[derive(Debug)]
pub struct Block<S, E>(Arc<BlockData<S, E>>);
impl<S, E> Clone for Block<S, E> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<S, E> PartialEq for Block<S, E> {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl<S, E> Eq for Block<S, E> {}
impl<S, E> Hash for Block<S, E> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Element<'a, S, E> {
    Statement(&'a S),
    Expression(&'a E),
}
impl<S, E> Block<S, E> {
    fn new(kind: BlockKind<S, E>) -> Self {
        Self(Arc::new(BlockData {
            id: NEXT_ID.fetch_add(1, Ordering::SeqCst).wrapping_add(1),
            kind,
        }))
    }
    pub fn statement(statements: Vec<S>) -> Self {
        Self::new(BlockKind::Statement {
            statements,
            invariants: None,
            loop_id: None,
        })
    }
    pub fn statement_with_loop_info(
        statements: Vec<S>,
        invariants: Vec<E>,
        loop_id: Option<i32>,
    ) -> Self {
        Self::new(BlockKind::Statement {
            statements,
            invariants: Some(invariants),
            loop_id: Some(loop_id),
        })
    }
    pub fn precondition(expressions: Vec<E>) -> Self {
        Self::new(BlockKind::Precondition(expressions))
    }
    pub fn postcondition(expressions: Vec<E>) -> Self {
        Self::new(BlockKind::Postcondition(expressions))
    }
    pub fn loop_head(invariants: Vec<E>, statements: Vec<S>, loop_id: Option<i32>) -> Self {
        Self::new(BlockKind::LoopHead {
            invariants,
            statements,
            loop_id,
        })
    }
    pub fn id(&self) -> i32 {
        self.0.id
    }
    pub fn kind(&self) -> &BlockKind<S, E> {
        &self.0.kind
    }
    pub fn elements(&self) -> Vec<Element<'_, S, E>> {
        match self.kind() {
            BlockKind::Statement { statements, .. } => {
                statements.iter().map(Element::Statement).collect()
            }
            BlockKind::Precondition(es) | BlockKind::Postcondition(es) => {
                es.iter().map(Element::Expression).collect()
            }
            BlockKind::LoopHead {
                invariants,
                statements,
                ..
            } => invariants
                .iter()
                .map(Element::Expression)
                .chain(statements.iter().map(Element::Statement))
                .collect(),
        }
    }
}
impl<S, E> fmt::Display for Block<S, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            BlockKind::Statement { .. } => write!(f, "StatementBlock({})", self.id()),
            BlockKind::Precondition(_) => write!(f, "PreconditionBlock({})", self.id()),
            BlockKind::Postcondition(_) => write!(f, "PostconditionBlock({})", self.id()),
            BlockKind::LoopHead {
                loop_id: Some(loop_id),
                ..
            } => write!(f, "LoopHeadBlock({}, {})", self.id(), loop_id),
            BlockKind::LoopHead { .. } => write!(f, "LoopHeadBlock({})", self.id()),
        }
    }
}
