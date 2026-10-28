//! Natural-loop detection and CFG loop-boundary augmentation.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/utility/LoopDetector.scala
//! Status: partial. Generic loop detection and augmentation are implemented;
//! AST information projection remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::expression::LocalVar;
use crate::ast::utility::statements::{self, VariableAnalysisError};
use crate::ast::{ast::ExtensionInfo, statement::Stmt};
use crate::cfg::{
    block::{Block, BlockKind},
    cfg::Cfg,
    edge::{Edge, Kind},
    utility::dominators::{DominatorError, Dominators},
};
use std::any::Any;
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdInfo {
    pub id: i32,
}
impl ExtensionInfo for IdInfo {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn comments(&self) -> Vec<String> {
        vec![format!("id = {}", self.id)]
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoopInfo {
    pub head: Option<i32>,
    pub loops: HashSet<i32>,
}
impl ExtensionInfo for LoopInfo {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn comments(&self) -> Vec<String> {
        let head = self
            .head
            .map(|id| format!("Some({id})"))
            .unwrap_or_else(|| "None".into());
        let loops = self
            .loops
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        vec![format!("LoopInfo({head},Set({loops}))")]
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoopError {
    Dominator(DominatorError),
    Irreducible,
    UnexpectedLoopHead,
    EmptyStatementLoopHead,
    SourceMultiBoundaryKindCast,
    Variables(VariableAnalysisError),
}
impl From<VariableAnalysisError> for LoopError {
    fn from(error: VariableAnalysisError) -> Self {
        Self::Variables(error)
    }
}
impl From<DominatorError> for LoopError {
    fn from(e: DominatorError) -> Self {
        Self::Dominator(e)
    }
}
pub type LoopMembership<S, E> = HashMap<Block<S, E>, HashSet<Block<S, E>>>;

pub fn collect_blocks<S, E>(cfg: &Cfg<S, E>, backedge: &Edge<S, E>) -> HashSet<Block<S, E>> {
    let head = backedge.target();
    let first = backedge.source().clone();
    let mut result = HashSet::from([first.clone()]);
    let mut stack = vec![first];
    while let Some(current) = stack.pop() {
        if &current != head {
            for pred in cfg.predecessors(&current) {
                if result.insert(pred.clone()) {
                    stack.push(pred);
                }
            }
        }
    }
    result
}

pub fn is_reducible<S, E>(
    cfg: &Cfg<S, E>,
    dominators: &Dominators<S, E>,
) -> Result<bool, LoopError> {
    fn dfs<S, E>(
        cfg: &Cfg<S, E>,
        dom: &Dominators<S, E>,
        block: Block<S, E>,
        index: usize,
        indices: &mut HashMap<Block<S, E>, usize>,
        low: &mut [usize],
    ) -> Result<(usize, bool), LoopError> {
        indices.insert(block.clone(), index);
        let mut current_index = index;
        let mut current_low = index;
        let mut reducible = true;
        for edge in cfg.out_edges(&block) {
            if !reducible || dom.is_backedge(edge)? {
                continue;
            }
            let target = edge.target();
            if let Some(successor_index) = indices.get(target) {
                current_low = current_low.min(low[*successor_index]);
            } else {
                let successor_index = current_index + 1;
                if successor_index >= low.len() {
                    return Err(LoopError::Dominator(
                        DominatorError::ReachableBlockOutsideList,
                    ));
                }
                let (next, successor_reducible) =
                    dfs(cfg, dom, target.clone(), successor_index, indices, low)?;
                current_index = next;
                current_low = current_low.min(low[successor_index]);
                reducible &= successor_reducible;
                low[successor_index] = usize::MAX;
            }
        }
        Ok((current_index, reducible && index <= current_low))
    }
    let mut low: Vec<usize> = (0..cfg.blocks().len()).collect();
    let mut indices = HashMap::new();
    if low.is_empty() {
        return Err(LoopError::Dominator(DominatorError::EmptyGraph));
    }
    Ok(dfs(
        cfg,
        dominators,
        cfg.entry().clone(),
        0,
        &mut indices,
        &mut low,
    )?
    .1)
}

pub fn natural_loops<S, E>(
    cfg: &Cfg<S, E>,
    mut loops: LoopMembership<S, E>,
) -> Result<(LoopMembership<S, E>, Dominators<S, E>), LoopError> {
    let dominators = Dominators::new(cfg)?;
    if !is_reducible(cfg, &dominators)? {
        return Err(LoopError::Irreducible);
    }
    for edge in cfg.edges() {
        if dominators.is_backedge(edge)? {
            let head = edge.target().clone();
            for block in collect_blocks(cfg, edge) {
                loops.entry(block).or_default().insert(head.clone());
            }
        }
    }
    Ok((loops, dominators))
}

/// Collect writes for every natural-loop head, retaining duplicates as upstream
/// does before its optional final distinct operation.
pub fn written_variables(
    cfg: &Cfg<Stmt, crate::ast::expression::Exp>,
    dominators: &Dominators<Stmt, crate::ast::expression::Exp>,
) -> Result<HashMap<Block<Stmt, crate::ast::expression::Exp>, Vec<LocalVar>>, LoopError> {
    let mut result: HashMap<_, Vec<_>> = HashMap::new();
    for edge in cfg.edges() {
        if dominators.is_backedge(edge)? {
            let head = edge.target().clone();
            for block in collect_blocks(cfg, edge) {
                let written = result.entry(head.clone()).or_default();
                for element in block.elements() {
                    if let crate::cfg::block::Element::Statement(stmt) = element {
                        written.extend(statements::written_vars(stmt)?);
                    }
                }
            }
        }
    }
    Ok(result)
}

pub fn detect<S: Clone + 'static, E: Clone + PartialEq>(
    cfg: &Cfg<S, E>,
    loops: LoopMembership<S, E>,
) -> Result<Cfg<S, E>, LoopError> {
    let (loops, _) = natural_loops(cfg, loops)?;
    augment(cfg, &loops)
}
pub fn detect_with<S: Clone + 'static, E: Clone + PartialEq, C>(
    cfg: &Cfg<S, E>,
    loops: LoopMembership<S, E>,
    factory: impl FnOnce(Cfg<S, E>) -> C,
) -> Result<C, LoopError> {
    Ok(factory(detect(cfg, loops)?))
}

pub fn augment<S: Clone + 'static, E: Clone + PartialEq>(
    cfg: &Cfg<S, E>,
    loops: &LoopMembership<S, E>,
) -> Result<Cfg<S, E>, LoopError> {
    let mut queue = VecDeque::from([cfg.entry().clone()]);
    let mut heads: HashMap<Block<S, E>, Block<S, E>> = HashMap::new();
    let mut blocks = vec![cfg.entry().clone()];
    let mut edges: Vec<Edge<S, E>> = Vec::new();
    let empty = HashSet::new();
    while let Some(block) = queue.pop_front() {
        for edge in cfg.out_edges(&block) {
            let src_heads = loops.get(edge.source()).unwrap_or(&empty);
            let dst_heads = loops.get(edge.target()).unwrap_or(&empty);
            let out = src_heads.difference(dst_heads).count();
            let inside = dst_heads.difference(src_heads).count();
            let mid = (out + inside).saturating_sub(1);
            let first = heads
                .get(edge.source())
                .cloned()
                .unwrap_or_else(|| edge.source().clone());
            let last = if inside > 0 && out == 0 {
                match edge.target().kind() {
                    BlockKind::LoopHead { .. } => edge.target().clone(),
                    BlockKind::Statement {
                        statements,
                        invariants,
                        ..
                    } => {
                        let first_stmt = statements
                            .first()
                            .ok_or(LoopError::EmptyStatementLoopHead)?;
                        let loop_id =
                            (first_stmt as &dyn Any)
                                .downcast_ref::<Stmt>()
                                .and_then(|s| {
                                    s.metadata().info.find_extension::<IdInfo>().map(|i| i.id)
                                });
                        let head = Block::loop_head(
                            invariants.clone().unwrap_or_default(),
                            statements.clone(),
                            loop_id,
                        );
                        heads.insert(edge.target().clone(), head.clone());
                        head
                    }
                    _ => return Err(LoopError::UnexpectedLoopHead),
                }
            } else {
                heads
                    .get(edge.target())
                    .cloned()
                    .unwrap_or_else(|| edge.target().clone())
            };
            if mid == 0 {
                let kind = if out > 0 {
                    Kind::Out
                } else if inside > 0 {
                    Kind::In
                } else {
                    Kind::Normal
                };
                let updated = match edge {
                    Edge::Unconditional { .. } => Edge::unconditional(first, last.clone(), kind),
                    Edge::Conditional { condition, .. } => {
                        Edge::conditional(condition.clone(), first, last.clone(), kind)
                    }
                };
                if !edges.contains(&updated) {
                    edges.push(updated);
                }
            } else {
                let mut source = first;
                let mut condition = match edge {
                    Edge::Conditional { condition, .. } => Some(condition.clone()),
                    _ => None,
                };
                for index in 0..=mid {
                    let target = if index == mid {
                        last.clone()
                    } else {
                        let intermediate = if index < inside {
                            Block::loop_head(vec![], vec![], None)
                        } else {
                            Block::statement(vec![])
                        };
                        blocks.push(intermediate.clone());
                        intermediate
                    };
                    // Upstream performs `Kind.asInstanceOf` here. When an entering
                    // edge reaches this arm it casts the Enumeration object to a
                    // Value and fails; do not invent a successful Kind::In.
                    if index >= out {
                        return Err(LoopError::SourceMultiBoundaryKindCast);
                    }
                    let current = match condition.take() {
                        Some(c) => Edge::conditional(c, source, target.clone(), Kind::Out),
                        None => Edge::unconditional(source, target.clone(), Kind::Out),
                    };
                    if !edges.contains(&current) {
                        edges.push(current);
                    }
                    source = target;
                }
            }
            if !blocks.contains(&last) {
                queue.push_back(edge.target().clone());
                blocks.push(last);
            }
        }
    }
    Ok(Cfg::new(
        blocks,
        edges,
        cfg.entry().clone(),
        cfg.exit().cloned(),
    ))
}
