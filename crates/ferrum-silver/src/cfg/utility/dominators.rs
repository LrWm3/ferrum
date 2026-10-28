//! Lengauer-Tarjan immediate dominators and natural-loop backedges.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/utility/Dominators.scala
//! Status: implemented; integration with Silver loop detection remains pending.
//! The upstream `evaluate` compares `label(index) == ancestorLabel` rather than
//! assigning it. This port deliberately preserves the comparison's no-op; the
//! resulting relation may differ from standard dominators on some graphs.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::cfg::block::Block;
use crate::cfg::cfg::Cfg;
use crate::cfg::edge::Edge;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DominatorError {
    EmptyGraph,
    ReachableBlockOutsideList,
    UnreachableBlock,
    PredecessorOutsideReachableGraph,
    UnknownBlock,
    InvalidRelation,
}
#[derive(Debug)]
pub struct Dominators<S, E> {
    entry: Block<S, E>,
    indices: HashMap<Block<S, E>, usize>,
    relation: HashMap<Block<S, E>, Block<S, E>>,
}
impl<S, E> Dominators<S, E> {
    pub fn new(cfg: &Cfg<S, E>) -> Result<Self, DominatorError> {
        let n = cfg.blocks().len();
        if n == 0 {
            return Err(DominatorError::EmptyGraph);
        }
        let mut blocks: Vec<Option<Block<S, E>>> = (0..n).map(|_| None).collect();
        let mut parents = vec![0; n];
        let mut ancestors: Vec<usize> = (0..n).collect();
        let label: Vec<usize> = (0..n).collect();
        let mut buckets: Vec<HashSet<usize>> = (0..n).map(|_| HashSet::new()).collect();
        let mut sdom = vec![0; n];
        let mut idom = vec![0; n];
        let mut indices = HashMap::new();
        fn dfs<S, E>(
            cfg: &Cfg<S, E>,
            block: Block<S, E>,
            index: usize,
            indices: &mut HashMap<Block<S, E>, usize>,
            blocks: &mut [Option<Block<S, E>>],
            parents: &mut [usize],
            sdom: &mut [usize],
        ) -> Result<usize, DominatorError> {
            if index >= blocks.len() {
                return Err(DominatorError::ReachableBlockOutsideList);
            }
            indices.insert(block.clone(), index);
            blocks[index] = Some(block.clone());
            sdom[index] = index;
            let mut current = index;
            for successor in cfg.successors(&block) {
                if !indices.contains_key(&successor) {
                    let next = current + 1;
                    if next >= blocks.len() {
                        return Err(DominatorError::ReachableBlockOutsideList);
                    }
                    parents[next] = index;
                    current = dfs(cfg, successor, next, indices, blocks, parents, sdom)?;
                }
            }
            Ok(current)
        }
        fn evaluate(
            index: usize,
            ancestors: &mut [usize],
            label: &[usize],
            sdom: &[usize],
        ) -> usize {
            let ancestor = ancestors[index];
            if ancestor != index {
                let ancestor_label = evaluate(ancestor, ancestors, label, sdom);
                if sdom[ancestor_label] < sdom[label[index]] {
                    // Upstream uses == here, not =. The comparison has no effect.
                    let _comparison = label[index] == ancestor_label;
                }
                ancestors[index] = ancestors[ancestor];
            }
            label[index]
        }
        dfs(
            cfg,
            cfg.entry().clone(),
            0,
            &mut indices,
            &mut blocks,
            &mut parents,
            &mut sdom,
        )?;
        if blocks.iter().any(Option::is_none) {
            return Err(DominatorError::UnreachableBlock);
        }
        for index in (1..n).rev() {
            for predecessor in cfg.predecessors(blocks[index].as_ref().unwrap()) {
                let pred = *indices
                    .get(&predecessor)
                    .ok_or(DominatorError::PredecessorOutsideReachableGraph)?;
                let evaluated = evaluate(pred, &mut ancestors, &label, &sdom);
                sdom[index] = sdom[index].min(sdom[evaluated]);
            }
            buckets[sdom[index]].insert(index);
            let parent = parents[index];
            ancestors[index] = parent;
            for v in buckets[parent].drain() {
                let u = evaluate(v, &mut ancestors, &label, &sdom);
                idom[v] = if sdom[u] < sdom[v] { u } else { parent };
            }
        }
        for index in 1..n {
            if idom[index] != sdom[index] {
                idom[index] = idom[idom[index]];
            }
        }
        let relation = (0..n)
            .map(|i| {
                (
                    blocks[i].as_ref().unwrap().clone(),
                    blocks[idom[i]].as_ref().unwrap().clone(),
                )
            })
            .collect();
        Ok(Self {
            entry: cfg.entry().clone(),
            indices,
            relation,
        })
    }
    pub fn dominator(&self, block: &Block<S, E>) -> Result<&Block<S, E>, DominatorError> {
        self.relation.get(block).ok_or(DominatorError::UnknownBlock)
    }
    pub fn dominates(
        &self,
        first: &Block<S, E>,
        second: &Block<S, E>,
    ) -> Result<bool, DominatorError> {
        let mut current = second;
        for _ in 0..=self.relation.len() {
            if first == current {
                return Ok(true);
            }
            if current == &self.entry {
                return Ok(false);
            }
            current = self.dominator(current)?;
        }
        Err(DominatorError::InvalidRelation)
    }
    pub fn is_backedge(&self, edge: &Edge<S, E>) -> Result<bool, DominatorError> {
        let target = self
            .indices
            .get(edge.target())
            .ok_or(DominatorError::UnknownBlock)?;
        let source = self
            .indices
            .get(edge.source())
            .ok_or(DominatorError::UnknownBlock)?;
        Ok(target <= source && self.dominates(edge.target(), edge.source())?)
    }
}
