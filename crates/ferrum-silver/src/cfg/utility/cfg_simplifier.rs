//! Reachability pruning and empty-block contraction.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/utility/CfgSimplifier.scala
//! Status: implemented; concrete Silver CFG integration remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::cfg::block::{Block, BlockKind};
use crate::cfg::cfg::Cfg;
use crate::cfg::edge::{Edge, Kind};
use std::collections::{HashSet, VecDeque};

pub fn prune_unreachable<S, E: Clone + PartialEq>(cfg: &Cfg<S, E>) -> Cfg<S, E> {
    let entry = cfg.entry().clone();
    let mut queue = VecDeque::from([entry.clone()]);
    let mut blocks = vec![entry.clone()];
    let mut edges = Vec::new();
    while let Some(block) = queue.pop_front() {
        for edge in cfg.out_edges(&block) {
            if !edges.contains(edge) {
                edges.push(edge.clone());
            }
            let target = edge.target();
            if !blocks.contains(target) {
                queue.push_back(target.clone());
                blocks.push(target.clone());
            }
        }
    }
    let exit = cfg.exit().filter(|b| blocks.contains(b)).cloned();
    Cfg::new(blocks, edges, entry, exit)
}

/// Rebuild a concrete graph wrapper around the pruned generic graph.
pub fn prune_unreachable_with<S, E: Clone + PartialEq, C>(
    cfg: &Cfg<S, E>,
    factory: impl FnOnce(Cfg<S, E>) -> C,
) -> C {
    factory(prune_unreachable(cfg))
}

fn join<S, E: Clone>(incoming: &Edge<S, E>, outgoing: &Edge<S, E>) -> Option<Edge<S, E>> {
    let kind = if incoming.kind() == Kind::Normal {
        outgoing.kind()
    } else if outgoing.kind() == Kind::Normal {
        incoming.kind()
    } else {
        return None;
    };
    let source = incoming.source().clone();
    let target = outgoing.target().clone();
    match (incoming, outgoing) {
        (Edge::Unconditional { .. }, Edge::Unconditional { .. }) => {
            Some(Edge::unconditional(source, target, kind))
        }
        (Edge::Conditional { condition, .. }, Edge::Unconditional { .. })
        | (Edge::Unconditional { .. }, Edge::Conditional { condition, .. }) => {
            Some(Edge::conditional(condition.clone(), source, target, kind))
        }
        (Edge::Conditional { .. }, Edge::Conditional { .. }) => None,
    }
}

/// Like upstream, this assumes the exit has no outgoing edges.
pub fn simplify<S, E: Clone + PartialEq>(cfg: &Cfg<S, E>) -> Cfg<S, E> {
    fn enqueue_edge<S, E: Clone + PartialEq>(
        edge: Edge<S, E>,
        visited: &mut HashSet<Block<S, E>>,
        queue: &mut VecDeque<Edge<S, E>>,
        edges: &mut Vec<Edge<S, E>>,
    ) {
        if visited.contains(edge.target()) {
            if !edges.contains(&edge) {
                edges.push(edge);
            }
        } else {
            visited.insert(edge.target().clone());
            queue.push_back(edge);
        }
    }
    fn enqueue_block<S, E: Clone + PartialEq>(
        block: Block<S, E>,
        cfg: &Cfg<S, E>,
        visited: &mut HashSet<Block<S, E>>,
        queue: &mut VecDeque<Edge<S, E>>,
        blocks: &mut Vec<Block<S, E>>,
        edges: &mut Vec<Edge<S, E>>,
    ) {
        if !blocks.contains(&block) {
            blocks.push(block.clone());
        }
        for edge in cfg.out_edges(&block) {
            enqueue_edge(edge.clone(), visited, queue, edges);
        }
    }
    let entry = cfg.entry().clone();
    let mut queue = VecDeque::new();
    let mut visited = HashSet::new();
    let mut blocks = Vec::new();
    let mut edges = Vec::new();
    enqueue_block(
        entry.clone(),
        cfg,
        &mut visited,
        &mut queue,
        &mut blocks,
        &mut edges,
    );
    while let Some(edge) = queue.pop_front() {
        let block = edge.target().clone();
        let joined = if matches!(block.kind(),BlockKind::Statement{statements,..} if statements.is_empty())
            && cfg.in_edges(&block).len() == 1
        {
            let out = cfg.out_edges(&block);
            if out.len() == 1 {
                join(&edge, out[0])
            } else {
                None
            }
        } else {
            None
        };
        if let Some(next) = joined {
            enqueue_edge(next, &mut visited, &mut queue, &mut edges);
        } else {
            if !edges.contains(&edge) {
                edges.push(edge);
            }
            enqueue_block(
                block,
                cfg,
                &mut visited,
                &mut queue,
                &mut blocks,
                &mut edges,
            );
        }
    }
    let exit = cfg.exit().filter(|b| blocks.contains(b)).cloned();
    Cfg::new(blocks, edges, entry, exit)
}

/// Rebuild a concrete graph wrapper around the simplified generic graph.
pub fn simplify_with<S, E: Clone + PartialEq, C>(
    cfg: &Cfg<S, E>,
    factory: impl FnOnce(Cfg<S, E>) -> C,
) -> C {
    factory(simplify(cfg))
}
