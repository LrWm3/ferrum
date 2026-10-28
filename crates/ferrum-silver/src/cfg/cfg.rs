//! Immutable generic CFG and its cached adjacency indexes.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/Cfg.scala
//! Status: source CFG operations and fallible DOT rendering connect to Silver and native verification.
//! Broad source compatibility remains unproved.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::block::{Block, BlockKind};
use super::edge::{Edge, Kind};
use std::collections::HashMap;
use std::fmt::Display;

#[derive(Debug)]
pub struct Cfg<S, E> {
    blocks: Vec<Block<S, E>>,
    edges: Vec<Edge<S, E>>,
    entry: Block<S, E>,
    exit: Option<Block<S, E>>,
    in_edges: HashMap<i32, Vec<usize>>,
    out_edges: HashMap<i32, Vec<usize>>,
}
impl<S, E: Clone> Clone for Cfg<S, E> {
    fn clone(&self) -> Self {
        Self::new(
            self.blocks.clone(),
            self.edges.clone(),
            self.entry.clone(),
            self.exit.clone(),
        )
    }
}
impl<S, E: Clone> Cfg<S, E> {
    /// Copy with selected fields replaced; `Some(None)` explicitly removes exit.
    /// The factory may capture and retain additional concrete CFG state.
    pub fn copy_with<C>(
        &self,
        blocks: Option<Vec<Block<S, E>>>,
        edges: Option<Vec<Edge<S, E>>>,
        entry: Option<Block<S, E>>,
        exit: Option<Option<Block<S, E>>>,
        factory: impl FnOnce(Cfg<S, E>) -> C,
    ) -> C {
        factory(Cfg::new(
            blocks.unwrap_or_else(|| self.blocks.clone()),
            edges.unwrap_or_else(|| self.edges.clone()),
            entry.unwrap_or_else(|| self.entry.clone()),
            exit.unwrap_or_else(|| self.exit.clone()),
        ))
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MapError {
    EdgeSourceNotInBlocks,
    EdgeTargetNotInBlocks,
    EntryNotInBlocks,
    ExitNotInBlocks,
}
impl<S, E> Cfg<S, E> {
    pub fn blocks(&self) -> &[Block<S, E>] {
        &self.blocks
    }
    pub fn edges(&self) -> &[Edge<S, E>] {
        &self.edges
    }
    pub fn entry(&self) -> &Block<S, E> {
        &self.entry
    }
    pub fn exit(&self) -> Option<&Block<S, E>> {
        self.exit.as_ref()
    }
    pub fn new(
        blocks: Vec<Block<S, E>>,
        edges: Vec<Edge<S, E>>,
        entry: Block<S, E>,
        exit: Option<Block<S, E>>,
    ) -> Self {
        let mut in_edges: HashMap<i32, Vec<usize>> = HashMap::new();
        let mut out_edges: HashMap<i32, Vec<usize>> = HashMap::new();
        for (index, edge) in edges.iter().enumerate() {
            in_edges.entry(edge.target().id()).or_default().push(index);
            out_edges.entry(edge.source().id()).or_default().push(index);
        }
        Self {
            blocks,
            edges,
            entry,
            exit,
            in_edges,
            out_edges,
        }
    }
    pub fn in_edges(&self, block: &Block<S, E>) -> Vec<&Edge<S, E>> {
        self.in_edges
            .get(&block.id())
            .map(|v| v.iter().map(|i| &self.edges[*i]).collect())
            .unwrap_or_default()
    }
    pub fn out_edges(&self, block: &Block<S, E>) -> Vec<&Edge<S, E>> {
        self.out_edges
            .get(&block.id())
            .map(|v| v.iter().map(|i| &self.edges[*i]).collect())
            .unwrap_or_default()
    }
    pub fn predecessors(&self, block: &Block<S, E>) -> Vec<Block<S, E>> {
        self.in_edges(block)
            .into_iter()
            .map(|e| e.source().clone())
            .collect()
    }
    pub fn successors(&self, block: &Block<S, E>) -> Vec<Block<S, E>> {
        self.out_edges(block)
            .into_iter()
            .map(|e| e.target().clone())
            .collect()
    }
    /// The factory lets a Silver-specific CFG retain its concrete wrapper on mapping.
    pub fn map_with<S2, E2, C>(
        &self,
        mut statements: impl FnMut(&S) -> Vec<S2>,
        mut expressions: impl FnMut(&E) -> E2,
        factory: impl FnOnce(Cfg<S2, E2>) -> C,
    ) -> Result<C, MapError> {
        let mut mapped: HashMap<Block<S, E>, Block<S2, E2>> = HashMap::new();
        for block in &self.blocks {
            let next = match block.kind() {
                // The Scala extractor only retains statements, discarding optional loop metadata.
                BlockKind::Statement { statements: xs, .. } => {
                    Block::statement(xs.iter().flat_map(&mut statements).collect())
                }
                BlockKind::Precondition(xs) => {
                    Block::precondition(xs.iter().map(&mut expressions).collect())
                }
                BlockKind::Postcondition(xs) => {
                    Block::postcondition(xs.iter().map(&mut expressions).collect())
                }
                BlockKind::LoopHead {
                    invariants,
                    statements: xs,
                    loop_id,
                } => Block::loop_head(
                    invariants.iter().map(&mut expressions).collect(),
                    xs.iter().flat_map(&mut statements).collect(),
                    *loop_id,
                ),
            };
            mapped.insert(block.clone(), next);
        }
        // Source uses Map.values; it does not guarantee original block ordering.
        let blocks = mapped.values().cloned().collect();
        let mut edges = Vec::with_capacity(self.edges.len());
        for edge in &self.edges {
            let source = mapped
                .get(edge.source())
                .ok_or(MapError::EdgeSourceNotInBlocks)?
                .clone();
            let target = mapped
                .get(edge.target())
                .ok_or(MapError::EdgeTargetNotInBlocks)?
                .clone();
            edges.push(match edge {
                Edge::Unconditional { kind, .. } => Edge::unconditional(source, target, *kind),
                Edge::Conditional {
                    condition, kind, ..
                } => Edge::conditional(expressions(condition), source, target, *kind),
            });
        }
        let entry = mapped
            .get(&self.entry)
            .ok_or(MapError::EntryNotInBlocks)?
            .clone();
        let exit = self
            .exit
            .as_ref()
            .map(|b| mapped.get(b).cloned().ok_or(MapError::ExitNotInBlocks))
            .transpose()?;
        Ok(factory(Cfg::new(blocks, edges, entry, exit)))
    }
}
impl<S: Display, E: Display> Cfg<S, E> {
    pub fn to_dot(&self) -> String {
        self.try_to_dot_with(
            |s| Ok::<_, std::convert::Infallible>(s.to_string()),
            |e| Ok::<_, std::convert::Infallible>(e.to_string()),
        )
        .unwrap_or_else(|never| match never {})
    }
}
impl<S, E> Cfg<S, E> {
    /// Render the source DOT structure without changing block identities. Native AST
    /// printers may fail on an unsupported extension, so their errors remain visible.
    pub fn try_to_dot_with<X>(
        &self,
        mut statement: impl FnMut(&S) -> Result<String, X>,
        mut expression: impl FnMut(&E) -> Result<String, X>,
    ) -> Result<String, X> {
        fn escape(s: String) -> String {
            s.replace('<', "\\<")
                .replace('>', "\\>")
                .replace('|', "\\|")
        }
        let mut output = String::from("digraph {\n  graph[rankdir=LR]");
        for block in &self.blocks {
            let label = match block.kind() {
                BlockKind::Statement { statements, .. } => format!(
                    "{}|{}",
                    block,
                    statements
                        .iter()
                        .map(|x| statement(x).map(escape))
                        .collect::<Result<Vec<_>, _>>()?
                        .join("|")
                ),
                BlockKind::Precondition(es) | BlockKind::Postcondition(es) => format!(
                    "{}|{}",
                    block,
                    es.iter()
                        .map(|x| expression(x).map(escape))
                        .collect::<Result<Vec<_>, _>>()?
                        .join("|")
                ),
                BlockKind::LoopHead {
                    invariants,
                    statements,
                    ..
                } => format!(
                    "{}|{}|{}",
                    block,
                    invariants
                        .iter()
                        .map(|x| expression(x).map(|text| format!("invariant {}", escape(text))))
                        .collect::<Result<Vec<_>, _>>()?
                        .join("|"),
                    statements
                        .iter()
                        .map(|x| statement(x).map(escape))
                        .collect::<Result<Vec<_>, _>>()?
                        .join("|")
                ),
            };
            // The Scala match compares the block with Option[Block], so its exit arm never matches.
            let style = if block == &self.entry {
                "style=\"filled\", fillcolor=\"palegreen\""
            } else {
                ""
            };
            output.push_str(&format!(
                "  BB{} [\n    shape=\"record\"\n    {}\n    label=\"{}\"\n  ];\n",
                block.id(),
                style,
                label
            ));
        }
        for edge in &self.edges {
            let suffix = match edge.kind() {
                Kind::In => Some("(in)"),
                Kind::Out => Some("(out)"),
                Kind::Unknown => Some("(??)"),
                Kind::Normal => None,
            };
            let label = match edge {
                Edge::Unconditional { .. } => suffix.map(str::to_owned),
                Edge::Conditional { condition, .. } => Some(match suffix {
                    Some(s) => format!("{} {}", escape(expression(condition)?), s),
                    None => escape(expression(condition)?),
                }),
            };
            output.push_str(&format!(
                "  BB{} -> BB{}{};\n",
                edge.source().id(),
                edge.target().id(),
                label
                    .map(|l| format!(" [label=\"{}\"]", l))
                    .unwrap_or_default()
            ));
        }
        output.push_str("}\n");
        Ok(output)
    }
}
