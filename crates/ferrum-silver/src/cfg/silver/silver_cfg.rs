//! Silver-specialized control-flow graph analyses.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/silver/SilverCfg.scala
//! Status: implemented and connected to CFG generation; verifier integration remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::expression::{Exp, LocalVar};
use crate::ast::statement::Stmt;
use crate::ast::utility::statements::{self, VariableAnalysisError};
use crate::cfg::{
    block::{Block, BlockKind, Element},
    cfg::Cfg,
    edge::{Edge, Kind},
};
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Mutex;

pub type SilverBlock = Block<Stmt, Exp>;
pub type SilverEdge = Edge<Stmt, Exp>;
#[derive(Debug)]
pub struct SilverCfg {
    graph: Cfg<Stmt, Exp>,
    written_cache: Mutex<HashMap<SilverBlock, Vec<LocalVar>>>,
    join_cache: Mutex<Option<HashMap<SilverBlock, SilverBlock>>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SilverCfgError {
    NotLoopHead,
    Variables(VariableAnalysisError),
    MoreThanTwoSuccessors,
    UnexpectedTopLevelJoin,
}
impl From<VariableAnalysisError> for SilverCfgError {
    fn from(e: VariableAnalysisError) -> Self {
        Self::Variables(e)
    }
}
impl SilverCfg {
    pub fn new(
        blocks: Vec<SilverBlock>,
        edges: Vec<SilverEdge>,
        entry: SilverBlock,
        exit: Option<SilverBlock>,
    ) -> Self {
        Self::from_cfg(Cfg::new(blocks, edges, entry, exit))
    }
    pub fn from_cfg(graph: Cfg<Stmt, Exp>) -> Self {
        Self {
            graph,
            written_cache: Mutex::new(HashMap::new()),
            join_cache: Mutex::new(None),
        }
    }
    pub fn graph(&self) -> &Cfg<Stmt, Exp> {
        &self.graph
    }
    pub fn copy_with(
        &self,
        blocks: Option<Vec<SilverBlock>>,
        edges: Option<Vec<SilverEdge>>,
        entry: Option<SilverBlock>,
        exit: Option<Option<SilverBlock>>,
    ) -> Self {
        self.graph
            .copy_with(blocks, edges, entry, exit, Self::from_cfg)
    }
    pub fn written_vars(&self, head: &SilverBlock) -> Result<Vec<LocalVar>, SilverCfgError> {
        if !matches!(head.kind(), BlockKind::LoopHead { .. }) {
            return Err(SilverCfgError::NotLoopHead);
        }
        let mut cache = self.written_cache.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(result) = cache.get(head) {
            return Ok(result.clone());
        }
        let mut visited = HashSet::from([head.clone()]);
        let mut queue = VecDeque::from([(head.clone(), 0_i32)]);
        let mut result = Vec::new();
        while let Some((block, depth)) = queue.pop_front() {
            for element in block.elements() {
                if let Element::Statement(stmt) = element {
                    for var in statements::written_vars(stmt)? {
                        if !result.contains(&var) {
                            result.push(var);
                        }
                    }
                }
            }
            for edge in self.graph.out_edges(&block) {
                let next_depth = match edge.kind() {
                    Kind::In => depth + 1,
                    Kind::Out => depth - 1,
                    _ => depth,
                };
                let target = edge.target();
                if next_depth >= 0 && visited.insert(target.clone()) {
                    queue.push_back((target.clone(), next_depth));
                }
            }
        }
        cache.insert(head.clone(), result.clone());
        Ok(result)
    }
    pub fn join_points(&self) -> Result<HashMap<SilverBlock, SilverBlock>, SilverCfgError> {
        let mut cache = self.join_cache.lock().unwrap_or_else(|e| e.into_inner());
        if let Some(map) = cache.as_ref() {
            return Ok(map.clone());
        }
        fn find(
            cfg: &Cfg<Stmt, Exp>,
            initial: Vec<SilverBlock>,
            visited_init: HashSet<SilverBlock>,
            heads_init: HashSet<SilverBlock>,
        ) -> Result<(Option<SilverBlock>, HashMap<SilverBlock, SilverBlock>), SilverCfgError>
        {
            let mut queue = VecDeque::from(initial);
            let mut visited = visited_init;
            let mut heads = heads_init;
            let mut map = HashMap::new();
            while let Some(current) = queue.pop_front() {
                if !visited.insert(current.clone()) {
                    return Ok((Some(current), map));
                }
                if matches!(current.kind(), BlockKind::LoopHead { .. }) {
                    heads.insert(current.clone());
                }
                let next = cfg.successors(&current);
                let next = match next.len() {
                    0 | 1 => next,
                    2 => {
                        let branch = next.into_iter().filter(|n| !heads.contains(n)).collect();
                        let (join, inner) =
                            find(cfg, branch, HashSet::from([current.clone()]), heads.clone())?;
                        map.extend(inner);
                        if let Some(j) = &join {
                            map.insert(current, j.clone());
                        }
                        join.into_iter().collect()
                    }
                    _ => return Err(SilverCfgError::MoreThanTwoSuccessors),
                };
                queue.extend(next.into_iter().filter(|n| !heads.contains(n)));
            }
            Ok((None, map))
        }
        let (join, map) = find(
            &self.graph,
            vec![self.graph.entry().clone()],
            HashSet::new(),
            HashSet::new(),
        )?;
        if join.is_some() {
            return Err(SilverCfgError::UnexpectedTopLevelJoin);
        }
        *cache = Some(map.clone());
        Ok(map)
    }
}
