//! Lower Silver statements and methods into control-flow graphs.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/cfg/silver/CfgGenerator.scala
//! Status: implemented. Phase 1/2 construction, pruning, optional loop detection and
//! simplification are connected; extension-controlled lowering remains upstream's TODO.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpKind},
    program::{Declaration, Method},
    statement::{Stmt, StmtKind},
};
use crate::cfg::{
    block::Block,
    cfg::Cfg,
    edge::{Edge, Kind},
    silver::silver_cfg::{SilverBlock, SilverCfg, SilverEdge},
    utility::{
        cfg_simplifier,
        loop_detector::{self, IdInfo, LoopError, LoopMembership},
    },
};
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicI32, Ordering};

static NEXT_LABEL: AtomicI32 = AtomicI32::new(0);
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TmpLabel(pub String);
impl TmpLabel {
    pub fn generate(name: &str) -> Self {
        let id = NEXT_LABEL.fetch_add(1, Ordering::SeqCst).wrapping_add(1);
        Self(format!("{id}_{name}"))
    }
}
#[derive(Clone, Debug)]
pub enum TmpStmt {
    Wrapped(Stmt),
    Jump(TmpLabel),
    ConditionalJump(Exp, TmpLabel, TmpLabel),
    LoopHead(Vec<Exp>, TmpLabel, Option<i32>),
    Empty,
}
#[derive(Clone, Debug)]
enum TmpEdge {
    Unconditional(usize, usize),
    Conditional(Exp, usize, usize),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GeneratorError {
    UnresolvedLabel(String),
    MissingBlock(usize),
    Loop(LoopError),
}
impl From<LoopError> for GeneratorError {
    fn from(e: LoopError) -> Self {
        Self::Loop(e)
    }
}

#[derive(Debug)]
pub struct Phase1 {
    pub labels: HashMap<TmpLabel, usize>,
    pub statements: Vec<TmpStmt>,
}
impl Phase1 {
    pub fn new(ast: &Stmt, preserve_gotos: bool) -> Self {
        let mut p = Self {
            labels: HashMap::new(),
            statements: vec![TmpStmt::Empty],
        };
        p.run(ast, preserve_gotos);
        p
    }
    fn label(&mut self, label: TmpLabel, empty: bool) {
        self.labels.insert(label, self.statements.len());
        if empty {
            self.statements.push(TmpStmt::Empty);
        }
    }
    fn run(&mut self, stmt: &Stmt, preserve_gotos: bool) {
        match stmt.kind() {
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let thn = TmpLabel::generate("then");
                let els = TmpLabel::generate("else");
                let after = TmpLabel::generate("after");
                self.statements.push(TmpStmt::ConditionalJump(
                    condition.clone(),
                    thn.clone(),
                    els.clone(),
                ));
                self.label(thn, true);
                self.run(then_branch, preserve_gotos);
                self.statements.push(TmpStmt::Jump(after.clone()));
                self.label(els, true);
                self.run(else_branch, preserve_gotos);
                self.statements.push(TmpStmt::Jump(after.clone()));
                self.label(after, true);
            }
            StmtKind::While {
                condition,
                invariants,
                body,
            } => {
                let id = stmt
                    .metadata()
                    .info
                    .find_extension::<IdInfo>()
                    .map(|i| i.id);
                let head = TmpLabel::generate("head");
                let body_label = TmpLabel::generate("loop");
                let after = TmpLabel::generate("after");
                self.label(head.clone(), false);
                self.statements
                    .push(TmpStmt::LoopHead(invariants.clone(), after.clone(), id));
                self.statements.push(TmpStmt::ConditionalJump(
                    condition.clone(),
                    body_label.clone(),
                    after.clone(),
                ));
                self.label(body_label, true);
                self.run(body, preserve_gotos);
                self.statements.push(TmpStmt::Jump(head));
                self.label(after, true);
            }
            StmtKind::Seqn {
                statements,
                declarations,
            } => {
                for local in declarations {
                    if let Declaration::Local(d) = local {
                        let meta = Metadata {
                            position: d.meta.position.clone(),
                            info: d.meta.info.clone(),
                            ..Metadata::default()
                        };
                        self.statements.push(TmpStmt::Wrapped(Stmt::new(
                            StmtKind::LocalVarDeclStmt(d.clone()),
                            meta,
                        )));
                    }
                }
                for child in statements {
                    self.run(child, preserve_gotos);
                }
            }
            StmtKind::Goto(name) => {
                if preserve_gotos {
                    self.statements.push(TmpStmt::Wrapped(stmt.clone()));
                }
                self.statements.push(TmpStmt::Jump(TmpLabel(name.clone())));
            }
            StmtKind::Label(label) => {
                self.label(TmpLabel(label.name.clone()), true);
                self.statements.push(TmpStmt::Wrapped(stmt.clone()));
            }
            StmtKind::NewStmt { .. }
            | StmtKind::LocalVarAssign { .. }
            | StmtKind::FieldAssign { .. }
            | StmtKind::MethodCall { .. }
            | StmtKind::Exhale(_)
            | StmtKind::Inhale(_)
            | StmtKind::Assert(_)
            | StmtKind::Assume(_)
            | StmtKind::Fold(_)
            | StmtKind::Unfold(_)
            | StmtKind::Package { .. }
            | StmtKind::Apply(_)
            | StmtKind::LocalVarDeclStmt(_)
            | StmtKind::Quasihavoc { .. }
            | StmtKind::Quasihavocall { .. }
            | StmtKind::Extension(_) => self.statements.push(TmpStmt::Wrapped(stmt.clone())),
        }
    }
}

struct Phase2<'a> {
    phase1: &'a Phase1,
    blocks: HashMap<usize, SilverBlock>,
    edges: Vec<TmpEdge>,
    buffered: Vec<Stmt>,
    current: Option<usize>,
    loop_stack: Vec<(SilverBlock, usize)>,
    loops: LoopMembership<Stmt, Exp>,
}
impl<'a> Phase2<'a> {
    fn new(phase1: &'a Phase1) -> Self {
        Self {
            phase1,
            blocks: HashMap::new(),
            edges: Vec::new(),
            buffered: Vec::new(),
            current: None,
            loop_stack: Vec::new(),
            loops: HashMap::new(),
        }
    }
    fn resolve(&self, label: &TmpLabel) -> Result<usize, GeneratorError> {
        self.phase1
            .labels
            .get(label)
            .copied()
            .ok_or_else(|| GeneratorError::UnresolvedLabel(label.0.clone()))
    }
    fn add_block(&mut self, index: usize, block: SilverBlock) {
        while self
            .loop_stack
            .last()
            .is_some_and(|(_, after)| *after <= index)
        {
            self.loop_stack.pop();
        }
        self.loops.insert(
            block.clone(),
            self.loop_stack
                .iter()
                .map(|(head, _)| head.clone())
                .collect::<HashSet<_>>(),
        );
        self.blocks.insert(index, block);
    }
    fn add_edge(&mut self, edge: TmpEdge) {
        let target = match &edge {
            TmpEdge::Unconditional(_, target) | TmpEdge::Conditional(_, _, target) => *target,
        };
        self.edges.push(edge);
        self.blocks
            .entry(target)
            .or_insert_with(|| Block::statement(vec![]));
    }
    fn finalize_block(&mut self) {
        if let Some(index) = self.current {
            let statements = std::mem::take(&mut self.buffered);
            let block = match statements.first().map(Stmt::kind) {
                Some(StmtKind::Label(original)) if !original.invariants.is_empty() => {
                    let first = &statements[0];
                    let id = first
                        .metadata()
                        .info
                        .find_extension::<IdInfo>()
                        .map(|i| i.id);
                    let meta = Metadata {
                        position: first.metadata().position.clone(),
                        info: first.metadata().info.clone(),
                        ..Metadata::default()
                    };
                    let label = Stmt::new(
                        StmtKind::Label(crate::ast::program::LabelDeclaration::new(
                            crate::ast::program::LabelDeclarationData {
                                name: original.name.clone(),
                                invariants: vec![],
                                meta: meta.clone(),
                            },
                        )),
                        meta,
                    );
                    let mut stmts = vec![label];
                    stmts.extend(statements.iter().skip(1).cloned());
                    Block::statement_with_loop_info(stmts, original.invariants.clone(), id)
                }
                _ => Block::statement(statements),
            };
            self.add_block(index, block);
        } else {
            self.buffered.clear();
        }
    }
    fn run(mut self) -> Result<(SilverCfg, LoopMembership<Stmt, Exp>), GeneratorError> {
        for (index, stmt) in self.phase1.statements.iter().enumerate() {
            if !matches!(stmt, TmpStmt::Wrapped(_)) && !self.buffered.is_empty() {
                self.finalize_block();
            }
            match stmt {
                TmpStmt::Wrapped(s) => self.buffered.push(s.clone()),
                TmpStmt::Jump(target) => {
                    if let Some(current) = self.current {
                        let target = self.resolve(target)?;
                        self.add_edge(TmpEdge::Unconditional(current, target));
                    }
                    self.current = None;
                }
                TmpStmt::ConditionalJump(cond, thn, els) => {
                    if let Some(current) = self.current {
                        let then_index = self.resolve(thn)?;
                        let else_index = self.resolve(els)?;
                        let not = Exp::new(ExpKind::Not(cond.clone()), cond.metadata().clone());
                        self.add_edge(TmpEdge::Conditional(cond.clone(), current, then_index));
                        self.add_edge(TmpEdge::Conditional(not, current, else_index));
                    }
                    self.current = None;
                }
                TmpStmt::LoopHead(invariants, after, id) => {
                    if let Some(last) = self.current {
                        let end = self.resolve(after)?;
                        self.current = Some(index);
                        let block = Block::loop_head(invariants.clone(), vec![], *id);
                        self.loop_stack.push((block.clone(), end));
                        self.add_block(index, block);
                        self.add_edge(TmpEdge::Unconditional(last, index));
                    }
                }
                TmpStmt::Empty => {
                    if let Some(last) = self.current {
                        self.add_edge(TmpEdge::Unconditional(last, index));
                    }
                    self.current = Some(index);
                    self.add_block(index, Block::statement(vec![]));
                }
            }
        }
        if !self.buffered.is_empty() {
            self.finalize_block();
        }
        let entry = self
            .blocks
            .get(&0)
            .cloned()
            .ok_or(GeneratorError::MissingBlock(0))?;
        let exit = self
            .current
            .and_then(|index| self.blocks.get(&index).cloned())
            .unwrap_or_else(|| Block::statement(vec![]));
        let mut edges: Vec<SilverEdge> = Vec::new();
        for edge in self.edges {
            let (source, target) = match &edge {
                TmpEdge::Unconditional(s, t) | TmpEdge::Conditional(_, s, t) => (*s, *t),
            };
            let src = self
                .blocks
                .get(&source)
                .cloned()
                .ok_or(GeneratorError::MissingBlock(source))?;
            let dst = self
                .blocks
                .get(&target)
                .cloned()
                .ok_or(GeneratorError::MissingBlock(target))?;
            edges.push(match edge {
                TmpEdge::Unconditional(..) => Edge::unconditional_default(src, dst),
                TmpEdge::Conditional(cond, ..) => Edge::conditional_default(cond, src, dst),
            });
        }
        // Upstream also emits mutable-map values here; neither map specifies block order.
        // Rust's randomized HashMap may choose a different order between runs.
        let graph = Cfg::new(
            self.blocks.into_values().collect(),
            edges,
            entry,
            Some(exit),
        );
        Ok((
            SilverCfg::from_cfg(cfg_simplifier::prune_unreachable(&graph)),
            self.loops,
        ))
    }
}

pub fn compute_cfg(
    ast: &Stmt,
    cfg_information_required_in_ast: bool,
) -> Result<(SilverCfg, LoopMembership<Stmt, Exp>), GeneratorError> {
    Phase2::new(&Phase1::new(ast, cfg_information_required_in_ast)).run()
}
pub fn statement_to_cfg(
    ast: &Stmt,
    simplify: bool,
    detect: bool,
) -> Result<SilverCfg, GeneratorError> {
    let (cfg, loops) = compute_cfg(ast, false)?;
    let graph = if detect {
        loop_detector::detect(cfg.graph(), loops)?
    } else {
        cfg.graph().clone()
    };
    Ok(SilverCfg::from_cfg(if simplify {
        cfg_simplifier::simplify(&graph)
    } else {
        graph
    }))
}
pub fn method_to_cfg(
    method: &Method,
    simplify: bool,
    detect: bool,
) -> Result<SilverCfg, GeneratorError> {
    let empty = Stmt::new(
        StmtKind::Seqn {
            statements: vec![],
            declarations: vec![],
        },
        Metadata::default(),
    );
    let body = statement_to_cfg(method.body.as_ref().unwrap_or(&empty), false, detect)?;
    let pre = Block::precondition(method.pres.clone());
    let pre_edge = Edge::unconditional(pre.clone(), body.graph().entry().clone(), Kind::Normal);
    let mut blocks = vec![pre.clone()];
    let mut edges = vec![pre_edge];
    let exit = if let Some(body_exit) = body.graph().exit() {
        let post = Block::postcondition(method.posts.clone());
        edges.push(Edge::unconditional(
            body_exit.clone(),
            post.clone(),
            Kind::Normal,
        ));
        blocks.push(post.clone());
        Some(post)
    } else {
        None
    };
    blocks.extend(body.graph().blocks().iter().cloned());
    edges.extend(body.graph().edges().iter().cloned());
    let graph = Cfg::new(blocks, edges, pre, exit);
    Ok(SilverCfg::from_cfg(if simplify {
        cfg_simplifier::simplify(&graph)
    } else {
        graph
    }))
}
