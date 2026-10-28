//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/smoke/SmokeDetectionPlugin.scala
//!
//! Purpose:
//! Insert refute-false probes to detect inconsistent specifications, excluding marked unreachable
//! paths.
//!
//! Planned Rust structure:
//! Port SmokeDetectionPlugin parser, beforeParse/beforeVerify, appendRefuteFalse/refuteFalse and
//! CFG reachability collection, plus SmokeDetectionInfo.
//!
//! Behavior to preserve:
//! Add probes at method ends, after nonsynthesized inhales, loop ends, nonempty branches and
//! before nonsynthesized gotos; preserve generated ID behavior and synthesized markers. Build
//! unsimplified CFG, track seen and reachable probe IDs, propagate unreachable through joins only
//! when all branches are unreachable, remove seen-but-unreachable probes and all Unreachable
//! markers. Refute plugin must run afterwards.
//!
//! Integration:
//! plugin::standard::refute::refute_plugin and refute_ast_extension; cfg::silver, parser and
//! ast::utility::rewriter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for node identity, CFG ordering and source metadata.
//!
//! Open decisions:
//! Reconcile CFG traversal/joins and ID reuse for method-end probes with cfg and refute; do not
//! silently repair upstream behavior.
//!
//! Status: partial; smoke metadata, refute construction and CFG reachability collection
//! implemented, together with fallible program instrumentation and CFG-based removal hooks.
//! Parser registration and general extension traversal remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright notice: the pinned upstream file does not carry an individual notice.

use super::unreachable_ast_extension::Unreachable;
use crate::ast::ast::{ExtensionInfo, Info, Metadata};
use crate::ast::expression::{Exp, ExpKind};
use crate::ast::position::Position;
use crate::ast::statement::{Stmt, StmtKind};
use crate::cfg::block::Element;
use crate::cfg::silver::silver_cfg::{SilverBlock, SilverCfg, SilverCfgError};
use crate::plugin::standard::refute::refute_ast_extension::Refute;
use std::any::Any;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct SmokeDetectionInfo {
    pub id: i32,
}
impl ExtensionInfo for SmokeDetectionInfo {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn comments(&self) -> Vec<String> {
        vec![format!("`refute false` #{}", self.id)]
    }
}
pub fn refute_false(pos: Position, id: i32) -> Stmt {
    let exp = Exp::new(
        ExpKind::FalseLit,
        Metadata {
            position: pos.clone(),
            ..Metadata::default()
        },
    );
    Refute::new(
        exp,
        Metadata {
            position: pos,
            info: Info::Extension(Arc::new(SmokeDetectionInfo { id })),
            ..Metadata::default()
        },
    )
    .statement()
}
pub fn append_refute_false(statement: Stmt, pos: Position, id: i32) -> Stmt {
    Stmt::new(
        StmtKind::Seqn {
            statements: vec![statement, refute_false(pos.clone(), id)],
            declarations: Vec::new(),
        },
        Metadata {
            position: pos,
            ..Metadata::default()
        },
    )
}
/// Collect IDs reachable without passing an Unreachable marker, and IDs actually seen.
/// Join-point errors are retained rather than silently losing any path.
pub fn collect_refutes_to_keep(cfg: &SilverCfg) -> Result<(Vec<i32>, Vec<i32>), SilverCfgError> {
    let joins = cfg.join_points()?;
    let exits = cfg.graph().exit().cloned().into_iter().collect::<Vec<_>>();
    let mut seen = Vec::new();
    let mut keep = Vec::new();
    let mut encountered = Vec::new();
    fn visit(
        cfg: &SilverCfg,
        current: &SilverBlock,
        exits: &[SilverBlock],
        joins: &std::collections::HashMap<SilverBlock, SilverBlock>,
        seen: &mut Vec<SilverBlock>,
        keep: &mut Vec<i32>,
        encountered: &mut Vec<i32>,
        unreachable: bool,
    ) -> bool {
        seen.push(current.clone());
        let mut unreachable_successors = unreachable;
        for element in current.elements() {
            let Element::Statement(stmt) = element else {
                continue;
            };
            let StmtKind::Extension(extension) = stmt.kind() else {
                continue;
            };
            if extension.0.as_any().is::<Unreachable>() {
                unreachable_successors = true;
            }
            if let Some(refute) = extension.0.as_any().downcast_ref::<Refute>() {
                if matches!(refute.exp.kind(), ExpKind::FalseLit) {
                    if let Some(info) = stmt.metadata().info.find_extension::<SmokeDetectionInfo>()
                    {
                        if !unreachable_successors {
                            keep.push(info.id);
                        }
                        encountered.push(info.id);
                    }
                }
            }
        }
        if exits.contains(current) {
            return unreachable_successors;
        }
        let successors = cfg
            .graph()
            .successors(current)
            .into_iter()
            .filter(|successor| !seen.contains(successor))
            .collect::<Vec<_>>();
        if let Some(join) = joins.get(current) {
            let predecessors = cfg.graph().predecessors(join);
            let mut all_unreachable = true;
            for next in successors {
                if !visit(
                    cfg,
                    &next,
                    &predecessors,
                    joins,
                    seen,
                    keep,
                    encountered,
                    unreachable_successors,
                ) {
                    all_unreachable = false;
                }
            }
            return visit(
                cfg,
                join,
                exits,
                joins,
                seen,
                keep,
                encountered,
                all_unreachable,
            );
        }
        successors.iter().all(|next| {
            visit(
                cfg,
                next,
                exits,
                joins,
                seen,
                keep,
                encountered,
                unreachable_successors,
            )
        })
    }
    visit(
        cfg,
        cfg.graph().entry(),
        &exits,
        &joins,
        &mut seen,
        &mut keep,
        &mut encountered,
        false,
    );
    Ok((keep, encountered))
}

fn preserve_rewrite(old: &Stmt, new: Stmt) -> Result<Stmt, &'static str> {
    use crate::ast::utility::nodes::Node;
    let Node::Stmt(result) = crate::ast::utility::viper_strategy::preserve_metadata(
        &Node::Stmt(old.clone()),
        &Node::Stmt(new),
        true,
    )
    .map_err(|_| "smoke rewrite metadata")?
    else {
        return Err("smoke rewrite metadata");
    };
    Ok(result)
}

/// Instrument a method body in the source strategy's top-down order. The caller
/// owns the shared program-wide counter and appends method-end probe zero separately.
pub fn instrument_body(body: &Stmt, counter: &mut i32) -> Result<Stmt, &'static str> {
    fn meta(stmt: &Stmt) -> Metadata {
        Metadata {
            position: stmt.metadata().position.clone(),
            ..Metadata::default()
        }
    }
    fn next(counter: &mut i32) -> i32 {
        *counter = counter.wrapping_add(1);
        *counter
    }
    fn visit(stmt: &Stmt, counter: &mut i32) -> Result<Stmt, &'static str> {
        let position = stmt.metadata().position.clone();
        let kind = match stmt.kind() {
            StmtKind::Inhale(exp)
                if !matches!(
                    stmt.metadata()
                        .info
                        .find(&|i| matches!(i, Info::Synthesized)),
                    Some(_)
                ) =>
            {
                let id = next(counter);
                let mut m = meta(stmt);
                m.info = Info::Synthesized;
                return preserve_rewrite(
                    stmt,
                    append_refute_false(Stmt::new(StmtKind::Inhale(exp.clone()), m), position, id),
                );
            }
            StmtKind::Goto(target)
                if !matches!(
                    stmt.metadata()
                        .info
                        .find(&|i| matches!(i, Info::Synthesized)),
                    Some(_)
                ) =>
            {
                let id = next(counter);
                let mut m = meta(stmt);
                m.info = Info::Synthesized;
                return preserve_rewrite(
                    stmt,
                    Stmt::new(
                        StmtKind::Seqn {
                            statements: vec![
                                refute_false(position.clone(), id),
                                Stmt::new(StmtKind::Goto(target.clone()), m),
                            ],
                            declarations: vec![],
                        },
                        meta(stmt),
                    ),
                );
            }
            StmtKind::While {
                condition,
                invariants,
                body,
            } => {
                let id = next(counter);
                let wrapped =
                    append_refute_false(body.clone(), body.metadata().position.clone(), id);
                StmtKind::While {
                    condition: condition.clone(),
                    invariants: invariants.clone(),
                    body: visit(&wrapped, counter)?,
                }
            }
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                fn nonempty(s: &Stmt) -> bool {
                    matches!(s.kind(), StmtKind::Seqn { statements, .. } if !statements.is_empty())
                }
                let thn = if nonempty(then_branch) {
                    append_refute_false(
                        then_branch.clone(),
                        then_branch.metadata().position.clone(),
                        next(counter),
                    )
                } else {
                    then_branch.clone()
                };
                let els = if nonempty(else_branch) {
                    append_refute_false(
                        else_branch.clone(),
                        else_branch.metadata().position.clone(),
                        next(counter),
                    )
                } else {
                    else_branch.clone()
                };
                StmtKind::If {
                    condition: condition.clone(),
                    then_branch: visit(&thn, counter)?,
                    else_branch: visit(&els, counter)?,
                }
            }
            StmtKind::Seqn {
                statements,
                declarations,
            } => StmtKind::Seqn {
                statements: statements
                    .iter()
                    .map(|s| visit(s, counter))
                    .collect::<Result<_, _>>()?,
                declarations: declarations.clone(),
            },
            StmtKind::Package { wand, proof_script } => StmtKind::Package {
                wand: wand.clone(),
                proof_script: visit(proof_script, counter)?,
            },
            StmtKind::Extension(e)
                if e.0.as_any().is::<Refute>() || e.0.as_any().is::<Unreachable>() =>
            {
                return Ok(stmt.clone());
            }
            StmtKind::Extension(extension) => {
                use crate::verifier::verification_result::DiagnosticError;
                let counter = std::cell::RefCell::new(counter);
                let failure = std::cell::RefCell::new(None);
                let mapped = extension.0.map_statements(&|child| {
                    visit(child, &mut counter.borrow_mut()).map_err(|error| {
                        *failure.borrow_mut() = Some(error);
                        DiagnosticError::Unsupported("smoke statement rewrite")
                    })
                });
                if let Some(error) = failure.into_inner() {
                    return Err(error);
                }
                return match mapped.map_err(|_| "unsupported extension statement traversal")? {
                    Some(mapped) if mapped != *extension => Ok(Stmt::new(
                        StmtKind::Extension(mapped),
                        stmt.metadata().clone(),
                    )),
                    _ => Ok(stmt.clone()),
                };
            }
            _ => return Ok(stmt.clone()),
        };
        let m = if matches!(stmt.kind(), StmtKind::If { .. } | StmtKind::While { .. }) {
            meta(stmt)
        } else {
            stmt.metadata().clone()
        };
        if &kind == stmt.kind()
            && !matches!(stmt.kind(), StmtKind::If { .. } | StmtKind::While { .. })
        {
            Ok(stmt.clone())
        } else if matches!(stmt.kind(), StmtKind::If { .. } | StmtKind::While { .. }) {
            preserve_rewrite(stmt, Stmt::new(kind, m))
        } else {
            Ok(Stmt::new(kind, m))
        }
    }
    visit(body, counter)
}

/// Apply smoke instrumentation and CFG-based removal to every method. Errors in
/// CFG construction or extension traversal abort the transformation.
pub fn instrument_program(
    program: &crate::ast::program::Program,
) -> Result<crate::ast::program::Program, &'static str> {
    use crate::cfg::silver::cfg_generator::method_to_cfg;
    fn remove(stmt: &Stmt, keep: &[i32], seen: &[i32]) -> Result<Stmt, &'static str> {
        let empty = || {
            Stmt::new(
                StmtKind::Seqn {
                    statements: vec![],
                    declarations: vec![],
                },
                Metadata {
                    position: stmt.metadata().position.clone(),
                    ..Metadata::default()
                },
            )
        };
        let kind = match stmt.kind() {
            StmtKind::Extension(ext) if ext.0.as_any().is::<Unreachable>() => {
                return preserve_rewrite(stmt, empty());
            }
            StmtKind::Extension(ext) if ext.0.as_any().is::<Refute>() => {
                if let Some(info) = stmt.metadata().info.find_extension::<SmokeDetectionInfo>() {
                    if !keep.contains(&info.id) && seen.contains(&info.id) {
                        return preserve_rewrite(stmt, empty());
                    }
                }
                return Ok(stmt.clone());
            }
            StmtKind::Extension(extension) => {
                use crate::verifier::verification_result::DiagnosticError;
                let failure = std::cell::RefCell::new(None);
                let mapped = extension.0.map_statements(&|child| {
                    remove(child, keep, seen).map_err(|error| {
                        *failure.borrow_mut() = Some(error);
                        DiagnosticError::Unsupported("smoke statement removal")
                    })
                });
                if let Some(error) = failure.into_inner() {
                    return Err(error);
                }
                return match mapped.map_err(|_| "unsupported extension statement traversal")? {
                    Some(mapped) if mapped != *extension => Ok(Stmt::new(
                        StmtKind::Extension(mapped),
                        stmt.metadata().clone(),
                    )),
                    _ => Ok(stmt.clone()),
                };
            }
            StmtKind::Seqn {
                statements,
                declarations,
            } => StmtKind::Seqn {
                statements: statements
                    .iter()
                    .map(|s| remove(s, keep, seen))
                    .collect::<Result<_, _>>()?,
                declarations: declarations.clone(),
            },
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => StmtKind::If {
                condition: condition.clone(),
                then_branch: remove(then_branch, keep, seen)?,
                else_branch: remove(else_branch, keep, seen)?,
            },
            StmtKind::While {
                condition,
                invariants,
                body,
            } => StmtKind::While {
                condition: condition.clone(),
                invariants: invariants.clone(),
                body: remove(body, keep, seen)?,
            },
            StmtKind::Package { wand, proof_script } => StmtKind::Package {
                wand: wand.clone(),
                proof_script: remove(proof_script, keep, seen)?,
            },
            _ => return Ok(stmt.clone()),
        };
        if &kind == stmt.kind() {
            Ok(stmt.clone())
        } else {
            Ok(Stmt::new(kind, stmt.metadata().clone()))
        }
    }
    let mut counter = 0;
    let mut methods = Vec::with_capacity(program.methods.len());
    for method in &program.methods {
        let body = match &method.body {
            Some(body) => {
                let end = refute_false(method.meta.position.clone(), 0);
                let initial = Stmt::new(
                    StmtKind::Seqn {
                        statements: vec![body.clone(), end],
                        declarations: vec![],
                    },
                    Metadata {
                        position: method.meta.position.clone(),
                        ..Metadata::default()
                    },
                );
                Some(instrument_body(&initial, &mut counter)?)
            }
            None => None,
        };
        methods.push(method.copy_with(|m| m.body = body));
    }
    for method in &mut methods {
        let cfg = method_to_cfg(method, false, true).map_err(|_| "smoke CFG generation")?;
        let (keep, seen) = collect_refutes_to_keep(&cfg).map_err(|_| "smoke CFG join points")?;
        if let Some(body) = &method.body {
            let body = remove(body, &keep, &seen)?;
            *method = method.copy_with(|m| m.body = Some(body));
        }
    }
    Ok(program.copy_with(|p| p.methods = methods))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfg::silver::silver_cfg::SilverBlock;
    #[test]
    fn instrumentation_keeps_end_and_inhale_probes() {
        use crate::parser::{
            fast_parser::parse_program,
            resolver::{NameAnalyser, check_program_core},
            translator::translate_program_core,
        };
        let parsed = parse_program("method m() { inhale true; }", "test.vpr").unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        let result = instrument_program(&program).unwrap();
        let cfg = crate::cfg::silver::cfg_generator::method_to_cfg(&result.methods[0], false, true)
            .unwrap();
        let (keep, _) = collect_refutes_to_keep(&cfg).unwrap();
        assert_eq!(keep, vec![1, 0]);
    }
    #[test]
    fn unreachable_marker_excludes_later_refutes_but_still_records_them() {
        let block = SilverBlock::statement(vec![
            refute_false(Position::NoPosition, 1),
            Unreachable {
                meta: Metadata::default(),
            }
            .statement(),
            refute_false(Position::NoPosition, 2),
        ]);
        let cfg = SilverCfg::new(vec![block.clone()], vec![], block.clone(), Some(block));
        assert_eq!(
            collect_refutes_to_keep(&cfg).unwrap(),
            (vec![1], vec![1, 2])
        );
    }
}

/// Runtime smoke transformation. Register refute after this plugin to consume probes.
pub struct SmokeDetectionPlugin;
impl crate::plugin::silver_plugin::SilverPlugin for SmokeDetectionPlugin {
    fn shared_entity_mapper(
        &self,
    ) -> Option<std::sync::Arc<dyn crate::reporter::reporter::EntityResultMapper>> {
        Some(crate::plugin::silver_plugin_manager::identity_entity_mapper())
    }

    fn parser_features(&self) -> Vec<crate::parser::fast_parser::ParserFeature> {
        vec![crate::parser::fast_parser::ParserFeature::Unreachable]
    }
    fn before_verify(
        &mut self,
        program: crate::ast::program::Program,
    ) -> Result<crate::ast::program::Program, crate::plugin::silver_plugin::PluginHookError> {
        instrument_program(&program)
            .map_err(|e| crate::plugin::silver_plugin::PluginHookError(e.into()))
    }
}
