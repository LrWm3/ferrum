//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/arp/ARPPlugin.scala
//!
//! Purpose:
//! Encode supported abstract read permissions in method contracts, calls and loops.
//!
//! Planned Rust structure:
//! Port ARPPlugin rdPerm, beforeParse/beforeVerify, checkSupported/misplacedRd, rdBounds,
//! replaceRd, rdConstraint, transformBody and FreshNames.
//!
//! Behavior to preserve:
//! The opt-in plugin adds rd keyword and expression parser. Reject occurrences outside methods,
//! inside magic wands or not directly an access-predicate amount before transforming. Add a
//! bounded fresh permission parameter to each method using rd; replace contract/body uses. For
//! calls instantiate callee preconditions and inhale bounds plus conditional current-permission
//! constraints before passing a fresh argument; loops similarly get fresh bounded permissions,
//! rewritten invariants/body and mapped invariant errors. Recurse through conjunction,
//! implication, conditionals, let, forall and exhale side of inhale-exhale, autotriggering
//! untriggered forall. Preserve synthesized metadata, error transformations and fresh-name
//! collision order.
//!
//! Integration:
//! parser::fast_parser; arp AST/PAST extensions, ast::utility::{expressions,rewriter}, verifier
//! errors and frontend plugin ordering.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact permissions, AST metadata, ordering and native plugin
//! registration.
//!
//! Open decisions:
//! Reconcile contextual traversal, generated names and error backtranslation with ast rewriter and
//! verifier.
//!
//! Status: partial; supported rd validation, fresh method parameters, bounds and contract/body
//! replacement, loop obligations and call obligations with capture-safe instantiation are
//! implemented. Unsupported extension traversal and unsupported trigger generation fail explicitly.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.

use super::arpast_extension::RdPerm;
use crate::ast::ast::Metadata;
use crate::ast::expression::{Exp, ExpKind, ExtensionExpHandle, LocalVar};
use crate::ast::program::{LocalVarDecl, Member, Program};
use crate::ast::statement::StmtKind;
use crate::ast::r#type::Type;
use crate::ast::utility::nodes::{
    Node, NodeReplacementError, map_expression_roots_with_extensions, subnodes,
};
use crate::ast::utility::rewriter::strategy::{
    ExpressionRewriteError, rewrite_expression_bottom_up,
};
use crate::ast::utility::statements::StatementReplacementError;
use crate::plugin::silver_plugin::{PluginHookError, SilverPlugin};
use std::collections::{HashMap, HashSet};

#[derive(Debug)]
pub enum ArpError {
    Unsupported(&'static str),
    Traversal,
    Reconstruction,
}
impl From<NodeReplacementError> for ArpError {
    fn from(_: NodeReplacementError) -> Self {
        Self::Reconstruction
    }
}
impl From<StatementReplacementError> for ArpError {
    fn from(_: StatementReplacementError) -> Self {
        Self::Reconstruction
    }
}
fn is_rd(exp: &Exp) -> bool {
    matches!(exp.kind(), ExpKind::Extension(e) if e.0.as_any().is::<RdPerm>())
}
fn contains_rd(node: &Node) -> Result<bool, ArpError> {
    if matches!(node, Node::Exp(exp) if is_rd(exp)) {
        return Ok(true);
    }
    for child in subnodes(node).map_err(|_| ArpError::Traversal)? {
        if contains_rd(&child)? {
            return Ok(true);
        }
    }
    Ok(false)
}
/// Validate the source's direct-permission rule and its magic-wand exclusion.
fn validate_method(node: &Node, in_wand: bool) -> Result<(), ArpError> {
    if let Node::Exp(exp) = node {
        if is_rd(exp) {
            return Err(ArpError::Unsupported(if in_wand {
                "rd cannot be used inside magic wands"
            } else {
                "rd must be a direct access-predicate permission"
            }));
        }
        if let ExpKind::MagicWand(..) = exp.kind() {
            for child in subnodes(node).map_err(|_| ArpError::Traversal)? {
                validate_method(&child, true)?;
            }
            return Ok(());
        }
        if let ExpKind::FieldAccessPredicate(location, Some(permission)) = exp.kind() {
            if is_rd(permission) {
                if in_wand {
                    return Err(ArpError::Unsupported(
                        "rd cannot be used inside magic wands",
                    ));
                }
                return validate_method(&Node::FieldAccess(location.clone()), in_wand);
            }
        }
        if let ExpKind::PredicateAccessPredicate(access) = exp.kind() {
            if access.permission.as_ref().is_some_and(is_rd) {
                if in_wand {
                    return Err(ArpError::Unsupported(
                        "rd cannot be used inside magic wands",
                    ));
                }
                return validate_method(&Node::PredicateAccess(access.location.clone()), in_wand);
            }
        }
    }
    if let Node::PredicateAccessPredicate(access) = node {
        if access.permission.as_ref().is_some_and(is_rd) {
            if in_wand {
                return Err(ArpError::Unsupported(
                    "rd cannot be used inside magic wands",
                ));
            }
            return validate_method(&Node::PredicateAccess(access.location.clone()), in_wand);
        }
    }
    for child in subnodes(node).map_err(|_| ArpError::Traversal)? {
        validate_method(&child, in_wand)?;
    }
    Ok(())
}
#[derive(Default)]
struct FreshNames {
    taken: HashSet<String>,
}
impl FreshNames {
    fn fresh(&mut self, base: &str) -> String {
        if self.taken.insert(base.to_owned()) {
            return base.into();
        }
        let mut i = 0i32;
        loop {
            let candidate = format!("{base}_{i}");
            if self.taken.insert(candidate.clone()) {
                return candidate;
            }
            i = i.wrapping_add(1);
        }
    }
}
fn used_names(node: &Node, names: &mut HashSet<String>) -> Result<(), ArpError> {
    match node {
        Node::Member(member) => {
            names.insert(member.name().to_owned());
        }
        Node::DomainFunc(f) => {
            names.insert(f.name.clone());
        }
        Node::LocalDecl(d) => {
            names.insert(d.name.clone());
        }
        Node::LabelDecl(d) => {
            names.insert(d.name.clone());
        }
        Node::LocalVar(v) => {
            names.insert(v.name.clone());
        }
        _ => {}
    }
    for child in subnodes(node).map_err(|_| ArpError::Traversal)? {
        used_names(&child, names)?;
    }
    Ok(())
}
fn rd_bounds(rd: &LocalVar) -> Exp {
    let meta = Metadata {
        position: rd.meta.position.clone(),
        ..Metadata::default()
    };
    let local = || Exp::new(ExpKind::LocalVar(rd.clone()), rd.meta.clone());
    let low = Exp::new(
        ExpKind::PermLtCmp(Exp::new(ExpKind::NoPerm, meta.clone()), local()),
        meta.clone(),
    );
    let high = Exp::new(
        ExpKind::PermLtCmp(local(), Exp::new(ExpKind::FullPerm, meta.clone())),
        meta.clone(),
    );
    Exp::new(ExpKind::And(low, high), meta)
}
fn replace_rd_expression(root: &Exp, rd: &LocalVar) -> Result<Exp, ArpError> {
    let extension =
        |handle: &ExtensionExpHandle,
         _: &mut dyn FnMut(&Exp) -> Result<Exp, ExpressionRewriteError<ArpError>>| {
            if handle.0.as_any().is::<RdPerm>() {
                Ok(handle.clone())
            } else {
                Err(ExpressionRewriteError::Callback(ArpError::Unsupported(
                    "ARP expression extension traversal",
                )))
            }
        };
    let mut rule = |exp: &Exp| -> Result<Exp, ArpError> {
        if !is_rd(exp) {
            return Ok(exp.clone());
        }
        let mut meta = exp.metadata().clone();
        meta.error_trafo = crate::ast::ast::ErrorTrafo::default();
        let replacement = Exp::new(
            ExpKind::LocalVar(LocalVar::new(rd.name.clone(), Type::Perm, meta)),
            exp.metadata().clone(),
        );
        let Node::Exp(result) = crate::ast::utility::viper_strategy::preserve_metadata(
            &Node::Exp(exp.clone()),
            &Node::Exp(replacement),
            true,
        )
        .map_err(|_| ArpError::Reconstruction)?
        else {
            return Err(ArpError::Reconstruction);
        };
        Ok(result)
    };
    rewrite_expression_bottom_up(root, &mut rule, &extension).map_err(|e| match e {
        ExpressionRewriteError::Callback(e) => e,
        _ => ArpError::Reconstruction,
    })
}

/// Build the source conditional permission bound for a callee precondition or
/// loop invariant. Pure unfolding/asserting contexts intentionally contribute none.
pub fn rd_constraint(expression: &Exp, rd: &LocalVar) -> Result<Option<Exp>, ArpError> {
    fn position_info(exp: &Exp) -> Metadata {
        Metadata {
            position: exp.metadata().position.clone(),
            info: exp.metadata().info.clone(),
            ..Metadata::default()
        }
    }
    fn rec(exp: &Exp, rd: &LocalVar) -> Result<Option<Exp>, ArpError> {
        let meta = position_info(exp);
        Ok(match exp.kind() {
            ExpKind::And(left, right) => match (rec(left, rd)?, rec(right, rd)?) {
                (Some(a), Some(b)) => Some(Exp::new(ExpKind::And(a, b), meta)),
                (Some(a), None) => Some(a),
                (None, Some(b)) => Some(b),
                _ => None,
            },
            ExpKind::Implies(condition, right) => {
                rec(right, rd)?.map(|r| Exp::new(ExpKind::Implies(condition.clone(), r), meta))
            }
            ExpKind::CondExp(condition, thn, els) => match (rec(thn, rd)?, rec(els, rd)?) {
                (None, None) => None,
                (a, b) => Some(Exp::new(
                    ExpKind::CondExp(
                        condition.clone(),
                        a.unwrap_or_else(|| {
                            Exp::new(
                                ExpKind::TrueLit,
                                Metadata {
                                    position: thn.metadata().position.clone(),
                                    ..Metadata::default()
                                },
                            )
                        }),
                        b.unwrap_or_else(|| {
                            Exp::new(
                                ExpKind::TrueLit,
                                Metadata {
                                    position: els.metadata().position.clone(),
                                    ..Metadata::default()
                                },
                            )
                        }),
                    ),
                    meta,
                )),
            },
            ExpKind::Let(variable, value, body) => rec(body, rd)?
                .map(|b| Exp::new(ExpKind::Let(variable.clone(), value.clone(), b), meta)),
            ExpKind::Forall(variables, triggers, body) => {
                if let Some(body) = rec(body, rd)? {
                    let quantifier = Exp::new(
                        ExpKind::Forall(variables.clone(), triggers.clone(), body),
                        meta,
                    );
                    Some(if triggers.is_empty() {
                        crate::ast::utility::triggers::auto_trigger(&quantifier).map_err(|_| {
                            ArpError::Unsupported("ARP quantifier trigger generation")
                        })?
                    } else {
                        quantifier
                    })
                } else {
                    None
                }
            }
            ExpKind::InhaleExhaleExp(_, exhale) => rec(exhale, rd)?,
            ExpKind::FieldAccessPredicate(location, Some(permission)) if is_rd(permission) => {
                let loc = Exp::new(
                    ExpKind::FieldAccess(location.clone()),
                    location.meta.clone(),
                );
                Some(bound_at_location(exp, loc, rd))
            }
            ExpKind::PredicateAccessPredicate(access)
                if access.permission.as_ref().is_some_and(is_rd) =>
            {
                let loc = Exp::new(
                    ExpKind::PredicateAccess(access.location.clone()),
                    access.location.meta.clone(),
                );
                Some(bound_at_location(exp, loc, rd))
            }
            _ => None,
        })
    }
    fn bound_at_location(source: &Exp, loc: Exp, rd: &LocalVar) -> Exp {
        let loc_meta = Metadata {
            position: loc.metadata().position.clone(),
            ..Metadata::default()
        };
        let perm = Exp::new(ExpKind::CurrentPerm(loc), loc_meta.clone());
        let nonzero = Exp::new(
            ExpKind::PermLtCmp(Exp::new(ExpKind::NoPerm, loc_meta.clone()), perm.clone()),
            loc_meta.clone(),
        );
        let bound = Exp::new(
            ExpKind::PermLtCmp(
                Exp::new(ExpKind::LocalVar(rd.clone()), rd.meta.clone()),
                perm,
            ),
            loc_meta,
        );
        Exp::new(
            ExpKind::Implies(nonzero, bound),
            Metadata {
                position: source.metadata().position.clone(),
                info: source.metadata().info.clone(),
                ..Metadata::default()
            },
        )
    }
    rec(expression, rd)?
        .map(|constraint| replace_rd_expression(&constraint, rd))
        .transpose()
}

#[derive(Debug)]
struct LoopInvariantErrorTrafo {
    invariant: Exp,
}
impl crate::ast::ast::ErrorTransformation for LoopInvariantErrorTrafo {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn transform_error(
        &self,
        diagnostic: &std::sync::Arc<
            dyn crate::verifier::verification_result::VerificationDiagnostic,
        >,
    ) -> Result<
        Option<std::sync::Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        use crate::verifier::verification_error::{
            RenderedVerificationError, VerificationError, VerificationErrorKind,
        };
        let Some(original) = diagnostic
            .as_any()
            .downcast_ref::<RenderedVerificationError>()
        else {
            return Ok(None);
        };
        if !matches!(
            original.error().kind,
            VerificationErrorKind::InhaleFailed(_)
        ) {
            return Ok(None);
        }
        let mut error = VerificationError::new(
            VerificationErrorKind::LoopInvariantNotEstablished(self.invariant.clone()),
            original.error().reason.clone(),
        );
        error.cached = original.error().cached;
        Ok(Some(std::sync::Arc::new(RenderedVerificationError::new(
            error,
            original.renderer(),
        )?)))
    }
}
#[derive(Debug)]
struct CallPreconditionErrorTrafo {
    call: crate::ast::statement::Stmt,
}
impl crate::ast::ast::ErrorTransformation for CallPreconditionErrorTrafo {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn transform_error(
        &self,
        diagnostic: &std::sync::Arc<
            dyn crate::verifier::verification_result::VerificationDiagnostic,
        >,
    ) -> Result<
        Option<std::sync::Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        use crate::verifier::verification_error::{
            RenderedVerificationError, VerificationError, VerificationErrorKind,
        };
        let Some(original) = diagnostic
            .as_any()
            .downcast_ref::<RenderedVerificationError>()
        else {
            return Ok(None);
        };
        if !matches!(
            original.error().kind,
            VerificationErrorKind::InhaleFailed(_)
        ) {
            return Ok(None);
        }
        let mut error = VerificationError::new(
            VerificationErrorKind::PreconditionInCallFalse(self.call.clone()),
            original.error().reason.clone(),
        );
        error.cached = original.error().cached;
        Ok(Some(std::sync::Arc::new(RenderedVerificationError::new(
            error,
            original.renderer(),
        )?)))
    }
}

fn synthesized(position: &crate::ast::position::Position) -> Metadata {
    Metadata {
        position: position.clone(),
        info: crate::ast::ast::Info::Synthesized,
        ..Metadata::default()
    }
}
fn transform_body(
    statement: &crate::ast::statement::Stmt,
    rd: Option<&LocalVar>,
    names: &mut FreshNames,
    program: &Program,
    params: &HashMap<String, String>,
) -> Result<crate::ast::statement::Stmt, ArpError> {
    use crate::ast::statement::Stmt;
    let node = Node::Stmt(statement.clone());
    match statement.kind() {
        StmtKind::Seqn {
            statements,
            declarations,
        } => {
            let statements = statements
                .iter()
                .map(|s| transform_body(s, rd, names, program, params))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Stmt::new(
                StmtKind::Seqn {
                    statements,
                    declarations: declarations.clone(),
                },
                statement.metadata().clone(),
            ))
        }
        StmtKind::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let condition = match rd {
                Some(rd) => replace_rd_expression(condition, rd)?,
                None => condition.clone(),
            };
            let then_branch = transform_body(then_branch, rd, names, program, params)?;
            let else_branch = transform_body(else_branch, rd, names, program, params)?;
            Ok(Stmt::new(
                StmtKind::If {
                    condition,
                    then_branch,
                    else_branch,
                },
                statement.metadata().clone(),
            ))
        }
        StmtKind::MethodCall {
            method_name,
            args,
            targets,
        } if params.contains_key(method_name) => {
            let callee = program
                .methods
                .iter()
                .find(|m| m.name == *method_name)
                .ok_or(ArpError::Unsupported("unknown ARP callee"))?;
            let position = statement.metadata().position.clone();
            let call_meta = Metadata {
                position: position.clone(),
                ..Metadata::default()
            };
            let call_rd = LocalVar::new(
                names.fresh(&format!("{method_name}_call_rd")),
                Type::Perm,
                call_meta.clone(),
            );
            fn locals(node: &Node, scope: &mut HashSet<String>) -> Result<(), ArpError> {
                match node {
                    Node::LocalVar(v) => {
                        scope.insert(v.name.clone());
                    }
                    Node::Exp(exp) => {
                        if let ExpKind::LocalVar(v) = exp.kind() {
                            scope.insert(v.name.clone());
                        }
                    }
                    _ => {}
                }
                for child in subnodes(node).map_err(|_| ArpError::Traversal)? {
                    locals(&child, scope)?;
                }
                Ok(())
            }
            let mut scope = HashSet::from([call_rd.name.clone()]);
            for arg in args {
                locals(&Node::Exp(arg.clone()), &mut scope)?;
            }
            let mut prefix = vec![Stmt::new(
                StmtKind::Inhale(rd_bounds(&call_rd)),
                synthesized(&position),
            )];
            for pre in &callee.pres {
                let instantiated = crate::ast::utility::expressions::instantiate_variables(
                    pre,
                    &callee.formal_args,
                    args,
                    &scope,
                )
                .map_err(|_| ArpError::Unsupported("ARP call precondition instantiation"))?;
                if let Some(constraint) = rd_constraint(&instantiated, &call_rd)? {
                    let mut meta = synthesized(&position);
                    meta.error_trafo = crate::ast::ast::ErrorTrafo::trafos(
                        vec![std::sync::Arc::new(CallPreconditionErrorTrafo {
                            call: statement.clone(),
                        })],
                        vec![],
                        None,
                    );
                    prefix.push(Stmt::new(StmtKind::Inhale(constraint), meta));
                }
            }
            let mut actuals = args.clone();
            actuals.push(Exp::new(
                ExpKind::LocalVar(call_rd.clone()),
                call_rd.meta.clone(),
            ));
            let mut meta = statement.metadata().clone();
            let backlink = crate::ast::ast::ErrorTrafo::trafos(
                vec![],
                vec![],
                Some(std::sync::Arc::new(crate::ast::ast::PreviousNode(
                    node.clone(),
                ))),
            );
            meta.error_trafo = meta.error_trafo.combine(&backlink);
            prefix.push(Stmt::new(
                StmtKind::MethodCall {
                    method_name: method_name.clone(),
                    args: actuals,
                    targets: targets.clone(),
                },
                meta,
            ));
            let result =
                Stmt::new(
                    StmtKind::Seqn {
                        statements: prefix,
                        declarations: vec![crate::ast::program::Declaration::Local(
                            LocalVarDecl::new(call_rd.name.clone(), Type::Perm, call_meta),
                        )],
                    },
                    synthesized(&position),
                );
            let Node::Stmt(result) = crate::ast::utility::viper_strategy::preserve_metadata(
                &node,
                &Node::Stmt(result),
                true,
            )
            .map_err(|_| ArpError::Reconstruction)?
            else {
                return Err(ArpError::Reconstruction);
            };
            Ok(result)
        }
        StmtKind::Package { wand, proof_script } => {
            let wand = match rd {
                Some(rd) => replace_rd_expression(wand, rd)?,
                None => wand.clone(),
            };
            let proof_script = transform_body(proof_script, rd, names, program, params)?;
            Ok(Stmt::new(
                StmtKind::Package { wand, proof_script },
                statement.metadata().clone(),
            ))
        }
        StmtKind::While {
            condition,
            invariants,
            body,
        } if contains_rd(&node)? => {
            if contains_rd(&Node::Exp(condition.clone()))? {
                return Err(ArpError::Unsupported("rd in loop condition"));
            }
            let position = statement.metadata().position.clone();
            let rd_meta = Metadata {
                position: position.clone(),
                ..Metadata::default()
            };
            let loop_rd = LocalVar::new(names.fresh("loop_rd"), Type::Perm, rd_meta.clone());
            let mut prefix = vec![Stmt::new(
                StmtKind::Inhale(rd_bounds(&loop_rd)),
                synthesized(&position),
            )];
            for invariant in invariants {
                if let Some(constraint) = rd_constraint(invariant, &loop_rd)? {
                    let mut meta = synthesized(&position);
                    meta.error_trafo = crate::ast::ast::ErrorTrafo::trafos(
                        vec![std::sync::Arc::new(LoopInvariantErrorTrafo {
                            invariant: invariant.clone(),
                        })],
                        vec![],
                        None,
                    );
                    prefix.push(Stmt::new(StmtKind::Inhale(constraint), meta));
                }
            }
            let invariants = invariants
                .iter()
                .map(|inv| replace_rd_expression(inv, &loop_rd))
                .collect::<Result<Vec<_>, _>>()?;
            let body = transform_body(body, Some(&loop_rd), names, program, params)?;
            let loop_stmt = Stmt::new(
                StmtKind::While {
                    condition: condition.clone(),
                    invariants,
                    body,
                },
                statement.metadata().clone(),
            );
            prefix.push(loop_stmt);
            let result =
                Stmt::new(
                    StmtKind::Seqn {
                        statements: prefix,
                        declarations: vec![crate::ast::program::Declaration::Local(
                            LocalVarDecl::new(loop_rd.name.clone(), Type::Perm, rd_meta),
                        )],
                    },
                    synthesized(&position),
                );
            let Node::Stmt(result) = crate::ast::utility::viper_strategy::preserve_metadata(
                &node,
                &Node::Stmt(result),
                true,
            )
            .map_err(|_| ArpError::Reconstruction)?
            else {
                return Err(ArpError::Reconstruction);
            };
            Ok(result)
        }
        StmtKind::While {
            condition,
            invariants,
            body,
        } => {
            let condition = match rd {
                Some(rd) => replace_rd_expression(condition, rd)?,
                None => condition.clone(),
            };
            let invariants = match rd {
                Some(rd) => invariants
                    .iter()
                    .map(|e| replace_rd_expression(e, rd))
                    .collect::<Result<_, _>>()?,
                None => invariants.clone(),
            };
            let body = transform_body(body, rd, names, program, params)?;
            Ok(Stmt::new(
                StmtKind::While {
                    condition,
                    invariants,
                    body,
                },
                statement.metadata().clone(),
            ))
        }
        StmtKind::Extension(extension) => {
            use crate::verifier::verification_result::DiagnosticError;
            let failure = std::cell::RefCell::new(None);
            let expressions = if let Some(rd) = rd {
                let mapped = extension.0.map_expressions(&|root| {
                    replace_rd_expression(root, rd).map_err(|error| {
                        *failure.borrow_mut() = Some(error);
                        DiagnosticError::Unsupported("ARP extension expression rewrite")
                    })
                });
                if let Some(error) = failure.borrow_mut().take() {
                    return Err(error);
                }
                mapped.map_err(|_| {
                    ArpError::Unsupported("ARP statement extension expression traversal")
                })?
            } else {
                extension.clone()
            };
            if let Some(error) = failure.borrow_mut().take() {
                return Err(error);
            }
            let names = std::cell::RefCell::new(names);
            let mapped = expressions.0.map_statements(&|child| {
                transform_body(child, rd, &mut names.borrow_mut(), program, params).map_err(
                    |error| {
                        *failure.borrow_mut() = Some(error);
                        DiagnosticError::Unsupported("ARP extension statement rewrite")
                    },
                )
            });
            if let Some(error) = failure.into_inner() {
                return Err(error);
            }
            let mapped = mapped
                .map_err(|_| ArpError::Unsupported("ARP statement extension traversal"))?
                .unwrap_or(expressions);
            Ok(Stmt::new(
                StmtKind::Extension(mapped),
                statement.metadata().clone(),
            ))
        }
        _ => {
            let Some(rd) = rd else {
                return Ok(statement.clone());
            };
            let replace = |root: &Exp| replace_rd_expression(root, rd);
            let extension =
                |_: &crate::ast::statement::ExtensionStmtHandle,
                 _: &dyn Fn(&Exp) -> Result<Exp, ArpError>|
                 -> Result<crate::ast::statement::ExtensionStmtHandle, ArpError> {
                    Err(ArpError::Unsupported("ARP statement extension traversal"))
                };
            let Node::Stmt(result) =
                map_expression_roots_with_extensions(&node, &replace, &extension)?
            else {
                return Err(ArpError::Reconstruction);
            };
            Ok(result)
        }
    }
}

/// Encode supported method, call and loop uses of abstract read permissions.
pub fn encode_arp(program: &Program) -> Result<Program, ArpError> {
    if !contains_rd(&Node::Program(program.clone()))? {
        return Ok(program.clone());
    }
    for member in program
        .domains
        .iter()
        .cloned()
        .map(Member::Domain)
        .chain(program.fields.iter().cloned().map(Member::Field))
        .chain(program.functions.iter().cloned().map(Member::Function))
        .chain(program.predicates.iter().cloned().map(Member::Predicate))
        .chain(program.extensions.iter().cloned().map(Member::Extension))
    {
        if contains_rd(&Node::Member(member))? {
            return Err(ArpError::Unsupported("rd can only be used in methods"));
        }
    }
    let mut names = FreshNames::default();
    used_names(&Node::Program(program.clone()), &mut names.taken)?;
    let mut parameters = HashMap::new();
    for method in &program.methods {
        let node = Node::Member(Member::Method(method.clone()));
        validate_method(&node, false)?;
        if contains_rd(&node)? {
            parameters.insert(
                method.name.clone(),
                names.fresh(&format!("{}_rd", method.name)),
            );
        }
    }
    let mut methods = Vec::with_capacity(program.methods.len());
    for method in &program.methods {
        let Some(name) = parameters.get(&method.name) else {
            let body = method
                .body
                .as_ref()
                .map(|body| transform_body(body, None, &mut names, program, &parameters))
                .transpose()?;
            methods.push(method.copy_with(|method| method.body = body));
            continue;
        };
        let rd_meta = Metadata {
            position: method.meta.position.clone(),
            ..Metadata::default()
        };
        let rd = LocalVar::new(name.clone(), Type::Perm, rd_meta.clone());
        let pres = method
            .pres
            .iter()
            .map(|e| replace_rd_expression(e, &rd))
            .collect::<Result<Vec<_>, _>>()?;
        let posts = method
            .posts
            .iter()
            .map(|e| replace_rd_expression(e, &rd))
            .collect::<Result<Vec<_>, _>>()?;
        let body = method
            .body
            .as_ref()
            .map(|body| transform_body(body, Some(&rd), &mut names, program, &parameters))
            .transpose()?;
        let rewritten = method.copy_with(|m| {
            m.pres = pres;
            m.posts = posts;
            m.body = body;
        });
        let bounds = rd_bounds(&rd);
        methods.push(rewritten.copy_with(|m| {
            m.formal_args
                .push(LocalVarDecl::new(name.clone(), Type::Perm, rd_meta));
            m.pres.insert(0, bounds);
        }));
    }
    Ok(program.copy_with(|p| p.methods = methods))
}
#[derive(Default)]
pub struct ArpPlugin {
    errors: Vec<crate::verifier::verification_result::AbstractError>,
}
impl ArpPlugin {
    pub fn new() -> Self {
        Self::default()
    }
}

/// Mirror ARPPlugin.checkSupported, including the two independent method passes.
fn arp_supported_errors(
    program: &Program,
) -> Result<Vec<crate::verifier::verification_result::AbstractError>, ArpError> {
    use crate::verifier::verification_result::{AbstractError, FrontendError, FrontendErrorKind};
    fn rd_in(node: &Node, out: &mut Vec<Exp>) -> Result<(), ArpError> {
        if let Node::Exp(exp) = node {
            if is_rd(exp) {
                out.push(exp.clone());
            }
        }
        for child in subnodes(node).map_err(|_| ArpError::Traversal)? {
            rd_in(&child, out)?;
        }
        Ok(())
    }
    fn wand_rd(node: &Node, out: &mut Vec<Exp>) -> Result<(), ArpError> {
        if matches!(node, Node::Exp(exp) if matches!(exp.kind(), ExpKind::MagicWand(..))) {
            rd_in(node, out)?;
        }
        for child in subnodes(node).map_err(|_| ArpError::Traversal)? {
            wand_rd(&child, out)?;
        }
        Ok(())
    }
    fn misplaced(node: &Node, out: &mut Vec<Exp>) -> Result<(), ArpError> {
        if let Node::Exp(exp) = node {
            if is_rd(exp) {
                out.push(exp.clone());
                return Ok(());
            }
            match exp.kind() {
                ExpKind::FieldAccessPredicate(location, Some(permission)) if is_rd(permission) => {
                    return misplaced(&Node::FieldAccess(location.clone()), out);
                }
                ExpKind::PredicateAccessPredicate(access)
                    if access.permission.as_ref().is_some_and(is_rd) =>
                {
                    return misplaced(&Node::PredicateAccess(access.location.clone()), out);
                }
                _ => {}
            }
        }
        if let Node::PredicateAccessPredicate(access) = node {
            if access.permission.as_ref().is_some_and(is_rd) {
                return misplaced(&Node::PredicateAccess(access.location.clone()), out);
            }
        }
        for child in subnodes(node).map_err(|_| ArpError::Traversal)? {
            misplaced(&child, out)?;
        }
        Ok(())
    }
    let mut errors = Vec::new();
    let mut report = |items: Vec<Exp>, reason: &str| {
        for exp in items {
            errors.push(AbstractError::Frontend(FrontendError::new(
                FrontendErrorKind::ConsistencyError(format!(
                    "Unsupported use of abstract read permission rd: {reason}"
                )),
                exp.metadata().position.clone(),
            )));
        }
    };
    for member in program.members() {
        let method = matches!(member, Member::Method(_));
        let node = Node::Member(member);
        if method {
            let mut items = Vec::new();
            wand_rd(&node, &mut items)?;
            report(items, "rd cannot be used inside magic wands.");
            let mut items = Vec::new();
            misplaced(&node, &mut items)?;
            report(
                items,
                "rd can only be used directly as the permission amount of an access predicate, e.g., acc(x.f, rd).",
            );
        } else {
            let mut items = Vec::new();
            rd_in(&node, &mut items)?;
            report(
                items,
                "rd can only be used in methods, not in functions, predicates, or domains.",
            );
        }
    }
    Ok(errors)
}
impl SilverPlugin for ArpPlugin {
    fn shared_entity_mapper(
        &self,
    ) -> Option<std::sync::Arc<dyn crate::reporter::reporter::EntityResultMapper>> {
        Some(crate::plugin::silver_plugin_manager::identity_entity_mapper())
    }

    fn parser_features(&self) -> Vec<crate::parser::fast_parser::ParserFeature> {
        vec![crate::parser::fast_parser::ParserFeature::Arp]
    }
    fn errors(&self) -> &[crate::verifier::verification_result::AbstractError] {
        &self.errors
    }
    fn before_parse(&mut self, input: String, imported: bool) -> String {
        if !imported {
            self.errors.clear();
        }
        input
    }
    fn before_verify(&mut self, input: Program) -> Result<Program, PluginHookError> {
        self.errors = arp_supported_errors(&input)
            .map_err(|e| PluginHookError(format!("ARP validation: {e:?}")))?;
        if !self.errors.is_empty() {
            return Ok(input);
        }
        encode_arp(&input).map_err(|e| PluginHookError(format!("ARP encoding: {e:?}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{
        fast_parser::{ParserFeature, parse_program_with_features},
        resolver::{NameAnalyser, check_program_core},
        translator::translate_program_core,
    };
    #[test]
    fn plugin_errors_clear_before_next_root_parse() {
        use crate::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
        use crate::plugin::silver_plugin_manager::SilverPluginManager;
        let mut phases = SilFrontendPhases::new(
            "test.vpr".into(),
            SilverPluginManager::new(vec![Box::new(ArpPlugin::new())]),
        );
        let parsed = phases
            .parse("method invalid() { assert rd == none }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let errors = phases.prepare_verification(program).unwrap_err();
        assert_eq!(errors.len(), 1);
        let parsed = phases.parse("method valid() { assert true }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        phases.prepare_verification(program).unwrap();
        assert!(phases.plugins.errors().is_empty());
    }
    #[test]
    fn source_method_call_reaches_arp_encoding() {
        let source =
            "field f: Int method m(x: Ref) requires acc(x.f, rd) method caller(y: Ref) { m(y); }";
        let parsed =
            parse_program_with_features(source, "test.vpr", &[ParserFeature::Arp]).unwrap();
        crate::parser::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let output = encode_arp(&translate_program_core(&parsed).unwrap()).unwrap();
        let StmtKind::Seqn { statements, .. } = output.methods[1].body.as_ref().unwrap().kind()
        else {
            panic!("body")
        };
        let StmtKind::Seqn { statements, .. } = statements[0].kind() else {
            panic!("call encoding")
        };
        assert!(
            matches!(statements.last().unwrap().kind(), StmtKind::MethodCall { args, .. } if args.len() == 2)
        );
    }
    #[test]
    fn call_to_rd_method_gets_fresh_argument_and_constraints() {
        use crate::ast::program::{Declaration, Method, MethodData};
        use crate::ast::statement::Stmt;
        let parsed = parse_program_with_features(
            "field f: Int method m(x: Ref) requires acc(x.f, rd)",
            "test.vpr",
            &[ParserFeature::Arp],
        )
        .unwrap();
        crate::parser::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        let meta = Metadata::default();
        let formal = LocalVarDecl::new("y".into(), Type::Ref, meta.clone());
        let arg = Exp::new(ExpKind::LocalVar(formal.local_var()), meta.clone());
        let call = Stmt::new(
            StmtKind::MethodCall {
                method_name: "m".into(),
                args: vec![arg],
                targets: vec![],
            },
            meta.clone(),
        );
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![call],
                declarations: Vec::<Declaration>::new(),
            },
            meta.clone(),
        );
        let caller = Method::new(MethodData {
            name: "caller".into(),
            formal_args: vec![formal],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta,
        });
        let program = program.copy_with(|p| p.methods.push(caller));
        let output = encode_arp(&program).unwrap();
        let StmtKind::Seqn { statements, .. } = output.methods[1].body.as_ref().unwrap().kind()
        else {
            panic!("body")
        };
        let StmtKind::Seqn {
            statements,
            declarations,
        } = statements[0].kind()
        else {
            panic!("call encoding")
        };
        assert_eq!(declarations.len(), 1);
        assert_eq!(statements.len(), 3);
        assert!(matches!(statements[0].kind(), StmtKind::Inhale(_)));
        assert!(matches!(statements[1].kind(), StmtKind::Inhale(_)));
        assert!(
            matches!(statements[2].kind(), StmtKind::MethodCall { args, .. } if args.len() == 2)
        );
        {
            use crate::verifier::verification_error::{
                ErrorNodeRenderer, ErrorReason, RenderedVerificationError, VerificationError,
                VerificationErrorKind,
            };
            use crate::verifier::verification_result::{DiagnosticError, VerificationDiagnostic};
            #[derive(Debug)]
            struct Renderer;
            impl ErrorNodeRenderer for Renderer {
                fn render_node(&self, _: &Node) -> Result<String, DiagnosticError> {
                    Ok("e".into())
                }
            }
            let reason =
                ErrorReason::AssertionFalse(Exp::new(ExpKind::FalseLit, Metadata::default()));
            let error = VerificationError::new(
                VerificationErrorKind::InhaleFailed(statements[1].clone()),
                reason,
            );
            let error =
                RenderedVerificationError::new(error, std::sync::Arc::new(Renderer)).unwrap();
            let mapped = error.transformed_error().unwrap();
            assert!(mapped.full_id().starts_with("call.precondition:"));
        }
        assert!(!contains_rd(&Node::Program(output)).unwrap());
    }
    #[test]
    fn simple_method_rd_becomes_bounded_permission_parameter() {
        let source = "field f: Int method m(x: Ref) requires acc(x.f, rd) { inhale acc(x.f, rd); }";
        let parsed =
            parse_program_with_features(source, "test.vpr", &[ParserFeature::Arp]).unwrap();
        crate::parser::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        let output = encode_arp(&program).unwrap();
        assert_eq!(output.methods[0].formal_args.len(), 2);
        assert_eq!(output.methods[0].formal_args[1].name, "m_rd");
        assert_eq!(output.methods[0].pres.len(), 2);
        assert!(matches!(
            output.methods[0].pres[0].kind(),
            ExpKind::And(_, _)
        ));
        assert!(!contains_rd(&Node::Program(output)).unwrap());
        let loop_source =
            "field f: Int method m(x: Ref) { while (true) invariant acc(x.f, rd) {} }";
        let parsed =
            parse_program_with_features(loop_source, "test.vpr", &[ParserFeature::Arp]).unwrap();
        crate::parser::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        let output = encode_arp(&program).unwrap();
        assert!(!contains_rd(&Node::Program(output.clone())).unwrap());
        let body = output.methods[0].body.as_ref().unwrap();
        let StmtKind::Seqn { statements, .. } = body.kind() else {
            panic!("method body")
        };
        let StmtKind::Seqn {
            statements,
            declarations,
        } = statements[0].kind()
        else {
            panic!("loop encoding")
        };
        assert_eq!(declarations.len(), 1);
        assert_eq!(statements.len(), 3);
        assert!(matches!(statements[0].kind(), StmtKind::Inhale(_)));
        assert!(matches!(statements[1].kind(), StmtKind::Inhale(_)));
        assert!(matches!(statements[2].kind(), StmtKind::While { .. }));
    }
}
