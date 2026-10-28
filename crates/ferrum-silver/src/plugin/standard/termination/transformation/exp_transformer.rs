//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/ExpTransformer.scala
//!
//! Purpose:
//! Turn expressions into statements that check termination while maintaining evaluation context.
//!
//! Planned Rust structure:
//! Port ExpTransformer transformExp, ExpressionContext, toPureBooleanExp, fresh-variable
//! substitution, emptiness and unsupported-expression helpers.
//!
//! Behavior to preserve:
//! Preserve conjunction inhale ordering via nondeterministic branch, short circuit for boolean
//! operators, conditional branches, unfolding/applying and inhale-exhale choices, let bindings and
//! quantified variable substitutions. ForPerm checks body under positive permission and kills
//! branch; Exists inhales witnesses. Access predicates check amount then inhale; unsupported
//! extension expressions report consistency errors.
//!
//! Integration:
//! function_check overrides function calls; program_manager, ast::utility::{expressions,rewriter}
//! and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for branching, state independence, metadata and name order.
//!
//! Open decisions:
//! Agree on traversal and explicit expression context with function_check and ast rewriter.
//!
//! Status: partial; source expression checks and pure-condition projection are implemented.
//! Function-specific overrides, diagnostic integration and lifecycle wiring remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::program_manager::ProgramManager;
use crate::ast::ast::Metadata;
use crate::ast::expression::{Exp, ExpKind};
use crate::ast::program::{Declaration, LocalVarDecl};
use crate::ast::statement::{Stmt, StmtKind};
use crate::ast::r#type::Type;
use crate::ast::utility::{
    expressions,
    nodes::{self, Node},
};

#[derive(Clone, Default)]
pub struct ExpressionContext {
    pub condition_in_ex: Option<LocalVarDecl>,
}
#[derive(Debug)]
pub struct ExpressionTransformError(pub String);
fn failure(e: impl std::fmt::Debug) -> ExpressionTransformError {
    ExpressionTransformError(format!("{e:?}"))
}
fn expr(kind: ExpKind, meta: &Metadata) -> Exp {
    Exp::new(kind, meta.clone())
}
fn stmt(kind: StmtKind, meta: &Metadata) -> Stmt {
    Stmt::new(kind, meta.clone())
}
fn seq(statements: Vec<Stmt>, declarations: Vec<LocalVarDecl>, meta: &Metadata) -> Stmt {
    stmt(
        StmtKind::Seqn {
            statements,
            declarations: declarations.into_iter().map(Declaration::Local).collect(),
        },
        meta,
    )
}
fn empty() -> Stmt {
    crate::ast::utility::statements::empty_stmt()
}
fn local(v: &LocalVarDecl) -> Exp {
    expr(ExpKind::LocalVar(v.local_var()), &v.meta)
}
fn preserve(old: &Exp, new: Exp) -> Result<Exp, ExpressionTransformError> {
    match crate::ast::utility::viper_strategy::preserve_metadata(
        &Node::Exp(old.clone()),
        &Node::Exp(new),
        true,
    )
    .map_err(failure)?
    {
        Node::Exp(exp) => Ok(exp),
        _ => Err(ExpressionTransformError("pure projection metadata".into())),
    }
}
fn inhale_false(meta: &Metadata) -> Stmt {
    stmt(StmtKind::Inhale(expr(ExpKind::FalseLit, meta)), meta)
}
pub fn is_empty_statement(statement: &Stmt) -> bool {
    match statement.kind() {
        StmtKind::Seqn { statements, .. } => statements.iter().all(is_empty_statement),
        _ => false,
    }
}
fn contains_inhale_exhale(e: &Exp) -> Result<bool, ExpressionTransformError> {
    fn visit(n: &Node) -> Result<bool, ExpressionTransformError> {
        if matches!(n, Node::Exp(e) if matches!(e.kind(), ExpKind::InhaleExhaleExp(..))) {
            return Ok(true);
        }
        for child in nodes::subnodes(n).map_err(failure)? {
            if visit(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    visit(&Node::Exp(e.clone()))
}

pub trait FunctionCallHandler: Send + Sync {
    fn transform_call(
        &self,
        transformer: &mut ExpTransformer,
        call: &Exp,
        context: &ExpressionContext,
    ) -> Result<Stmt, ExpressionTransformError>;
}
pub struct ExpTransformer {
    pub manager: ProgramManager,
    pub call_handler: Option<std::sync::Arc<dyn FunctionCallHandler>>,
}
impl ExpTransformer {
    fn fresh(&mut self, base: &str, typ: Type, meta: &Metadata) -> LocalVarDecl {
        LocalVarDecl::new(self.manager.unique_name(base), typ, meta.clone())
    }
    fn fresh_vars(
        &mut self,
        vars: &[LocalVarDecl],
        body: &Exp,
    ) -> Result<(Vec<LocalVarDecl>, Exp), ExpressionTransformError> {
        let fresh: Vec<_> = vars
            .iter()
            .map(|v| self.fresh(&v.name, v.typ.clone(), &v.meta))
            .collect();
        let old: Vec<_> = vars.iter().map(local).collect();
        let new: Vec<_> = fresh.iter().map(local).collect();
        let body =
            expressions::instantiate_abstract_variables(body, &old, &new).map_err(failure)?;
        Ok((fresh, body))
    }
    pub fn transform_exp(
        &mut self,
        e: &Exp,
        c: &ExpressionContext,
        inhale: bool,
    ) -> Result<Stmt, ExpressionTransformError> {
        use ExpKind::*;
        let m = Metadata::default();
        Ok(match e.kind() {
            And(first, second) if inhale => {
                let check_first = self.transform_exp(first, c, inhale)?;
                let nondet = self.fresh("b", Type::Bool, e.metadata());
                let mut inhaled = stmt(StmtKind::Inhale(first.clone()), &m);
                if contains_inhale_exhale(first)? {
                    if let Some(v) = &c.condition_in_ex {
                        let exhale = expressions::when_exhaling(first).map_err(failure)?;
                        inhaled = stmt(
                            StmtKind::If {
                                condition: local(v),
                                then_branch: seq(vec![inhaled], vec![], &m),
                                else_branch: seq(
                                    vec![stmt(StmtKind::Inhale(exhale), &m)],
                                    vec![],
                                    &m,
                                ),
                            },
                            &m,
                        );
                    }
                }
                let branch = stmt(
                    StmtKind::If {
                        condition: local(&nondet),
                        then_branch: seq(vec![check_first, inhale_false(&m)], vec![], &m),
                        else_branch: seq(vec![inhaled], vec![], &m),
                    },
                    e.metadata(),
                );
                let first_block = seq(vec![branch], vec![nondet], &m);
                let second = self.transform_exp(second, c, inhale)?;
                seq(vec![first_block, second], vec![], &m)
            }
            CondExp(cond, yes, no) => {
                let check = self.transform_exp(cond, c, false)?;
                let yes = self.transform_exp(yes, c, inhale)?;
                let no = self.transform_exp(no, c, inhale)?;
                let branch = if is_empty_statement(&yes) && is_empty_statement(&no) {
                    empty()
                } else {
                    stmt(
                        StmtKind::If {
                            condition: cond.clone(),
                            then_branch: seq(vec![yes], vec![], &m),
                            else_branch: seq(vec![no], vec![], &m),
                        },
                        &m,
                    )
                };
                seq(vec![check, branch], vec![], &m)
            }
            Unfolding(access, body) => {
                let PredicateAccessPredicate(pap) = access.kind() else {
                    return Err(ExpressionTransformError(
                        "unfolding access predicate".into(),
                    ));
                };
                let perm = self.transform_exp(&pap.permission_or_full(), c, false)?;
                let transformed = self.transform_exp(body, c, inhale)?;
                let nondet = self.fresh("b", Type::Bool, e.metadata());
                let unfold_part = if is_empty_statement(&transformed) {
                    empty()
                } else {
                    seq(
                        vec![stmt(StmtKind::Unfold(pap.clone()), &m), transformed],
                        vec![],
                        &m,
                    )
                };
                let else_branch = if inhale {
                    seq(
                        vec![stmt(
                            StmtKind::Inhale(e.clone()),
                            &Metadata {
                                position: e.metadata().position.clone(),
                                info: e.metadata().info.clone(),
                                ..Default::default()
                            },
                        )],
                        vec![],
                        &m,
                    )
                } else {
                    empty()
                };
                if is_empty_statement(&perm) && is_empty_statement(&unfold_part) {
                    else_branch
                } else {
                    let then_branch = seq(vec![perm, unfold_part, inhale_false(&m)], vec![], &m);
                    seq(
                        vec![stmt(
                            StmtKind::If {
                                condition: local(&nondet),
                                then_branch,
                                else_branch,
                            },
                            &m,
                        )],
                        vec![nondet],
                        &m,
                    )
                }
            }
            Applying(wand, body) => {
                let nondet = self.fresh("b", Type::Bool, e.metadata());
                let body = self.transform_exp(body, c, inhale)?;
                let then_branch = seq(
                    vec![
                        stmt(StmtKind::Apply(wand.clone()), e.metadata()),
                        body,
                        inhale_false(e.metadata()),
                    ],
                    vec![],
                    &m,
                );
                seq(
                    vec![stmt(
                        StmtKind::If {
                            condition: local(&nondet),
                            then_branch,
                            else_branch: empty(),
                        },
                        e.metadata(),
                    )],
                    vec![nondet],
                    e.metadata(),
                )
            }
            InhaleExhaleExp(yes, no) => {
                let yes = self.transform_exp(yes, c, inhale)?;
                let no = self.transform_exp(no, c, inhale)?;
                if let Some(v) = &c.condition_in_ex {
                    stmt(
                        StmtKind::If {
                            condition: local(v),
                            then_branch: seq(vec![yes], vec![], &m),
                            else_branch: seq(vec![no], vec![], &m),
                        },
                        &m,
                    )
                } else {
                    seq(vec![yes, no], vec![], &m)
                }
            }
            Let(var, value, body) => {
                let value_check = self.transform_exp(value, c, false)?;
                let body = self.transform_exp(body, c, inhale)?;
                let bind = stmt(
                    StmtKind::Inhale(expr(EqCmp(local(var), value.clone()), &m)),
                    &m,
                );
                let body = if is_empty_statement(&body) {
                    empty()
                } else {
                    seq(vec![bind, body], vec![var.clone()], &m)
                };
                seq(vec![value_check, body], vec![], &m)
            }
            Forall(vars, _, body) => {
                let (vars, body) = self.fresh_vars(vars, body)?;
                let body = self.transform_exp(&body, c, inhale)?;
                seq(vec![body], vars, e.metadata())
            }
            Exists(vars, _, body) => {
                let (vars, body) = self.fresh_vars(vars, body)?;
                let check = self.transform_exp(&body, c, inhale)?;
                seq(
                    vec![stmt(StmtKind::Inhale(body), e.metadata()), check],
                    vars,
                    e.metadata(),
                )
            }
            ForPerm(vars, resource, body) => {
                let (fresh, body) = self.fresh_vars(vars, body)?;
                let old: Vec<_> = vars.iter().map(local).collect();
                let new: Vec<_> = fresh.iter().map(local).collect();
                let resource = expressions::instantiate_abstract_variables(resource, &old, &new)
                    .map_err(failure)?;
                let body = self.transform_exp(&body, c, inhale)?;
                let condition = expr(
                    GtCmp(
                        expr(CurrentPerm(resource), e.metadata()),
                        expr(NoPerm, e.metadata()),
                    ),
                    e.metadata(),
                );
                let yes = seq(vec![body, inhale_false(e.metadata())], vec![], e.metadata());
                seq(
                    vec![stmt(
                        StmtKind::If {
                            condition,
                            then_branch: yes,
                            else_branch: empty(),
                        },
                        e.metadata(),
                    )],
                    fresh,
                    e.metadata(),
                )
            }
            FieldAccessPredicate(..) | PredicateAccessPredicate(..) => {
                let permission = e
                    .permission_or_full()
                    .ok_or(ExpressionTransformError("access permission".into()))?;
                let check = self.transform_exp(&permission, c, false)?;
                let meta = Metadata {
                    position: e.metadata().position.clone(),
                    ..Default::default()
                };
                seq(
                    vec![check, stmt(StmtKind::Inhale(e.clone()), &meta)],
                    vec![],
                    &m,
                )
            }
            Extension(_) => {
                return Err(ExpressionTransformError(
                    "unsupported extension expression in termination check".into(),
                ));
            }
            _ if binary_operands(e).is_some() => {
                let (left, right) = binary_operands(e).expect("binary operands");
                let left_check = self.transform_exp(left, c, inhale)?;
                let right_check = self.transform_exp(right, c, inhale)?;
                let pure = self.to_pure_boolean_exp(left, c)?;
                let right_check = if is_empty_statement(&right_check) {
                    empty()
                } else {
                    match e.kind() {
                        Or(..) => stmt(
                            StmtKind::If {
                                condition: expr(Not(pure), &m),
                                then_branch: seq(vec![right_check], vec![], &m),
                                else_branch: empty(),
                            },
                            &m,
                        ),
                        And(..) | Implies(..) => stmt(
                            StmtKind::If {
                                condition: pure,
                                then_branch: seq(vec![right_check], vec![], &m),
                                else_branch: empty(),
                            },
                            &m,
                        ),
                        _ => seq(vec![right_check], vec![], &m),
                    }
                };
                seq(vec![left_check, right_check], vec![], &m)
            }
            IntLit(_)
            | TrueLit
            | FalseLit
            | NullLit
            | RefLit(_)
            | BackendValueLit(..)
            | LocalVar(_)
            | LocalVarWithVersion(..)
            | Result(_)
            | FullPerm
            | NoPerm
            | WildcardPerm
            | EpsilonPerm
            | CurrentPerm(_)
            | FieldAccess(_)
            | PredicateAccess(_) => empty(),
            FuncApp(_, args) => {
                if let Some(handler) = self.call_handler.clone() {
                    return handler.transform_call(self, e, c);
                }
                let mut checks = Vec::new();
                for arg in args {
                    checks.push(self.transform_exp(arg, c, false)?);
                }
                seq(checks, vec![], &m)
            }
            DomainFuncApp(_, args, _) | BackendFuncApp(_, args) => {
                let mut checks = Vec::new();
                for arg in args {
                    checks.push(self.transform_exp(arg, c, false)?);
                }
                seq(checks, vec![], &m)
            }
            _ => {
                let mut checks = Vec::new();
                for child in expressions::sub_expressions(e).map_err(failure)? {
                    checks.push(self.transform_exp(&child, c, false)?);
                }
                seq(checks, vec![], &m)
            }
        })
    }
    pub fn to_pure_boolean_exp(
        &self,
        e: &Exp,
        c: &ExpressionContext,
    ) -> Result<Exp, ExpressionTransformError> {
        use ExpKind::*;
        let m = Metadata::default();
        match e.kind() {
            FieldAccessPredicate(..) | PredicateAccessPredicate(..) | MagicWand(..) => {
                preserve(e, expr(TrueLit, &m))
            }
            InhaleExhaleExp(yes, no) => {
                let meta = Metadata {
                    position: e.metadata().position.clone(),
                    ..Default::default()
                };
                let replaced = if let Some(v) = &c.condition_in_ex {
                    expr(CondExp(local(v), yes.clone(), no.clone()), &meta)
                } else {
                    expr(Or(yes.clone(), no.clone()), &meta)
                };
                self.to_pure_boolean_exp(&preserve(e, replaced)?, c)
            }
            Unfolding(access, body) => Ok(expr(
                Unfolding(access.clone(), self.to_pure_boolean_exp(body, c)?),
                e.metadata(),
            )),
            Applying(wand, body) => Ok(expr(
                Applying(wand.clone(), self.to_pure_boolean_exp(body, c)?),
                e.metadata(),
            )),
            Forall(vars, triggers, body) => Ok(expr(
                Forall(
                    vars.clone(),
                    triggers.clone(),
                    self.to_pure_boolean_exp(body, c)?,
                ),
                e.metadata(),
            )),
            _ => e.map_expression_children(
                &mut |child| self.to_pure_boolean_exp(child, c),
                &mut |_| {
                    Err(ExpressionTransformError(
                        "unsupported extension expression projection".into(),
                    ))
                },
                &mut |field| {
                    Ok(crate::ast::expression::FieldAccess::new(
                        self.to_pure_boolean_exp(&field.receiver, c)?,
                        field.field.clone(),
                        field.meta.clone(),
                    ))
                },
                &mut |pred| {
                    Ok(crate::ast::expression::PredicateAccess::new(
                        pred.args
                            .iter()
                            .map(|arg| self.to_pure_boolean_exp(arg, c))
                            .collect::<std::result::Result<Vec<_>, _>>()?,
                        pred.predicate_name.clone(),
                        pred.meta.clone(),
                    ))
                },
                &mut |trigger| {
                    Ok(crate::ast::expression::Trigger::new(
                        trigger
                            .exps
                            .iter()
                            .map(|exp| self.to_pure_boolean_exp(exp, c))
                            .collect::<std::result::Result<Vec<_>, _>>()?,
                        trigger.meta.clone(),
                    ))
                },
            ),
        }
    }
}
fn binary_operands(e: &Exp) -> Option<(&Exp, &Exp)> {
    use ExpKind::*;
    match e.kind() {
        Add(a, b)
        | Sub(a, b)
        | Mul(a, b)
        | Div(a, b)
        | Mod(a, b)
        | LtCmp(a, b)
        | LeCmp(a, b)
        | GtCmp(a, b)
        | GeCmp(a, b)
        | EqCmp(a, b)
        | NeCmp(a, b)
        | Or(a, b)
        | And(a, b)
        | Implies(a, b)
        | MagicWand(a, b)
        | FractionalPerm(a, b)
        | PermDiv(a, b)
        | PermPermDiv(a, b)
        | PermAdd(a, b)
        | PermSub(a, b)
        | PermMul(a, b)
        | IntPermMul(a, b)
        | DebugPermMin(a, b)
        | PermLtCmp(a, b)
        | PermLeCmp(a, b)
        | PermGtCmp(a, b)
        | PermGeCmp(a, b)
        | AnySetUnion(a, b)
        | AnySetIntersection(a, b)
        | AnySetSubset(a, b)
        | AnySetMinus(a, b)
        | AnySetContains(a, b) => Some((a, b)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::program::Program;

    #[test]
    fn inhaled_conjunction_checks_first_before_inhaling_and_second() {
        let meta = Metadata::default();
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], meta.clone());
        let mut transformer = ExpTransformer {
            manager: ProgramManager::new(program, Vec::<String>::new()),
            call_handler: None,
        };
        let first = expr(ExpKind::TrueLit, &meta);
        let second = expr(ExpKind::FalseLit, &meta);
        let input = expr(ExpKind::And(first, second), &meta);
        let result = transformer
            .transform_exp(&input, &ExpressionContext::default(), true)
            .unwrap();
        let StmtKind::Seqn { statements, .. } = result.kind() else {
            panic!()
        };
        let StmtKind::Seqn {
            statements: block,
            declarations,
        } = statements[0].kind()
        else {
            panic!()
        };
        assert_eq!(declarations.len(), 1);
        assert!(matches!(block[0].kind(), StmtKind::If { .. }));
        assert!(is_empty_statement(&statements[1]));
    }
}
