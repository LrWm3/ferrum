//! Inverse-function generation for quantified permission assertions.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/InverseFunctions.scala
//! Status: partial; field, predicate and wand inverse axioms and rewritten forall are
//! implemented using expression replacement. Unsupported extension reconstruction propagates.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::{
    expressions::MagicWandError,
    quantified_permissions::quantified_permission_assertion,
    rewriter::strategy::{ExpressionReplacementError, replace_expressions},
};
use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpExtra, ExpKind, FieldAccess, PredicateAccess, Trigger},
    program::{AnyLocalVarDecl, Domain, DomainFunc, LocalVarDecl, Program},
    statement::PredicateAccessPredicate,
    r#type::Type,
};
use std::{
    collections::HashMap,
    sync::atomic::{AtomicI32, Ordering},
};
static COUNTER: AtomicI32 = AtomicI32::new(0);
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InverseError {
    NotForall,
    MissingPredicate(String),
    MissingExpressionType,
    InvalidResource,
    EmptyConjunction,
    ArityMismatch,
    Replacement(ExpressionReplacementError),
    Wand(MagicWandError),
}
impl From<ExpressionReplacementError> for InverseError {
    fn from(e: ExpressionReplacementError) -> Self {
        Self::Replacement(e)
    }
}
impl From<MagicWandError> for InverseError {
    fn from(e: MagicWandError) -> Self {
        Self::Wand(e)
    }
}
pub type InverseResult = (Option<(Vec<DomainFunc>, Domain)>, Option<Vec<Exp>>, Exp);
fn local(v: &LocalVarDecl) -> Exp {
    Exp::new(ExpKind::LocalVar(v.local_var()), v.meta.clone())
}
fn app(fun: &DomainFunc, args: Vec<Exp>, meta: &Metadata) -> Exp {
    Exp::with_extra(
        ExpKind::DomainFuncApp(fun.name.clone(), args, HashMap::new()),
        meta.clone(),
        ExpExtra {
            typ: Some(fun.typ.clone()),
            domain_name: Some(fun.domain_name.clone()),
            interpretation: fun.interpretation.clone(),
        },
    )
}
fn forall(vars: Vec<LocalVarDecl>, triggers: Vec<Trigger>, body: Exp, meta: &Metadata) -> Exp {
    Exp::new(ExpKind::Forall(vars, triggers, body), meta.clone())
}
fn conjunction(items: Vec<Exp>, meta: &Metadata) -> Result<Exp, InverseError> {
    let mut items = items.into_iter();
    let mut out = items.next().ok_or(InverseError::EmptyConjunction)?;
    for item in items {
        out = Exp::new(ExpKind::And(out, item), meta.clone());
    }
    Ok(out)
}
fn replacements(vars: &[LocalVarDecl], exps: &[Exp]) -> Vec<(Exp, Exp)> {
    vars.iter().map(local).zip(exps.iter().cloned()).collect()
}
/// Mirrors the source process-global counter. Concurrent generation order is not promised.
pub fn get_fresh_inverse(source: &Exp, program: &Program) -> Result<InverseResult, InverseError> {
    let ExpKind::Forall(qvars, triggers, _) = source.kind() else {
        return Err(InverseError::NotForall);
    };
    let Some((_, condition, access)) = quantified_permission_assertion(source) else {
        return Ok((None, None, source.clone()));
    };
    let start = COUNTER.load(Ordering::SeqCst);
    let domain_name = format!("Inverse_{start}");
    let meta = source.metadata().clone();
    let fresh_fun = |name: String, formals: &[LocalVarDecl], typ: Type| {
        DomainFunc::new(crate::ast::program::DomainFuncData {
            name,
            formal_args: formals
                .iter()
                .cloned()
                .map(AnyLocalVarDecl::Named)
                .collect(),
            typ,
            unique: false,
            interpretation: None,
            domain_name: domain_name.clone(),
            meta: meta.clone(),
        })
    };
    match access.kind() {
        ExpKind::FieldAccessPredicate(location, permission) => {
            let r = LocalVarDecl::new("r".into(), Type::Ref, Metadata::default());
            let mut inverses = Vec::new();
            for v in qvars {
                let id = COUNTER.fetch_add(1, Ordering::SeqCst);
                inverses.push(fresh_fun(
                    format!("inv_{id}"),
                    std::slice::from_ref(&r),
                    v.typ.clone(),
                ));
            }
            let invs_r: Vec<_> = inverses
                .iter()
                .map(|f| app(f, vec![local(&r)], &meta))
                .collect();
            let mut equalities = Exp::new(ExpKind::TrueLit, Metadata::default());
            for (inv, var) in inverses.iter().zip(qvars) {
                let eq = Exp::new(
                    ExpKind::EqCmp(app(inv, vec![location.receiver.clone()], &meta), local(var)),
                    meta.clone(),
                );
                equalities = Exp::new(ExpKind::And(equalities, eq), meta.clone());
            }
            let axiom1 = forall(
                qvars.clone(),
                triggers.clone(),
                Exp::new(
                    ExpKind::Implies(condition.clone(), equalities),
                    meta.clone(),
                ),
                &meta,
            );
            let mut cond = condition.clone();
            let mut receiver = location.receiver.clone();
            let mut perm = permission.clone();
            for (var, inv) in qvars.iter().zip(&invs_r) {
                let map = [(local(var), inv.clone())];
                cond = replace_expressions(&cond, &map)?;
                receiver = replace_expressions(&receiver, &map)?;
                perm = perm
                    .as_ref()
                    .map(|p| replace_expressions(p, &map))
                    .transpose()?;
            }
            let rhs = Exp::new(ExpKind::EqCmp(receiver, local(&r)), meta.clone());
            let axiom2 = forall(
                vec![r.clone()],
                vec![Trigger::new(invs_r.clone(), meta.clone())],
                Exp::new(ExpKind::Implies(cond.clone(), rhs), meta.clone()),
                &meta,
            );
            let loc = FieldAccess::new(local(&r), location.field.clone(), Metadata::default());
            let acc = Exp::new(
                ExpKind::FieldAccessPredicate(loc, perm),
                Metadata::default(),
            );
            let rewritten = forall(
                vec![r],
                vec![Trigger::new(invs_r, Metadata::default())],
                Exp::new(ExpKind::Implies(cond, acc), meta.clone()),
                &meta,
            );
            let domain = Domain::new(crate::ast::program::DomainData {
                name: domain_name,
                functions: inverses.clone(),
                axioms: vec![],
                type_vars: vec![],
                interpretations: None,
                meta,
            });
            Ok((
                Some((inverses, domain)),
                Some(vec![axiom1, axiom2]),
                rewritten,
            ))
        }
        ExpKind::PredicateAccessPredicate(p) => {
            let pred = program
                .find_predicate_optionally(&p.location.predicate_name)
                .ok_or_else(|| InverseError::MissingPredicate(p.location.predicate_name.clone()))?;
            let formal = pred.formal_args.clone();
            let actual = p.location.args.clone();
            if actual.len() > formal.len() {
                return Err(InverseError::ArityMismatch);
            }
            let id = COUNTER.fetch_add(1, Ordering::SeqCst);
            let inverses: Vec<_> = qvars
                .iter()
                .enumerate()
                .map(|(i, v)| fresh_fun(format!("inv_{id}_{i}"), &formal, v.typ.clone()))
                .collect();
            let invs_formal: Vec<_> = inverses
                .iter()
                .map(|f| app(f, formal.iter().map(local).collect(), &meta))
                .collect();
            let eqs: Vec<_> = inverses
                .iter()
                .zip(qvars)
                .map(|(f, v)| {
                    Exp::new(
                        ExpKind::EqCmp(app(f, actual.clone(), &meta), local(v)),
                        meta.clone(),
                    )
                })
                .collect();
            let map = replacements(qvars, &invs_formal);
            let reverse_eqs = actual
                .iter()
                .zip(&formal)
                .map(|(a, v)| {
                    Ok(Exp::new(
                        ExpKind::EqCmp(replace_expressions(a, &map)?, local(v)),
                        meta.clone(),
                    ))
                })
                .collect::<Result<Vec<_>, InverseError>>()?;
            let axiom1 = forall(
                qvars.clone(),
                triggers.clone(),
                Exp::new(
                    ExpKind::Implies(condition.clone(), conjunction(eqs, &meta)?),
                    meta.clone(),
                ),
                &meta,
            );
            let cond = replace_expressions(&condition, &map)?;
            let axiom2 = forall(
                formal.clone(),
                vec![Trigger::new(invs_formal.clone(), meta.clone())],
                Exp::new(
                    ExpKind::Implies(cond.clone(), conjunction(reverse_eqs, &meta)?),
                    meta.clone(),
                ),
                &meta,
            );
            let perm = p
                .permission
                .as_ref()
                .map(|e| replace_expressions(e, &map))
                .transpose()?;
            let loc = PredicateAccess::new(
                formal.iter().map(local).collect(),
                pred.name.clone(),
                meta.clone(),
            );
            let acc = Exp::new(
                ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                    loc,
                    perm,
                    meta.clone(),
                )),
                meta.clone(),
            );
            let rewritten = forall(
                formal,
                vec![Trigger::new(invs_formal, meta.clone())],
                Exp::new(ExpKind::Implies(cond, acc), meta.clone()),
                &meta,
            );
            let domain = Domain::new(crate::ast::program::DomainData {
                name: domain_name,
                functions: inverses.clone(),
                axioms: vec![],
                type_vars: vec![],
                interpretations: None,
                meta,
            });
            Ok((
                Some((inverses, domain)),
                Some(vec![axiom1, axiom2]),
                rewritten,
            ))
        }
        ExpKind::MagicWand(..) => {
            let actual = access.magic_wand_subexpressions(program)?;
            let formal = actual
                .iter()
                .enumerate()
                .map(|(i, e)| {
                    Ok(LocalVarDecl::new(
                        format!("x{i}"),
                        e.typ().map_err(|_| InverseError::MissingExpressionType)?,
                        meta.clone(),
                    ))
                })
                .collect::<Result<Vec<_>, InverseError>>()?;
            let id = COUNTER.fetch_add(1, Ordering::SeqCst);
            let inverses: Vec<_> = qvars
                .iter()
                .enumerate()
                .map(|(i, v)| fresh_fun(format!("inv_{id}_{i}"), &formal, v.typ.clone()))
                .collect();
            let invs_formal: Vec<_> = inverses
                .iter()
                .map(|f| app(f, formal.iter().map(local).collect(), &meta))
                .collect();
            let eqs: Vec<_> = inverses
                .iter()
                .zip(qvars)
                .map(|(f, v)| {
                    Exp::new(
                        ExpKind::EqCmp(app(f, actual.clone(), &meta), local(v)),
                        Metadata::default(),
                    )
                })
                .collect();
            let map = replacements(qvars, &invs_formal);
            let reverse_eqs = actual
                .iter()
                .zip(&formal)
                .map(|(a, v)| {
                    Ok(Exp::new(
                        ExpKind::EqCmp(replace_expressions(a, &map)?, local(v)),
                        meta.clone(),
                    ))
                })
                .collect::<Result<Vec<_>, InverseError>>()?;
            let axiom1 = forall(
                qvars.clone(),
                triggers.clone(),
                Exp::new(
                    ExpKind::Implies(condition.clone(), conjunction(eqs, &meta)?),
                    meta.clone(),
                ),
                &meta,
            );
            let cond = replace_expressions(&condition, &map)?;
            let axiom2 = forall(
                formal.clone(),
                vec![Trigger::new(invs_formal.clone(), meta.clone())],
                Exp::new(
                    ExpKind::Implies(cond.clone(), conjunction(reverse_eqs, &meta)?),
                    meta.clone(),
                ),
                &meta,
            );
            let holes: Vec<_> = actual.into_iter().zip(formal.iter().map(local)).collect();
            let acc = replace_expressions(&access, &holes)?;
            let rewritten = forall(
                formal,
                vec![Trigger::new(invs_formal, meta.clone())],
                Exp::new(ExpKind::Implies(cond, acc), meta.clone()),
                &meta,
            );
            let domain = Domain::new(crate::ast::program::DomainData {
                name: domain_name,
                functions: inverses.clone(),
                axioms: vec![],
                type_vars: vec![],
                interpretations: None,
                meta,
            });
            Ok((
                Some((inverses, domain)),
                Some(vec![axiom1, axiom2]),
                rewritten,
            ))
        }
        _ => Err(InverseError::InvalidResource),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::program::Field;
    #[test]
    fn field_inverse_retains_optional_permission_and_produces_two_axioms() {
        let m = Metadata::default();
        let q = LocalVarDecl::new("x".into(), Type::Ref, m.clone());
        let field = Field::new(crate::ast::program::FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: m.clone(),
        });
        let access = Exp::new(
            ExpKind::FieldAccessPredicate(FieldAccess::new(local(&q), field, m.clone()), None),
            m.clone(),
        );
        let source = forall(vec![q], vec![], access, &m);
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], m);
        let (domain, axioms, result) = get_fresh_inverse(&source, &program).unwrap();
        assert_eq!(domain.unwrap().0.len(), 1);
        assert_eq!(axioms.unwrap().len(), 2);
        let ExpKind::Forall(_, _, body) = result.kind() else {
            panic!("forall")
        };
        let ExpKind::Implies(_, right) = body.kind() else {
            panic!("implication")
        };
        assert!(matches!(
            right.kind(),
            ExpKind::FieldAccessPredicate(_, None)
        ));
    }
}
