//! Permission expression queries and scaling.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Permissions.scala
//! Status: partial; built-in expressions and explicit extension failure are implemented;
//! generic source reconstruction and extension hooks remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::nodes::{Node, TraversalError, subnodes};
use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpKind, ExpressionTypeError, FieldAccess, PredicateAccess, Trigger},
    statement::PredicateAccessPredicate,
    r#type::Type,
};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PermissionError {
    Type(ExpressionTypeError),
    Traversal(TraversalError),
    ExpectedPermission(Type),
    MagicWand,
    Extension,
}
impl From<ExpressionTypeError> for PermissionError {
    fn from(e: ExpressionTypeError) -> Self {
        Self::Type(e)
    }
}
impl From<TraversalError> for PermissionError {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
pub fn is_conditional(exp: &Exp) -> Result<bool, PermissionError> {
    fn search(n: &Node) -> Result<bool, PermissionError> {
        if let Node::Exp(e) = n {
            if matches!(e.kind(), ExpKind::CondExp(..)) {
                return Ok(true);
            }
        }
        for child in subnodes(n)? {
            if search(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    search(&Node::Exp(exp.clone()))
}
pub fn positivity_constraints(exp: &Exp) -> Result<Vec<Exp>, PermissionError> {
    let typ = exp.typ()?;
    if typ != Type::Perm {
        return Err(PermissionError::ExpectedPermission(typ));
    }
    Ok(if is_conditional(exp)? {
        Vec::new()
    } else {
        vec![exp.clone()]
    })
}
pub fn multiply_exp_by_perm(exp: &Exp, factor: &Exp) -> Result<Exp, PermissionError> {
    let typ = factor.typ()?;
    if typ != Type::Perm {
        return Err(PermissionError::ExpectedPermission(typ));
    }
    if matches!(factor.kind(), ExpKind::FullPerm) {
        return Ok(exp.clone());
    }
    fn scaled(p: &Option<Exp>, factor: &Exp) -> Option<Exp> {
        Some(match p {
            Some(p) => Exp::new(
                ExpKind::PermMul(p.clone(), factor.clone()),
                Metadata {
                    position: p.metadata().position.clone(),
                    info: p.metadata().info.clone(),
                    ..Metadata::default()
                },
            ),
            None => factor.clone(),
        })
    }
    fn go(e: &Exp, factor: &Exp) -> Result<Exp, PermissionError> {
        let meta = || Metadata {
            position: e.metadata().position.clone(),
            info: e.metadata().info.clone(),
            ..Metadata::default()
        };
        match e.kind() {
            ExpKind::MagicWand(..) => return Err(PermissionError::MagicWand),
            ExpKind::FieldAccessPredicate(loc, p) => {
                return Ok(Exp::new(
                    ExpKind::FieldAccessPredicate(loc.clone(), scaled(p, factor)),
                    meta(),
                ));
            }
            ExpKind::PredicateAccessPredicate(p) => {
                return Ok(Exp::new(
                    ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                        p.location.clone(),
                        scaled(&p.permission, factor),
                        meta(),
                    )),
                    meta(),
                ));
            }
            _ => {}
        }
        e.map_expression_children(
            &mut |v| go(v, factor),
            &mut |_| Err(PermissionError::Extension),
            &mut |v| {
                let receiver = go(&v.receiver, factor)?;
                Ok(if receiver == v.receiver {
                    v.clone()
                } else {
                    FieldAccess::new(receiver, v.field.clone(), v.meta.clone())
                })
            },
            &mut |v| {
                let args = v
                    .args
                    .iter()
                    .map(|e| go(e, factor))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(if args == v.args {
                    v.clone()
                } else {
                    PredicateAccess::new(args, v.predicate_name.clone(), v.meta.clone())
                })
            },
            &mut |v| {
                let exps = v
                    .exps
                    .iter()
                    .map(|e| go(e, factor))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(if exps == v.exps {
                    v.clone()
                } else {
                    Trigger::new(exps, v.meta.clone())
                })
            },
        )
    }
    go(exp, factor)
}
