//! Bottom-up simplification of Silver expressions.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Simplifier.scala
//! Status: partial; expression rules and their source cache are implemented. Statement
//! dispatch and built-in well-definedness analysis remain pending; the latter is supplied
//! by a fallible callback. Unsupported extension reconstruction and checker errors propagate.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpKind, SimplifiedExp, Trigger},
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SimplifyError<E> {
    WellDefined(E),
    Extension,
    PoisonedCache,
    ZeroDenominator,
}
fn permission_parts(e: &Exp) -> Option<(BigInt, BigInt)> {
    match e.kind() {
        ExpKind::FullPerm => Some((BigInt::one(), BigInt::one())),
        ExpKind::NoPerm => Some((BigInt::zero(), BigInt::one())),
        ExpKind::FractionalPerm(n, d) => match (n.kind(), d.kind()) {
            (ExpKind::IntLit(n), ExpKind::IntLit(d)) => Some((n.clone(), d.clone())),
            _ => None,
        },
        _ => None,
    }
}
fn rational<E>(e: &Exp) -> Result<Option<BigRational>, SimplifyError<E>> {
    match permission_parts(e) {
        Some((_, ref d)) if d.is_zero() => Err(SimplifyError::ZeroDenominator),
        Some((n, d)) => Ok(Some(BigRational::new(n, d))),
        None => Ok(None),
    }
}
fn fraction(e: &Exp, r: &BigRational, preserve_trafo: bool) -> Exp {
    let metadata = if preserve_trafo {
        e.metadata().clone()
    } else {
        meta(e)
    };
    let n = Exp::new(ExpKind::IntLit(r.numer().clone()), metadata.clone());
    let d = Exp::new(ExpKind::IntLit(r.denom().clone()), metadata.clone());
    Exp::new(ExpKind::FractionalPerm(n, d), metadata)
}
fn rational_to_perm(e: &Exp, r: &BigRational, preserve_trafo: bool) -> Exp {
    let metadata = if preserve_trafo {
        e.metadata().clone()
    } else {
        meta(e)
    };
    if r.is_zero() {
        Exp::new(ExpKind::NoPerm, metadata.clone())
    } else if r.is_one() {
        Exp::new(ExpKind::FullPerm, metadata.clone())
    } else {
        fraction(e, r, preserve_trafo)
    }
}
fn meta(e: &Exp) -> Metadata {
    Metadata {
        position: e.metadata().position.clone(),
        info: e.metadata().info.clone(),
        ..Metadata::default()
    }
}
fn literal(e: &Exp, value: bool) -> Exp {
    Exp::new(
        if value {
            ExpKind::TrueLit
        } else {
            ExpKind::FalseLit
        },
        meta(e),
    )
}
fn bool_value(e: &Exp) -> Option<bool> {
    match e.kind() {
        ExpKind::TrueLit => Some(true),
        ExpKind::FalseLit => Some(false),
        _ => None,
    }
}

/// The callback implements Expressions.isKnownWellDefined and may fail for unsupported nodes.
/// Source caches per node irrespective of the assume_well_defined flag, including unchanged nodes.
pub fn simplify<E>(
    root: &Exp,
    assume_well_defined: bool,
    known_well_defined: &impl Fn(&Exp) -> Result<bool, E>,
) -> Result<Exp, SimplifyError<E>> {
    fn go<E>(
        e: &Exp,
        assume: bool,
        known: &impl Fn(&Exp) -> Result<bool, E>,
    ) -> Result<Exp, SimplifyError<E>> {
        let cached =
            e.0.simplified
                .read()
                .map_err(|_| SimplifyError::PoisonedCache)?
                .clone();
        if let Some(cached) = cached {
            return Ok(match cached {
                SimplifiedExp::Same => e.clone(),
                SimplifiedExp::Other(x) => x,
            });
        }
        let rebuilt = e.map_expression_children(
            &mut |x| go(x, assume, known),
            &mut |_| Err(SimplifyError::Extension),
            &mut |v| {
                let receiver = go(&v.receiver, assume, known)?;
                Ok(if receiver == v.receiver {
                    v.clone()
                } else {
                    crate::ast::expression::FieldAccess::new(
                        receiver,
                        v.field.clone(),
                        v.meta.clone(),
                    )
                })
            },
            &mut |v| {
                let args = v
                    .args
                    .iter()
                    .map(|x| go(x, assume, known))
                    .collect::<std::result::Result<Vec<_>, _>>()?;
                Ok(if args == v.args {
                    v.clone()
                } else {
                    crate::ast::expression::PredicateAccess::new(
                        args,
                        v.predicate_name.clone(),
                        v.meta.clone(),
                    )
                })
            },
            &mut |v| {
                let exps = v
                    .exps
                    .iter()
                    .map(|x| go(x, assume, known))
                    .collect::<std::result::Result<Vec<_>, _>>()?;
                Ok(if exps == v.exps {
                    v.clone()
                } else {
                    Trigger::new(exps, v.meta.clone())
                })
            },
        )?;
        let defined = |e: &Exp| {
            if assume {
                Ok(true)
            } else {
                known(e).map_err(SimplifyError::WellDefined)
            }
        };
        use ExpKind::*;
        let result = match rebuilt.kind() {
            Not(x) => match x.kind() {
                TrueLit => literal(&rebuilt, false),
                FalseLit => literal(&rebuilt, true),
                Not(y) => y.clone(),
                EqCmp(a, b) => Exp::new(NeCmp(a.clone(), b.clone()), meta(&rebuilt)),
                NeCmp(a, b) => Exp::new(EqCmp(a.clone(), b.clone()), meta(&rebuilt)),
                GtCmp(a, b) => Exp::new(LeCmp(a.clone(), b.clone()), meta(&rebuilt)),
                GeCmp(a, b) => Exp::new(LtCmp(a.clone(), b.clone()), meta(&rebuilt)),
                LtCmp(a, b) => Exp::new(GeCmp(a.clone(), b.clone()), meta(&rebuilt)),
                LeCmp(a, b) => Exp::new(GtCmp(a.clone(), b.clone()), meta(&rebuilt)),
                _ => rebuilt.clone(),
            },
            And(a, b) if matches!(a.kind(), TrueLit) => b.clone(),
            And(a, b) if matches!(b.kind(), TrueLit) => a.clone(),
            And(a, b) if matches!(a.kind(), FalseLit) || matches!(b.kind(), FalseLit) => {
                literal(&rebuilt, false)
            }
            And(a, b)
                if matches!(
                    (a.kind(), b.kind()),
                    (
                        FieldAccessPredicate(_, Some(_)),
                        FieldAccessPredicate(_, Some(_))
                    )
                ) =>
            {
                let (FieldAccessPredicate(left, Some(p)), FieldAccessPredicate(right, Some(q))) =
                    (a.kind(), b.kind())
                else {
                    unreachable!()
                };
                if left == right {
                    let sum = Exp::new(PermAdd(p.clone(), q.clone()), meta(p));
                    Exp::new(FieldAccessPredicate(left.clone(), Some(sum)), meta(a))
                } else {
                    rebuilt.clone()
                }
            }
            Or(a, b) if matches!(a.kind(), FalseLit) => b.clone(),
            Or(a, b) if matches!(b.kind(), FalseLit) => a.clone(),
            Or(a, b) if matches!(a.kind(), TrueLit) || matches!(b.kind(), TrueLit) => {
                literal(&rebuilt, true)
            }
            Implies(a, _) if matches!(a.kind(), FalseLit) => literal(&rebuilt, true),
            Implies(a, b) if matches!(b.kind(), TrueLit) && defined(a)? => b.clone(),
            Implies(a, b) if matches!(a.kind(), TrueLit) => b.clone(),
            Implies(a, b) if matches!(b.kind(), Implies(..)) => {
                let Implies(c, d) = b.kind() else {
                    unreachable!()
                };
                if a == c {
                    b.clone()
                } else {
                    let both = Exp::new(And(a.clone(), c.clone()), Metadata::default());
                    Exp::new(Implies(both, d.clone()), meta(&rebuilt))
                }
            }
            EqCmp(a, b) if a == b && defined(a)? => literal(&rebuilt, true),
            EqCmp(a, b) if bool_value(a).is_some() && bool_value(b).is_some() => {
                literal(&rebuilt, bool_value(a) == bool_value(b))
            }
            EqCmp(a, b) if matches!(a.kind(), FalseLit) => Exp::new(Not(b.clone()), meta(&rebuilt)),
            EqCmp(a, b) if matches!(b.kind(), FalseLit) => Exp::new(Not(a.clone()), meta(&rebuilt)),
            EqCmp(a, b) if matches!(a.kind(), TrueLit) => b.clone(),
            EqCmp(a, b) if matches!(b.kind(), TrueLit) => a.clone(),
            EqCmp(a, b)
                if matches!(
                    (a.kind(), b.kind()),
                    (IntLit(_), IntLit(_)) | (NullLit, NullLit)
                ) =>
            {
                literal(&rebuilt, a == b)
            }
            EqCmp(a, b) if permission_parts(a).is_some() && permission_parts(b).is_some() => {
                literal(&rebuilt, rational(a)?.unwrap() == rational(b)?.unwrap())
            }
            NeCmp(a, b) if bool_value(a).is_some() && bool_value(b).is_some() => {
                literal(&rebuilt, bool_value(a) != bool_value(b))
            }
            NeCmp(a, b) if matches!(a.kind(), FalseLit) => b.clone(),
            NeCmp(a, b) if matches!(b.kind(), FalseLit) => a.clone(),
            NeCmp(a, b) if matches!(a.kind(), TrueLit) => Exp::new(Not(b.clone()), meta(&rebuilt)),
            NeCmp(a, b) if matches!(b.kind(), TrueLit) => Exp::new(Not(a.clone()), meta(&rebuilt)),
            NeCmp(a, b)
                if matches!(
                    (a.kind(), b.kind()),
                    (IntLit(_), IntLit(_)) | (NullLit, NullLit)
                ) =>
            {
                literal(&rebuilt, a != b)
            }
            NeCmp(a, b) if a == b && defined(a)? => literal(&rebuilt, false),
            NeCmp(a, b) if permission_parts(a).is_some() && permission_parts(b).is_some() => {
                literal(&rebuilt, rational(a)?.unwrap() != rational(b)?.unwrap())
            }
            NeCmp(a, b) if matches!((a.kind(), b.kind()), (WildcardPerm, NoPerm)) => {
                literal(&rebuilt, true)
            }
            CondExp(c, a, _) if matches!(c.kind(), TrueLit) => a.clone(),
            CondExp(c, _, b) if matches!(c.kind(), FalseLit) => b.clone(),
            CondExp(c, a, b) if a == b && defined(c)? && defined(a)? => a.clone(),
            CondExp(c, a, b) if matches!((a.kind(), b.kind()), (FalseLit, TrueLit)) => {
                Exp::new(Not(c.clone()), meta(&rebuilt))
            }
            CondExp(c, a, b) if matches!((a.kind(), b.kind()), (TrueLit, FalseLit)) => c.clone(),
            CondExp(c, a, b) if matches!(a.kind(), FalseLit) => {
                let not = Exp::new(Not(c.clone()), Metadata::default());
                Exp::new(And(not, b.clone()), meta(&rebuilt))
            }
            CondExp(c, a, b) if matches!(a.kind(), TrueLit) => {
                if b.is_pure() {
                    Exp::new(Or(c.clone(), b.clone()), meta(&rebuilt))
                } else {
                    let not = Exp::new(Not(c.clone()), Metadata::default());
                    Exp::new(Implies(not, b.clone()), meta(&rebuilt))
                }
            }
            CondExp(c, a, b) if matches!(b.kind(), FalseLit) => {
                Exp::new(And(c.clone(), a.clone()), meta(&rebuilt))
            }
            CondExp(c, a, b) if matches!(b.kind(), TrueLit) => {
                Exp::new(Implies(c.clone(), a.clone()), meta(&rebuilt))
            }
            CondExp(c, a, b) if matches!(a.kind(), CondExp(inner,x,y) if c == inner || ((x == b || y == b) && !matches!(b.kind(),CondExp(other,_,_) if c == other))) =>
            {
                let CondExp(inner, x, y) = a.kind() else {
                    unreachable!()
                };
                if c == inner {
                    if x == b && defined(c)? {
                        x.clone()
                    } else {
                        Exp::new(CondExp(c.clone(), x.clone(), b.clone()), meta(&rebuilt))
                    }
                } else if x == b {
                    let not = Exp::new(Not(inner.clone()), meta(inner));
                    let both = Exp::new(And(c.clone(), not), meta(c));
                    Exp::new(CondExp(both, y.clone(), x.clone()), meta(&rebuilt))
                } else if y == b {
                    let both = Exp::new(And(c.clone(), inner.clone()), meta(c));
                    Exp::new(CondExp(both, x.clone(), y.clone()), meta(&rebuilt))
                } else {
                    rebuilt.clone()
                }
            }
            CondExp(c, a, b) if matches!(b.kind(), CondExp(inner,x,y) if c == inner || a == x || a == y) =>
            {
                let CondExp(inner, x, y) = b.kind() else {
                    unreachable!()
                };
                if c == inner {
                    if a == y && defined(c)? {
                        a.clone()
                    } else {
                        Exp::new(CondExp(c.clone(), a.clone(), y.clone()), meta(&rebuilt))
                    }
                } else if a == x {
                    let either = Exp::new(Or(c.clone(), inner.clone()), meta(c));
                    Exp::new(CondExp(either, a.clone(), y.clone()), meta(&rebuilt))
                } else if a == y {
                    let not = Exp::new(Not(inner.clone()), meta(inner));
                    let either = Exp::new(Or(c.clone(), not), meta(c));
                    Exp::new(CondExp(either, a.clone(), x.clone()), meta(&rebuilt))
                } else {
                    rebuilt.clone()
                }
            }
            CondExp(c, a, b) if matches!(b.kind(),Implies(_,x) if a == x) => {
                let Implies(inner, x) = b.kind() else {
                    unreachable!()
                };
                if a == x {
                    let either = Exp::new(Or(c.clone(), inner.clone()), meta(c));
                    Exp::new(Implies(either, a.clone()), meta(&rebuilt))
                } else {
                    rebuilt.clone()
                }
            }
            CondExp(c, a, b) if matches!(a.kind(),Implies(_,x) if x == b) => {
                let Implies(inner, x) = a.kind() else {
                    unreachable!()
                };
                if x == b {
                    let not = Exp::new(Not(c.clone()), meta(c));
                    let either = Exp::new(Or(not, inner.clone()), meta(c));
                    Exp::new(Implies(either, x.clone()), meta(&rebuilt))
                } else {
                    rebuilt.clone()
                }
            }
            Forall(_, _, x) | Exists(_, _, x) if bool_value(x).is_some() => {
                literal(&rebuilt, bool_value(x).unwrap())
            }
            Minus(x) => match x.kind() {
                IntLit(n) => Exp::new(IntLit(-n), meta(&rebuilt)),
                Minus(y) => y.clone(),
                _ => rebuilt.clone(),
            },
            PermMinus(x) => match x.kind() {
                PermMinus(y) => y.clone(),
                _ => rebuilt.clone(),
            },
            PermMul(a, b) if matches!(a.kind(), FullPerm) => b.clone(),
            PermMul(a, b) if matches!(b.kind(), FullPerm) => a.clone(),
            PermMul(a, b) if permission_parts(a).is_some() && permission_parts(b).is_some() => {
                fraction(
                    &rebuilt,
                    &(rational(a)?.unwrap() * rational(b)?.unwrap()),
                    false,
                )
            }
            PermMul(a, b) if matches!(b.kind(), NoPerm) && defined(a)? => b.clone(),
            PermMul(a, b) if matches!(a.kind(), NoPerm) && defined(b)? => a.clone(),
            PermMul(a, b) if matches!(a.kind(), WildcardPerm) && defined(b)? => a.clone(),
            PermMul(a, b) if matches!(b.kind(), WildcardPerm) && defined(a)? => b.clone(),
            PermGeCmp(a, b) | PermLeCmp(a, b) | PermGtCmp(a, b) | PermLtCmp(a, b)
                if a == b && defined(a)? =>
            {
                literal(
                    &rebuilt,
                    matches!(rebuilt.kind(), PermGeCmp(..) | PermLeCmp(..)),
                )
            }
            PermGeCmp(a, b) | PermLeCmp(a, b) | PermGtCmp(a, b) | PermLtCmp(a, b)
                if permission_parts(a).is_some() && permission_parts(b).is_some() =>
            {
                let (a, b) = (rational(a)?.unwrap(), rational(b)?.unwrap());
                literal(
                    &rebuilt,
                    match rebuilt.kind() {
                        PermGeCmp(..) => a >= b,
                        PermLeCmp(..) => a <= b,
                        PermGtCmp(..) => a > b,
                        _ => a < b,
                    },
                )
            }
            PermLeCmp(a, b) if matches!((a.kind(), b.kind()), (NoPerm, WildcardPerm)) => {
                literal(&rebuilt, true)
            }
            DebugPermMin(a, b)
                if permission_parts(a).is_some() && permission_parts(b).is_some() =>
            {
                if rational(a)?.unwrap() < rational(b)?.unwrap() {
                    a.clone()
                } else {
                    b.clone()
                }
            }
            DebugPermMin(a, b) if matches!(a.kind(), NoPerm) && defined(b)? => {
                Exp::new(NoPerm, Metadata::default())
            }
            DebugPermMin(a, b) if matches!(b.kind(), NoPerm) && defined(a)? => {
                Exp::new(NoPerm, Metadata::default())
            }
            DebugPermMin(a, b)
                if permission_parts(a).is_some()
                    && matches!(b.kind(), CondExp(_,x,y) if permission_parts(x).is_some() && permission_parts(y).is_some()) =>
            {
                let CondExp(c, x, y) = b.kind() else {
                    unreachable!()
                };
                let r = rational(a)?.unwrap();
                let x = if r < rational(x)?.unwrap() {
                    a.clone()
                } else {
                    x.clone()
                };
                let y = if r < rational(y)?.unwrap() {
                    a.clone()
                } else {
                    y.clone()
                };
                Exp::new(CondExp(c.clone(), x, y), meta(&rebuilt))
            }
            DebugPermMin(a, b)
                if permission_parts(b).is_some()
                    && matches!(a.kind(), CondExp(_,x,y) if permission_parts(x).is_some() && permission_parts(y).is_some()) =>
            {
                let CondExp(c, x, y) = a.kind() else {
                    unreachable!()
                };
                let r = rational(b)?.unwrap();
                let x = if r < rational(x)?.unwrap() {
                    b.clone()
                } else {
                    x.clone()
                };
                let y = if r < rational(y)?.unwrap() {
                    b.clone()
                } else {
                    y.clone()
                };
                Exp::new(CondExp(c.clone(), x, y), meta(&rebuilt))
            }
            PermAdd(a, b) | PermSub(a, b)
                if permission_parts(a).is_some() && permission_parts(b).is_some() =>
            {
                let (a, b) = (rational(a)?.unwrap(), rational(b)?.unwrap());
                rational_to_perm(
                    &rebuilt,
                    &if matches!(rebuilt.kind(), PermAdd(..)) {
                        a + b
                    } else {
                        a - b
                    },
                    true,
                )
            }
            PermAdd(a, b) if matches!(a.kind(), NoPerm) => b.clone(),
            PermAdd(a, b) | PermSub(a, b) if matches!(b.kind(), NoPerm) => a.clone(),
            PermSub(a, b)
                if permission_parts(a).is_some()
                    && matches!(b.kind(),CondExp(_,x,y) if permission_parts(x).is_some() && permission_parts(y).is_some()) =>
            {
                let CondExp(c, x, y) = b.kind() else {
                    unreachable!()
                };
                let r = rational(a)?.unwrap();
                let x = rational_to_perm(&rebuilt, &(r.clone() - rational(x)?.unwrap()), false);
                let y = rational_to_perm(&rebuilt, &(r - rational(y)?.unwrap()), false);
                Exp::new(CondExp(c.clone(), x, y), meta(&rebuilt))
            }
            PermSub(a, b)
                if permission_parts(b).is_some()
                    && matches!(a.kind(),CondExp(_,x,y) if permission_parts(x).is_some() && permission_parts(y).is_some()) =>
            {
                let CondExp(c, x, y) = a.kind() else {
                    unreachable!()
                };
                let r = rational(b)?.unwrap();
                let x = rational_to_perm(&rebuilt, &(rational(x)?.unwrap() - r.clone()), false);
                let y = rational_to_perm(&rebuilt, &(rational(y)?.unwrap() - r), false);
                Exp::new(CondExp(c.clone(), x, y), meta(&rebuilt))
            }
            Add(a, b) | Sub(a, b) | Mul(a, b) | Div(a, b) | Mod(a, b) => match (a.kind(), b.kind())
            {
                (IntLit(x), IntLit(y)) => {
                    let value = match rebuilt.kind() {
                        Add(..) => Some(x + y),
                        Sub(..) => Some(x - y),
                        Mul(..) => Some(x * y),
                        Div(..) if !x.is_negative() && y > &0.into() => Some(x / y),
                        Mod(..) if !x.is_negative() && y > &0.into() => Some(x % y),
                        _ => None,
                    };
                    value
                        .map(|n| Exp::new(IntLit(n), meta(&rebuilt)))
                        .unwrap_or_else(|| rebuilt.clone())
                }
                _ => rebuilt.clone(),
            },
            GtCmp(a, b) | GeCmp(a, b) | LtCmp(a, b) | LeCmp(a, b) => match (a.kind(), b.kind()) {
                (IntLit(x), IntLit(y)) => literal(
                    &rebuilt,
                    match rebuilt.kind() {
                        GtCmp(..) => x > y,
                        GeCmp(..) => x >= y,
                        LtCmp(..) => x < y,
                        _ => x <= y,
                    },
                ),
                _ => rebuilt.clone(),
            },
            _ => rebuilt.clone(),
        };
        // Cache is mutable source state, so never hold a guard while recursively invoking callbacks.
        *rebuilt
            .0
            .simplified
            .write()
            .map_err(|_| SimplifyError::PoisonedCache)? = Some(if rebuilt.same_node(&result) {
            SimplifiedExp::Same
        } else {
            SimplifiedExp::Other(result.clone())
        });
        *result
            .0
            .simplified
            .write()
            .map_err(|_| SimplifyError::PoisonedCache)? = Some(SimplifiedExp::Same);
        Ok(result)
    }
    go(root, assume_well_defined, known_well_defined)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{expression::LocalVar, r#type::Type};
    #[test]
    fn cache_is_shared_across_well_definedness_modes_without_self_cycle() {
        let m = Metadata::default();
        let v = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Int, m.clone())),
            m.clone(),
        );
        let eq = Exp::new(ExpKind::EqCmp(v.clone(), v), m);
        let first = simplify(&eq, true, &|_| -> Result<bool, ()> {
            panic!("must not query")
        })
        .unwrap();
        let second = simplify(&eq, false, &|_| -> Result<bool, ()> {
            panic!("must use cache")
        })
        .unwrap();
        assert!(matches!(first.kind(), ExpKind::TrueLit));
        assert!(first.same_node(&second));
        let weak = std::sync::Arc::downgrade(&first.0);
        drop(first);
        drop(second);
        drop(eq);
        assert!(weak.upgrade().is_none());
    }
}

#[derive(Debug)]
pub enum StatementSimplifyError<E> {
    Expression(SimplifyError<E>),
    Reconstruction(super::statements::StatementReplacementError),
    Extension(crate::verifier::verification_result::DiagnosticError),
    Unsupported(&'static str),
}
impl<E> From<super::statements::StatementReplacementError> for StatementSimplifyError<E> {
    fn from(value: super::statements::StatementReplacementError) -> Self {
        Self::Reconstruction(value)
    }
}
/// Source bottom-up statement rules, with expression caching delegated to
/// `simplify`. Unsupported declaration products and extension hooks fail closed.
pub fn simplify_statement<E>(
    statement: &crate::ast::statement::Stmt,
    assume_well_defined: bool,
    known_well_defined: &impl Fn(&Exp) -> Result<bool, E>,
) -> Result<crate::ast::statement::Stmt, StatementSimplifyError<E>> {
    use crate::ast::{
        statement::{Stmt, StmtKind},
        utility::{
            nodes::Node,
            statements::{empty_stmt, map_statement_tree_with_post},
        },
    };
    use crate::verifier::verification_result::DiagnosticError;
    let simplify_exp = |e: &Exp| {
        simplify(e, assume_well_defined, known_well_defined)
            .map_err(StatementSimplifyError::Expression)
    };
    let empty = empty_stmt();
    let post = |node: &Node| -> Result<Node, StatementSimplifyError<E>> {
        let Node::Stmt(stmt) = node else {
            return Ok(node.clone());
        };
        let simplified = match stmt.kind() {
            // The source's earlier `Seqn(EmptyStmt, _)` constant pattern compares
            // a sequence with a statement and cannot match a Scala Seqn product.
            StmtKind::Seqn {
                statements,
                declarations,
            } if statements.contains(&empty) => Stmt::new(
                StmtKind::Seqn {
                    statements: statements
                        .iter()
                        .filter(|s| *s != &empty)
                        .cloned()
                        .collect(),
                    declarations: declarations.clone(),
                },
                stmt.metadata().clone(),
            ),
            StmtKind::If {
                then_branch,
                else_branch,
                ..
            } if then_branch == &empty && else_branch == &empty => empty.clone(),
            StmtKind::If {
                condition,
                then_branch,
                ..
            } if matches!(condition.kind(), ExpKind::TrueLit) => then_branch.clone(),
            StmtKind::If {
                condition,
                else_branch,
                ..
            } if matches!(condition.kind(), ExpKind::FalseLit) => else_branch.clone(),
            _ => stmt.clone(),
        };
        Ok(Node::Stmt(simplified))
    };
    let child = |node: &Node| -> Result<Node, StatementSimplifyError<E>> {
        match node {
            Node::LocalDecl(_)
            | Node::UnnamedLocalDecl(_)
            | Node::Member(crate::ast::program::Member::Field(_)) => Ok(node.clone()),
            Node::LabelDecl(label) => {
                let invariants = label
                    .invariants
                    .iter()
                    .map(&simplify_exp)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Node::LabelDecl(if invariants == label.invariants {
                    label.clone()
                } else {
                    label.copy_with(|v| v.invariants = invariants)
                }))
            }
            _ => Err(StatementSimplifyError::Unsupported(
                "statement declaration product",
            )),
        }
    };
    let extension =
        |extension: &crate::ast::statement::ExtensionStmtHandle,
         _map: &dyn Fn(&Exp) -> Result<Exp, StatementSimplifyError<E>>| {
            let failure = std::cell::RefCell::new(None);
            let mapped = extension.0.map_expressions(&|e| match simplify_exp(e) {
                Ok(value) => Ok(value),
                Err(error) => {
                    *failure.borrow_mut() = Some(error);
                    Err(DiagnosticError::Unsupported("statement simplification"))
                }
            });
            if let Some(error) = failure.into_inner() {
                return Err(error);
            }
            mapped.map_err(StatementSimplifyError::Extension)
        };
    map_statement_tree_with_post(
        statement,
        &simplify_exp,
        &|n| Ok(n.clone()),
        &child,
        &extension,
        Some(&post),
        false,
    )
}

#[cfg(test)]
mod statement_tests {
    use super::*;
    use crate::ast::{
        program::{Declaration, LocalVarDecl},
        statement::{Stmt, StmtKind},
        r#type::Type,
        utility::statements::empty_stmt,
    };
    #[test]
    fn statement_simplification_keeps_scoped_declarations_and_removes_empty_children() {
        let meta = Metadata::default();
        let declaration =
            Declaration::Local(LocalVarDecl::new("x".into(), Type::Int, meta.clone()));
        let stmt = Stmt::new(
            StmtKind::Seqn {
                statements: vec![empty_stmt()],
                declarations: vec![declaration],
            },
            meta,
        );
        let result =
            simplify_statement(&stmt, false, &|_| Ok::<_, std::convert::Infallible>(true)).unwrap();
        assert!(
            matches!(result.kind(),StmtKind::Seqn{statements,declarations} if statements.is_empty()&&declarations.len()==1)
        );
    }
    #[test]
    fn empty_branches_use_shared_source_empty_statement() {
        let meta = Metadata::default();
        let stmt = Stmt::new(
            StmtKind::If {
                condition: Exp::new(ExpKind::TrueLit, meta.clone()),
                then_branch: empty_stmt(),
                else_branch: empty_stmt(),
            },
            meta,
        );
        let result =
            simplify_statement(&stmt, false, &|_| Ok::<_, std::convert::Infallible>(true)).unwrap();
        assert!(result.same_node(&empty_stmt()));
    }
}
