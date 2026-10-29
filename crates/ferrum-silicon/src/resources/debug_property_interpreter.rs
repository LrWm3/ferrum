//! Ferrum paired symbolic/debug resource-property assembly described in PLAN.md.
//! Source traversal: [PropertyInterpreter.scala](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/PropertyInterpreter.scala).
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::property_expressions::{
    ArgumentExpression as A, BooleanExpression as B, ChunkPlaceholder, PermissionExpression as P,
    ValueExpression as V,
};
use super::property_interpreter::PropertyError;
use crate::state::terms::{Term, TermFactory, TermKind};
use ferrum_silver::ast::{
    ast::Metadata,
    expression::{Exp, ExpKind},
    position::Position,
};
use num_traits::Zero;

pub type Pair = (Term, Exp);
pub trait DebugPropertyContext {
    type Error;
    fn permission(&mut self, chunk: &ChunkPlaceholder) -> Result<Pair, Self::Error>;
    fn value(&mut self, chunk: &ChunkPlaceholder) -> Result<Pair, Self::Error>;
    fn arguments(&mut self, chunk: &ChunkPlaceholder)
    -> Result<(Vec<Term>, Vec<Exp>), Self::Error>;
    fn check(&mut self, condition: &Term) -> Result<Option<bool>, Self::Error>;
    fn for_each(
        &mut self,
        factory: &TermFactory,
        variables: &[ChunkPlaceholder],
        body: &B,
    ) -> Result<Pair, PropertyError<Self::Error>>;
}
pub struct DebugPropertyInterpreter<'a, C> {
    pub factory: &'a TermFactory,
    pub context: C,
}
fn literal(kind: ExpKind) -> Exp {
    Exp::new(kind, Metadata::default())
}
fn unary(arg: Exp, kind: impl FnOnce(Exp) -> ExpKind) -> Exp {
    let meta = arg.metadata().clone();
    Exp::new(kind(arg), meta)
}
fn binary(a: Exp, b: Exp, kind: impl FnOnce(Exp, Exp) -> ExpKind) -> Exp {
    let meta = a.metadata().clone();
    Exp::new(kind(a, b), meta)
}
fn big_and(items: Vec<Exp>) -> Exp {
    crate::utils::ast::big_and(items, |e| e, Position::NoPosition)
}
impl<C: DebugPropertyContext> DebugPropertyInterpreter<'_, C> {
    fn arguments(&mut self, a: &A) -> Result<(Vec<Term>, Vec<Exp>), PropertyError<C::Error>> {
        match a {
            A::Null => Ok((vec![self.factory.null()], vec![literal(ExpKind::NullLit)])),
            A::Access(c) => self.context.arguments(c).map_err(PropertyError::Context),
        }
    }
    pub fn boolean(&mut self, e: &B) -> Result<Pair, PropertyError<C::Error>> {
        let f = self.factory;
        Ok(match e {
            B::Literal(v) => (
                f.boolean(*v),
                literal(if *v {
                    ExpKind::TrueLit
                } else {
                    ExpKind::FalseLit
                }),
            ),
            B::Not(x) => {
                let (t, e) = self.boolean(x)?;
                (f.not(t), unary(e, ExpKind::Not))
            }
            B::And(a, b) | B::Or(a, b) | B::Implies(a, b) => {
                let (x, xe) = self.boolean(a)?;
                if matches!(e, B::And(..)) && matches!(x.kind(), TermKind::False)
                    || matches!(e, B::Or(..)) && matches!(x.kind(), TermKind::True)
                {
                    (x, xe)
                } else if matches!(e, B::Implies(..)) && matches!(x.kind(), TermKind::False) {
                    (f.boolean(true), literal(ExpKind::TrueLit))
                } else {
                    let (y, ye) = self.boolean(b)?;
                    match e {
                        B::And(..) => (f.and([x, y]), binary(xe, ye, ExpKind::And)),
                        B::Or(..) => (f.or([x, y]), binary(xe, ye, ExpKind::Or)),
                        _ => (f.implies(x, y), binary(xe, ye, ExpKind::Implies)),
                    }
                }
            }
            B::EqualsBoolean(a, b) => {
                let (x, xe) = self.boolean(a)?;
                let (y, ye) = self.boolean(b)?;
                (f.equals(x, y), binary(xe, ye, ExpKind::EqCmp))
            }
            B::EqualsValue(a, b) => {
                let (x, xe) = self.value(a)?;
                let (y, ye) = self.value(b)?;
                (f.equals(x, y), binary(xe, ye, ExpKind::EqCmp))
            }
            B::EqualsPermission(a, b) => {
                let (x, xe) = self.permission(a)?;
                let (y, ye) = self.permission(b)?;
                (f.equals(x, y), binary(xe, ye, ExpKind::EqCmp))
            }
            B::EqualsArgument(A::Null, A::Null) => (f.boolean(true), literal(ExpKind::TrueLit)),
            B::EqualsArgument(A::Access(c), A::Null) | B::EqualsArgument(A::Null, A::Access(c)) => {
                let (args, exps) = self.context.arguments(c).map_err(PropertyError::Context)?;
                (
                    f.and(args.into_iter().map(|t| f.equals(t, f.null()))),
                    big_and(
                        exps.into_iter()
                            .map(|e| {
                                Exp::new(
                                    ExpKind::EqCmp(e, literal(ExpKind::NullLit)),
                                    Metadata::default(),
                                )
                            })
                            .collect(),
                    ),
                )
            }
            B::EqualsArgument(a, b) => {
                let (x, xe) = self.arguments(a)?;
                let (y, ye) = self.arguments(b)?;
                if x == y {
                    (f.boolean(true), literal(ExpKind::TrueLit))
                } else {
                    (
                        f.and(x.into_iter().zip(y).map(|(a, b)| f.equals(a, b))),
                        big_and(
                            xe.into_iter()
                                .zip(ye)
                                .map(|(a, b)| binary(a, b, ExpKind::EqCmp))
                                .collect(),
                        ),
                    )
                }
            }
            B::GreaterThan(a, b)
            | B::GreaterThanEquals(a, b)
            | B::LessThan(a, b)
            | B::LessThanEquals(a, b) => {
                let (a, b) = if matches!(e, B::GreaterThan(..) | B::GreaterThanEquals(..)) {
                    (b, a)
                } else {
                    (a, b)
                };
                let (x, xe) = self.permission(a)?;
                let (y, ye) = self.permission(b)?;
                if matches!(e, B::GreaterThan(..) | B::LessThan(..)) {
                    (f.perm_less(x, y), binary(xe, ye, ExpKind::PermLtCmp))
                } else {
                    (f.perm_at_most(x, y), binary(xe, ye, ExpKind::PermLeCmp))
                }
            }
            B::IfThenElse(c, a, b) => {
                let (ct, ce) = self.boolean(c)?;
                let (at, ae) = self.boolean(a)?;
                let (bt, be) = self.boolean(b)?;
                (f.ite(ct, at, bt), ite_exp(ce, ae, be))
            }
            B::Check(c, a, b) => {
                let (ct, ce) = self.boolean(c)?;
                match self.context.check(&ct).map_err(PropertyError::Context)? {
                    Some(true) => self.boolean(a)?,
                    Some(false) => self.boolean(b)?,
                    None => {
                        let (at, ae) = self.boolean(a)?;
                        let (bt, be) = self.boolean(b)?;
                        (f.ite(ct, at, bt), ite_exp(ce, ae, be))
                    }
                }
            }
            B::ForEach(vars, body) => {
                let unique: std::collections::HashSet<_> = vars.iter().collect();
                if vars.is_empty()
                    || unique.len() != vars.len()
                    || vars.iter().any(|v| matches!(v, ChunkPlaceholder::This))
                {
                    return Err(PropertyError::InvalidQuantifier);
                }
                self.context.for_each(f, vars, body)?
            }
        })
    }
    pub fn permission(&mut self, e: &P) -> Result<Pair, PropertyError<C::Error>> {
        let f = self.factory;
        Ok(match e {
            P::Literal(_, d) if d.is_zero() => return Err(PropertyError::ZeroDenominator),
            P::Literal(n, _) if n.is_zero() => (f.no_perm(), literal(ExpKind::NoPerm)),
            P::Literal(n, d) if n == d => (f.full_perm(), literal(ExpKind::FullPerm)),
            P::Literal(n, d) => (
                f.fraction_perm(f.int_literal(n.clone()), f.int_literal(d.clone())),
                literal(ExpKind::FractionalPerm(
                    literal(ExpKind::IntLit(n.clone())),
                    literal(ExpKind::IntLit(d.clone())),
                )),
            ),
            P::Access(c) => self.context.permission(c).map_err(PropertyError::Context)?,
            P::Plus(a, b) | P::Minus(a, b) | P::Times(a, b) | P::Div(a, b) => {
                let (x, xe) = self.permission(a)?;
                let (y, ye) = self.permission(b)?;
                match e {
                    P::Plus(..) => (f.perm_plus(x, y), binary(xe, ye, ExpKind::PermAdd)),
                    P::Minus(..) => (f.perm_minus(x, y), binary(xe, ye, ExpKind::PermSub)),
                    P::Times(..) => (f.perm_times(x, y), binary(xe, ye, ExpKind::PermMul)),
                    _ => (f.perm_div(x, y), binary(xe, ye, ExpKind::PermDiv)),
                }
            }
            P::IfThenElse(c, a, b) => {
                let (ct, ce) = self.boolean(c)?;
                let (at, ae) = self.permission(a)?;
                let (bt, be) = self.permission(b)?;
                (f.ite(ct, at, bt), ite_exp(ce, ae, be))
            }
            P::Check(c, a, b) => {
                let (ct, ce) = self.boolean(c)?;
                match self.context.check(&ct).map_err(PropertyError::Context)? {
                    Some(true) => self.permission(a)?,
                    Some(false) => self.permission(b)?,
                    None => {
                        let (at, ae) = self.permission(a)?;
                        let (bt, be) = self.permission(b)?;
                        (f.ite(ct, at, bt), ite_exp(ce, ae, be))
                    }
                }
            }
        })
    }
    pub fn value(&mut self, e: &V) -> Result<Pair, PropertyError<C::Error>> {
        let f = self.factory;
        Ok(match e {
            V::Access(c) => self.context.value(c).map_err(PropertyError::Context)?,
            V::IfThenElse(c, a, b) => {
                let (ct, ce) = self.boolean(c)?;
                let (at, ae) = self.value(a)?;
                let (bt, be) = self.value(b)?;
                (f.ite(ct, at, bt), ite_exp(ce, ae, be))
            }
            V::Check(c, a, b) => {
                let (ct, ce) = self.boolean(c)?;
                match self.context.check(&ct).map_err(PropertyError::Context)? {
                    Some(true) => self.value(a)?,
                    Some(false) => self.value(b)?,
                    None => {
                        let (at, ae) = self.value(a)?;
                        let (bt, be) = self.value(b)?;
                        (f.ite(ct, at, bt), ite_exp(ce, ae, be))
                    }
                }
            }
        })
    }
}
fn ite_exp(c: Exp, a: Exp, b: Exp) -> Exp {
    literal(ExpKind::And(
        literal(ExpKind::Implies(c.clone(), a)),
        literal(ExpKind::Implies(literal(ExpKind::Not(c)), b)),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::TermOptions;
    struct Checks {
        calls: Vec<bool>,
    }
    impl DebugPropertyContext for &mut Checks {
        type Error = ();
        fn permission(&mut self, _: &ChunkPlaceholder) -> Result<Pair, ()> {
            panic!("unexpected permission")
        }
        fn value(&mut self, _: &ChunkPlaceholder) -> Result<Pair, ()> {
            panic!("unexpected value")
        }
        fn arguments(&mut self, _: &ChunkPlaceholder) -> Result<(Vec<Term>, Vec<Exp>), ()> {
            panic!("unexpected arguments")
        }
        fn check(&mut self, term: &Term) -> Result<Option<bool>, ()> {
            let b = matches!(term.kind(), TermKind::True);
            self.calls.push(b);
            Ok(Some(b))
        }
        fn for_each(
            &mut self,
            _: &TermFactory,
            _: &[ChunkPlaceholder],
            _: &B,
        ) -> Result<Pair, PropertyError<()>> {
            panic!("unexpected foreach")
        }
    }
    #[test]
    fn nested_checks_execute_once_and_only_follow_selected_branch() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let check = |c, a, b| B::Check(Box::new(B::Literal(c)), Box::new(a), Box::new(b));
        let property = check(
            true,
            check(false, B::Literal(false), B::Literal(true)),
            check(true, B::Literal(false), B::Literal(false)),
        );
        let mut context = Checks { calls: vec![] };
        let (term, exp) = DebugPropertyInterpreter {
            factory: &f,
            context: &mut context,
        }
        .boolean(&property)
        .unwrap();
        assert!(matches!(term.kind(), TermKind::True));
        assert!(matches!(exp.kind(), ExpKind::TrueLit));
        assert_eq!(context.calls, vec![true, false]);
    }
}
