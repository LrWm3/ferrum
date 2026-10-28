//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/PropertyInterpreter.scala
//!
//! Purpose:
//! Translate property expressions to symbolic path conditions and optional debug AST.
//!
//! Planned Rust structure:
//! Port PropertyInterpreter buildPathCondition and literal, Boolean, equality, arithmetic, ITE and
//! abstract chunk/check/foreach helpers.
//!
//! Behavior to preserve:
//! Short circuit And/Or/Implies when left is syntactically decisive. Compare argument lists
//! componentwise, handle Null specially; reject zero denominator and retain exact fractions. Debug
//! mode constructs corresponding AST; Check and ForEach are delegated. Preserve greater
//! comparisons by swapping operands and conditional AST shape.
//!
//! Integration:
//! resources::{property_expressions,non_quantified_property_interpreter,quantified_property_interpreter};
//! state::terms, verifier and Silver AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for symbolic/debug expression pairing and exact arithmetic.
//!
//! Open decisions:
//! Reconcile debug expression availability and generic interpreter dispatch with specialized
//! implementations.
//!
//! Status: partial; term interpretation implemented using explicit heap/control callbacks.
//! Debug expression construction and concrete chunk contexts remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::property_expressions::{
    ArgumentExpression as A, BooleanExpression as B, ChunkPlaceholder, PermissionExpression as P,
    ValueExpression as V,
};
use crate::state::terms::{Term, TermFactory, TermKind};
use num_traits::Zero;

#[derive(Debug)]
pub enum PropertyError<E> {
    Context(E),
    ZeroDenominator,
    InvalidQuantifier,
}
/// Supplies heap accesses and the two source-specific control constructs.
pub trait PropertyContext {
    type Error;
    fn permission(&mut self, chunk: &ChunkPlaceholder) -> Result<Term, Self::Error>;
    fn value(&mut self, chunk: &ChunkPlaceholder) -> Result<Term, Self::Error>;
    fn arguments(&mut self, chunk: &ChunkPlaceholder) -> Result<Vec<Term>, Self::Error>;
    /// Nonquantified evaluation checks the prover; quantified evaluation returns an ITE.
    fn check(&mut self, condition: &Term) -> Result<Option<bool>, Self::Error>;
    fn for_each(
        &mut self,
        factory: &TermFactory,
        variables: &[ChunkPlaceholder],
        body: &B,
    ) -> Result<Term, PropertyError<Self::Error>>;
}
pub struct PropertyInterpreter<'a, C> {
    pub factory: &'a TermFactory,
    pub context: C,
}
impl<C: PropertyContext> PropertyInterpreter<'_, C> {
    fn arguments(&mut self, arg: &A) -> Result<Vec<Term>, PropertyError<C::Error>> {
        match arg {
            A::Null => Ok(vec![self.factory.null()]),
            A::Access(c) => self.context.arguments(c).map_err(PropertyError::Context),
        }
    }
    pub fn boolean(&mut self, e: &B) -> Result<Term, PropertyError<C::Error>> {
        let f = self.factory;
        Ok(match e {
            B::Literal(v) => f.boolean(*v),
            B::Not(x) => f.not(self.boolean(x)?),
            B::And(a, b) => {
                let x = self.boolean(a)?;
                if matches!(x.kind(), TermKind::False) {
                    x
                } else {
                    f.and([x, self.boolean(b)?])
                }
            }
            B::Or(a, b) => {
                let x = self.boolean(a)?;
                if matches!(x.kind(), TermKind::True) {
                    x
                } else {
                    f.or([x, self.boolean(b)?])
                }
            }
            B::Implies(a, b) => {
                let x = self.boolean(a)?;
                if matches!(x.kind(), TermKind::False) {
                    f.boolean(true)
                } else {
                    f.implies(x, self.boolean(b)?)
                }
            }
            B::EqualsBoolean(a, b) => f.equals(self.boolean(a)?, self.boolean(b)?),
            B::EqualsValue(a, b) => f.equals(self.value(a)?, self.value(b)?),
            B::EqualsPermission(a, b) => f.equals(self.permission(a)?, self.permission(b)?),
            B::EqualsArgument(A::Null, A::Null) => f.boolean(true),
            B::EqualsArgument(A::Access(c), A::Null) | B::EqualsArgument(A::Null, A::Access(c)) => {
                f.and(
                    self.context
                        .arguments(c)
                        .map_err(PropertyError::Context)?
                        .into_iter()
                        .map(|x| f.equals(x, f.null())),
                )
            }
            B::EqualsArgument(a, b) => {
                let a = self.arguments(a)?;
                let b = self.arguments(b)?;
                if a == b {
                    f.boolean(true)
                } else {
                    f.and(a.into_iter().zip(b).map(|(a, b)| f.equals(a, b)))
                }
            }
            B::GreaterThan(a, b) => f.perm_less(self.permission(b)?, self.permission(a)?),
            B::GreaterThanEquals(a, b) => f.perm_at_most(self.permission(b)?, self.permission(a)?),
            B::LessThan(a, b) => f.perm_less(self.permission(a)?, self.permission(b)?),
            B::LessThanEquals(a, b) => f.perm_at_most(self.permission(a)?, self.permission(b)?),
            B::IfThenElse(c, a, b) => f.ite(self.boolean(c)?, self.boolean(a)?, self.boolean(b)?),
            B::Check(c, a, b) => {
                let c = self.boolean(c)?;
                match self.context.check(&c).map_err(PropertyError::Context)? {
                    Some(true) => self.boolean(a)?,
                    Some(false) => self.boolean(b)?,
                    None => f.ite(c, self.boolean(a)?, self.boolean(b)?),
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
    pub fn permission(&mut self, e: &P) -> Result<Term, PropertyError<C::Error>> {
        let f = self.factory;
        Ok(match e {
            P::Literal(_, d) if d.is_zero() => return Err(PropertyError::ZeroDenominator),
            P::Literal(n, _) if n.is_zero() => f.no_perm(),
            P::Literal(n, d) if n == d => f.full_perm(),
            P::Literal(n, d) => f.fraction_perm(f.int_literal(n.clone()), f.int_literal(d.clone())),
            P::Access(c) => self.context.permission(c).map_err(PropertyError::Context)?,
            P::Plus(a, b) => f.perm_plus(self.permission(a)?, self.permission(b)?),
            P::Minus(a, b) => f.perm_minus(self.permission(a)?, self.permission(b)?),
            P::Times(a, b) => f.perm_times(self.permission(a)?, self.permission(b)?),
            P::Div(a, b) => f.perm_div(self.permission(a)?, self.permission(b)?),
            P::IfThenElse(c, a, b) => {
                f.ite(self.boolean(c)?, self.permission(a)?, self.permission(b)?)
            }
            P::Check(c, a, b) => {
                let c = self.boolean(c)?;
                match self.context.check(&c).map_err(PropertyError::Context)? {
                    Some(true) => self.permission(a)?,
                    Some(false) => self.permission(b)?,
                    None => f.ite(c, self.permission(a)?, self.permission(b)?),
                }
            }
        })
    }
    pub fn value(&mut self, e: &V) -> Result<Term, PropertyError<C::Error>> {
        let f = self.factory;
        Ok(match e {
            V::Access(c) => self.context.value(c).map_err(PropertyError::Context)?,
            V::IfThenElse(c, a, b) => f.ite(self.boolean(c)?, self.value(a)?, self.value(b)?),
            V::Check(c, a, b) => {
                let c = self.boolean(c)?;
                match self.context.check(&c).map_err(PropertyError::Context)? {
                    Some(true) => self.value(a)?,
                    Some(false) => self.value(b)?,
                    None => f.ite(c, self.value(a)?, self.value(b)?),
                }
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::TermOptions;
    struct NoAccess;
    impl PropertyContext for NoAccess {
        type Error = ();
        fn permission(&mut self, _: &ChunkPlaceholder) -> Result<Term, ()> {
            panic!("short circuit")
        }
        fn value(&mut self, _: &ChunkPlaceholder) -> Result<Term, ()> {
            panic!("short circuit")
        }
        fn arguments(&mut self, _: &ChunkPlaceholder) -> Result<Vec<Term>, ()> {
            panic!("short circuit")
        }
        fn check(&mut self, _: &Term) -> Result<Option<bool>, ()> {
            panic!("short circuit")
        }
        fn for_each(
            &mut self,
            _: &TermFactory,
            _: &[ChunkPlaceholder],
            _: &B,
        ) -> Result<Term, PropertyError<()>> {
            panic!("short circuit")
        }
    }
    #[test]
    fn false_and_skips_heap_and_solver() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let right = B::GreaterThan(
            P::Access(ChunkPlaceholder::This),
            P::Literal(0.into(), 1.into()),
        );
        let expr = B::And(Box::new(B::Literal(false)), Box::new(right));
        let result = PropertyInterpreter {
            factory: &f,
            context: NoAccess,
        }
        .boolean(&expr)
        .unwrap();
        assert!(matches!(result.kind(), TermKind::False));
    }
}
