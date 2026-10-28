//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/ResourceDescriptions.scala
//!
//! Purpose:
//! Define assumptions for field, predicate and wand chunks.
//!
//! Planned Rust structure:
//! Port ResourceDescription, BasicDescription, PredicateDescription, FieldDescription and
//! MagicWandDescription, including named property constructors.
//!
//! Behavior to preserve:
//! All require nonnegative permissions; fields additionally require positive permission implies
//! non-null receiver. Configured upper bounds add at-most-one instance property and delayed
//! pairwise permission-sum disequality. Basic delayed property checks positive permissions and
//! distinct values imply distinct arguments; wand has no delayed properties. Preserve property
//! order and Check semantics.
//!
//! Integration:
//! resources::{resources,property,property_expressions}, property interpreters and
//! rules::state_consolidator.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact permission terms, ordering and delayed assumptions.
//!
//! Open decisions:
//! Agree on upper-bound configuration and heap consolidation boundaries with rules and state.
//!
//! Status: implemented source property descriptions and upper-bound selection.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::property::Property;
use super::property_expressions::{
    ArgumentExpression as A, BooleanExpression as B, ChunkPlaceholder as C,
    PermissionExpression as P, ValueExpression as V,
};
use num_bigint::BigInt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceDescription {
    Predicate,
    Field,
    MagicWand,
}
fn lit(n: i32) -> P {
    P::Literal(BigInt::from(n), BigInt::from(1))
}
fn perm(c: C) -> P {
    P::Access(c)
}
fn property(expression: B, name: &str, description: &str) -> Property {
    Property::new(expression, name, description).expect("static property name")
}
fn nonnegative(wand: bool) -> Property {
    property(
        B::GreaterThanEquals(perm(C::This), lit(0)),
        "permAtLeastZero",
        if wand {
            "Permissons are non-negative"
        } else {
            "Permissions are non-negative"
        },
    )
}
fn different_values() -> Property {
    let a = C::variable("c1").unwrap();
    let b = C::variable("c2").unwrap();
    let positive = B::And(
        Box::new(B::GreaterThan(perm(a.clone()), lit(0))),
        Box::new(B::GreaterThan(perm(b.clone()), lit(0))),
    );
    let unequal_values = B::Not(Box::new(B::EqualsValue(
        V::Access(a.clone()),
        V::Access(b.clone()),
    )));
    let condition = B::And(Box::new(positive), Box::new(unequal_values));
    let unequal_args = B::Not(Box::new(B::EqualsArgument(
        A::Access(a.clone()),
        A::Access(b.clone()),
    )));
    let body = B::Check(
        Box::new(condition),
        Box::new(unequal_args),
        Box::new(B::Literal(true)),
    );
    property(
        B::for_each(vec![a, b], body).unwrap(),
        "valNeqImpliesLocNeq",
        "Different values imply different arguments",
    )
}
fn upper_bound_disequality() -> Property {
    let a = C::variable("c1").unwrap();
    let b = C::variable("c2").unwrap();
    let sum = P::Plus(Box::new(perm(a.clone())), Box::new(perm(b.clone())));
    let condition = B::GreaterThan(sum, lit(1));
    let unequal_args = B::Not(Box::new(B::EqualsArgument(
        A::Access(a.clone()),
        A::Access(b.clone()),
    )));
    let body = B::Check(
        Box::new(condition),
        Box::new(unequal_args),
        Box::new(B::Literal(true)),
    );
    property(
        B::for_each(vec![a, b], body).unwrap(),
        "permUpperBoundDiseq",
        "Permission sum greater than one implies non-equal receivers",
    )
}
impl ResourceDescription {
    pub fn instance_properties(self, with_perm_upper_bounds: bool) -> Vec<Property> {
        let mut result = vec![nonnegative(self == Self::MagicWand)];
        if self == Self::Field {
            if with_perm_upper_bounds {
                result.push(property(
                    B::LessThanEquals(perm(C::This), lit(1)),
                    "permAtMostOne",
                    "Field permissions are at most one",
                ));
            }
            let nonnull = B::Not(Box::new(B::EqualsArgument(A::Access(C::This), A::Null)));
            result.push(property(
                B::Implies(
                    Box::new(B::GreaterThan(perm(C::This), lit(0))),
                    Box::new(nonnull),
                ),
                "permImpliesNonNull",
                "Permission implies non-null receiver",
            ));
        }
        result
    }
    pub fn delayed_properties(self, with_perm_upper_bounds: bool) -> Vec<Property> {
        if self == Self::MagicWand {
            return vec![];
        }
        let mut result = Vec::new();
        if self == Self::Field && with_perm_upper_bounds {
            result.push(upper_bound_disequality());
        }
        result.push(different_values());
        result
    }
}
impl std::fmt::Display for ResourceDescription {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Predicate => "Predicate",
            Self::Field => "Field",
            Self::MagicWand => "Magic Wand",
        })
    }
}
