//! Counterexample values and rational permissions.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/Counterexample.scala
//! Status: partial; literal conversion and Rational are implemented. Raw/resolved heap,
//! collection, store, domain/function models and wand substitution remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpKind},
    r#type::Type,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use regex::Regex;
use std::{cmp::Ordering, fmt, sync::OnceLock};

pub fn parse_int(value: &str) -> Option<BigInt> {
    let value = value.trim();
    if let Ok(i) = value.parse() {
        return Some(i);
    }
    static NEGATIVE: OnceLock<Regex> = OnceLock::new();
    let captures = NEGATIVE
        .get_or_init(|| Regex::new(r"^\(\s*-\s*(\d+)\s*\)$").unwrap())
        .captures(value)?;
    captures[1].parse::<BigInt>().ok().map(|n| -n)
}
pub fn parse_bool(value: &str) -> Option<bool> {
    match value.trim().to_lowercase().as_str() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}
fn rational_token(value: &str) -> Option<(BigInt, BigInt)> {
    let value = value.trim();
    let mut pieces: Vec<_> = value.split('/').collect();
    if !value.is_empty() {
        while pieces.last() == Some(&"") {
            pieces.pop();
        }
    }
    match pieces.as_slice() {
        [n, d] => {
            let n = parse_int(n)?;
            let d = parse_int(d)?;
            (!d.is_zero()).then_some((n, d))
        }
        [single] if single.contains('.') => {
            let (i, f) = single.split_once('.')?;
            let digits = format!("{i}{f}");
            Some((
                parse_int(if digits.is_empty() { "0" } else { &digits })?,
                BigInt::from(10).pow(f.len().try_into().ok()?),
            ))
        }
        [single] => Some((parse_int(single)?, BigInt::one())),
        _ => None,
    }
}
pub fn parse_perm(value: &str) -> Option<Exp> {
    static DIV: OnceLock<Regex> = OnceLock::new();
    let value = value.trim();
    let (n, d) = if let Some(c) = DIV
        .get_or_init(|| Regex::new(r"^\(\s*/\s+(\S+)\s+(\S+)\s*\)$").unwrap())
        .captures(value)
    {
        let (an, ad) = rational_token(&c[1])?;
        let (bn, bd) = rational_token(&c[2])?;
        if bn.is_zero() {
            return None;
        }
        (an * bd, ad * bn)
    } else {
        rational_token(value)?
    };
    // Scala reduces by a nonnegative gcd, but does not normalize the denominator's sign here.
    let gcd = BigRational::new(n.clone(), d.clone()).denom().clone();
    let divisor = d.abs() / gcd;
    Some(Exp::new(
        ExpKind::BackendValueLit(format!("{}/{}", n / &divisor, d / divisor), Type::Perm),
        Metadata::default(),
    ))
}
pub fn infer_literal(value: &str) -> Exp {
    literal(value, None)
}
pub fn literal(value: &str, typ: Option<&Type>) -> Exp {
    let kind = match typ {
        Some(Type::Int) => parse_int(value)
            .map(ExpKind::IntLit)
            .unwrap_or_else(|| ExpKind::BackendValueLit(value.into(), Type::Int)),
        Some(Type::Bool) => parse_bool(value)
            .map(|v| {
                if v {
                    ExpKind::TrueLit
                } else {
                    ExpKind::FalseLit
                }
            })
            .unwrap_or_else(|| ExpKind::BackendValueLit(value.into(), Type::Bool)),
        Some(Type::Ref) => ExpKind::RefLit(value.into()),
        Some(Type::Perm) => {
            return parse_perm(value).unwrap_or_else(|| {
                Exp::new(
                    ExpKind::BackendValueLit(value.into(), Type::Perm),
                    Metadata::default(),
                )
            });
        }
        Some(t) => ExpKind::BackendValueLit(value.into(), t.clone()),
        None => {
            if let Some(n) = parse_int(value) {
                ExpKind::IntLit(n)
            } else if let Some(b) = parse_bool(value) {
                if b {
                    ExpKind::TrueLit
                } else {
                    ExpKind::FalseLit
                }
            } else {
                ExpKind::BackendValueLit(value.into(), Type::InternalType)
            }
        }
    };
    Exp::new(kind, Metadata::default())
}

/// Exact normalized rational. The Scala hash uses the original inputs despite normalized
/// equality, so no Hash implementation is offered here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rational(BigRational);
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ZeroDenominator;
impl Rational {
    pub fn new(n: BigInt, d: BigInt) -> Result<Self, ZeroDenominator> {
        if d.is_zero() {
            Err(ZeroDenominator)
        } else {
            Ok(Self(BigRational::new(n, d)))
        }
    }
    pub fn numerator(&self) -> &BigInt {
        self.0.numer()
    }
    pub fn denominator(&self) -> &BigInt {
        self.0.denom()
    }
    pub fn inverse(&self) -> Result<Self, ZeroDenominator> {
        Self::new(self.denominator().clone(), self.numerator().clone())
    }
    pub fn abs(&self) -> Self {
        Self(self.0.abs())
    }
    pub fn signum(&self) -> Self {
        Self(BigRational::from_integer(self.numerator().signum()))
    }
    pub fn add(&self, other: &Self) -> Self {
        Self(&self.0 + &other.0)
    }
    pub fn subtract(&self, other: &Self) -> Self {
        Self(&self.0 - &other.0)
    }
    pub fn multiply(&self, other: &Self) -> Self {
        Self(&self.0 * &other.0)
    }
    pub fn divide(&self, other: &Self) -> Result<Self, ZeroDenominator> {
        Ok(self.multiply(&other.inverse()?))
    }
    pub fn negate(&self) -> Self {
        Self(-&self.0)
    }
}
impl Ord for Rational {
    fn cmp(&self, rhs: &Self) -> Ordering {
        self.0.cmp(&rhs.0)
    }
}
impl PartialOrd for Rational {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}
impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.numerator(), self.denominator())
    }
}
