//! Interpreted bitvector and floating-point domain factories.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/BackendTypeFactories.scala
//! Status: implemented; callers still need the backend interpretation consumers.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use crate::ast::{
    ast::Metadata,
    program::{AnyLocalVarDecl, Domain, DomainFunc, LocalVarDecl},
    r#type::{BackendType, Type},
};
use std::collections::HashMap;

fn interpretations(boogie: String, smt: String) -> HashMap<String, String> {
    [("Boogie".into(), boogie), ("SMTLIB".into(), smt)]
        .into_iter()
        .collect()
}
fn function(name: &str, smt: String, result: Type, args: Vec<Type>) -> DomainFunc {
    DomainFunc::new(crate::ast::program::DomainFuncData {
        name: name.into(),
        domain_name: name.into(),
        formal_args: args
            .into_iter()
            .enumerate()
            .map(|(i, t)| {
                AnyLocalVarDecl::Named(LocalVarDecl::new(
                    if i == 0 { "x" } else { "y" }.into(),
                    t,
                    Metadata::default(),
                ))
            })
            .collect(),
        typ: result,
        unique: false,
        interpretation: Some(smt),
        meta: Metadata::default(),
    })
}
fn domain(
    name: String,
    interpretations: HashMap<String, String>,
    functions: Vec<DomainFunc>,
) -> Domain {
    Domain::new(crate::ast::program::DomainData {
        name,
        functions,
        axioms: Vec::new(),
        type_vars: Vec::new(),
        interpretations: Some(interpretations),
        meta: Metadata::default(),
    })
}
macro_rules! bit_binary {
    ($($method:ident => $op:literal),* $(,)?) => { $(pub fn $method(&self, name: &str) -> DomainFunc { self.binary(name, $op) })* };
}
macro_rules! bit_unary {
    ($($method:ident => $op:literal),* $(,)?) => { $(pub fn $method(&self, name: &str) -> DomainFunc { function(name, $op.into(), self.typ(), vec![self.typ()]) })* };
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BVFactory {
    pub size: i32,
}
impl BVFactory {
    pub fn name(&self) -> String {
        format!("BitVectorDomain{}", self.size)
    }
    pub fn interpretations(&self) -> HashMap<String, String> {
        interpretations(
            format!("bv{}", self.size),
            format!("(_ BitVec {})", self.size),
        )
    }
    pub fn typ(&self) -> Type {
        Type::Backend(BackendType::new(self.name(), self.interpretations()))
    }
    pub fn construct_domain(&self, functions: Vec<DomainFunc>) -> Domain {
        domain(self.name(), self.interpretations(), functions)
    }
    fn binary(&self, name: &str, op: &str) -> DomainFunc {
        function(name, op.into(), self.typ(), vec![self.typ(), self.typ()])
    }
    bit_binary!(xor => "bvxor", xnor => "bvxnor", and => "bvand", nand => "bvnand", or => "bvor", nor => "bvnor", add => "bvadd", sub => "bvsub", mul => "bvmul", smod => "bvsmod", udiv => "bvudiv", urem => "bvurem", srem => "bvsrem", shl => "bvshl", lshr => "bvlshr", ashr => "bvashr");
    bit_unary!(not => "bvnot", neg => "bvneg");
    pub fn from_int(&self, name: &str) -> DomainFunc {
        function(
            name,
            format!("(_ int2bv {})", self.size),
            self.typ(),
            vec![Type::Int],
        )
    }
    pub fn to_int(&self, name: &str) -> DomainFunc {
        function(
            name,
            format!("(_ bv2int {})", self.size),
            Type::Int,
            vec![self.typ()],
        )
    }
    pub fn from_nat(&self, name: &str) -> DomainFunc {
        function(
            name,
            format!("(_ nat2bv {})", self.size),
            self.typ(),
            vec![Type::Int],
        )
    }
    pub fn to_nat(&self, name: &str) -> DomainFunc {
        function(
            name,
            format!("(_ bv2nat {})", self.size),
            Type::Int,
            vec![self.typ()],
        )
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoundingMode {
    RNE,
    RNA,
    RTP,
    RTN,
    RTZ,
}
impl std::fmt::Display for RoundingMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self:?}")
    }
}
macro_rules! float_binary {
    ($($method:ident => ($op:literal, $result:expr, $rounded:expr)),* $(,)?) => { $(pub fn $method(&self, name: &str) -> DomainFunc { let op = if $rounded {format!("{} {}", $op, self.rounding_mode)} else {$op.into()}; function(name, op, if $result { Type::Bool } else { self.typ() }, vec![self.typ(), self.typ()]) })* };
}
macro_rules! float_unary {
    ($($method:ident => ($op:literal, $result:expr)),* $(,)?) => { $(pub fn $method(&self, name: &str) -> DomainFunc { function(name, $op.into(), if $result {Type::Bool} else {self.typ()}, vec![self.typ()]) })* };
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FloatFactory {
    pub mant: i32,
    pub exp: i32,
    pub rounding_mode: RoundingMode,
}
impl FloatFactory {
    pub fn name(&self) -> String {
        format!("FloatDomain{}e{}", self.mant, self.exp)
    }
    pub fn interpretations(&self) -> HashMap<String, String> {
        interpretations(
            format!("float{}e{}", self.mant, self.exp),
            format!("(_ FloatingPoint {} {})", self.exp, self.mant),
        )
    }
    pub fn typ(&self) -> Type {
        Type::Backend(BackendType::new(self.name(), self.interpretations()))
    }
    pub fn construct_domain(&self, functions: Vec<DomainFunc>) -> Domain {
        domain(self.name(), self.interpretations(), functions)
    }
    float_unary!(neg => ("fp.neg", false), abs => ("fp.abs", false), is_zero => ("fp.isZero", true), is_infinite => ("fp.isInfinite", true), is_nan => ("fp.isNaN", true), is_negative => ("fp.isNegative", true), is_positive => ("fp.isPositive", true));
    float_binary!(add => ("fp.add", false, true), sub => ("fp.sub", false, true), mul => ("fp.mul", false, true), div => ("fp.div", false, true), min => ("fp.min", false, false), max => ("fp.max", false, false), eq => ("fp.eq", true, false), leq => ("fp.leq", true, false), geq => ("fp.geq", true, false), lt => ("fp.lt", true, false), gt => ("fp.gt", true, false));
    pub fn from_bv(&self, name: &str) -> DomainFunc {
        function(
            name,
            format!("(_ to_fp {} {}) ", self.exp, self.mant),
            self.typ(),
            vec![
                BVFactory {
                    size: self.mant.wrapping_add(self.exp),
                }
                .typ(),
            ],
        )
    }
    pub fn to_bv(&self, name: &str) -> DomainFunc {
        function(
            name,
            format!(
                "(_ fp.to_sbv {}) {} ",
                self.exp.wrapping_add(self.mant),
                self.rounding_mode
            ),
            BVFactory {
                size: self.exp.wrapping_add(self.mant),
            }
            .typ(),
            vec![self.typ()],
        )
    }
}
