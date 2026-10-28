//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/PropertyExpressions.scala
//!
//! Purpose:
//! Define the typed expression language used for resource assumptions.
//!
//! Planned Rust structure:
//! Port Kind/equatable/ITE categories, Boolean, Argument, Value, Permission and Chunk kinds;
//! IfThenElse, Check, ForEach, comparisons, Boolean/permission operators, literals, placeholders
//! and accessors.
//!
//! Behavior to preserve:
//! ForEach requires nonempty distinct variable names and quantifies distinct chunk tuples of the
//! same ID; ChunkVariable cannot be named this. Preserve exact arbitrary precision fraction
//! literals and typed accessor constraints.
//!
//! Integration:
//! resources::property_interpreter and specialized interpreters, resource_descriptions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact arithmetic and typed enums or equivalent; concrete
//! representation is open.
//!
//! Open decisions:
//! Agree on typed construction and placeholder identity with both interpreters.
//!
//! Status: implemented data representation and source constructor checks.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use num_bigint::BigInt;
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ChunkPlaceholder {
    This,
    Variable(String),
}
impl ChunkPlaceholder {
    pub fn variable(name: impl Into<String>) -> Result<Self, &'static str> {
        let name = name.into();
        if name == "this" {
            Err("chunk variable cannot be named this")
        } else {
            Ok(Self::Variable(name))
        }
    }
    pub fn name(&self) -> &str {
        match self {
            Self::This => "this",
            Self::Variable(name) => name,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ArgumentExpression {
    Access(ChunkPlaceholder),
    Null,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueExpression {
    Access(ChunkPlaceholder),
    IfThenElse(Box<BooleanExpression>, Box<Self>, Box<Self>),
    Check(Box<BooleanExpression>, Box<Self>, Box<Self>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PermissionExpression {
    Literal(BigInt, BigInt),
    Access(ChunkPlaceholder),
    Plus(Box<Self>, Box<Self>),
    Minus(Box<Self>, Box<Self>),
    Times(Box<Self>, Box<Self>),
    Div(Box<Self>, Box<Self>),
    IfThenElse(Box<BooleanExpression>, Box<Self>, Box<Self>),
    Check(Box<BooleanExpression>, Box<Self>, Box<Self>),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BooleanExpression {
    Literal(bool),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Implies(Box<Self>, Box<Self>),
    EqualsBoolean(Box<Self>, Box<Self>),
    EqualsArgument(ArgumentExpression, ArgumentExpression),
    EqualsValue(ValueExpression, ValueExpression),
    EqualsPermission(PermissionExpression, PermissionExpression),
    GreaterThan(PermissionExpression, PermissionExpression),
    GreaterThanEquals(PermissionExpression, PermissionExpression),
    LessThan(PermissionExpression, PermissionExpression),
    LessThanEquals(PermissionExpression, PermissionExpression),
    IfThenElse(Box<Self>, Box<Self>, Box<Self>),
    Check(Box<Self>, Box<Self>, Box<Self>),
    ForEach(Vec<ChunkPlaceholder>, Box<Self>),
}
impl BooleanExpression {
    pub fn for_each(variables: Vec<ChunkPlaceholder>, body: Self) -> Result<Self, &'static str> {
        if variables.is_empty() {
            return Err("Cannot quantify over no variable.");
        }
        if variables
            .iter()
            .any(|v| matches!(v, ChunkPlaceholder::This))
        {
            return Err("Cannot quantify over this.");
        }
        if variables.iter().collect::<HashSet<_>>().len() != variables.len() {
            return Err("Cannot quantify over non-distinct variables.");
        }
        Ok(Self::ForEach(variables, Box::new(body)))
    }
}
