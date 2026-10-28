//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/Property.scala
//!
//! Purpose:
//! Name and describe a Boolean resource property.
//!
//! Planned Rust structure:
//! Port Property expression, name and description fields and display.
//!
//! Behavior to preserve:
//! Reject names containing spaces and display the name.
//!
//! Integration:
//! resources::property_expressions and resource_descriptions, property interpreters.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for property expression ownership.
//!
//! Open decisions:
//! Agree on typed property expression representation with property_expressions.
//!
//! Status: implemented data representation and source constructor checks.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::property_expressions::BooleanExpression;
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Property {
    pub expression: BooleanExpression,
    pub name: String,
    pub description: String,
}
impl Property {
    pub fn new(
        expression: BooleanExpression,
        name: impl Into<String>,
        description: impl Into<String>,
    ) -> Result<Self, &'static str> {
        let name = name.into();
        if name.contains(' ') {
            return Err("Property names may not contain whitespace characters.");
        }
        Ok(Self {
            expression,
            name,
            description: description.into(),
        })
    }
}
impl std::fmt::Display for Property {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.name)
    }
}
