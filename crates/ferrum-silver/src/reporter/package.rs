//! Port plan: Provide reporting aliases and source symbol definitions.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/reporter/package.scala
//!
//! Purpose:
//! Provide reporting aliases and source symbol definitions.
//!
//! Planned Rust structure:
//! Time, File, Entity, DefPosition/DefScope/ViperType, SymbolKind and TypedSymbol variants,
//! Definition and Import; print entity helper.
//!
//! Behavior to preserve:
//! Entity printing replaces newlines and collapses whitespace. Preserve symbol kind display names,
//! typed payloads, optional scope and import origin.
//!
//! Integration:
//! reporter::{message,reporter}, ast::{program,type,position} and frontend definition reporting.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Agree on member handles and file/scope ownership with frontend and reporter consumers.
//!
//! Status: partial; symbol definitions are implemented. Entity source rendering awaits the AST printer.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::position::{AbstractSourcePosition, Position};
use crate::ast::program::Member;
use crate::ast::r#type::Type;
use std::path::PathBuf;
use std::sync::Arc;

pub type Time = i64;
pub type File = PathBuf;
pub type Entity = Arc<Member>;
pub type DefPosition = Position;
pub type DefScope = AbstractSourcePosition;
pub type ViperType = Type;

/// Collapse Java-regex ASCII whitespace in a rendered entity, retaining boundary spaces.
/// Rendering a `Member` awaits the AST pretty printer; callers supply its source rendering.
pub fn print_rendered_entity(rendered: &str) -> String {
    let mut result = String::with_capacity(rendered.len());
    let mut whitespace = false;
    for c in rendered.chars() {
        if matches!(c, ' ' | '\t' | '\n' | '\r' | '\x0b' | '\x0c') {
            if !whitespace {
                result.push(' ');
                whitespace = true;
            }
        } else {
            result.push(c);
            whitespace = false;
        }
    }
    result
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymbolKind {
    Domain,
    Axiom,
    Function,
    Predicate,
    Field(ViperType),
    Method,
    Argument(ViperType),
    ReturnParameter(ViperType),
    UntypedLocalDefinition,
    TypedLocalDefinition(ViperType),
}
impl SymbolKind {
    pub fn name(&self) -> &'static str {
        match self {
            Self::Domain => "Domain",
            Self::Axiom => "Axiom",
            Self::Function => "Function",
            Self::Predicate => "Predicate",
            Self::Field(_) => "Field",
            Self::Method => "Method",
            Self::Argument(_) => "Argument",
            Self::ReturnParameter(_) => "Return",
            Self::UntypedLocalDefinition | Self::TypedLocalDefinition(_) => "Local",
        }
    }
    pub fn viper_type(&self) -> Option<&ViperType> {
        match self {
            Self::Field(t)
            | Self::Argument(t)
            | Self::ReturnParameter(t)
            | Self::TypedLocalDefinition(t) => Some(t),
            _ => None,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Definition {
    pub name: String,
    pub typ: SymbolKind,
    pub location: DefPosition,
    pub scope: Option<DefScope>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Import {
    pub file: File,
    pub from: Option<DefScope>,
}
