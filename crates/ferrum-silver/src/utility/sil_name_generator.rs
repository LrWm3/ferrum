//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/SilNameGenerator.scala
//!
//! Purpose:
//! Configure the general name generator for valid Silver identifiers.
//!
//! Planned Rust structure:
//! Port SilNameGenerator specialization with first/other character patterns, reserved names and
//! underscore separator.
//!
//! Behavior to preserve:
//! Preserve allowed ASCII letters, $, _, digits and apostrophe in subsequent positions and
//! postcondition validIdentifier.
//!
//! Integration:
//! utility::name_generator and ast::utility::consistency.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on shared identifier validation and context ownership with name_generator.
//!
//! Status: implemented; not yet wired or validated.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::name_generator::{NameContext, NameRules};
use crate::ast::utility::consistency::{reserved_names, valid_identifier};

pub struct SilNameGenerator(NameContext);

impl SilNameGenerator {
    pub fn new() -> Self {
        Self(sil_name_generator())
    }
}

impl Default for SilNameGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl std::ops::Deref for SilNameGenerator {
    type Target = NameContext;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub fn sil_name_generator() -> NameContext {
    NameContext::new(NameRules {
        separator: "_".into(),
        default_ident: "v".into(),
        first_character: |c| c.is_ascii_alphabetic() || c == '$' || c == '_',
        other_character: |c| c.is_ascii_alphanumeric() || matches!(c, '$' | '_' | '\''),
        reserved_names: reserved_names(),
    })
}

/// Equivalent to the upstream postcondition for identifier creation.
pub fn valid_sil_identifier(name: &str) -> bool {
    valid_identifier(name)
}
