//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/ProgramManager.scala
//!
//! Purpose:
//! Manage original program, fresh generated names and transformation errors.
//!
//! Planned Rust structure:
//! Port ProgramManager containsName/uniqueName and ErrorReporter callback.
//!
//! Behavior to preserve:
//! Seed used names from transitive scoped declarations; choose base then append 1, 2, ... and
//! reserve each generated name.
//!
//! Integration:
//! trafo, decreases_check, exp_transformer, nested_predicates and function/method checks.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for mutable transformation context and stable names.
//!
//! Open decisions:
//! Choose program and reporter ownership shared by cooperating transformers.
//!
//! Status: partial; name reservation and error callback implemented. Seeding from
//! transitive AST declarations remains an explicit caller responsibility.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::program::Program;
use crate::verifier::verification_result::AbstractError;
use std::collections::HashSet;

pub struct ProgramManager {
    pub program: Program,
    used_names: HashSet<String>,
}
impl ProgramManager {
    /// Names must include every transitively scoped declaration in the program.
    pub fn new(
        program: Program,
        transitive_scoped_names: impl IntoIterator<Item = String>,
    ) -> Self {
        Self {
            program,
            used_names: transitive_scoped_names.into_iter().collect(),
        }
    }
    pub fn contains_name(&self, name: &str) -> bool {
        self.used_names.contains(name)
    }
    pub fn unique_name(&mut self, name: &str) -> String {
        let mut counter = 1i32;
        let mut result = name.to_owned();
        while self.contains_name(&result) {
            result = format!("{name}{counter}");
            counter = counter.wrapping_add(1);
        }
        self.used_names.insert(result.clone());
        result
    }
}
pub trait ErrorReporter {
    fn report_error(&mut self, error: AbstractError);
}
