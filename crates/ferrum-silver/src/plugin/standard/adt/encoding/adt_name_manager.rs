//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/encoding/AdtNameManager.scala
//!
//! Purpose:
//! Generate and remember collision-free names for ADT encoding.
//!
//! Planned Rust structure:
//! Port AdtNameManager usedNames, memoized getName, uniqueName and fixed
//! contains/well-founded/destructor/tag naming helpers.
//!
//! Behavior to preserve:
//! Seed from transitive scoped declarations; reuse mapping for each requested base and append
//! numeric suffixes from 1 on collision. ContainsDomain, contains and well-founded names are fixed
//! resource interfaces; preserve source reservation behavior for initially unused names.
//!
//! Integration:
//! encoding::adt_encoder and resources/adt/contains.vpr; termination well-founded-order resources.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for deterministic naming and collection semantics.
//!
//! Open decisions:
//! Reconcile name collisions and generated-name reservation with encoder and resources.
//!
//! Status: partial; naming and collision logic implemented with caller-supplied
//! transitive declarations. Concrete AST traversal integration remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use crate::ast::program::Program;
use std::collections::{HashMap, HashSet};

pub struct AdtNameManager {
    pub program: Program,
    used_names: HashSet<String>,
    mappings: HashMap<String, String>,
}
impl AdtNameManager {
    /// Caller supplies names from all transitively scoped declarations. The AST
    /// traversal adapter is kept explicit until extension declarations are connected.
    pub fn new(
        program: Program,
        transitive_scoped_names: impl IntoIterator<Item = String>,
    ) -> Self {
        Self {
            program,
            used_names: transitive_scoped_names.into_iter().collect(),
            mappings: HashMap::new(),
        }
    }
    pub fn contains_domain_name(&self) -> &'static str {
        "ContainsDomain"
    }
    pub fn contains_function_name(&self) -> &'static str {
        "contains"
    }
    pub fn well_founded_domain_name(&self, type_name: &str) -> String {
        format!("{type_name}WellFoundedOrder")
    }
    pub fn well_founded_order_declaration_domain_name(&self) -> &'static str {
        "WellFoundedOrder"
    }
    pub fn decreases_function_name(&self) -> &'static str {
        "decreasing"
    }
    pub fn bounded_function_name(&self) -> &'static str {
        "bounded"
    }
    pub fn contains_transitivity_domain(&mut self) -> String {
        self.get_name("ContainsTransitivityDomain")
    }
    pub fn destructor_name(&mut self, adt_name: &str, argument: &str) -> String {
        self.get_name(&format!("get_{adt_name}_{argument}"))
    }
    pub fn tag_name(&mut self, adt_name: &str) -> String {
        self.get_name(&format!("{adt_name}_tag"))
    }
    fn get_name(&mut self, true_name: &str) -> String {
        if let Some(name) = self.mappings.get(true_name) {
            return name.clone();
        }
        let name = if self.used_names.contains(true_name) {
            let mut i = 1i32;
            let mut candidate = true_name.to_owned();
            while self.used_names.contains(&candidate) {
                candidate = format!("{true_name}{i}");
                i = i.wrapping_add(1);
            }
            self.used_names.insert(candidate.clone());
            candidate
        } else {
            true_name.to_owned()
        };
        self.mappings.insert(true_name.into(), name.clone());
        name
    }
}
