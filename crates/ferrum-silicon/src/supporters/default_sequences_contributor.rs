//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/DefaultSequencesContributor.scala
//!
//! Purpose:
//! Instantiate builtin sequence axioms, including integer ranges.
//!
//! Planned Rust structure:
//! Port DefaultSequencesContributor specialization and transformSourceDomainInstance.
//!
//! Behavior to preserve:
//! Select sequences_old.vpr or sequences.vpr and configured override; use $Seq unary sort. Retain
//! Seq_range function and named Seq_range_ axioms only for Seq[Int] to avoid duplicate
//! declarations.
//!
//! Integration:
//! supporters::{builtin_domains_contributor,domains}, config and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered declarations and .vpr resources.
//!
//! Open decisions:
//! Agree on resource selection and type-instantiation ordering with builtin_domains_contributor.
//!
//! Status: partial; resource selection and target sort factory implemented.
//! Domain parsing, instantiation and axiom emission await BuiltinDomainsContributor.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::Sort;

pub const SOURCE_DOMAIN_NAME: &str = "$Seq";
pub fn source_resource(use_old_axiomatization: bool) -> &'static str {
    if use_old_axiomatization {
        "/dafny_axioms/sequences_old.vpr"
    } else {
        "/dafny_axioms/sequences.vpr"
    }
}
/// An explicit arity error replaces the source assertion.
pub fn target_sort(arguments: &[Sort]) -> Result<Sort, &'static str> {
    if let [element] = arguments {
        Ok(Sort::Seq(Box::new(element.clone())))
    } else {
        Err("sequences requires one sort argument")
    }
}

/// Keep Seq_range only in the Int instance, avoiding duplicate SMT declarations.
pub fn transform_source_domain_instance(
    domain: &ferrum_silver::ast::program::Domain,
    element_type: &ferrum_silver::ast::r#type::Type,
) -> ferrum_silver::ast::program::Domain {
    use ferrum_silver::ast::{program::DomainAxiomKind, r#type::Type};
    if *element_type == Type::Int {
        return domain.clone();
    }
    let mut result = domain.clone();
    result
        .functions
        .retain(|function| function.name != "Seq_range");
    result.axioms.retain(
        |axiom| !matches!(axiom.kind(), DomainAxiomKind::Named { name, .. } if name.starts_with("Seq_range_")),
    );
    result
}
