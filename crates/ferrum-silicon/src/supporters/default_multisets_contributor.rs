//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/DefaultMultisetsContributor.scala
//!
//! Purpose:
//! Instantiate builtin multiset axioms.
//!
//! Planned Rust structure:
//! Port DefaultMultisetsContributor specialization and unary sort factory.
//!
//! Behavior to preserve:
//! Choose multisets_old.vpr under useOldAxiomatization, otherwise multisets.vpr, with configured
//! file override; use $Multiset.
//!
//! Integration:
//! supporters::{builtin_domains_contributor,domains}, config and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for configuration and native resources; retain .vpr formats.
//!
//! Open decisions:
//! Reconcile configuration access with verifier and builtin_domains_contributor.
//!
//! Status: partial; resource selection and target sort factory implemented.
//! Domain parsing, instantiation and axiom emission await BuiltinDomainsContributor.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::Sort;

pub const SOURCE_DOMAIN_NAME: &str = "$Multiset";
pub fn source_resource(use_old_axiomatization: bool) -> &'static str {
    if use_old_axiomatization {
        "/dafny_axioms/multisets_old.vpr"
    } else {
        "/dafny_axioms/multisets.vpr"
    }
}
/// An explicit arity error replaces the source assertion.
pub fn target_sort(arguments: &[Sort]) -> Result<Sort, &'static str> {
    if let [element] = arguments {
        Ok(Sort::Multiset(Box::new(element.clone())))
    } else {
        Err("multisets requires one sort argument")
    }
}
