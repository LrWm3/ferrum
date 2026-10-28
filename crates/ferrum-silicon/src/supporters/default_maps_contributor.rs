//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/DefaultMapsContributor.scala
//!
//! Purpose:
//! Instantiate the builtin map domain for used map sorts.
//!
//! Planned Rust structure:
//! Port DefaultMapsContributor specialization of BuiltinDomainsContributor.
//!
//! Behavior to preserve:
//! Use $Map and /dafny_axioms/maps.vpr unless configured file overrides; require two sort
//! arguments in key/value order.
//!
//! Integration:
//! supporters::{builtin_domains_contributor,domains}, state::terms and config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for resource loading; preserve .vpr source format.
//!
//! Open decisions:
//! Agree on resource embedding and override handling with builtin_domains_contributor.
//!
//! Status: partial; resource selection and target sort factory implemented.
//! Domain parsing, instantiation and axiom emission await BuiltinDomainsContributor.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::Sort;

pub const SOURCE_DOMAIN_NAME: &str = "$Map";
pub fn source_resource(use_old_axiomatization: bool) -> &'static str {
    let _ = use_old_axiomatization;
    "/dafny_axioms/maps.vpr"
}
/// An explicit arity error replaces the source assertion.
pub fn target_sort(arguments: &[Sort]) -> Result<Sort, &'static str> {
    if let [key, value] = arguments {
        Ok(Sort::Map(Box::new(key.clone()), Box::new(value.clone())))
    } else {
        Err("map requires two sort arguments")
    }
}
