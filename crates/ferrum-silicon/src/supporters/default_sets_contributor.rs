//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/DefaultSetsContributor.scala
//!
//! Purpose:
//! Instantiate builtin set axioms including sets needed indirectly.
//!
//! Planned Rust structure:
//! Port DefaultSetsContributor specialization and computeGroundTypeInstances.
//!
//! Behavior to preserve:
//! Select sets_old.vpr or sets.vpr and user override. In quantified-permission cases add set types
//! of every field, Ref and embedded Snap; add sets of map key/value types for map domains.
//! Preserve insertion order and unary sort.
//!
//! Integration:
//! supporters::builtin_domains_contributor and qps contributors, state::terms, Silver AST and
//! config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered ground instances and .vpr resources.
//!
//! Open decisions:
//! Reconcile indirect set-type contributions with quantified contributors and type embedding.
//!
//! Status: partial; resource selection and target sort factory implemented.
//! Domain parsing, instantiation and axiom emission await BuiltinDomainsContributor.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::Sort;

pub const SOURCE_DOMAIN_NAME: &str = "$Set";
pub fn source_resource(use_old_axiomatization: bool) -> &'static str {
    if use_old_axiomatization {
        "/dafny_axioms/sets_old.vpr"
    } else {
        "/dafny_axioms/sets.vpr"
    }
}
/// An explicit arity error replaces the source assertion.
pub fn target_sort(arguments: &[Sort]) -> Result<Sort, &'static str> {
    if let [element] = arguments {
        Ok(Sort::Set(Box::new(element.clone())))
    } else {
        Err("sets requires one sort argument")
    }
}

/// Add the set instances needed by quantified permissions and map domain/range axioms.
/// The caller computes the source's trigger/resource-access predicate and supplies Snap's
/// Silver embedding; both require the pending program traversal and extension adapters.
pub fn additional_ground_types(
    initial: impl IntoIterator<Item = ferrum_silver::ast::r#type::Type>,
    ground_types: &[ferrum_silver::ast::r#type::Type],
    field_types: &[ferrum_silver::ast::r#type::Type],
    uses_quantified_permissions: bool,
    snap_embedding: ferrum_silver::ast::r#type::Type,
) -> crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
    ferrum_silver::ast::r#type::Type,
> {
    use ferrum_silver::ast::r#type::Type;
    let mut result: crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<Type> = initial.into_iter().collect();
    if uses_quantified_permissions {
        for ty in field_types {
            result = result.incl(Type::Set(std::sync::Arc::new(ty.clone())));
        }
        result = result.incl(Type::Set(std::sync::Arc::new(Type::Ref)));
        result = result.incl(Type::Set(std::sync::Arc::new(snap_embedding)));
    }
    for ty in ground_types {
        if let Type::Map(pair) = ty {
            result = result.incl(Type::Set(std::sync::Arc::new(pair.0.clone())));
            result = result.incl(Type::Set(std::sync::Arc::new(pair.1.clone())));
        }
    }
    result
}
