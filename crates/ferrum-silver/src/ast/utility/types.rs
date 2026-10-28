//! Type-variable and constituent queries.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Types.scala
//! Status: partial. Type and domain-member queries are implemented; extension
//! constituent behavior requires a source-compatible hook.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::nodes::{self, Node, TraversalError};
use crate::ast::program::{DomainAxiom, DomainFunc};
use crate::ast::r#type::{Type, TypeVar};
use std::collections::HashSet;

pub fn type_variables(typ: &Type) -> HashSet<TypeVar> {
    match typ {
        Type::Var(v) => [v.clone()].into_iter().collect(),
        // The case-class extractor exposes the partial constructor map, not
        // the separately computed complete mapping of declared parameters.
        Type::Domain(d) => d
            .partial_type_vars
            .values()
            .flat_map(type_variables)
            .collect(),
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => type_variables(t),
        Type::Map(pair) => type_variables(&pair.0)
            .union(&type_variables(&pair.1))
            .cloned()
            .collect(),
        Type::Int
        | Type::Bool
        | Type::Perm
        | Type::Ref
        | Type::InternalType
        | Type::Wand
        | Type::Backend(_)
        | Type::Extension(_) => HashSet::new(),
    }
}

pub fn domain_function_free_type_variables(f: &DomainFunc) -> HashSet<TypeVar> {
    let mut variables = type_variables(&f.typ);
    for argument in &f.formal_args {
        variables.extend(type_variables(argument.typ()));
    }
    variables
}

pub fn domain_axiom_free_type_variables(
    axiom: &DomainAxiom,
) -> Result<HashSet<TypeVar>, TraversalError> {
    fn collect(node: &Node, result: &mut HashSet<TypeVar>) -> Result<(), TraversalError> {
        if let Some(typ) = node.typ()? {
            result.extend(type_variables(&typ));
        }
        for child in nodes::subnodes(node)? {
            collect(&child, result)?;
        }
        Ok(())
    }
    let mut result = HashSet::new();
    collect(&Node::Exp(axiom.exp().clone()), &mut result)?;
    Ok(result)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnsupportedExtensionConstituents;

pub fn type_constituents(typ: &Type) -> Result<Vec<Type>, UnsupportedExtensionConstituents> {
    Ok(match typ {
        Type::Domain(d) => d.type_arguments(),
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => std::iter::once((**t).clone())
            .chain(type_constituents(t)?)
            .collect(),
        Type::Map(pair) => [pair.0.clone(), pair.1.clone()]
            .into_iter()
            .chain(type_constituents(&pair.0)?)
            .chain(type_constituents(&pair.1)?)
            .collect(),
        Type::Int
        | Type::Bool
        | Type::Perm
        | Type::Ref
        | Type::InternalType
        | Type::Wand
        | Type::Var(_)
        | Type::Backend(_) => Vec::new(),
        Type::Extension(_) => return Err(UnsupportedExtensionConstituents),
    })
}
