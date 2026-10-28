//! Domain type instance analysis.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/DomainInstances.scala
//! Status: partial; ground-type collection, free-variable depths, downward closures,
//! type-variable and domain-type discovery are implemented. Instance closure, SCC
//! coordinates and whole-node substitution require generic reconstruction.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    expression::ExpKind,
    program::{Domain, Program},
    r#type::{DomainType, Type, TypeVar},
    utility::nodes::{Node, TraversalError, subnodes},
};
use std::collections::{HashMap, HashSet};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DomainInstanceError {
    Traversal(TraversalError),
    MissingDomainName,
    MissingDomain(String),
    MissingExpressionType,
    ExtensionType,
}
impl From<TraversalError> for DomainInstanceError {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GroundTypeInstance {
    TypeInstance {
        domain: Domain,
        arguments: Vec<GroundTypeInstance>,
    },
    AtomicTypeInstance(Type),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DomainParameter {
    pub domain: Domain,
    pub variable: TypeVar,
}
impl DomainParameter {
    pub fn new(domain: Domain, variable: TypeVar) -> Self {
        assert!(domain.type_vars.contains(&variable));
        Self { domain, variable }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DomainParameterDependency {
    pub domain_parameter: DomainParameter,
    pub depth: i32,
}
pub fn get_ftv_depths(t: &Type) -> Result<HashMap<TypeVar, i32>, DomainInstanceError> {
    let mut result = HashMap::new();
    match t {
        Type::Var(v) => {
            result.insert(v.clone(), 0);
        }
        Type::Domain(d) => {
            for child in d.type_vars_map().into_values() {
                for (var, depth) in get_ftv_depths(&child)? {
                    result.insert(var, depth.wrapping_add(1));
                }
            }
        }
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => {
            for (var, depth) in get_ftv_depths(t)? {
                result.insert(var, depth.wrapping_add(1));
            }
        }
        Type::Map(k, v) => {
            for child in [k.as_ref(), v.as_ref()] {
                for (var, depth) in get_ftv_depths(child)? {
                    let depth = depth.wrapping_add(1);
                    result
                        .entry(var)
                        .and_modify(|old: &mut i32| *old = (*old).max(depth))
                        .or_insert(depth);
                }
            }
        }
        Type::Extension(_) => return Err(DomainInstanceError::ExtensionType),
        _ => {}
    }
    Ok(result)
}
pub fn down1_types(t: &Type) -> Result<HashSet<Type>, DomainInstanceError> {
    Ok(match t {
        Type::Domain(d) => d.type_vars_map().into_values().collect(),
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => {
            [t.as_ref().clone()].into_iter().collect()
        }
        Type::Map(k, v) => [k.as_ref().clone(), v.as_ref().clone()]
            .into_iter()
            .collect(),
        _ => HashSet::new(),
    })
}
pub fn down_closure(t: &Type) -> Result<HashSet<Type>, DomainInstanceError> {
    let mut result = HashSet::from([t.clone()]);
    for child in down1_types(t)? {
        result.extend(down_closure(&child)?);
    }
    Ok(result)
}
/// Source filters only the root; descendants use downClosure even when non-ground.
pub fn down_closure_ground(t: &Type) -> Result<HashSet<Type>, DomainInstanceError> {
    let mut result = HashSet::new();
    if t.is_concrete() {
        result.insert(t.clone());
    }
    for child in down1_types(t)? {
        result.extend(down_closure(&child)?);
    }
    Ok(result)
}
pub fn get_tvs(t: &Type) -> Result<HashSet<TypeVar>, DomainInstanceError> {
    Ok(match t {
        Type::Var(v) => HashSet::from([v.clone()]),
        Type::Domain(d) => {
            let mut result = HashSet::new();
            for child in d.type_vars_map().into_values() {
                result.extend(get_tvs(&child)?);
            }
            result
        }
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => get_tvs(t)?,
        Type::Map(k, v) => {
            let mut result = get_tvs(k)?;
            result.extend(get_tvs(v)?);
            result
        }
        Type::Extension(_) => return Err(DomainInstanceError::ExtensionType),
        _ => HashSet::new(),
    })
}
pub fn collect_ground_types(
    root: &Node,
    program: &Program,
) -> Result<HashSet<Type>, DomainInstanceError> {
    fn walk(n: &Node, p: &Program, out: &mut HashSet<Type>) -> Result<(), DomainInstanceError> {
        match n {
            Node::Type(t) if t.is_concrete() => {
                out.insert(t.clone());
            }
            Node::Exp(e) => {
                if let ExpKind::DomainFuncApp(_, _, map) = e.kind() {
                    if map.values().all(Type::is_concrete) {
                        let name =
                            e.0.extra
                                .domain_name
                                .as_ref()
                                .ok_or(DomainInstanceError::MissingDomainName)?;
                        let domain = p
                            .find_domain_optionally(name)
                            .ok_or_else(|| DomainInstanceError::MissingDomain(name.clone()))?;
                        out.insert(Type::Domain(DomainType::new(
                            name.clone(),
                            map.clone(),
                            domain.type_vars.clone(),
                        )));
                    }
                }
            }
            _ => {}
        }
        for child in subnodes(n)? {
            walk(&child, p, out)?;
        }
        Ok(())
    }
    let mut out = HashSet::new();
    walk(root, program, &mut out)?;
    Ok(out)
}
pub fn get_domain_type_instances(domain: &Domain) -> Result<HashSet<Type>, DomainInstanceError> {
    fn walk(node: &Node, out: &mut HashSet<Type>) -> Result<(), DomainInstanceError> {
        if let Node::Type(t) = node {
            out.insert(t.clone());
        }
        for child in subnodes(node)? {
            walk(&child, out)?;
        }
        Ok(())
    }
    let mut out = HashSet::new();
    walk(
        &Node::Member(crate::ast::program::Member::Domain(domain.clone())),
        &mut out,
    )?;
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn ground_closure_keeps_nonground_descendants_as_upstream() {
        let variable = Type::Var(TypeVar::new("T"));
        let seq = Type::Seq(Box::new(variable.clone()));
        let closure = down_closure_ground(&seq).unwrap();
        assert!(!closure.contains(&seq));
        assert!(closure.contains(&variable));
    }
}
