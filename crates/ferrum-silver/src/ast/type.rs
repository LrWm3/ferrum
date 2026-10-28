//! Silver types and generic substitution.
//!
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Type.scala
//!
//! Status: core type operations implemented; extension and AST integration are provisional.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct TypeVar(Arc<TypeVarData>);
#[derive(Debug, PartialEq, Eq, Hash)]
pub struct TypeVarData {
    pub name: String,
}
impl std::ops::Deref for TypeVar {
    type Target = TypeVarData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl TypeVar {
    pub fn new(name: impl Into<String>) -> Self {
        Self(Arc::new(TypeVarData { name: name.into() }))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
pub type TypeSubstitution = HashMap<TypeVar, Type>;

/// Plugin type behavior is provisional until extension-node reconstruction and
/// pretty printing are connected. Implementations define their own equality.
pub trait ExtensionType: fmt::Debug + Send + Sync {
    fn as_any(&self) -> &dyn Any;
    fn equals(&self, other: &dyn ExtensionType) -> bool;
    /// Equal extension values must return the same hash.
    fn hash_value(&self) -> u64;
    fn substitute(&self, substitutions: &TypeSubstitution) -> Arc<dyn ExtensionType>;
    fn is_concrete(&self) -> bool;
    /// Upstream leaves these methods unimplemented by default.
    fn get_ast_type(&self) -> Result<Type, UnsupportedExtensionOperation> {
        Err(UnsupportedExtensionOperation::GetAstType)
    }
    /// Provisional textual boundary until the pretty-printer document API exists.
    fn pretty_print(&self) -> Result<String, UnsupportedExtensionOperation> {
        Err(UnsupportedExtensionOperation::PrettyPrint)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnsupportedExtensionOperation {
    GetAstType,
    PrettyPrint,
}

/// The second Scala constructor parameter list (`type_parameters`) is not part
/// of case-class equality. The first-list partial map, including extra keys, is.
#[derive(Clone, Debug)]
pub struct DomainTypeData {
    pub domain_name: String,
    pub partial_type_vars: TypeSubstitution,
    pub type_parameters: Vec<TypeVar>,
}
#[derive(Clone, Debug)]
pub struct DomainType(Arc<DomainTypeData>);
impl std::ops::Deref for DomainType {
    type Target = DomainTypeData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl PartialEq for DomainType {
    fn eq(&self, other: &Self) -> bool {
        self.domain_name == other.domain_name && self.partial_type_vars == other.partial_type_vars
    }
}
impl Eq for DomainType {}
impl Hash for DomainType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.domain_name.hash(state);
        let mut entries: Vec<_> = self.partial_type_vars.iter().collect();
        entries.sort_by(|(a, _), (b, _)| a.name.cmp(&b.name));
        entries.len().hash(state);
        for (var, typ) in entries {
            var.hash(state);
            typ.hash(state);
        }
    }
}
impl DomainType {
    pub fn new(
        domain_name: impl Into<String>,
        partial_type_vars: TypeSubstitution,
        type_parameters: Vec<TypeVar>,
    ) -> Self {
        Self(Arc::new(DomainTypeData {
            domain_name: domain_name.into(),
            partial_type_vars,
            type_parameters,
        }))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    /// Complete the mapping for declared parameters, ignoring extra partial-map keys.
    pub fn type_vars_map(&self) -> TypeSubstitution {
        self.type_parameters
            .iter()
            .map(|p| {
                (
                    p.clone(),
                    self.partial_type_vars
                        .get(p)
                        .cloned()
                        .unwrap_or_else(|| Type::Var(p.clone())),
                )
            })
            .collect()
    }
    pub fn type_arguments(&self) -> Vec<Type> {
        let map = self.type_vars_map();
        self.type_parameters
            .iter()
            .map(|p| map[p].clone())
            .collect()
    }
    pub fn substitute(&self, substitutions: &TypeSubstitution) -> Self {
        let map = self
            .type_vars_map()
            .into_iter()
            .map(|(var, typ)| (var, typ.substitute(substitutions)))
            .collect();
        Self::new(self.domain_name.clone(), map, self.type_parameters.clone())
    }
    /// Mirrors the source's parameter-set consistency check.
    pub fn has_consistent_parameters(&self) -> bool {
        self.type_parameters.iter().cloned().collect::<HashSet<_>>()
            == self.type_vars_map().into_keys().collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BackendType(Arc<BackendTypeData>);
#[derive(Debug, PartialEq, Eq)]
pub struct BackendTypeData {
    pub viper_name: String,
    pub interpretations: HashMap<String, String>,
}
impl std::ops::Deref for BackendType {
    type Target = BackendTypeData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl BackendType {
    pub fn new(viper_name: String, interpretations: HashMap<String, String>) -> Self {
        Self(Arc::new(BackendTypeData {
            viper_name,
            interpretations,
        }))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// The built-in, generic, backend and plugin type families from Type.scala.
#[derive(Clone, Debug)]
pub enum Type {
    Int,
    Bool,
    Perm,
    Ref,
    InternalType,
    Wand,
    Seq(Arc<Type>),
    Set(Arc<Type>),
    Multiset(Arc<Type>),
    Map(Arc<(Type, Type)>),
    Domain(DomainType),
    Var(TypeVar),
    Backend(BackendType),
    Extension(Arc<dyn ExtensionType>),
}
impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Int, Self::Int)
            | (Self::Bool, Self::Bool)
            | (Self::Perm, Self::Perm)
            | (Self::Ref, Self::Ref)
            | (Self::InternalType, Self::InternalType)
            | (Self::Wand, Self::Wand) => true,
            (Self::Seq(a), Self::Seq(b))
            | (Self::Set(a), Self::Set(b))
            | (Self::Multiset(a), Self::Multiset(b)) => a == b,
            (Self::Map(a), Self::Map(b)) => a == b,
            (Self::Domain(a), Self::Domain(b)) => a == b,
            (Self::Var(a), Self::Var(b)) => a == b,
            (Self::Backend(a), Self::Backend(b)) => a == b,
            (Self::Extension(a), Self::Extension(b)) => a.equals(b.as_ref()),
            _ => false,
        }
    }
}
impl Eq for Type {}
impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::mem::discriminant(self).hash(state);
        match self {
            Self::Seq(t) | Self::Set(t) | Self::Multiset(t) => t.hash(state),
            Self::Map(pair) => {
                pair.0.hash(state);
                pair.1.hash(state);
            }
            Self::Domain(d) => d.hash(state),
            Self::Var(v) => v.hash(state),
            Self::Backend(b) => {
                b.viper_name.hash(state);
                let mut entries: Vec<_> = b.interpretations.iter().collect();
                entries.sort_by_key(|(key, _)| *key);
                entries.len().hash(state);
                for (key, value) in entries {
                    key.hash(state);
                    value.hash(state);
                }
            }
            Self::Extension(t) => t.hash_value().hash(state),
            _ => {}
        }
    }
}
impl Type {
    pub fn map(key: Type, value: Type) -> Self {
        Self::Map(Arc::new((key, value)))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Seq(a), Self::Seq(b))
            | (Self::Set(a), Self::Set(b))
            | (Self::Multiset(a), Self::Multiset(b)) => Arc::ptr_eq(a, b),
            (Self::Map(a), Self::Map(b)) => Arc::ptr_eq(a, b),
            (Self::Var(a), Self::Var(b)) => a.same_node(b),
            (Self::Domain(a), Self::Domain(b)) => a.same_node(b),
            (Self::Backend(a), Self::Backend(b)) => a.same_node(b),
            (Self::Extension(a), Self::Extension(b)) => Arc::ptr_eq(a, b),
            (Self::Int, Self::Int)
            | (Self::Bool, Self::Bool)
            | (Self::Perm, Self::Perm)
            | (Self::Ref, Self::Ref)
            | (Self::InternalType, Self::InternalType)
            | (Self::Wand, Self::Wand) => true,
            _ => false,
        }
    }
    pub fn substitute(&self, substitutions: &TypeSubstitution) -> Self {
        match self {
            Self::Var(v) => substitutions
                .get(v)
                .cloned()
                .unwrap_or_else(|| self.clone()),
            Self::Seq(t) => Self::Seq(Arc::new(t.substitute(substitutions))),
            Self::Set(t) => Self::Set(Arc::new(t.substitute(substitutions))),
            Self::Multiset(t) => Self::Multiset(Arc::new(t.substitute(substitutions))),
            Self::Map(pair) => Self::map(
                pair.0.substitute(substitutions),
                pair.1.substitute(substitutions),
            ),
            Self::Domain(d) => Self::Domain(d.substitute(substitutions)),
            Self::Extension(t) => Self::Extension(t.substitute(substitutions)),
            _ => self.clone(),
        }
    }
    pub fn is_subtype(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Domain(a), Self::Domain(b)) => {
                let b_map = b.type_vars_map();
                a.domain_name == b.domain_name
                    && a.type_vars_map()
                        .iter()
                        .all(|(v, t)| b_map.get(v).is_some_and(|u| t.is_subtype(u)))
            }
            (Self::Wand, Self::Bool) => true,
            _ => self == other,
        }
    }
    pub fn is_concrete(&self) -> bool {
        match self {
            Self::Var(_) => false,
            Self::Seq(t) | Self::Set(t) | Self::Multiset(t) => t.is_concrete(),
            Self::Map(pair) => pair.0.is_concrete() && pair.1.is_concrete(),
            Self::Domain(d) => d.type_vars_map().values().all(Self::is_concrete),
            Self::Extension(t) => t.is_concrete(),
            _ => true,
        }
    }
    /// Mirrors `ast.utility.Types.typeVariables`, including its use of the
    /// domain's partial map rather than the completed parameter mapping.
    pub fn type_variables(&self) -> HashSet<TypeVar> {
        match self {
            Self::Var(v) => HashSet::from([v.clone()]),
            Self::Domain(d) => d
                .partial_type_vars
                .values()
                .flat_map(Self::type_variables)
                .collect(),
            Self::Seq(t) | Self::Set(t) | Self::Multiset(t) => t.type_variables(),
            Self::Map(pair) => pair
                .0
                .type_variables()
                .union(&pair.1.type_variables())
                .cloned()
                .collect(),
            _ => HashSet::new(),
        }
    }
    pub fn generic_name(&self) -> Option<&str> {
        match self {
            Self::Seq(_) => Some("Seq"),
            Self::Set(_) => Some("Set"),
            Self::Multiset(_) => Some("MultiSet"),
            Self::Map(_) => Some("Map"),
            Self::Domain(d) => Some(&d.domain_name),
            _ => None,
        }
    }
    pub fn type_parameters(&self) -> Option<Vec<TypeVar>> {
        match self {
            Self::Seq(_) | Self::Set(_) | Self::Multiset(_) => Some(vec![TypeVar::new("X")]),
            Self::Map(_) => Some(vec![TypeVar::new("K"), TypeVar::new("E")]),
            Self::Domain(d) => Some(d.type_parameters.clone()),
            _ => None,
        }
    }
    pub fn type_arguments(&self) -> Option<Vec<Type>> {
        match self {
            Self::Seq(t) | Self::Set(t) | Self::Multiset(t) => Some(vec![(**t).clone()]),
            Self::Map(pair) => Some(vec![pair.0.clone(), pair.1.clone()]),
            Self::Domain(d) => Some(d.type_arguments()),
            _ => None,
        }
    }
}

#[cfg(test)]
mod identity_tests {
    use super::*;
    #[test]
    fn compounds_have_source_identity_separate_from_structural_equality() {
        let a = Type::map(Type::Int, Type::Bool);
        let b = Type::map(Type::Int, Type::Bool);
        assert_eq!(a, b);
        assert!(!a.same_node(&b));
        assert!(a.same_node(&a.clone()));
        let x = TypeVar::new("T");
        let y = TypeVar::new("T");
        assert_eq!(x, y);
        assert!(!x.same_node(&y));
        assert!(Type::Int.same_node(&Type::Int));
    }
}
