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
pub struct TypeVar {
    pub name: String,
}
impl TypeVar {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
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
pub struct DomainType {
    pub domain_name: String,
    pub partial_type_vars: TypeSubstitution,
    pub type_parameters: Vec<TypeVar>,
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
        Self {
            domain_name: domain_name.into(),
            partial_type_vars,
            type_parameters,
        }
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
pub struct BackendType {
    pub viper_name: String,
    pub interpretations: HashMap<String, String>,
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
    Seq(Box<Type>),
    Set(Box<Type>),
    Multiset(Box<Type>),
    Map(Box<Type>, Box<Type>),
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
            (Self::Map(ak, av), Self::Map(bk, bv)) => ak == bk && av == bv,
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
            Self::Map(k, v) => {
                k.hash(state);
                v.hash(state);
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
    pub fn substitute(&self, substitutions: &TypeSubstitution) -> Self {
        match self {
            Self::Var(v) => substitutions
                .get(v)
                .cloned()
                .unwrap_or_else(|| self.clone()),
            Self::Seq(t) => Self::Seq(Box::new(t.substitute(substitutions))),
            Self::Set(t) => Self::Set(Box::new(t.substitute(substitutions))),
            Self::Multiset(t) => Self::Multiset(Box::new(t.substitute(substitutions))),
            Self::Map(k, v) => Self::Map(
                Box::new(k.substitute(substitutions)),
                Box::new(v.substitute(substitutions)),
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
            Self::Map(k, v) => k.is_concrete() && v.is_concrete(),
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
            Self::Map(k, v) => k
                .type_variables()
                .union(&v.type_variables())
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
            Self::Map(_, _) => Some("Map"),
            Self::Domain(d) => Some(&d.domain_name),
            _ => None,
        }
    }
    pub fn type_parameters(&self) -> Option<Vec<TypeVar>> {
        match self {
            Self::Seq(_) | Self::Set(_) | Self::Multiset(_) => Some(vec![TypeVar::new("X")]),
            Self::Map(_, _) => Some(vec![TypeVar::new("K"), TypeVar::new("E")]),
            Self::Domain(d) => Some(d.type_parameters.clone()),
            _ => None,
        }
    }
    pub fn type_arguments(&self) -> Option<Vec<Type>> {
        match self {
            Self::Seq(t) | Self::Set(t) | Self::Multiset(t) => Some(vec![(**t).clone()]),
            Self::Map(k, v) => Some(vec![(**k).clone(), (**v).clone()]),
            Self::Domain(d) => Some(d.type_arguments()),
            _ => None,
        }
    }
}
