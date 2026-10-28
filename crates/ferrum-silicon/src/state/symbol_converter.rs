// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Symbol conversion from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/SymbolConverter.scala
//! Status: primitive/collection/domain/backend sorts and domain/heap function conversion
//! implemented. Mask-heap resources and Silicon extension-type embedding are supplied
//! explicitly until their owning supporters are connected.

use super::identifiers::Identifier;
use super::terms::{Applicable, ApplicableData, ApplicableKind, ResourceKey, Sort, TermFactory};
use ferrum_silver::ast::program::{DomainFunc, Function, Program};
use ferrum_silver::ast::r#type::{ExtensionType, Type};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SymbolConversionError {
    NonConcreteDomain,
    MissingSmtlibName,
    UnexpectedType,
    UnsupportedExtensionType,
    UnsupportedTypePrinter,
    EmptySorts,
    MissingHeapResources,
    InvalidBuiltinArity,
}
impl std::fmt::Display for SymbolConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "symbol conversion error: {self:?}")
    }
}
impl std::error::Error for SymbolConversionError {}

/// Source builtin-domain specializations supported by the default contributors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinDomainSort {
    Sequence,
    Set,
    Multiset,
    Map,
}
pub type EmbeddingResolver = dyn Fn(&dyn ExtensionType) -> Option<Sort> + Send + Sync;
#[derive(Clone)]
pub struct DefaultSymbolConverter {
    factory: TermFactory,
    mask_heap_mode: bool,
    embedding: Option<Arc<EmbeddingResolver>>,
    builtin_domain: Option<(String, BuiltinDomainSort)>,
}
impl DefaultSymbolConverter {
    pub fn new(factory: TermFactory, mask_heap_mode: bool) -> Self {
        Self {
            factory,
            mask_heap_mode,
            embedding: None,
            builtin_domain: None,
        }
    }
    pub fn with_embedding_resolver(mut self, resolver: Arc<EmbeddingResolver>) -> Self {
        self.embedding = Some(resolver);
        self
    }
    /// Add an embedding case without discarding a caller's existing resolver.
    pub fn with_embedding_override(mut self, resolver: Arc<EmbeddingResolver>) -> Self {
        let previous = self.embedding.take();
        self.embedding = Some(Arc::new(move |value| {
            resolver(value).or_else(|| previous.as_ref().and_then(|f| f(value)))
        }));
        self
    }
    /// Source BuiltinDomainAwareSymbolConverter overrides one domain name per contributor.
    pub fn with_builtin_domain(mut self, name: impl Into<String>, kind: BuiltinDomainSort) -> Self {
        self.builtin_domain = Some((name.into(), kind));
        self
    }
    fn type_name(typ: &Type) -> Result<String, SymbolConversionError> {
        Ok(match typ {
            Type::Int => "Int".into(),
            Type::Bool => "Bool".into(),
            Type::Perm => "Perm".into(),
            Type::Ref => "Ref".into(),
            Type::InternalType => "InternalType".into(),
            Type::Wand => "$WandType".into(),
            Type::Var(v) => v.name.clone(),
            Type::Seq(t) => format!("Seq[{}]", Self::type_name(t)?),
            Type::Set(t) => format!("Set[{}]", Self::type_name(t)?),
            Type::Multiset(t) => format!("Multiset[{}]", Self::type_name(t)?),
            Type::Map(pair) => format!(
                "Map[{},{}]",
                Self::type_name(&pair.0)?,
                Self::type_name(&pair.1)?
            ),
            Type::Domain(d) => {
                let args = d
                    .type_arguments()
                    .iter()
                    .map(Self::type_name)
                    .collect::<Result<Vec<_>, _>>()?;
                if args.is_empty() {
                    d.domain_name.clone()
                } else {
                    format!("{}[{}]", d.domain_name, args.join(", "))
                }
            }
            Type::Backend(t) => t.viper_name.clone(),
            Type::Extension(t) => t
                .pretty_print()
                .map_err(|_| SymbolConversionError::UnsupportedTypePrinter)?,
        })
    }
    pub fn to_sort(&self, typ: &Type) -> Result<Sort, SymbolConversionError> {
        Ok(match typ {
            Type::Bool => Sort::Bool,
            Type::Int => Sort::Int,
            Type::Perm => Sort::Perm,
            Type::Ref => Sort::Ref,
            Type::Seq(t) => Sort::Seq(Box::new(self.to_sort(t)?)),
            Type::Set(t) => Sort::Set(Box::new(self.to_sort(t)?)),
            Type::Multiset(t) => Sort::Multiset(Box::new(self.to_sort(t)?)),
            Type::Map(pair) => Sort::Map(
                Box::new(self.to_sort(&pair.0)?),
                Box::new(self.to_sort(&pair.1)?),
            ),
            Type::Domain(d)
                if self
                    .builtin_domain
                    .as_ref()
                    .is_some_and(|(name, _)| *name == d.domain_name) =>
            {
                let args = d
                    .type_arguments()
                    .iter()
                    .map(|t| self.to_sort(t))
                    .collect::<Result<Vec<_>, _>>()?;
                match (
                    self.builtin_domain.as_ref().expect("checked builtin").1,
                    args.as_slice(),
                ) {
                    (BuiltinDomainSort::Sequence, [element]) => {
                        Sort::Seq(Box::new(element.clone()))
                    }
                    (BuiltinDomainSort::Set, [element]) => Sort::Set(Box::new(element.clone())),
                    (BuiltinDomainSort::Multiset, [element]) => {
                        Sort::Multiset(Box::new(element.clone()))
                    }
                    (BuiltinDomainSort::Map, [key, value]) => {
                        Sort::Map(Box::new(key.clone()), Box::new(value.clone()))
                    }
                    _ => return Err(SymbolConversionError::InvalidBuiltinArity),
                }
            }
            Type::Domain(_) if !typ.is_concrete() => {
                return Err(SymbolConversionError::NonConcreteDomain);
            }
            Type::Domain(_) => Sort::UserSort(Identifier::new(Self::type_name(typ)?)),
            Type::Backend(t) => Sort::SmtSort(Identifier::new(
                t.interpretations
                    .get("SMTLIB")
                    .ok_or(SymbolConversionError::MissingSmtlibName)?
                    .clone(),
            )),
            Type::Extension(t) => self
                .embedding
                .as_ref()
                .and_then(|r| r(t.as_ref()))
                .ok_or(SymbolConversionError::UnsupportedExtensionType)?,
            Type::InternalType | Type::Var(_) | Type::Wand => {
                return Err(SymbolConversionError::UnexpectedType);
            }
        })
    }
    pub fn to_sort_specific_id(name: &str, sorts: &[Sort]) -> Identifier {
        Identifier::new(format!(
            "{}[{}]",
            name,
            sorts
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(",")
        ))
    }
    pub fn domain_function(
        &self,
        function: &DomainFunc,
        program: &Program,
    ) -> Result<Applicable, SymbolConversionError> {
        let mut sorts = function
            .formal_args
            .iter()
            .map(|a| self.to_sort(a.typ()))
            .collect::<Result<Vec<_>, _>>()?;
        let out = self.to_sort(&function.typ)?;
        if let Some(interpretation) = &function.interpretation {
            Ok(self.factory.applicable(ApplicableData {
                kind: ApplicableKind::SmtFun,
                id: Identifier::new(interpretation.clone()),
                arg_sorts: sorts,
                result_sort: out,
            }))
        } else {
            sorts.push(out);
            self.domain_function_with_sorts(function, &sorts, program)
        }
    }
    pub fn domain_function_with_sorts(
        &self,
        function: &DomainFunc,
        sorts: &[Sort],
        program: &Program,
    ) -> Result<Applicable, SymbolConversionError> {
        let (out, args) = sorts
            .split_last()
            .ok_or(SymbolConversionError::EmptySorts)?;
        let id = if program
            .find_domain_function_optionally(&function.name)
            .is_none()
        {
            Identifier::new(function.name.clone())
        } else {
            Self::to_sort_specific_id(&function.name, std::slice::from_ref(out))
        };
        Ok(self.factory.applicable(ApplicableData {
            kind: ApplicableKind::DomainFun,
            id,
            arg_sorts: args.to_vec(),
            result_sort: out.clone(),
        }))
    }
    /// In mask mode `resources` must be the exact source-ordered result of
    /// maskHeapSupporter.getResourceSeq; standard mode ignores it.
    pub fn heap_dependent_function(
        &self,
        function: &Function,
        _program: &Program,
        resources: Option<&[ResourceKey]>,
    ) -> Result<Applicable, SymbolConversionError> {
        let mut sorts = if self.mask_heap_mode {
            resources
                .ok_or(SymbolConversionError::MissingHeapResources)?
                .iter()
                .map(|r| match r {
                    ResourceKey::Field(f) => Ok(Sort::Heap(Box::new(self.to_sort(&f.typ)?))),
                    ResourceKey::Predicate(_) => Ok(Sort::PredHeap),
                    ResourceKey::Wand(_) => Ok(Sort::WandHeap),
                })
                .collect::<Result<Vec<_>, SymbolConversionError>>()?
        } else {
            vec![Sort::Snap]
        };
        sorts.extend(
            function
                .formal_args
                .iter()
                .map(|a| self.to_sort(&a.typ))
                .collect::<Result<Vec<_>, _>>()?,
        );
        Ok(self.factory.applicable(ApplicableData {
            kind: ApplicableKind::HeapDepFun,
            id: Identifier::new(function.name.clone()),
            arg_sorts: sorts,
            result_sort: self.to_sort(&function.typ)?,
        }))
    }
}

/// Source conversion contract; mask-mode resource discovery is explicit until
/// the rule supporter is connected.
pub trait SymbolConverter {
    fn to_sort(&self, typ: &Type) -> Result<Sort, SymbolConversionError>;
    fn domain_function(
        &self,
        function: &DomainFunc,
        program: &Program,
    ) -> Result<Applicable, SymbolConversionError>;
    fn domain_function_with_sorts(
        &self,
        function: &DomainFunc,
        sorts: &[Sort],
        program: &Program,
    ) -> Result<Applicable, SymbolConversionError>;
    fn heap_dependent_function(
        &self,
        function: &Function,
        program: &Program,
        resources: Option<&[ResourceKey]>,
    ) -> Result<Applicable, SymbolConversionError>;
}
impl SymbolConverter for DefaultSymbolConverter {
    fn to_sort(&self, typ: &Type) -> Result<Sort, SymbolConversionError> {
        Self::to_sort(self, typ)
    }
    fn domain_function(
        &self,
        function: &DomainFunc,
        program: &Program,
    ) -> Result<Applicable, SymbolConversionError> {
        Self::domain_function(self, function, program)
    }
    fn domain_function_with_sorts(
        &self,
        function: &DomainFunc,
        sorts: &[Sort],
        program: &Program,
    ) -> Result<Applicable, SymbolConversionError> {
        Self::domain_function_with_sorts(self, function, sorts, program)
    }
    fn heap_dependent_function(
        &self,
        function: &Function,
        program: &Program,
        resources: Option<&[ResourceKey]>,
    ) -> Result<Applicable, SymbolConversionError> {
        Self::heap_dependent_function(self, function, program, resources)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::TermOptions;
    use ferrum_silver::ast::ast::Metadata;
    #[test]
    fn builtin_domain_override_uses_collection_sort_and_respects_parameter_order() {
        use ferrum_silver::ast::r#type::{DomainType, TypeVar};
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let a = TypeVar::new("K");
        let b = TypeVar::new("V");
        let typ = Type::Domain(DomainType::new(
            "$Map",
            [(a.clone(), Type::Int), (b.clone(), Type::Bool)]
                .into_iter()
                .collect(),
            vec![a, b],
        ));
        let ordinary = DefaultSymbolConverter::new(factory.clone(), false);
        let builtin = ordinary
            .clone()
            .with_builtin_domain("$Map", BuiltinDomainSort::Map);
        assert!(matches!(ordinary.to_sort(&typ).unwrap(), Sort::UserSort(_)));
        assert_eq!(
            builtin.to_sort(&typ).unwrap(),
            Sort::Map(Box::new(Sort::Int), Box::new(Sort::Bool))
        );
    }
    #[test]
    fn backend_smt_name_and_uninterpreted_function_signature_are_preserved() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory, false);
        let backend = Type::Backend(ferrum_silver::ast::r#type::BackendType::new(
            "T".into(),
            [("SMTLIB".into(), "(_ BitVec 8)".into())]
                .into_iter()
                .collect(),
        ));
        assert_eq!(
            converter.to_sort(&backend).unwrap(),
            Sort::SmtSort(Identifier::new("(_ BitVec 8)"))
        );
        let function = DomainFunc::new(ferrum_silver::ast::program::DomainFuncData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Int,
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: Metadata::default(),
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let converted = converter.domain_function(&function, &program).unwrap();
        assert_eq!(converted.data().id, Identifier::new("f"));
        assert_eq!(converted.data().kind, ApplicableKind::DomainFun);
        assert!(matches!(
            converter.domain_function_with_sorts(&function, &[], &program),
            Err(SymbolConversionError::EmptySorts)
        ));
    }
}
