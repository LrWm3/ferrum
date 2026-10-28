//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/AdtPASTExtension.scala
//!
//! Purpose:
//! Represent, resolve, typecheck and translate ADT syntax in the parse tree.
//!
//! Planned Rust structure:
//! Port PAdt, constructors/fields/derives, PAdtType and kind, PAdtOpApp and
//! constructor/destructor/discriminator calls with typechecking, substitution and translation.
//!
//! Behavior to preserve:
//! Check constructor argument types and discriminator name clashes, duplicate derivations and
//! without-field membership. Resolve ADT type arity and undefined/ambiguous references. Refresh
//! ADT type variables, unify operator signatures and force grounded substitutions before
//! translating calls; preserve member-signature-before-body construction and metadata.
//!
//! Integration:
//! adt_plugin rewrites parse nodes; parser::resolver/translator, adt_ast_extension and ast
//! rewriter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parse node identity, mutation and type substitutions.
//!
//! Open decisions:
//! Agree on ADT declaration lookup and mutable inference state with parser and AST.
//!
//! Status: partial; typed ADT member/constructor/derivation/type records, resolution, two-stage
//! translation and operator inference substitution are implemented. Grammar, name analysis,
//! source product punctuation and concrete operator-call typechecking/translation remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use super::adt_ast_extension::{Adt, AdtConstructor, AdtType};
use crate::ast::ast::Metadata;
use crate::ast::program::LocalVarDecl;
use crate::ast::r#type::{Type, TypeSubstitution, TypeVar};
use crate::parser::parse_ast::{
    PAnnotation, PDeclarationHandle, PExtender, PFormalArgs, PMember, PMemberHandle, PMemberKind,
    PNodeHandle, PNodeKind, PTypeHandle, PTypeRenaming, PTypeSubstitution,
};
use crate::parser::parse_ast_keyword::{
    PExtensionKeyword, PExtensionKeywordCategory, PGraphElement, PReserved, Span,
};
use std::{
    any::Any,
    collections::{HashMap, HashSet},
    sync::{Arc, RwLock},
};

pub fn adt_keyword(spelling: &'static str, pos: Span) -> PReserved<PExtensionKeyword> {
    PReserved::new(
        PExtensionKeyword {
            spelling: spelling.into(),
            category: PExtensionKeywordCategory::Language,
        },
        pos,
    )
}
fn definition_name(node: &PNodeHandle) -> Result<String, PAdtError> {
    match &node.read().expect("poisoned parse node").kind {
        PNodeKind::IdnDef(id) => Ok(id.name.clone()),
        _ => Err(PAdtError::InvalidNode("ADT identifier definition")),
    }
}
fn reference_name(node: &PNodeHandle) -> Result<String, PAdtError> {
    match &node.read().expect("poisoned parse node").kind {
        PNodeKind::IdnRef(id) => Ok(id.name.clone()),
        _ => Err(PAdtError::InvalidNode("ADT identifier reference")),
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PAdtError {
    InvalidNode(&'static str),
    UndeclaredType(String),
    AmbiguousType(String),
    WrongTypeArity { expected: usize, actual: usize },
    DuplicateDerivation(String),
    UndeclaredField(String),
    AmbiguousField(String),
    UngroundedType(String),
    Translation(String),
}

/// Constructor nodes retain the real parsed argument group and annotations.
#[derive(Clone, Debug)]
pub struct PAdtConstructor {
    pub annotations: Vec<PAnnotation>,
    pub idndef: PNodeHandle,
    pub args: PFormalArgs,
    pub pos: Span,
}
impl PExtender for PAdtConstructor {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        let mut nodes: Vec<_> = self
            .annotations
            .iter()
            .flat_map(PGraphElement::graph_nodes)
            .collect();
        nodes.push(self.idndef.clone());
        nodes.extend(self.args.graph_nodes());
        nodes
    }
}
impl PAdtConstructor {
    pub fn name(&self) -> Result<String, PAdtError> {
        definition_name(&self.idndef)
    }
    pub fn formal_args(&self) -> Vec<PDeclarationHandle> {
        self.args.inner().to_seq().into_iter().cloned().collect()
    }
    pub fn translate(
        &self,
        adt_name: &str,
        parameters: &[TypeVar],
        mut translate_arg: impl FnMut(&PDeclarationHandle) -> Result<LocalVarDecl, PAdtError>,
        meta: Metadata,
    ) -> Result<AdtConstructor, PAdtError> {
        let args = self
            .formal_args()
            .iter()
            .map(&mut translate_arg)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(AdtConstructor::new(
            adt_name,
            parameters.to_vec(),
            self.name()?,
            args,
            meta,
        ))
    }
}

#[derive(Clone, Debug)]
pub struct PAdtDerivingInfo {
    pub idndef: PNodeHandle,
    pub parameter: Option<PTypeHandle>,
    /// Resolved by the caller against fields belonging to the containing ADT.
    pub without: Vec<PNodeHandle>,
    pub pos: Span,
}
impl PExtender for PAdtDerivingInfo {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        let mut nodes = vec![self.idndef.clone()];
        if let Some(parameter) = &self.parameter {
            nodes.push(parameter.node().clone());
        }
        nodes.extend(self.without.iter().cloned());
        nodes
    }
}
impl PAdtDerivingInfo {
    /// Candidate counts must be computed after filtering to this ADT's fields.
    pub fn validate_fields(
        &self,
        mut candidate_count: impl FnMut(&PNodeHandle) -> usize,
    ) -> Result<(), PAdtError> {
        for reference in &self.without {
            let name = reference_name(reference)?;
            match candidate_count(reference) {
                0 => return Err(PAdtError::UndeclaredField(name)),
                1 => {}
                _ => return Err(PAdtError::AmbiguousField(name)),
            }
        }
        Ok(())
    }
}

/// A typed ADT member; constructor and deriving handles are actual parse nodes.
#[derive(Clone, Debug)]
pub struct PAdt {
    pub keyword: PReserved<PExtensionKeyword>,
    pub idndef: PNodeHandle,
    pub type_vars: Vec<PNodeHandle>,
    pub constructors: Vec<PNodeHandle>,
    pub deriving: Vec<PNodeHandle>,
    pub pos: Span,
}
impl PExtender for PAdt {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        let mut nodes = vec![self.keyword.node().clone(), self.idndef.clone()];
        nodes.extend(self.type_vars.iter().cloned());
        nodes.extend(self.constructors.iter().cloned());
        nodes.extend(self.deriving.iter().cloned());
        nodes
    }
}
impl PAdt {
    pub fn member(self, annotations: Vec<PAnnotation>) -> PMemberHandle {
        let pos = self.pos.clone();
        PMemberHandle::new(
            PMember::new(annotations, PMemberKind::Extension(Arc::new(self))),
            pos,
        )
    }
    pub fn name(&self) -> Result<String, PAdtError> {
        definition_name(&self.idndef)
    }
    pub fn validate_derivations(&self) -> Result<(), PAdtError> {
        let mut names = HashSet::new();
        for node in &self.deriving {
            let guard = node.read().expect("poisoned parse node");
            let PNodeKind::Extension(extension) = &guard.kind else {
                return Err(PAdtError::InvalidNode("ADT derivation"));
            };
            let info = extension
                .as_any()
                .downcast_ref::<PAdtDerivingInfo>()
                .ok_or(PAdtError::InvalidNode("ADT derivation"))?;
            let name = definition_name(&info.idndef)?;
            if !names.insert(name.clone()) {
                return Err(PAdtError::DuplicateDerivation(name));
            }
        }
        Ok(())
    }
    /// Builds the source signature first; constructors are populated in the
    /// second translation stage by the caller after member registration.
    pub fn translate_signature(
        &self,
        type_parameters: Vec<TypeVar>,
        deriving_info: HashMap<String, (Option<Type>, HashSet<String>)>,
        meta: Metadata,
    ) -> Result<Adt, PAdtError> {
        Ok(Adt {
            name: self.name()?,
            constructors: vec![],
            type_vars: type_parameters,
            deriving_info,
            meta,
        })
    }
    pub fn translate_constructors(
        &self,
        signature: &Adt,
        mut translate_arg: impl FnMut(&PDeclarationHandle) -> Result<LocalVarDecl, PAdtError>,
        mut metadata: impl FnMut(&PAdtConstructor) -> Metadata,
    ) -> Result<Adt, PAdtError> {
        let mut constructors = Vec::new();
        for node in &self.constructors {
            let c = {
                let guard = node.read().expect("poisoned parse node");
                let PNodeKind::Extension(extension) = &guard.kind else {
                    return Err(PAdtError::InvalidNode("ADT constructor"));
                };
                extension
                    .as_any()
                    .downcast_ref::<PAdtConstructor>()
                    .ok_or(PAdtError::InvalidNode("ADT constructor"))?
                    .clone()
            };
            constructors.push(Arc::new(c.translate(
                &signature.name,
                &signature.type_vars,
                &mut translate_arg,
                metadata(&c),
            )?));
        }
        let mut result = signature.clone();
        result.constructors = constructors;
        Ok(result)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PAdtTypeKind {
    Unresolved,
    Adt,
    Undeclared,
}
#[derive(Clone, Debug)]
pub struct PAdtType {
    pub reference: PNodeHandle,
    /// None and an explicitly present empty type-argument list remain distinct.
    pub args: Option<Vec<PTypeHandle>>,
    pub pos: Span,
    pub kind: Arc<RwLock<PAdtTypeKind>>,
}
impl PExtender for PAdtType {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        let mut nodes = vec![self.reference.clone()];
        if let Some(args) = &self.args {
            nodes.extend(args.iter().map(|v| v.node().clone()));
        }
        nodes
    }
}
impl PAdtType {
    pub fn new(reference: PNodeHandle, args: Option<Vec<PTypeHandle>>, pos: Span) -> Self {
        Self {
            reference,
            args,
            pos,
            kind: Arc::new(RwLock::new(PAdtTypeKind::Unresolved)),
        }
    }
    pub fn resolve(&self, candidate_arities: &[Option<usize>]) -> Result<(), PAdtError> {
        if *self.kind.read().expect("poisoned ADT type") != PAdtTypeKind::Unresolved {
            return Ok(());
        }
        let name = reference_name(&self.reference)?;
        *self.kind.write().expect("poisoned ADT type") = PAdtTypeKind::Undeclared;
        match candidate_arities {
            [] => Err(PAdtError::UndeclaredType(name)),
            [expected] => {
                *self.kind.write().expect("poisoned ADT type") = PAdtTypeKind::Adt;
                let actual = self.args.as_ref().map(Vec::len);
                if *expected != actual {
                    Err(PAdtError::WrongTypeArity {
                        expected: expected.unwrap_or(0),
                        actual: actual.unwrap_or(0),
                    })
                } else {
                    Ok(())
                }
            }
            _ => Err(PAdtError::AmbiguousType(name)),
        }
    }
    pub fn substitute(&self, substitution: &PTypeSubstitution) -> Result<Self, PAdtError> {
        let kind = *self.kind.read().expect("poisoned ADT type");
        if kind == PAdtTypeKind::Unresolved {
            return Err(PAdtError::InvalidNode("unresolved ADT type"));
        }
        let args = self.args.as_ref().map(|args| {
            args.iter()
                .map(|a| a.substitute(substitution))
                .collect::<Vec<_>>()
        });
        let unchanged = self
            .args
            .as_ref()
            .zip(args.as_ref())
            .is_some_and(|(a, b)| a.iter().zip(b).all(|(a, b)| a.structurally_equals(b)))
            || self.args.is_none();
        if unchanged {
            return Ok(self.clone());
        }
        let result = Self::new(
            self.reference.clone(),
            args,
            (
                crate::ast::position::Position::NoPosition,
                crate::ast::position::Position::NoPosition,
            ),
        );
        *result.kind.write().expect("poisoned ADT type") = PAdtTypeKind::Adt;
        Ok(result)
    }
    pub fn translate(
        &self,
        signature: &Adt,
        mut translate: impl FnMut(&PTypeHandle) -> Result<Type, PAdtError>,
    ) -> Result<Type, PAdtError> {
        if *self.kind.read().expect("poisoned ADT type") != PAdtTypeKind::Adt {
            return Err(PAdtError::InvalidNode("unresolved ADT type translation"));
        }
        let args = self.args.as_deref().unwrap_or(&[]);
        if args.len() != signature.type_vars.len() {
            return Err(PAdtError::WrongTypeArity {
                expected: signature.type_vars.len(),
                actual: args.len(),
            });
        }
        let mut mapping = TypeSubstitution::new();
        for (var, arg) in signature.type_vars.iter().zip(args) {
            mapping.insert(var.clone(), translate(arg)?);
        }
        Ok(AdtType::new(signature.name.clone(), mapping, signature.type_vars.clone()).as_type())
    }
}

/// Mutable inference extras shared by ADT constructor/destructor/discriminator applications.
#[derive(Clone, Debug, Default)]
pub struct PAdtInference {
    pub renaming: Option<PTypeRenaming>,
    pub substitution: Option<PTypeSubstitution>,
    pub extra_local_type_variables: HashSet<String>,
}
impl PAdtInference {
    /// Reconstruct the original ADT-parameter substitution, defaulting absent
    /// fresh variables to Int as the source forceSubstitution does.
    pub fn force_substitution(
        &mut self,
        chosen: &PTypeSubstitution,
    ) -> Result<PTypeSubstitution, PAdtError> {
        let Some(renaming) = &self.renaming else {
            return Ok(chosen.clone());
        };
        let mut mappings = HashMap::new();
        let mut result = chosen.clone();
        let default = crate::parser::parse_ast::type_from_signature(
            &crate::parser::parse_ast_keyword::SignatureType::Int,
        );
        for (original, fresh) in &renaming.mappings {
            let value = chosen
                .get(fresh)
                .cloned()
                .unwrap_or_else(|| default.clone());
            if !value.is_ground() {
                return Err(PAdtError::UngroundedType(original.clone()));
            }
            mappings.insert(original.clone(), value);
            if !result.contains(fresh) {
                result = result
                    .add(&crate::parser::parse_ast::p_type_var(fresh), &default)
                    .map_err(|e| PAdtError::Translation(format!("{e:?}")))?;
            }
        }
        self.substitution = Some(PTypeSubstitution::new(mappings, false));
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::position::Position;
    use crate::parser::parse_ast::{PIdnRef, PNode, type_from_signature};
    use crate::parser::parse_ast_keyword::SignatureType;

    fn pos() -> Span {
        (Position::NoPosition, Position::NoPosition)
    }
    #[test]
    fn resolves_adt_arity_and_preserves_missing_argument_list() {
        let reference = PNode::new(PNodeKind::IdnRef(PIdnRef::new("List")), pos());
        let typ = PAdtType::new(reference, None, pos());
        assert!(typ.resolve(&[None]).is_ok());
        assert_eq!(*typ.kind.read().unwrap(), PAdtTypeKind::Adt);
        let reference = PNode::new(PNodeKind::IdnRef(PIdnRef::new("List")), pos());
        let explicit_empty = PAdtType::new(reference, Some(vec![]), pos());
        assert!(matches!(
            explicit_empty.resolve(&[None]),
            Err(PAdtError::WrongTypeArity { .. })
        ));
    }
    #[test]
    fn inference_defaults_unbound_fresh_variables_to_int() {
        let mut inference = PAdtInference {
            renaming: Some(PTypeRenaming {
                mappings: [("T".into(), "fresh#1".into())].into_iter().collect(),
            }),
            ..Default::default()
        };
        let forced = inference
            .force_substitution(&PTypeSubstitution::default())
            .unwrap();
        let expected = type_from_signature(&SignatureType::Int);
        assert!(
            forced
                .get("fresh#1")
                .unwrap()
                .structurally_equals(&expected)
        );
        assert!(
            inference
                .substitution
                .as_ref()
                .unwrap()
                .get("T")
                .unwrap()
                .structurally_equals(&expected)
        );
    }
}
