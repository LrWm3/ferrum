//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/AdtASTExtension.scala
//!
//! Purpose:
//! Represent ADT declarations, types and constructor/destructor/discriminator expressions.
//!
//! Planned Rust structure:
//! Port Adt, AdtConstructor, AdtType, AdtConstructorApp, AdtDestructorApp and AdtDiscriminatorApp,
//! constructors, custom reconstruction, pretty printing and consistency/trigger checks.
//!
//! Behavior to preserve:
//! Require at least one constructor and pure expression arguments/receivers; fill missing type
//! parameters with themselves and substitute structurally. Constructor/destructor triggers are
//! valid only without forbidden subexpressions; discriminators are forbidden. Preserve extra
//! metadata and unresolved direct verification failure until encoding.
//!
//! Integration:
//! adt_past_extension and encoding::adt_encoder; ast types, rewriter, consistency and pretty
//! printing.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for type equality, metadata, reconstruction and ownership.
//!
//! Open decisions:
//! Agree on ADT/type handles and extension elimination with ast and encoder.
//!
//! Status: partial; ADT type, declarations and application nodes are implemented. Complete printing,
//! consistency, trigger traversal and rewrite integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use crate::ast::ast::Metadata;
use crate::ast::program::{
    Declaration, ExtensionMember, ExtensionMemberHandle, LocalVarDecl, Member,
};
use crate::ast::r#type::{
    ExtensionType, Type, TypeSubstitution, TypeVar, UnsupportedExtensionOperation,
};
use crate::ast::utility::nodes::{Node, TraversalError};
use std::any::Any;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

fn adt_scala_type_map_hash(
    map: &TypeSubstitution,
) -> Result<i32, crate::ast::utility::expressions::ScalaHashError> {
    use crate::ast::utility::expressions::{
        scala_map_hash, scala_product, scala_string_hash, scala_type_hash,
    };
    let entries = map
        .iter()
        .map(|(key, value)| {
            Ok((
                scala_product("TypeVar", &[scala_string_hash(&key.name)]),
                scala_type_hash(value)?,
            ))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(scala_map_hash(entries))
}

#[derive(Clone, Debug)]
pub struct AdtType {
    pub adt_name: String,
    pub partial_type_vars: TypeSubstitution,
    pub type_parameters: Vec<TypeVar>,
}
impl AdtType {
    pub fn new(
        adt_name: impl Into<String>,
        partial_type_vars: TypeSubstitution,
        type_parameters: Vec<TypeVar>,
    ) -> Self {
        Self {
            adt_name: adt_name.into(),
            partial_type_vars,
            type_parameters,
        }
    }
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
    pub fn as_type(self) -> Type {
        Type::Extension(Arc::new(self))
    }
}
impl ExtensionType for AdtType {
    fn pretty_doc(
        &self,
    ) -> Result<
        crate::ast::pretty::pretty_printer::Doc,
        crate::ast::pretty::pretty_printer::PrintError,
    > {
        use crate::ast::pretty::pretty_printer::{Doc, show_type_doc};
        let mapping = self.type_vars_map();
        let mut args = Vec::new();
        for (index, param) in self.type_parameters.iter().enumerate() {
            if index != 0 {
                args.push(Doc::text(", "));
            }
            args.push(show_type_doc(
                mapping.get(param).expect("complete ADT type map"),
            )?);
        }
        let mut docs = vec![Doc::text(&self.adt_name)];
        if !args.is_empty() {
            docs.extend([Doc::text("["), Doc::concat(args), Doc::text("]")]);
        }
        Ok(Doc::concat(docs))
    }
    fn scala_hash(&self) -> Result<i32, crate::ast::utility::expressions::ScalaHashError> {
        Ok(crate::ast::utility::expressions::scala_product(
            "AdtType",
            &[
                crate::ast::utility::expressions::scala_string_hash(&self.adt_name),
                adt_scala_type_map_hash(&self.partial_type_vars)?,
            ],
        ))
    }

    fn check_product_nodes(
        &self,
    ) -> Result<
        Vec<crate::ast::utility::nodes::Node>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(vec![])
    }

    fn check(
        &self,
    ) -> Result<
        Vec<crate::verifier::verification_result::FrontendError>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        if self.type_parameters.iter().cloned().collect::<HashSet<_>>()
            == self.type_vars_map().into_keys().collect()
        {
            Ok(vec![])
        } else {
            Err(
                crate::verifier::verification_result::DiagnosticError::Unsupported(
                    "ADT type parameter diagnostic rendering",
                ),
            )
        }
    }
    fn scope_declarations(
        &self,
    ) -> Result<Option<Vec<Declaration>>, crate::verifier::verification_result::DiagnosticError>
    {
        Ok(None)
    }

    fn map_types(
        &self,
        map: &dyn Fn(&Type) -> Result<Type, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<Arc<dyn ExtensionType>, crate::verifier::verification_result::DiagnosticError> {
        use crate::verifier::verification_result::DiagnosticError;
        let mut types = TypeSubstitution::new();
        for (key, value) in &self.partial_type_vars {
            let Type::Var(key) = map(&Type::Var(key.clone()))? else {
                return Err(DiagnosticError::InvalidNode("ADT type substitution key"));
            };
            types.insert(key, map(value)?);
        }
        Ok(Arc::new(Self::new(
            self.adt_name.clone(),
            types,
            self.type_parameters.clone(),
        )))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionType) -> bool {
        other.as_any().downcast_ref::<Self>().is_some_and(|o| {
            self.adt_name == o.adt_name && self.partial_type_vars == o.partial_type_vars
        })
    }
    fn hash_value(&self) -> u64 {
        let mut hash = std::collections::hash_map::DefaultHasher::new();
        self.adt_name.hash(&mut hash);
        let mut entries = self.partial_type_vars.iter().collect::<Vec<_>>();
        entries.sort_by(|a, b| a.0.name.cmp(&b.0.name));
        for (key, value) in entries {
            key.hash(&mut hash);
            value.hash(&mut hash);
        }
        hash.finish()
    }
    fn substitute(&self, substitutions: &TypeSubstitution) -> Arc<dyn ExtensionType> {
        Arc::new(Self::new(
            self.adt_name.clone(),
            self.type_vars_map()
                .into_iter()
                .map(|(key, value)| (key, value.substitute(substitutions)))
                .collect(),
            self.type_parameters.clone(),
        ))
    }
    fn is_concrete(&self) -> bool {
        self.type_vars_map().values().all(Type::is_concrete)
    }
    fn pretty_print(&self) -> Result<String, UnsupportedExtensionOperation> {
        let mapping = self.type_vars_map();
        let args = self
            .type_parameters
            .iter()
            .map(|p| pretty_type(mapping.get(p).expect("complete ADT type map")))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(if args.is_empty() {
            self.adt_name.clone()
        } else {
            format!("{}[{}]", self.adt_name, args.join(", "))
        })
    }
}
fn pretty_type(typ: &Type) -> Result<String, UnsupportedExtensionOperation> {
    Ok(match typ {
        Type::Int => "Int".into(),
        Type::Bool => "Bool".into(),
        Type::Perm => "Perm".into(),
        Type::Ref => "Ref".into(),
        Type::InternalType => "InternalType".into(),
        Type::Wand => "$WandType".into(),
        Type::Var(v) => v.name.clone(),
        Type::Seq(t) => format!("Seq[{}]", pretty_type(t)?),
        Type::Set(t) => format!("Set[{}]", pretty_type(t)?),
        Type::Multiset(t) => format!("Multiset[{}]", pretty_type(t)?),
        Type::Map(pair) => format!("Map[{},{}]", pretty_type(&pair.0)?, pretty_type(&pair.1)?),
        Type::Domain(d) => {
            let args = d
                .type_arguments()
                .iter()
                .map(pretty_type)
                .collect::<Result<Vec<_>, _>>()?;
            if args.is_empty() {
                d.domain_name.clone()
            } else {
                format!("{}[{}]", d.domain_name, args.join(", "))
            }
        }
        Type::Backend(t) => t.viper_name.clone(),
        Type::Extension(t) => t.pretty_print()?,
    })
}
#[derive(Clone, Debug)]
pub struct AdtConstructor {
    pub name: String,
    pub formal_args: Vec<LocalVarDecl>,
    pub typ: AdtType,
    pub adt_name: String,
    pub meta: Metadata,
}
impl AdtConstructor {
    pub fn new(
        adt_name: impl Into<String>,
        type_parameters: Vec<TypeVar>,
        name: impl Into<String>,
        formal_args: Vec<LocalVarDecl>,
        meta: Metadata,
    ) -> Self {
        let adt_name = adt_name.into();
        let type_vars = type_parameters
            .iter()
            .map(|v| (v.clone(), Type::Var(v.clone())))
            .collect();
        Self {
            name: name.into(),
            formal_args,
            typ: AdtType::new(adt_name.clone(), type_vars, type_parameters),
            adt_name,
            meta,
        }
    }
    pub fn scoped_declarations(&self) -> Vec<Declaration> {
        self.formal_args
            .iter()
            .cloned()
            .map(Declaration::Local)
            .collect()
    }
    pub fn as_member(self) -> Member {
        Member::Extension(ExtensionMemberHandle(Arc::new(self)))
    }
}
impl ExtensionMember for AdtConstructor {
    fn pretty_doc(
        &self,
    ) -> Result<
        crate::ast::pretty::pretty_printer::Doc,
        crate::ast::pretty::pretty_printer::PrintError,
    > {
        use crate::ast::pretty::pretty_printer::{Doc, show_node};
        let mut args = Vec::new();
        for (index, arg) in self.formal_args.iter().enumerate() {
            if index != 0 {
                args.push(Doc::concat([Doc::text(","), Doc::line()]).group());
            }
            args.push(show_node(&Node::LocalDecl(arg.clone()))?);
        }
        Ok(Doc::concat([
            Doc::text(&self.name),
            Doc::concat(args).parens(),
        ]))
    }
    fn check_product_nodes(
        &self,
    ) -> Result<
        Vec<crate::ast::utility::nodes::Node>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(self
            .formal_args
            .iter()
            .cloned()
            .map(Node::LocalDecl)
            .collect())
    }

    fn check(
        &self,
    ) -> Result<
        Vec<crate::verifier::verification_result::FrontendError>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(vec![])
    }
    fn scope_declarations(
        &self,
    ) -> Result<Vec<Declaration>, crate::verifier::verification_result::DiagnosticError> {
        Ok(self.scoped_declarations())
    }

    fn metadata(&self) -> Result<&Metadata, crate::verifier::verification_result::DiagnosticError> {
        Ok(&self.meta)
    }
    fn with_metadata(
        &self,
        meta: Metadata,
    ) -> Result<ExtensionMemberHandle, crate::verifier::verification_result::DiagnosticError> {
        let mut copy = self.clone();
        copy.meta = meta;
        Ok(ExtensionMemberHandle(Arc::new(copy)))
    }
    fn map_nodes(
        &self,
        map: &dyn Fn(&Node) -> Result<Node, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionMemberHandle, crate::verifier::verification_result::DiagnosticError> {
        use crate::verifier::verification_result::DiagnosticError;
        let mut args = Vec::with_capacity(self.formal_args.len());
        for arg in &self.formal_args {
            let Node::LocalDecl(arg) = map(&Node::LocalDecl(arg.clone()))? else {
                return Err(DiagnosticError::InvalidNode(
                    "ADT constructor formal argument",
                ));
            };
            args.push(arg);
        }
        let mut copy = self.clone();
        copy.formal_args = args;
        Ok(ExtensionMemberHandle(Arc::new(copy)))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn name(&self) -> &str {
        &self.name
    }
    fn equals(&self, other: &dyn ExtensionMember) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|o| self.name == o.name && self.formal_args == o.formal_args)
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        Ok(self
            .formal_args
            .iter()
            .cloned()
            .map(Node::LocalDecl)
            .collect())
    }
}
#[derive(Clone, Debug)]
pub struct Adt {
    pub name: String,
    pub constructors: Vec<Arc<AdtConstructor>>,
    pub type_vars: Vec<TypeVar>,
    pub deriving_info: HashMap<String, (Option<Type>, HashSet<String>)>,
    pub meta: Metadata,
}
impl Adt {
    pub fn as_member(self) -> Member {
        Member::Extension(ExtensionMemberHandle(Arc::new(self)))
    }
    pub fn check(&self) -> Vec<crate::verifier::verification_result::FrontendError> {
        if self.constructors.is_empty() {
            vec![crate::verifier::verification_result::FrontendError::new(
                crate::verifier::verification_result::FrontendErrorKind::ConsistencyError(format!(
                    "ADT {} must have at least one constructor.",
                    self.name
                )),
                self.meta.position.clone(),
            )]
        } else {
            Vec::new()
        }
    }
}
impl ExtensionMember for Adt {
    fn pretty_doc(
        &self,
    ) -> Result<
        crate::ast::pretty::pretty_printer::Doc,
        crate::ast::pretty::pretty_printer::PrintError,
    > {
        use crate::ast::pretty::pretty_printer::{Doc, show_member, show_type_doc};
        let mut docs = vec![Doc::text("adt "), Doc::text(&self.name)];
        if !self.type_vars.is_empty() {
            docs.push(Doc::text("["));
            for (index, var) in self.type_vars.iter().enumerate() {
                if index != 0 {
                    docs.push(Doc::text(", "));
                }
                docs.push(show_type_doc(&Type::Var(var.clone()))?);
            }
            docs.push(Doc::text("]"));
        }
        let mut body = Vec::new();
        for constructor in &self.constructors {
            body.push(Doc::Line(String::new()));
            body.push(show_member(&Member::Extension(ExtensionMemberHandle(
                constructor.clone(),
            )))?);
        }
        docs.extend([
            Doc::text(" {"),
            Doc::concat(body).nest(2),
            Doc::Line(String::new()),
            Doc::text("}"),
        ]);
        if !self.deriving_info.is_empty() {
            let mut body = Vec::new();
            for (name, (param, blocklist)) in &self.deriving_info {
                body.push(Doc::Line(String::new()));
                body.push(Doc::text(name));
                if let Some(param) = param {
                    body.extend([Doc::text("["), show_type_doc(param)?, Doc::text(" ]")]);
                }
                body.push(Doc::text(" "));
                if !blocklist.is_empty() {
                    body.push(Doc::text("without "));
                    for (index, entry) in blocklist.iter().enumerate() {
                        if index != 0 {
                            body.push(Doc::text(", "));
                        }
                        body.push(Doc::text(entry));
                    }
                }
            }
            docs.extend([
                Doc::text(" derives {"),
                Doc::concat(body).nest(2),
                Doc::Line(String::new()),
                Doc::text("}"),
            ]);
        }
        Ok(Doc::concat(docs))
    }
    fn check_product_nodes(
        &self,
    ) -> Result<
        Vec<crate::ast::utility::nodes::Node>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(self
            .constructors
            .iter()
            .cloned()
            .map(|c| Node::Member(Member::Extension(ExtensionMemberHandle(c))))
            .chain(
                self.type_vars
                    .iter()
                    .cloned()
                    .map(|v| Node::Type(Type::Var(v))),
            )
            .collect())
    }

    fn check(
        &self,
    ) -> Result<
        Vec<crate::verifier::verification_result::FrontendError>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(Adt::check(self))
    }
    fn scope_declarations(
        &self,
    ) -> Result<Vec<Declaration>, crate::verifier::verification_result::DiagnosticError> {
        Ok(vec![])
    }

    fn metadata(&self) -> Result<&Metadata, crate::verifier::verification_result::DiagnosticError> {
        Ok(&self.meta)
    }
    fn with_metadata(
        &self,
        meta: Metadata,
    ) -> Result<ExtensionMemberHandle, crate::verifier::verification_result::DiagnosticError> {
        let mut copy = self.clone();
        copy.meta = meta;
        Ok(ExtensionMemberHandle(Arc::new(copy)))
    }
    fn map_nodes(
        &self,
        map: &dyn Fn(&Node) -> Result<Node, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionMemberHandle, crate::verifier::verification_result::DiagnosticError> {
        use crate::verifier::verification_result::DiagnosticError;
        let mut constructors = Vec::with_capacity(self.constructors.len());
        for constructor in &self.constructors {
            let original: Arc<dyn ExtensionMember> = constructor.clone();
            let Node::Member(Member::Extension(result)) = map(&Node::Member(Member::Extension(
                ExtensionMemberHandle(original.clone()),
            )))?
            else {
                return Err(DiagnosticError::InvalidNode("ADT constructor"));
            };
            if Arc::ptr_eq(&original, &result.0) {
                constructors.push(constructor.clone());
            } else {
                constructors.push(Arc::new(
                    result
                        .0
                        .as_any()
                        .downcast_ref::<AdtConstructor>()
                        .ok_or(DiagnosticError::InvalidNode("ADT constructor"))?
                        .clone(),
                ));
            }
        }
        let mut type_vars = Vec::with_capacity(self.type_vars.len());
        for var in &self.type_vars {
            let Node::Type(Type::Var(var)) = map(&Node::Type(Type::Var(var.clone())))? else {
                return Err(DiagnosticError::InvalidNode("ADT type parameter"));
            };
            type_vars.push(var);
        }
        let mut deriving_info = self.deriving_info.clone();
        for (typ, _) in deriving_info.values_mut() {
            if let Some(old) = typ {
                let Node::Type(new) = map(&Node::Type(old.clone()))? else {
                    return Err(DiagnosticError::InvalidNode("ADT deriving type"));
                };
                *typ = Some(new);
            }
        }
        let mut copy = self.clone();
        copy.constructors = constructors;
        copy.type_vars = type_vars;
        copy.deriving_info = deriving_info;
        Ok(ExtensionMemberHandle(Arc::new(copy)))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn name(&self) -> &str {
        &self.name
    }
    fn equals(&self, other: &dyn ExtensionMember) -> bool {
        other.as_any().downcast_ref::<Self>().is_some_and(|o| {
            self.name == o.name
                && self.constructors.len() == o.constructors.len()
                && self
                    .constructors
                    .iter()
                    .zip(&o.constructors)
                    .all(|(a, b)| a.name == b.name && a.formal_args == b.formal_args)
                && self.type_vars == o.type_vars
                && self.deriving_info == o.deriving_info
        })
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        let mut nodes = self
            .constructors
            .iter()
            .cloned()
            .map(|c| Node::Member(Member::Extension(ExtensionMemberHandle(c))))
            .collect::<Vec<_>>();
        nodes.extend(
            self.type_vars
                .iter()
                .cloned()
                .map(|v| Node::Type(Type::Var(v))),
        );
        nodes.extend(
            self.deriving_info
                .values()
                .filter_map(|(t, _)| t.clone())
                .map(Node::Type),
        );
        Ok(nodes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn adt_type_fills_parameters_and_substitutes() {
        let t = TypeVar::new("T");
        let adt = AdtType::new("Box", HashMap::new(), vec![t.clone()]);
        assert!(!adt.is_concrete());
        assert_eq!(adt.pretty_print().unwrap(), "Box[T]");
        let replacement = [(t, Type::Int)].into_iter().collect();
        let concrete = adt.substitute(&replacement);
        assert!(concrete.is_concrete());
        assert_eq!(concrete.pretty_print().unwrap(), "Box[Int]");
    }
}

use crate::ast::expression::{Exp, ExpKind, ExtensionExp, ExtensionExpHandle};
#[derive(Clone, Debug)]
pub struct AdtConstructorApp {
    pub name: String,
    pub args: Vec<Exp>,
    pub type_vars: TypeSubstitution,
    pub typ: Type,
    pub adt_name: String,
    pub meta: Metadata,
}
impl AdtConstructorApp {
    pub fn new(
        constructor: &AdtConstructor,
        args: Vec<Exp>,
        type_vars: TypeSubstitution,
        meta: Metadata,
    ) -> Self {
        let typ = constructor.typ.clone().as_type().substitute(&type_vars);
        Self {
            name: constructor.name.clone(),
            args,
            type_vars,
            typ,
            adt_name: constructor.adt_name.clone(),
            meta,
        }
    }
    pub fn expression(self) -> Exp {
        let meta = self.meta.clone();
        Exp::new(ExpKind::Extension(ExtensionExpHandle(Arc::new(self))), meta)
    }
    pub fn is_valid_trigger(&self, forbidden: impl Fn(&Exp) -> bool) -> bool {
        self.args.iter().all(|e| !forbidden(e))
    }
    pub fn verify_unlowered(&self) -> Result<(), &'static str> {
        Err("AdtConstructorApp: verifyExtExp has not been implemented.")
    }
    pub fn pretty(
        &self,
        print_exp: impl Fn(&Exp) -> String,
        print_type: impl Fn(&Type) -> String,
    ) -> String {
        let call = format!(
            "{}({})",
            self.name,
            self.args
                .iter()
                .map(print_exp)
                .collect::<Vec<_>>()
                .join(", ")
        );
        if self.type_vars.is_empty() {
            call
        } else {
            format!("({call}: {})", print_type(&self.typ))
        }
    }
}
impl ExtensionExp for AdtConstructorApp {
    fn pretty_doc(
        &self,
    ) -> Result<
        crate::ast::pretty::pretty_printer::Doc,
        crate::ast::pretty::pretty_printer::PrintError,
    > {
        use crate::ast::pretty::pretty_printer::{Doc, show_exp, show_type_doc};
        let mut args = Vec::new();
        for (index, exp) in self.args.iter().enumerate() {
            if index != 0 {
                args.push(Doc::text(", "));
            }
            args.push(show_exp(exp)?);
        }
        let call = Doc::concat([Doc::text(&self.name), Doc::concat(args).parens()]);
        if self.type_vars.is_empty() {
            Ok(call)
        } else {
            Ok(Doc::concat([call, Doc::text(": "), show_type_doc(&self.typ)?]).parens())
        }
    }
    fn scala_hash(&self) -> Result<i32, crate::ast::utility::expressions::ScalaHashError> {
        Ok(crate::ast::utility::expressions::scala_product(
            "AdtConstructorApp",
            &[
                crate::ast::utility::expressions::scala_string_hash(&self.name),
                crate::ast::utility::expressions::scala_expression_sequence_hash(&self.args)?,
                adt_scala_type_map_hash(&self.type_vars)?,
            ],
        ))
    }
    fn pretty_print(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        use crate::ast::pretty::pretty_printer::{pretty_expression, show_type};
        let args = self
            .args
            .iter()
            .map(pretty_expression)
            .collect::<Result<Vec<_>, _>>()?;
        let call = format!("{}({})", self.name, args.join(", "));
        if self.type_vars.is_empty() {
            Ok(call)
        } else {
            Ok(format!("({call}: {})", show_type(&self.typ)?))
        }
    }

    fn check_product_nodes(
        &self,
    ) -> Result<
        Vec<crate::ast::utility::nodes::Node>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(self.args.iter().cloned().map(Node::Exp).collect())
    }

    fn check(
        &self,
    ) -> Result<
        Vec<crate::verifier::verification_result::FrontendError>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        crate::plugin::silver_plugin::check_pure_expressions(self.args.iter())
    }
    fn scope_declarations(
        &self,
    ) -> Result<Option<Vec<Declaration>>, crate::verifier::verification_result::DiagnosticError>
    {
        Ok(None)
    }

    fn map_expressions(
        &self,
        map: &dyn Fn(&Exp) -> Result<Exp, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionExpHandle, crate::verifier::verification_result::DiagnosticError> {
        let mut copy = self.clone();
        copy.args = self.args.iter().map(map).collect::<Result<_, _>>()?;
        Ok(ExtensionExpHandle(Arc::new(copy)))
    }

    fn metadata(&self) -> &Metadata {
        &self.meta
    }
    fn with_metadata(&self, meta: Metadata) -> ExtensionExpHandle {
        let mut copy = self.clone();
        copy.meta = meta;
        ExtensionExpHandle(Arc::new(copy))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionExp) -> bool {
        other.as_any().downcast_ref::<Self>().is_some_and(|o| {
            self.name == o.name && self.args == o.args && self.type_vars == o.type_vars
        })
    }
    fn typ(&self) -> Type {
        self.typ.clone()
    }
    fn is_pure(&self) -> bool {
        true
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        let mut nodes = self.args.iter().cloned().map(Node::Exp).collect::<Vec<_>>();
        nodes.extend(
            self.type_vars
                .keys()
                .cloned()
                .map(|key| Node::Type(Type::Var(key))),
        );
        nodes.extend(self.type_vars.values().cloned().map(Node::Type));
        Ok(nodes)
    }
}
#[derive(Clone, Debug)]
pub struct AdtDestructorApp {
    pub name: String,
    pub receiver: Exp,
    pub type_vars: TypeSubstitution,
    pub typ: Type,
    pub adt_name: String,
    pub meta: Metadata,
}
impl AdtDestructorApp {
    pub fn new(
        adt: &Adt,
        name: impl Into<String>,
        receiver: Exp,
        type_vars: TypeSubstitution,
        meta: Metadata,
    ) -> Result<Self, &'static str> {
        let name = name.into();
        let args = adt
            .constructors
            .iter()
            .flat_map(|c| c.formal_args.iter())
            .filter(|a| a.name == name)
            .collect::<Vec<_>>();
        if args.len() != 1 {
            return Err("ADT destructor must identify exactly one constructor argument");
        }
        let typ = args[0].typ.substitute(&type_vars);
        Ok(Self {
            name,
            receiver,
            type_vars,
            typ,
            adt_name: adt.name.clone(),
            meta,
        })
    }
    pub fn expression(self) -> Exp {
        let meta = self.meta.clone();
        Exp::new(ExpKind::Extension(ExtensionExpHandle(Arc::new(self))), meta)
    }
    pub fn is_valid_trigger(&self, forbidden: impl Fn(&Exp) -> bool) -> bool {
        !forbidden(&self.receiver)
    }
    pub fn verify_unlowered(&self) -> Result<(), &'static str> {
        Err("AdtDestructorApp: verifyExtExp has not been implemented.")
    }
    pub fn pretty(&self, print_exp: impl FnOnce(&Exp) -> String) -> String {
        format!("{}.{}", print_exp(&self.receiver), self.name)
    }
}
impl ExtensionExp for AdtDestructorApp {
    fn pretty_doc(
        &self,
    ) -> Result<
        crate::ast::pretty::pretty_printer::Doc,
        crate::ast::pretty::pretty_printer::PrintError,
    > {
        use crate::ast::pretty::pretty_printer::{Doc, show_exp};
        Ok(Doc::concat([
            show_exp(&self.receiver)?,
            Doc::text("."),
            Doc::text(&self.name),
        ]))
    }
    fn scala_hash(&self) -> Result<i32, crate::ast::utility::expressions::ScalaHashError> {
        Ok(crate::ast::utility::expressions::scala_product(
            "AdtDestructorApp",
            &[
                crate::ast::utility::expressions::scala_string_hash(&self.name),
                crate::ast::utility::expressions::scala_expression_hash(&self.receiver)?,
                adt_scala_type_map_hash(&self.type_vars)?,
            ],
        ))
    }
    fn pretty_print(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        Ok(format!(
            "{}.{}",
            crate::ast::pretty::pretty_printer::pretty_expression(&self.receiver)?,
            self.name
        ))
    }

    fn check_product_nodes(
        &self,
    ) -> Result<
        Vec<crate::ast::utility::nodes::Node>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(vec![Node::Exp(self.receiver.clone())])
    }

    fn check(
        &self,
    ) -> Result<
        Vec<crate::verifier::verification_result::FrontendError>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        crate::plugin::silver_plugin::check_pure_expressions(std::iter::once(&self.receiver))
    }
    fn scope_declarations(
        &self,
    ) -> Result<Option<Vec<Declaration>>, crate::verifier::verification_result::DiagnosticError>
    {
        Ok(None)
    }

    fn map_expressions(
        &self,
        map: &dyn Fn(&Exp) -> Result<Exp, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionExpHandle, crate::verifier::verification_result::DiagnosticError> {
        let mut copy = self.clone();
        copy.receiver = map(&self.receiver)?;
        Ok(ExtensionExpHandle(Arc::new(copy)))
    }

    fn metadata(&self) -> &Metadata {
        &self.meta
    }
    fn with_metadata(&self, meta: Metadata) -> ExtensionExpHandle {
        let mut copy = self.clone();
        copy.meta = meta;
        ExtensionExpHandle(Arc::new(copy))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionExp) -> bool {
        other.as_any().downcast_ref::<Self>().is_some_and(|o| {
            self.name == o.name && self.receiver == o.receiver && self.type_vars == o.type_vars
        })
    }
    fn typ(&self) -> Type {
        self.typ.clone()
    }
    fn is_pure(&self) -> bool {
        true
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        let mut nodes = vec![Node::Exp(self.receiver.clone())];
        nodes.extend(
            self.type_vars
                .keys()
                .cloned()
                .map(|key| Node::Type(Type::Var(key))),
        );
        nodes.extend(self.type_vars.values().cloned().map(Node::Type));
        Ok(nodes)
    }
}
#[derive(Clone, Debug)]
pub struct AdtDiscriminatorApp {
    pub name: String,
    pub receiver: Exp,
    pub type_vars: TypeSubstitution,
    pub adt_name: String,
    pub meta: Metadata,
}
impl AdtDiscriminatorApp {
    pub fn expression(self) -> Exp {
        let meta = self.meta.clone();
        Exp::new(ExpKind::Extension(ExtensionExpHandle(Arc::new(self))), meta)
    }
    pub fn is_valid_trigger(&self) -> bool {
        false
    }
    pub fn is_forbidden_in_trigger(&self) -> bool {
        true
    }
    pub fn verify_unlowered(&self) -> Result<(), &'static str> {
        Err("AdtDiscriminatorApp: verifyExtExp has not been implemented.")
    }
    pub fn pretty(&self, print_exp: impl FnOnce(&Exp) -> String) -> String {
        format!("{}.is{}", print_exp(&self.receiver), self.name)
    }
}
impl ExtensionExp for AdtDiscriminatorApp {
    fn pretty_doc(
        &self,
    ) -> Result<
        crate::ast::pretty::pretty_printer::Doc,
        crate::ast::pretty::pretty_printer::PrintError,
    > {
        use crate::ast::pretty::pretty_printer::{Doc, show_exp};
        Ok(Doc::concat([
            show_exp(&self.receiver)?,
            Doc::text(".is"),
            Doc::text(&self.name),
        ]))
    }
    fn scala_hash(&self) -> Result<i32, crate::ast::utility::expressions::ScalaHashError> {
        Ok(crate::ast::utility::expressions::scala_product(
            "AdtDiscriminatorApp",
            &[
                crate::ast::utility::expressions::scala_string_hash(&self.name),
                crate::ast::utility::expressions::scala_expression_hash(&self.receiver)?,
                adt_scala_type_map_hash(&self.type_vars)?,
            ],
        ))
    }
    fn pretty_print(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        Ok(format!(
            "{}.is{}",
            crate::ast::pretty::pretty_printer::pretty_expression(&self.receiver)?,
            self.name
        ))
    }

    fn check_product_nodes(
        &self,
    ) -> Result<
        Vec<crate::ast::utility::nodes::Node>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(vec![Node::Exp(self.receiver.clone())])
    }

    fn check(
        &self,
    ) -> Result<
        Vec<crate::verifier::verification_result::FrontendError>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        crate::plugin::silver_plugin::check_pure_expressions(std::iter::once(&self.receiver))
    }
    fn scope_declarations(
        &self,
    ) -> Result<Option<Vec<Declaration>>, crate::verifier::verification_result::DiagnosticError>
    {
        Ok(None)
    }

    fn map_expressions(
        &self,
        map: &dyn Fn(&Exp) -> Result<Exp, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionExpHandle, crate::verifier::verification_result::DiagnosticError> {
        let mut copy = self.clone();
        copy.receiver = map(&self.receiver)?;
        Ok(ExtensionExpHandle(Arc::new(copy)))
    }

    fn metadata(&self) -> &Metadata {
        &self.meta
    }
    fn with_metadata(&self, meta: Metadata) -> ExtensionExpHandle {
        let mut copy = self.clone();
        copy.meta = meta;
        ExtensionExpHandle(Arc::new(copy))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionExp) -> bool {
        other.as_any().downcast_ref::<Self>().is_some_and(|o| {
            self.name == o.name && self.receiver == o.receiver && self.type_vars == o.type_vars
        })
    }
    fn typ(&self) -> Type {
        Type::Bool
    }
    fn is_pure(&self) -> bool {
        true
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        let mut nodes = vec![Node::Exp(self.receiver.clone())];
        nodes.extend(
            self.type_vars
                .keys()
                .cloned()
                .map(|key| Node::Type(Type::Var(key))),
        );
        nodes.extend(self.type_vars.values().cloned().map(Node::Type));
        Ok(nodes)
    }
}
