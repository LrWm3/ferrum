//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/predicateinstance/PredicateInstanceASTExtension.scala
//!
//! Purpose:
//! Represent predicate instance expressions before lowering.
//!
//! Planned Rust structure:
//! Port PredicateInstance with predicate name, arguments, pure extension type, subnodes, pretty
//! printer and purity consistency checks; expose PredicateInstance domain type helper.
//!
//! Behavior to preserve:
//! Type is the nullary PredicateInstance domain; each argument must be pure. verifyExtExp is
//! unimplemented upstream, so lowering is required before backend verification.
//!
//! Integration:
//! predicate_instance_plugin lowers nodes; parser extension translates them; ast consistency and
//! pretty printing.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for extension nodes, type and metadata.
//!
//! Open decisions:
//! Agree on domain lookup/type representation and unsupported unlowered extension handling with
//! ast and verifier.
//!
//! Status: partial; typed expression, purity-check adapter and explicit unlowered
//! verification failure implemented. Concrete consistency and lowering integration remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::ast::Metadata;
use crate::ast::expression::{Exp, ExpKind, ExtensionExp, ExtensionExpHandle};
use crate::ast::r#type::{DomainType, Type};
use crate::ast::utility::nodes::{Node, TraversalError};
use std::any::Any;
use std::sync::Arc;

pub const PREDICATE_INSTANCE_DOMAIN_NAME: &str = "PredicateInstance";
pub fn predicate_instance_type() -> Type {
    Type::Domain(DomainType::new(
        PREDICATE_INSTANCE_DOMAIN_NAME,
        Default::default(),
        Vec::new(),
    ))
}
#[derive(Clone, Debug)]
pub struct PredicateInstance {
    pub predicate: String,
    pub args: Vec<Exp>,
    pub meta: Metadata,
}
impl PredicateInstance {
    pub fn expression(self) -> Exp {
        let meta = self.meta.clone();
        Exp::new(ExpKind::Extension(ExtensionExpHandle(Arc::new(self))), meta)
    }
    pub fn pretty(&self, print_exp: impl Fn(&Exp) -> String) -> String {
        format!(
            "{}({})",
            self.predicate,
            self.args
                .iter()
                .map(print_exp)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
    /// Invoke Silver's consistency purity check once per argument, preserving order.
    pub fn check_purity<E>(&self, mut check: impl FnMut(&Exp) -> Vec<E>) -> Vec<E> {
        self.args.iter().flat_map(&mut check).collect()
    }
    /// Upstream leaves verifyExtExp undefined; backend verification must lower this node.
    pub fn verify_unlowered(&self) -> Result<(), &'static str> {
        Err("predicate instance must be lowered before verification")
    }
}
impl ExtensionExp for PredicateInstance {
    fn pretty_doc(
        &self,
    ) -> Result<
        crate::ast::pretty::pretty_printer::Doc,
        crate::ast::pretty::pretty_printer::PrintError,
    > {
        use crate::ast::pretty::pretty_printer::{Doc, show_exp};
        let mut args = Vec::new();
        for (index, exp) in self.args.iter().enumerate() {
            if index != 0 {
                args.push(Doc::text(", "));
            }
            args.push(show_exp(exp)?);
        }
        Ok(Doc::concat([
            Doc::text(&self.predicate),
            Doc::concat(args).parens(),
        ]))
    }
    fn scala_hash(&self) -> Result<i32, crate::ast::utility::expressions::ScalaHashError> {
        Ok(crate::ast::utility::expressions::scala_product(
            "PredicateInstance",
            &[
                crate::ast::utility::expressions::scala_string_hash(&self.predicate),
                crate::ast::utility::expressions::scala_expression_sequence_hash(&self.args)?,
            ],
        ))
    }
    fn pretty_print(&self) -> Result<String, crate::ast::pretty::pretty_printer::PrintError> {
        let args = self
            .args
            .iter()
            .map(crate::ast::pretty::pretty_printer::pretty_expression)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("{}({})", self.predicate, args.join(", ")))
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
        crate::plugin::silver_plugin::check_pure_expressions(&self.args)
    }
    fn scope_declarations(
        &self,
    ) -> Result<
        Option<Vec<crate::ast::program::Declaration>>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(None)
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
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|other| self.predicate == other.predicate && self.args == other.args)
    }
    fn typ(&self) -> Type {
        predicate_instance_type()
    }
    fn is_pure(&self) -> bool {
        true
    }
    fn map_expressions(
        &self,
        map: &dyn Fn(&Exp) -> Result<Exp, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionExpHandle, crate::verifier::verification_result::DiagnosticError> {
        Ok(ExtensionExpHandle(Arc::new(Self {
            predicate: self.predicate.clone(),
            args: self.args.iter().map(map).collect::<Result<_, _>>()?,
            meta: self.meta.clone(),
        })))
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        Ok(self.args.iter().cloned().map(Node::Exp).collect())
    }
}

#[cfg(test)]
mod doc_tests {
    use super::*;
    use crate::ast::pretty::pretty_printer::{pretty, show_exp};

    #[test]
    fn nested_expression_keeps_its_line_breaks_in_plugin_document() {
        let meta = Metadata::default();
        let arg = Exp::new(
            ExpKind::And(
                Exp::new(ExpKind::TrueLit, meta.clone()),
                Exp::new(ExpKind::FalseLit, meta.clone()),
            ),
            meta.clone(),
        );
        let instance = PredicateInstance {
            predicate: "predicate".into(),
            args: vec![arg],
            meta,
        }
        .expression();
        let doc = show_exp(&instance).unwrap();
        assert!(pretty(12, &doc).contains('\n'));
        assert!(!pretty(80, &doc).contains('\n'));
    }
}
