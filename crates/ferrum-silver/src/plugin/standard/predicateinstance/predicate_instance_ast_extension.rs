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
