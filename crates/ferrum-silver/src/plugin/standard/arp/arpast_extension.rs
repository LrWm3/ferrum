//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/arp/ARPASTExtension.scala
//!
//! Purpose:
//! Represent abstract read permission rd in the Silver AST until lowering.
//!
//! Planned Rust structure:
//! Port RdPerm as a pure Perm-typed extension expression with no children and rd pretty printing.
//!
//! Behavior to preserve:
//! Preserve position, metadata and error transformation; verifyExtExp is unimplemented upstream
//! and the plugin must eliminate it.
//!
//! Integration:
//! arp_plugin lowers the node; arppast_extension constructs it; ast expressions and verifier
//! interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for AST and metadata ownership.
//!
//! Open decisions:
//! Agree on unsupported unlowered extension handling with verifier.
//!
//! Status: partial; typed read-permission extension and translation adapter implemented.
//! Parser registration and ARP lowering remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.

use crate::ast::ast::Metadata;
use crate::ast::expression::{Exp, ExpKind, ExtensionExp, ExtensionExpHandle};
use crate::ast::r#type::Type;
use crate::ast::utility::nodes::{Node, TraversalError};
use std::any::Any;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct RdPerm {
    pub meta: Metadata,
}
impl RdPerm {
    pub fn expression(self) -> Exp {
        let meta = self.meta.clone();
        Exp::new(ExpKind::Extension(ExtensionExpHandle(Arc::new(self))), meta)
    }
    pub fn pretty(&self) -> &'static str {
        "rd"
    }
    pub fn verify_unlowered(&self) -> Result<(), &'static str> {
        Err("abstract read permission must be lowered before verification")
    }
}
impl ExtensionExp for RdPerm {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionExp) -> bool {
        other.as_any().is::<Self>()
    }
    fn typ(&self) -> Type {
        Type::Perm
    }
    fn is_pure(&self) -> bool {
        true
    }
    fn map_expressions(
        &self,
        _: &dyn Fn(&Exp) -> Result<Exp, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionExpHandle, crate::verifier::verification_result::DiagnosticError> {
        Ok(ExtensionExpHandle(Arc::new(self.clone())))
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        Ok(Vec::new())
    }
}
