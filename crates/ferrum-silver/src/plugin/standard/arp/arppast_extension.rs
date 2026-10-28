//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/arp/ARPPASTExtension.scala
//!
//! Purpose:
//! Represent and typecheck rd in the parse AST.
//!
//! Planned Rust structure:
//! Port PRdKeyword and PRdPerm, including fixed Perm type, identity substitution, expected-type
//! check and translateExp.
//!
//! Behavior to preserve:
//! No typecheck error without an expected type; delegate expected-type checking to TypeChecker and
//! preserve source position in RdPerm.
//!
//! Integration:
//! parser::fast_parser, resolver and translator; arp_plugin and arpast_extension.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser extensions and type inference.
//!
//! Open decisions:
//! Agree on parser hooks and extension dispatch with parser modules.
//!
//! Status: partial; typed read-permission extension and translation adapter implemented.
//! Parser registration and ARP lowering remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.

use super::arpast_extension::RdPerm;
use crate::ast::ast::Metadata;
use crate::ast::expression::Exp;
use crate::parser::parse_ast::{
    PExpHandle, PExpression, PExpressionKind, PExtender, PNodeHandle, PTypeHandle,
    PTypeSubstitution, type_from_signature,
};
use crate::parser::parse_ast_keyword::{
    PExtensionKeyword, PExtensionKeywordCategory, PReserved, SignatureType, Span,
};
use std::sync::Arc;

pub fn rd_keyword(pos: Span) -> PReserved<PExtensionKeyword> {
    PReserved::new(
        PExtensionKeyword {
            spelling: "rd".into(),
            category: PExtensionKeywordCategory::Constant,
        },
        pos,
    )
}
#[derive(Clone, Debug)]
pub struct PRdPerm {
    pub keyword: PReserved<PExtensionKeyword>,
    pub pos: Span,
}
impl PExtender for PRdPerm {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        vec![self.keyword.node().clone()]
    }
}
impl PRdPerm {
    pub fn expression(self) -> PExpHandle {
        let pos = self.pos.clone();
        let mut expression = PExpression::from_kind(PExpressionKind::Extension(Arc::new(self)));
        expression.typ = type_from_signature(&SignatureType::Perm);
        expression.type_substitutions = Some(vec![PTypeSubstitution::default()]);
        PExpHandle::new(expression, pos)
    }
    pub fn force_substitution(&self, _: &PTypeSubstitution) {}
    pub fn typecheck_with_expected<E>(
        &self,
        expected: &PTypeHandle,
        check_top_typed: impl FnOnce(&Self, &PTypeHandle) -> Result<(), E>,
    ) -> Result<(), E> {
        check_top_typed(self, expected)
    }
    pub fn translate(&self, lift_metadata: impl FnOnce(&Span) -> Metadata) -> Exp {
        RdPerm {
            meta: lift_metadata(&self.pos),
        }
        .expression()
    }
}
