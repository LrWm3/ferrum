//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/predicateinstance/PredicateInstancePASTExtension.scala
//!
//! Purpose:
//! Represent #predicate(args) in the parse AST.
//!
//! Planned Rust structure:
//! Port PPredicateInstanceKeyword, PMarkerSymbol and PPredicateInstance with mutable
//! substitutions, typecheck, forceSubstitution and translateExp.
//!
//! Behavior to preserve:
//! Retype reference as a predicate call and reuse its typechecking/substitutions; force
//! substitutions on arguments; preserve source position on translation. The undefined-name branch
//! lacks a return before the subsequent independent if, so examine its observed behavior rather
//! than assume the intended error.
//!
//! Integration:
//! parser::parse_ast, resolver and translator; predicate_instance_ast_extension and
//! predicate_instance_plugin.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for mutable parse nodes and extension hooks.
//!
//! Open decisions:
//! Reconcile undefined-name control flow and type representation with resolver before
//! implementation.
//!
//! Status: partial; typed syntax, substitution and predicate-call adapters are implemented.
//! Parser registration and concrete resolver/translator extension dispatch remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::predicate_instance_ast_extension::PredicateInstance;
use crate::ast::ast::Metadata;
use crate::ast::expression::Exp;
use crate::ast::position::Position;
use crate::parser::parse_ast::{
    ForceSubstitutionError, PExpArguments, PExpHandle, PExpression, PExpressionKind, PExtender,
    PIdnRef, PNodeHandle, PNodeKind, PTypeHandle, PTypeKind, PTypeSubstitution,
};
use crate::parser::parse_ast_keyword::{
    PExtensionKeyword, PExtensionKeywordCategory, PExtensionSymbol, PExtensionSymbolCategory,
    PReserved, Span,
};
use std::sync::Arc;

pub fn predicate_instance_keyword(pos: Span) -> PReserved<PExtensionKeyword> {
    PReserved::new(
        PExtensionKeyword {
            spelling: "PredicateInstance".into(),
            category: PExtensionKeywordCategory::Type,
        },
        pos,
    )
}
pub fn marker_symbol(pos: Span) -> PReserved<PExtensionSymbol> {
    PReserved::new(
        PExtensionSymbol {
            spelling: "#".into(),
            category: PExtensionSymbolCategory::Language,
        },
        pos,
    )
}
#[derive(Clone, Debug)]
pub struct PPredicateInstance {
    pub marker: PReserved<PExtensionSymbol>,
    pub idnuse: PNodeHandle,
    pub args: PExpArguments,
    pub pos: Span,
}
impl PExtender for PPredicateInstance {
    fn reformat_as_product(&self) -> bool {
        true
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        vec![
            self.marker.node().clone(),
            self.idnuse.clone(),
            self.args.node().clone(),
        ]
    }
}
impl PPredicateInstance {
    pub fn expression(self) -> PExpHandle {
        let pos = self.pos.clone();
        let mut exp = PExpression::from_kind(PExpressionKind::Extension(Arc::new(self)));
        let no_pos = (Position::NoPosition, Position::NoPosition);
        exp.typ = PTypeHandle::new(
            PTypeKind::ExtensionPrimitive {
                name: predicate_instance_keyword(no_pos.clone()),
            },
            no_pos,
        );
        exp.type_substitutions = Some(Vec::new());
        PExpHandle::new(exp, pos)
    }
    pub fn force_substitution(
        &self,
        substitution: &PTypeSubstitution,
    ) -> Result<(), ForceSubstitutionError> {
        for arg in self.args.inner().to_seq() {
            arg.force_substitution(substitution)?;
        }
        Ok(())
    }
    /// The first empty-declarations diagnostic in the Scala source is discarded by
    /// its following independent `if`; empty declarations therefore reach the call checker.
    pub fn check_as_predicate_call(
        &self,
        owner: &PExpHandle,
    ) -> Result<Option<String>, crate::parser::resolver::TypeCheckError> {
        let decls = PIdnRef::decls(&self.idnuse, |_| true);
        if decls.len() > 1 {
            let name = match &self.idnuse.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(id) => id.name.clone(),
                _ => {
                    return Err(crate::parser::resolver::TypeCheckError::Unsupported(
                        "predicate instance identifier",
                    ));
                }
            };
            return Ok(Some(format!("ambiguous predicate instance `{name}`")));
        }
        let call = PExpHandle::new(
            PExpression::from_kind(PExpressionKind::Call {
                idnref: self.idnuse.clone(),
                call_args: self.args.clone(),
                type_annotated: None,
                extra_local_type_variables: vec![],
                domain_type_renaming: None,
                domain_substitution: None,
            }),
            self.pos.clone(),
        );
        crate::parser::resolver::check_expression(&call, None)?;
        let substitutions = match &call.node().read().expect("poisoned parse node").kind {
            PNodeKind::Expression(e) => e.type_substitutions.clone(),
            _ => unreachable!(),
        };
        if let PNodeKind::Expression(e) =
            &mut owner.node().write().expect("poisoned parse node").kind
        {
            e.type_substitutions = substitutions;
        }
        Ok(None)
    }
    pub fn translate<E>(
        &self,
        lift_metadata: impl FnOnce(&Span) -> Metadata,
        mut translate_exp: impl FnMut(&PExpHandle) -> Result<Exp, E>,
    ) -> Result<Exp, E> {
        let name = match &self.idnuse.read().expect("poisoned parse node").kind {
            PNodeKind::IdnRef(id) => id.name.clone(),
            _ => panic!("predicate instance must have an identifier reference"),
        };
        let args = self
            .args
            .inner()
            .to_seq()
            .into_iter()
            .map(&mut translate_exp)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(PredicateInstance {
            predicate: name,
            args,
            meta: lift_metadata(&self.pos),
        }
        .expression())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn extension_type_and_marker_keep_their_categories() {
        use crate::parser::parse_ast_keyword::{PReservedString, PToken};
        let pos = (Position::NoPosition, Position::NoPosition);
        let keyword = predicate_instance_keyword(pos.clone());
        let marker = marker_symbol(pos.clone());
        assert_eq!(keyword.value().token(), "PredicateInstance");
        assert_eq!(marker.value().token(), "#");
        assert!(matches!(
            &marker.node().read().unwrap().kind,
            PNodeKind::Reserved(PToken::ExtensionSymbol(_))
        ));
        let first = PTypeHandle::new(PTypeKind::ExtensionPrimitive { name: keyword }, pos.clone());
        let second = PTypeHandle::new(
            PTypeKind::ExtensionPrimitive {
                name: predicate_instance_keyword(pos.clone()),
            },
            pos,
        );
        assert!(first.structurally_equals(&second));
        assert!(first.is_ground());
    }
}
