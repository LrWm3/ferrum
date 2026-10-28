//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/sif/SIFPAstExtensions.scala
//!
//! Purpose:
//! Typecheck and translate low, lowEvent and rel parse expressions.
//!
//! Planned Rust structure:
//! Port PLowExp, PLowEventExp and PRelExp typechecking, substitution and translateExp hooks.
//!
//! Behavior to preserve:
//! low and lowEvent are Bool accepted as Bool or Impure; low checks operand without expected type.
//! rel checks its operand and integer index, permits only 0 or 1, and matches expected operand
//! type. Preserve positions and substitution behavior.
//!
//! Integration:
//! sif_plugin grammar, parser::resolver/translator and sif_ast_extensions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for mutable parse AST, types and positions.
//!
//! Open decisions:
//! Agree on extension typechecking and substitution representation with parser.
//!
//! Status: partial; low, lowEvent and rel parse expressions, source typecheck ordering and
//! translation adapters implemented. Parser registration and extension dispatch remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2025 ETH Zurich.

use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
use crate::ast::ast::Metadata;
use crate::ast::expression::Exp;
use crate::parser::parse_ast::{
    ForceSubstitutionError, PExpHandle, PExpression, PExpressionKind, PExtender, PNodeHandle,
    PNodeKind, PTypeHandle, PTypeSubstitution, type_from_signature,
};
use crate::parser::parse_ast_keyword::{SignatureType, Span};
use crate::verifier::verification_result::DiagnosticError;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub enum PSifKind {
    Low(PExpHandle),
    LowEvent,
    Rel { exp: PExpHandle, index: PExpHandle },
}
#[derive(Clone, Debug)]
pub struct PSifExpression {
    pub kind: PSifKind,
    pub pos: Span,
}
#[derive(Clone, Debug)]
pub enum SifTypeError {
    Expected {
        expected: PTypeHandle,
        actual: PTypeHandle,
    },
    InvalidRelIndex(num_bigint::BigInt),
    NonLiteralRelIndex,
}
impl PExtender for PSifExpression {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        match &self.kind {
            PSifKind::Low(exp) => vec![exp.node().clone()],
            PSifKind::LowEvent => vec![],
            PSifKind::Rel { exp, index } => vec![exp.node().clone(), index.node().clone()],
        }
    }
}
impl PSifExpression {
    pub fn expression(self) -> PExpHandle {
        let pos = self.pos.clone();
        let is_rel = matches!(&self.kind, PSifKind::Rel { .. });
        let mut expression = PExpression::from_kind(PExpressionKind::Extension(Arc::new(self)));
        if !is_rel {
            expression.typ = type_from_signature(&SignatureType::Bool);
        }
        expression.type_substitutions = Some(vec![]);
        PExpHandle::new(expression, pos)
    }
    pub fn type_substitutions(&self) -> Option<Vec<PTypeSubstitution>> {
        let exp = match &self.kind {
            PSifKind::Low(exp) | PSifKind::Rel { exp, .. } => exp,
            PSifKind::LowEvent => return Some(vec![]),
        };
        match &exp.node().read().expect("poisoned parse node").kind {
            PNodeKind::Expression(e) => e.type_substitutions.clone(),
            _ => None,
        }
    }
    pub fn force_substitution(
        &self,
        substitution: &PTypeSubstitution,
    ) -> Result<(), ForceSubstitutionError> {
        match &self.kind {
            PSifKind::Low(exp) | PSifKind::Rel { exp, .. } => exp.force_substitution(substitution),
            PSifKind::LowEvent => Ok(()),
        }
    }
    /// Calls ordinary top-typed checking in source order and returns typed errors for
    /// the caller's source pretty-printer and diagnostic collector.
    pub fn typecheck<E>(
        &self,
        owner: &PExpHandle,
        expected: Option<&PTypeHandle>,
        mut check: impl FnMut(&PExpHandle, Option<&PTypeHandle>) -> Result<(), E>,
    ) -> Result<Option<SifTypeError>, E> {
        let boolean = type_from_signature(&SignatureType::Bool);
        let impure = type_from_signature(&SignatureType::Impure);
        match &self.kind {
            PSifKind::Low(exp) => {
                check(exp, None)?;
            }
            PSifKind::LowEvent => {}
            PSifKind::Rel { exp, index } => {
                check(exp, None)?;
                check(index, Some(&type_from_signature(&SignatureType::Int)))?;
                let typ = match &exp.node().read().expect("poisoned parse node").kind {
                    PNodeKind::Expression(e) => e.typ.clone(),
                    _ => unreachable!(),
                };
                if let PNodeKind::Expression(e) =
                    &mut owner.node().write().expect("poisoned parse node").kind
                {
                    e.typ = typ.clone();
                }
                let integer = match &index.node().read().expect("poisoned parse node").kind {
                    PNodeKind::Expression(e) => match &e.kind {
                        PExpressionKind::IntLit(i) => i.clone(),
                        _ => return Ok(Some(SifTypeError::NonLiteralRelIndex)),
                    },
                    _ => return Ok(Some(SifTypeError::NonLiteralRelIndex)),
                };
                if integer != num_bigint::BigInt::from(0) && integer != num_bigint::BigInt::from(1)
                {
                    return Ok(Some(SifTypeError::InvalidRelIndex(integer)));
                }
                if let Some(expected) = expected {
                    if !expected.structurally_equals(&typ) {
                        return Ok(Some(SifTypeError::Expected {
                            expected: expected.clone(),
                            actual: typ,
                        }));
                    }
                }
                return Ok(None);
            }
        }
        if let Some(expected) = expected {
            if !expected.structurally_equals(&boolean) && !expected.structurally_equals(&impure) {
                return Ok(Some(SifTypeError::Expected {
                    expected: expected.clone(),
                    actual: boolean,
                }));
            }
        }
        Ok(None)
    }
    pub fn translate<E>(
        &self,
        lift_metadata: impl FnOnce(&Span) -> Metadata,
        mut translate: impl FnMut(&PExpHandle) -> Result<Exp, E>,
    ) -> Result<Result<Exp, DiagnosticError>, E> {
        let kind = match &self.kind {
            PSifKind::Low(exp) => SifExpressionKind::Low {
                exp: translate(exp)?,
                comparator: None,
                type_variables: Default::default(),
            },
            PSifKind::LowEvent => SifExpressionKind::LowEvent,
            PSifKind::Rel { exp, index } => SifExpressionKind::Rel {
                exp: translate(exp)?,
                index: translate(index)?,
            },
        };
        Ok(SifExpression {
            kind,
            meta: lift_metadata(&self.pos),
        }
        .expression())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::position::Position;
    #[test]
    fn rel_checks_expression_before_index_and_rejects_out_of_range() {
        let exp = crate::parser::fast_parser::parse_expression("true", "test.vpr")
            .unwrap()
            .expression;
        let index = crate::parser::fast_parser::parse_expression("2", "test.vpr")
            .unwrap()
            .expression;
        let sif = PSifExpression {
            kind: PSifKind::Rel {
                exp: exp.clone(),
                index: index.clone(),
            },
            pos: (Position::NoPosition, Position::NoPosition),
        };
        let owner = sif.clone().expression();
        let mut order = Vec::new();
        let error = sif
            .typecheck(&owner, None, |node, expected| {
                order.push((
                    std::sync::Arc::ptr_eq(node.node(), index.node()),
                    expected.is_some(),
                ));
                Ok::<_, ()>(())
            })
            .unwrap();
        assert_eq!(order, vec![(false, false), (true, true)]);
        assert!(
            matches!(error, Some(SifTypeError::InvalidRelIndex(i)) if i == num_bigint::BigInt::from(2))
        );
    }
}
