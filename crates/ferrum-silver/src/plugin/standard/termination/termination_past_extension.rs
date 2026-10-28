//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/TerminationPASTExtension.scala
//!
//! Purpose:
//! Represent decreases syntax and resolve its types before AST translation.
//!
//! Planned Rust structure:
//! Port PDecreasesKeyword, PIfKeyword, PWildcardSym, PDecreasesClause and tuple/wildcard/star
//! variants with typecheck and translateExp.
//!
//! Behavior to preserve:
//! Clause is Bool with identity substitution; conditions are checked Bool and tuple expressions
//! checked without a required type. Translate corresponding AST clause with position; star has no
//! condition.
//!
//! Integration:
//! termination_plugin supplies grammar; parser::resolver and translator;
//! termination_ast_extension.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser extensions, type inference and positions.
//!
//! Open decisions:
//! Reconcile extension dispatch and position ownership with parser and AST.
//!
//! Status: partial; clause syntax, parser registration, predicate-access rewriting, ordered
//! checking and translation dispatch are implemented. General plugin dispatch remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::termination_ast_extension::{DecreasesClause, DecreasesKind};
use crate::ast::ast::Metadata;
use crate::ast::expression::Exp;
use crate::parser::parse_ast::{
    PExpHandle, PExpression, PExpressionKind, PExtender, PNodeHandle, PTypeHandle,
    PTypeSubstitution, type_from_signature,
};
use crate::parser::parse_ast_keyword::{
    Formatting, PDelimited, PExtensionKeyword, PExtensionKeywordCategory, PExtensionSymbol,
    PExtensionSymbolCategory, PFormatting, PGraphElement, PReserved, PReservedString, PSym, PToken,
    PTokenValue, Pad, SignatureType, Span,
};
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PIfKeyword;
impl PReservedString for PIfKeyword {
    fn token(&self) -> &str {
        "if"
    }
}
impl PTokenValue for PIfKeyword {
    fn graph_token(&self) -> PToken {
        PToken::ExtensionKeyword(PExtensionKeyword {
            spelling: "if".into(),
            category: PExtensionKeywordCategory::Language,
        })
    }
}
impl PFormatting for PIfKeyword {
    fn formatting(&self) -> Formatting {
        Formatting {
            left: Some(Pad::Space),
            right: Some(Pad::Space),
            ..Formatting::default()
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PWildcardSym;
impl PReservedString for PWildcardSym {
    fn token(&self) -> &str {
        "_"
    }
}
impl PTokenValue for PWildcardSym {
    fn graph_token(&self) -> PToken {
        PToken::ExtensionSymbol(PExtensionSymbol {
            spelling: "_".into(),
            category: PExtensionSymbolCategory::Language,
        })
    }
}
impl PFormatting for PWildcardSym {
    fn formatting(&self) -> Formatting {
        Formatting {
            left: Some(Pad::Space),
            ..Formatting::default()
        }
    }
}
pub fn decreases_keyword(pos: Span) -> PReserved<PExtensionKeyword> {
    PReserved::new(
        PExtensionKeyword {
            spelling: "decreases".into(),
            category: PExtensionKeywordCategory::Language,
        },
        pos,
    )
}

#[derive(Clone, Debug)]
pub enum PDecreasesKind {
    Tuple {
        tuple: PDelimited<PExpHandle, PReserved<PSym>>,
        condition: Option<(PReserved<PIfKeyword>, PExpHandle)>,
    },
    Wildcard {
        wildcard: PReserved<PWildcardSym>,
        condition: Option<(PReserved<PIfKeyword>, PExpHandle)>,
    },
    Star {
        star: PReserved<PSym>,
    },
}
#[derive(Clone, Debug)]
pub struct PDecreasesClause {
    pub kind: PDecreasesKind,
    pub pos: Span,
}
impl PExtender for PDecreasesClause {
    fn reformat_as_product(&self) -> bool {
        true
    }
    fn reformat_child_formatting(&self, child: &PNodeHandle) -> Option<Formatting> {
        let condition = match &self.kind {
            PDecreasesKind::Tuple { condition, .. } => condition.as_ref(),
            PDecreasesKind::Wildcard {
                wildcard,
                condition,
            } => {
                if Arc::ptr_eq(wildcard.node(), child) {
                    return Some(wildcard.value().formatting());
                }
                condition.as_ref()
            }
            PDecreasesKind::Star { .. } => None,
        };
        condition.and_then(|(keyword, _)| {
            Arc::ptr_eq(keyword.node(), child).then(|| keyword.value().formatting())
        })
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn subnodes(&self) -> Vec<PNodeHandle> {
        let mut nodes = Vec::new();
        match &self.kind {
            PDecreasesKind::Tuple { tuple, condition } => {
                nodes.extend(tuple.graph_nodes());
                if let Some((keyword, exp)) = condition {
                    nodes.extend(keyword.graph_nodes());
                    nodes.push(exp.node().clone());
                }
            }
            PDecreasesKind::Wildcard {
                wildcard,
                condition,
            } => {
                nodes.extend(wildcard.graph_nodes());
                if let Some((keyword, exp)) = condition {
                    nodes.extend(keyword.graph_nodes());
                    nodes.push(exp.node().clone());
                }
            }
            PDecreasesKind::Star { star } => nodes.extend(star.graph_nodes()),
        }
        nodes
    }
}
impl PDecreasesClause {
    pub fn expression(self) -> PExpHandle {
        let pos = self.pos.clone();
        let mut exp = PExpression::from_kind(PExpressionKind::Extension(Arc::new(self)));
        exp.typ = type_from_signature(&SignatureType::Bool);
        exp.type_substitutions = Some(vec![PTypeSubstitution::default()]);
        PExpHandle::new(exp, pos)
    }
    /// Source intentionally does not propagate substitution to the contained expressions.
    pub fn force_substitution(&self, _: &PTypeSubstitution) {}
    pub fn typecheck<E>(
        &self,
        mut check: impl FnMut(&PExpHandle, Option<&PTypeHandle>) -> Result<(), E>,
    ) -> Result<(), E> {
        let boolean = type_from_signature(&SignatureType::Bool);
        match &self.kind {
            PDecreasesKind::Tuple { tuple, condition } => {
                if let Some((_, condition)) = condition {
                    check(condition, Some(&boolean))?;
                }
                for expression in tuple.to_seq() {
                    check(expression, None)?;
                }
            }
            PDecreasesKind::Wildcard { condition, .. } => {
                if let Some((_, condition)) = condition {
                    check(condition, Some(&boolean))?;
                }
            }
            PDecreasesKind::Star { .. } => {}
        }
        Ok(())
    }
    pub fn translate<E>(
        &self,
        lift_metadata: impl FnOnce(&Span) -> Metadata,
        mut translate: impl FnMut(&PExpHandle) -> Result<Exp, E>,
    ) -> Result<Exp, E> {
        let kind = match &self.kind {
            PDecreasesKind::Tuple { tuple, condition } => DecreasesKind::Tuple {
                tuple: tuple
                    .to_seq()
                    .into_iter()
                    .map(&mut translate)
                    .collect::<Result<_, _>>()?,
                condition: condition.as_ref().map(|(_, e)| translate(e)).transpose()?,
            },
            PDecreasesKind::Wildcard { condition, .. } => DecreasesKind::Wildcard {
                condition: condition.as_ref().map(|(_, e)| translate(e)).transpose()?,
            },
            PDecreasesKind::Star { .. } => DecreasesKind::Star,
        };
        Ok(DecreasesClause::new(kind, lift_metadata(&self.pos)).expression())
    }
}
