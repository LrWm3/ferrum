//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/TerminationASTExtension.scala
//!
//! Purpose:
//! Represent decreases clauses and attach termination specifications to AST members and loops.
//!
//! Planned Rust structure:
//! Port DecreasesClause, DecreasesTuple, DecreasesWildcard, DecreasesStar and
//! DecreasesSpecification with condition helpers, append/fromNode, metadata and pretty printing.
//!
//! Behavior to preserve:
//! Clauses are pure Bool extensions; tuple expressions and conditions require purity. Missing
//! clause conditions mean true; termination condition is tuple/wildcard disjunction, or false when
//! neither exists. Specifications preserve tuple, wildcard and star and are not cached. Direct
//! verification is unimplemented and must be preceded by extraction.
//!
//! Integration:
//! termination_plugin extracts clauses;
//! transformation::{decreases_check,function_check,method_check}; ast metadata/consistency.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for metadata, extension nodes and failure handling.
//!
//! Open decisions:
//! Agree on information lookup and lifetime with AST and termination transformation.
//!
//! Status: partial; decreases clauses, conditions, purity adapters and specification metadata
//! are implemented. Pretty-printer integration for metadata comments remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::ast::{ExtensionInfo, Info, Metadata};
use crate::ast::expression::{Exp, ExpKind, ExtensionExp, ExtensionExpHandle};
use crate::ast::program::{Function, Method};
use crate::ast::statement::{Stmt, StmtKind};
use crate::ast::r#type::Type;
use crate::ast::utility::nodes::{Node, TraversalError};
use std::{
    any::Any,
    sync::{Arc, OnceLock},
};

/// The three source decreases clause variants, excluding metadata from equality.
#[derive(Clone, Debug)]
pub enum DecreasesKind {
    Tuple {
        tuple: Vec<Exp>,
        condition: Option<Exp>,
    },
    Wildcard {
        condition: Option<Exp>,
    },
    Star,
}
#[derive(Clone, Debug)]
pub struct DecreasesClause {
    pub kind: DecreasesKind,
    pub meta: Metadata,
    effective_condition: Arc<OnceLock<Exp>>,
}
impl DecreasesClause {
    pub fn new(kind: DecreasesKind, meta: Metadata) -> Self {
        Self {
            kind,
            meta,
            effective_condition: Arc::new(OnceLock::new()),
        }
    }
    pub fn expression(self) -> Exp {
        let meta = self.meta.clone();
        Exp::new(ExpKind::Extension(ExtensionExpHandle(Arc::new(self))), meta)
    }
    pub fn condition(&self) -> Option<&Exp> {
        match &self.kind {
            DecreasesKind::Tuple { condition, .. } | DecreasesKind::Wildcard { condition } => {
                condition.as_ref()
            }
            DecreasesKind::Star => None,
        }
    }
    pub fn effective_condition(&self) -> Exp {
        self.effective_condition
            .get_or_init(|| {
                self.condition().cloned().unwrap_or_else(|| {
                    Exp::new(
                        ExpKind::TrueLit,
                        Metadata {
                            position: self.meta.position.clone(),
                            ..Metadata::default()
                        },
                    )
                })
            })
            .clone()
    }
    pub fn pretty(&self, render: &impl Fn(&Exp) -> String) -> String {
        let mut text = match &self.kind {
            DecreasesKind::Tuple { tuple, .. } => format!(
                "decreases{}",
                if tuple.is_empty() {
                    String::new()
                } else {
                    format!(
                        " {}",
                        tuple.iter().map(render).collect::<Vec<_>>().join(", ")
                    )
                }
            ),
            DecreasesKind::Wildcard { .. } => "decreases _".into(),
            DecreasesKind::Star => "decreases *".into(),
        };
        if let Some(condition) = self.condition() {
            text.push_str(&format!(" if {}", render(condition)));
        }
        text
    }
    pub fn check_purity<E>(&self, mut check: impl FnMut(&Exp) -> Vec<E>) -> Vec<E> {
        let expressions = match &self.kind {
            DecreasesKind::Tuple { tuple, condition } => {
                tuple.iter().chain(condition.iter()).collect::<Vec<_>>()
            }
            DecreasesKind::Wildcard { condition } => condition.iter().collect(),
            DecreasesKind::Star => vec![],
        };
        expressions.into_iter().flat_map(&mut check).collect()
    }
    pub fn verify_unlowered(&self) -> Result<(), &'static str> {
        Err("DecreasesClause: verifyExtExp has not been implemented.")
    }
}
impl ExtensionExp for DecreasesClause {
    fn metadata(&self) -> &Metadata {
        &self.meta
    }
    fn with_metadata(&self, meta: Metadata) -> ExtensionExpHandle {
        ExtensionExpHandle(Arc::new(Self::new(self.kind.clone(), meta)))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
    fn equals(&self, other: &dyn ExtensionExp) -> bool {
        let Some(other) = other.as_any().downcast_ref::<Self>() else {
            return false;
        };
        match (&self.kind, &other.kind) {
            (
                DecreasesKind::Tuple {
                    tuple: a,
                    condition: ac,
                },
                DecreasesKind::Tuple {
                    tuple: b,
                    condition: bc,
                },
            ) => a == b && ac == bc,
            (
                DecreasesKind::Wildcard { condition: a },
                DecreasesKind::Wildcard { condition: b },
            ) => a == b,
            (DecreasesKind::Star, DecreasesKind::Star) => true,
            _ => false,
        }
    }
    fn typ(&self) -> Type {
        Type::Bool
    }
    fn is_pure(&self) -> bool {
        true
    }
    fn map_expressions(
        &self,
        map: &dyn Fn(&Exp) -> Result<Exp, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionExpHandle, crate::verifier::verification_result::DiagnosticError> {
        let kind = match &self.kind {
            DecreasesKind::Tuple { tuple, condition } => DecreasesKind::Tuple {
                tuple: tuple.iter().map(map).collect::<Result<_, _>>()?,
                condition: condition.as_ref().map(map).transpose()?,
            },
            DecreasesKind::Wildcard { condition } => DecreasesKind::Wildcard {
                condition: condition.as_ref().map(map).transpose()?,
            },
            DecreasesKind::Star => DecreasesKind::Star,
        };
        Ok(ExtensionExpHandle(Arc::new(Self::new(
            kind,
            self.meta.clone(),
        ))))
    }
    fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
        Ok(match &self.kind {
            DecreasesKind::Tuple { tuple, condition } => tuple
                .iter()
                .chain(condition.iter())
                .cloned()
                .map(Node::Exp)
                .collect(),
            DecreasesKind::Wildcard { condition } => {
                condition.iter().cloned().map(Node::Exp).collect()
            }
            DecreasesKind::Star => vec![],
        })
    }
}

#[derive(Clone, Debug, Default)]
pub struct DecreasesSpecification {
    pub tuple: Option<DecreasesClause>,
    pub wildcard: Option<DecreasesClause>,
    pub star: Option<DecreasesClause>,
}
impl DecreasesSpecification {
    /// Source comments use the full pretty printer; the callback supplies its parenthesization.
    pub fn comments_with(&self, render: &impl Fn(&Exp) -> String) -> Vec<String> {
        self.tuple
            .iter()
            .chain(self.wildcard.iter())
            .chain(self.star.iter())
            .map(|c| c.pretty(render))
            .collect()
    }
    pub fn termination_condition(&self) -> Exp {
        fn condition(c: &DecreasesClause) -> Exp {
            c.condition()
                .cloned()
                .unwrap_or_else(|| Exp::new(ExpKind::TrueLit, Metadata::default()))
        }
        match (&self.tuple, &self.wildcard) {
            (Some(tuple), Some(wildcard)) => Exp::new(
                ExpKind::Or(condition(tuple), condition(wildcard)),
                Metadata::default(),
            ),
            (Some(tuple), None) => condition(tuple),
            (None, Some(wildcard)) => condition(wildcard),
            _ => Exp::new(ExpKind::FalseLit, Metadata::default()),
        }
    }
    pub fn tuple_condition(&self) -> Exp {
        self.tuple
            .as_ref()
            .map(|t| {
                t.condition()
                    .cloned()
                    .unwrap_or_else(|| Exp::new(ExpKind::TrueLit, Metadata::default()))
            })
            .unwrap_or_else(|| Exp::new(ExpKind::FalseLit, Metadata::default()))
    }
    fn prepend(&self, info: &Info) -> Info {
        Info::pair(Info::Extension(Arc::new(self.clone())), info.clone())
    }
    pub fn append_to_function(&self, f: &Function) -> Function {
        f.copy_with(|d| d.meta.info = self.prepend(&d.meta.info))
    }
    pub fn append_to_method(&self, m: &Method) -> Method {
        m.copy_with(|d| d.meta.info = self.prepend(&d.meta.info))
    }
    pub fn append_to_while(&self, stmt: &Stmt) -> Result<Stmt, &'static str> {
        if !matches!(stmt.kind(), StmtKind::While { .. }) {
            return Err("expected while statement");
        }
        let mut meta = stmt.metadata().clone();
        meta.info = self.prepend(&meta.info);
        Ok(Stmt::new(stmt.kind().clone(), meta))
    }
    pub fn from_info(info: &Info) -> Result<Self, &'static str> {
        let found = info.all_extensions::<Self>();
        match found.as_slice() {
            [] => Ok(Self::default()),
            [single] => Ok((*single).clone()),
            _ => Err("multiple decreases specifications"),
        }
    }
}
impl ExtensionInfo for DecreasesSpecification {
    fn as_any(&self) -> &dyn Any {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn default_termination_and_tuple_conditions_match_source() {
        let empty = DecreasesSpecification::default();
        assert!(matches!(
            empty.termination_condition().kind(),
            ExpKind::FalseLit
        ));
        let tuple = DecreasesClause::new(
            DecreasesKind::Tuple {
                tuple: vec![],
                condition: None,
            },
            Metadata::default(),
        );
        assert!(
            tuple
                .effective_condition()
                .same_node(&tuple.effective_condition())
        );
        let both = DecreasesSpecification {
            tuple: Some(tuple),
            wildcard: Some(DecreasesClause::new(
                DecreasesKind::Wildcard { condition: None },
                Metadata::default(),
            )),
            star: None,
        };
        assert!(
            matches!(both.termination_condition().kind(), ExpKind::Or(a, b) if matches!(a.kind(), ExpKind::TrueLit) && matches!(b.kind(), ExpKind::TrueLit))
        );
        assert!(matches!(both.tuple_condition().kind(), ExpKind::TrueLit));
    }
}
