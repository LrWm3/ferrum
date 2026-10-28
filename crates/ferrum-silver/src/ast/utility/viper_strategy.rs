//! Metadata and back-translation support for Viper rewriting strategies.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/ViperStrategy.scala
//! Status: partial; built-in node metadata and direct-rewrite back-links are implemented.
//! Generic strategy adapters, extension metadata and error traversal remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    ast::{Info, Metadata, PreviousNode},
    expression::{Exp, ExpKind, FieldAccess, LocalVar, PredicateAccess, Trigger},
    program::{DomainAxiomKind, LocalVarDecl, Member},
    statement::{PredicateAccessPredicate, Stmt},
    utility::nodes::Node,
};
use std::sync::Arc;
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MetadataError {
    UnsupportedNode(&'static str),
    MissingIdentity,
}
pub(crate) fn metadata(node: &Node) -> Result<&Metadata, MetadataError> {
    match node {
        Node::Program(p) => Ok(&p.meta),
        Node::Member(m) => match m {
            Member::Domain(v) => Ok(&v.meta),
            Member::Field(v) => Ok(&v.meta),
            Member::Function(v) => Ok(&v.meta),
            Member::Predicate(v) => Ok(&v.meta),
            Member::Method(v) => Ok(&v.meta),
            Member::Extension(v) => {
                v.0.metadata()
                    .map_err(|_| MetadataError::UnsupportedNode("extension member metadata"))
            }
        },
        Node::DomainFunc(v) => Ok(&v.meta),
        Node::DomainAxiom(v) => match v.kind() {
            DomainAxiomKind::Named { meta, .. } | DomainAxiomKind::Anonymous { meta, .. } => {
                Ok(meta)
            }
        },
        Node::LocalDecl(v) => Ok(&v.meta),
        Node::LabelDecl(v) => Ok(&v.meta),
        Node::UnnamedLocalDecl(v) => Ok(&v.meta),
        Node::LocalVar(v) => Ok(&v.meta),
        Node::FieldAccess(v) => Ok(&v.meta),
        Node::PredicateAccess(v) => Ok(&v.meta),
        Node::PredicateAccessPredicate(v) => Ok(&v.meta),
        Node::Trigger(v) => Ok(&v.meta),
        Node::Exp(e) => Ok(e.metadata()),
        Node::Stmt(s) => Ok(s.metadata()),
        _ => Err(MetadataError::UnsupportedNode(
            "metadata for this node family",
        )),
    }
}
fn is_empty(meta: &Metadata) -> bool {
    matches!(meta.position, crate::ast::position::Position::NoPosition)
        && matches!(meta.info, Info::NoInfo)
        && meta.error_trafo.is_no_trafos()
}
fn with_metadata(node: &Node, meta: Metadata) -> Result<Node, MetadataError> {
    Ok(match node {
        Node::Program(v) => Node::Program(v.copy_with(|data| data.meta = meta)),
        Node::Member(v) => Node::Member(match v {
            Member::Domain(v) => Member::Domain(v.copy_with(|data| data.meta = meta)),
            Member::Field(v) => Member::Field(v.copy_with(|data| data.meta = meta)),
            Member::Function(v) => Member::Function(v.copy_with(|data| data.meta = meta)),
            Member::Predicate(v) => Member::Predicate(v.copy_with(|data| data.meta = meta)),
            Member::Method(v) => Member::Method(v.copy_with(|data| data.meta = meta)),
            Member::Extension(v) => Member::Extension(
                v.0.with_metadata(meta)
                    .map_err(|_| MetadataError::UnsupportedNode("extension member metadata"))?,
            ),
        }),
        Node::DomainFunc(v) => Node::DomainFunc(v.copy_with(|data| data.meta = meta)),
        Node::DomainAxiom(v) => Node::DomainAxiom(v.copy_with(|kind| match kind {
            DomainAxiomKind::Named { meta: m, .. } | DomainAxiomKind::Anonymous { meta: m, .. } => {
                *m = meta
            }
        })),
        Node::LocalDecl(v) => {
            Node::LocalDecl(LocalVarDecl::new(v.name.clone(), v.typ.clone(), meta))
        }
        Node::UnnamedLocalDecl(v) => Node::UnnamedLocalDecl(v.copy_with(|data| data.meta = meta)),
        Node::LocalVar(v) => Node::LocalVar(LocalVar::new(v.name.clone(), v.typ.clone(), meta)),
        Node::FieldAccess(v) => {
            Node::FieldAccess(FieldAccess::new(v.receiver.clone(), v.field.clone(), meta))
        }
        Node::PredicateAccess(v) => Node::PredicateAccess(PredicateAccess::new(
            v.args.clone(),
            v.predicate_name.clone(),
            meta,
        )),
        Node::PredicateAccessPredicate(v) => Node::PredicateAccessPredicate(
            PredicateAccessPredicate::new(v.location.clone(), v.permission.clone(), meta),
        ),
        Node::Trigger(v) => Node::Trigger(Trigger::new(v.exps.clone(), meta)),
        Node::Exp(e) => {
            let kind = match e.kind() {
                ExpKind::Extension(v) => ExpKind::Extension(v.0.with_metadata(meta.clone())),
                ExpKind::LocalVar(v) => {
                    ExpKind::LocalVar(LocalVar::new(v.name.clone(), v.typ.clone(), meta.clone()))
                }
                ExpKind::FieldAccess(v) => ExpKind::FieldAccess(FieldAccess::new(
                    v.receiver.clone(),
                    v.field.clone(),
                    meta.clone(),
                )),
                ExpKind::PredicateAccess(v) => ExpKind::PredicateAccess(PredicateAccess::new(
                    v.args.clone(),
                    v.predicate_name.clone(),
                    meta.clone(),
                )),
                ExpKind::PredicateAccessPredicate(v) => {
                    ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                        v.location.clone(),
                        v.permission.clone(),
                        meta.clone(),
                    ))
                }
                kind => kind.clone(),
            };
            Node::Exp(Exp::with_extra(kind, meta, e.0.extra.clone()))
        }
        Node::Stmt(s) => {
            let kind = match s.kind() {
                crate::ast::statement::StmtKind::Extension(v) => {
                    crate::ast::statement::StmtKind::Extension(v.0.with_metadata(meta.clone()))
                }
                crate::ast::statement::StmtKind::Label(v) => {
                    crate::ast::statement::StmtKind::Label(
                        v.copy_with(|data| data.meta = meta.clone()),
                    )
                }
                kind => kind.clone(),
            };
            Node::Stmt(Stmt::new(kind, meta))
        }
        _ => {
            return Err(MetadataError::UnsupportedNode(
                "with metadata for this node family",
            ));
        }
    })
}
/// Source returns the original new node if it is the same source object. On a
/// direct replacement it adds a previous-node backlink only when none exists.
pub fn preserve_metadata(
    old: &Node,
    now: &Node,
    directly_rewritten: bool,
) -> Result<Node, MetadataError> {
    // Types and triggers are not TransformableErrors in the upstream hierarchy.
    if matches!(old, Node::Type(_) | Node::Trigger(_)) {
        return Ok(now.clone());
    }
    let old_meta = metadata(old)?;
    let mut new_meta = metadata(now)?.clone();
    if is_empty(&new_meta) {
        new_meta = old_meta.clone();
    }
    // Distinct node families cannot share identity; equivalent typed views are
    // handled explicitly by Node::same_node.
    let same = old.same_node(now).unwrap_or(false);
    if same {
        return Ok(now.clone());
    }
    if directly_rewritten && new_meta.error_trafo.node.is_none() {
        new_meta.error_trafo.node = Some(Arc::new(PreviousNode(old.clone())));
    }
    with_metadata(now, new_meta)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{ast::ErrorTrafo, position::Position};
    #[test]
    fn extension_views_share_identity_and_metadata_copy_is_fresh() {
        use crate::plugin::standard::predicateinstance::predicate_instance_ast_extension::PredicateInstance;
        let e = PredicateInstance {
            predicate: "p".into(),
            args: vec![],
            meta: Metadata::default(),
        }
        .expression();
        let ExpKind::Extension(handle) = e.kind() else {
            panic!("extension")
        };
        let view = Exp::new(ExpKind::Extension(handle.clone()), Metadata::default());
        assert!(e.same_node(&view));
        let old = Exp::new(
            ExpKind::TrueLit,
            Metadata {
                position: Position::Virtual("old".into()),
                ..Metadata::default()
            },
        );
        let Node::Exp(copied) =
            preserve_metadata(&Node::Exp(old), &Node::Exp(e.clone()), true).unwrap()
        else {
            panic!("expression")
        };
        assert!(!e.same_node(&copied));
        assert_eq!(copied.metadata().position, Position::Virtual("old".into()));
        let ExpKind::Extension(payload) = copied.kind() else {
            panic!("extension")
        };
        assert_eq!(payload.0.metadata().position, copied.metadata().position);
    }
    #[test]
    fn direct_rewrite_preserves_empty_metadata_and_adds_old_node_link() {
        let old = Exp::new(
            ExpKind::TrueLit,
            Metadata {
                position: Position::Virtual("original".into()),
                ..Metadata::default()
            },
        );
        let now = Exp::new(ExpKind::FalseLit, Metadata::default());
        let result = preserve_metadata(&Node::Exp(old.clone()), &Node::Exp(now), true).unwrap();
        let Node::Exp(result) = result else {
            panic!("expression")
        };
        assert_eq!(
            result.metadata().position,
            Position::Virtual("original".into())
        );
        let backlink = result
            .metadata()
            .error_trafo
            .node
            .as_ref()
            .unwrap()
            .as_any()
            .downcast_ref::<PreviousNode>()
            .unwrap();
        assert!(matches!(&backlink.0,Node::Exp(e) if e.same_node(&old)));
    }
    #[test]
    fn explicitly_empty_trafos_are_not_no_trafos() {
        let old = Exp::new(
            ExpKind::TrueLit,
            Metadata {
                position: Position::Virtual("original".into()),
                ..Metadata::default()
            },
        );
        let now = Exp::new(
            ExpKind::FalseLit,
            Metadata {
                error_trafo: ErrorTrafo::trafos(vec![], vec![], None),
                ..Metadata::default()
            },
        );
        let Node::Exp(result) = preserve_metadata(&Node::Exp(old), &Node::Exp(now), false).unwrap()
        else {
            panic!("expression")
        };
        assert_eq!(result.metadata().position, Position::NoPosition);
        assert!(!result.metadata().error_trafo.is_no_trafos());
    }
    #[test]
    fn member_metadata_and_non_error_trigger_follow_source() {
        use crate::ast::{
            program::{Field, FieldData, Member},
            r#type::Type,
        };
        let old = Node::Member(Member::Field(Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: Metadata {
                position: Position::Virtual("field".into()),
                ..Metadata::default()
            },
        })));
        let now = Node::Member(Member::Field(Field::new(FieldData {
            name: "g".into(),
            typ: Type::Int,
            meta: Metadata::default(),
        })));
        let Node::Member(Member::Field(result)) = preserve_metadata(&old, &now, true).unwrap()
        else {
            panic!("field")
        };
        assert_eq!(result.meta.position, Position::Virtual("field".into()));
        let backlink = result
            .meta
            .error_trafo
            .node
            .as_ref()
            .unwrap()
            .as_any()
            .downcast_ref::<PreviousNode>()
            .unwrap();
        assert_eq!(backlink.0.same_node(&old), Some(true));
        let trigger = Node::Trigger(Trigger::new(vec![], Metadata::default()));
        assert_eq!(
            preserve_metadata(&trigger, &now, true)
                .unwrap()
                .same_node(&now),
            Some(true)
        );
    }
}
