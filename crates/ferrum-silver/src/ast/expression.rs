//! Silver expressions.
//!
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Expression.scala
//!
//! Status: partial. Node families and structural equality are
//! represented, with purity, typing and expression-child reconstruction; full
//! consistency, general rewriting, trigger generation and pretty printing remain
//! pending; wand canonicalization is implemented in ast::utility::expressions.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::ast::Metadata;
use super::program::{Field, LocalVarDecl};
use super::statement::PredicateAccessPredicate;
use super::r#type::{Type, TypeSubstitution};
use num_bigint::BigInt;
use std::any::Any;
use std::fmt::Debug;
use std::sync::{Arc, OnceLock, RwLock};

#[derive(Clone, Debug)]
pub struct LocalVarNode {
    pub name: String,
    pub typ: Type,
    pub meta: Metadata,
}
#[derive(Clone, Debug)]
pub struct LocalVar(pub Arc<LocalVarNode>);
impl LocalVar {
    pub fn new(name: String, typ: Type, meta: Metadata) -> Self {
        Self(Arc::new(LocalVarNode { name, typ, meta }))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl std::ops::Deref for LocalVar {
    type Target = LocalVarNode;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl PartialEq for LocalVar {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name && self.typ == other.typ
    }
}
impl Eq for LocalVar {}
#[derive(Clone, Debug)]
pub struct FieldAccessNode {
    pub receiver: Exp,
    pub field: Field,
    pub meta: Metadata,
}
#[derive(Clone, Debug)]
pub struct FieldAccess(pub Arc<FieldAccessNode>);
impl FieldAccess {
    pub fn new(receiver: Exp, field: Field, meta: Metadata) -> Self {
        Self(Arc::new(FieldAccessNode {
            receiver,
            field,
            meta,
        }))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl std::ops::Deref for FieldAccess {
    type Target = FieldAccessNode;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl PartialEq for FieldAccess {
    fn eq(&self, other: &Self) -> bool {
        self.receiver == other.receiver && self.field == other.field
    }
}
impl Eq for FieldAccess {}
#[derive(Clone, Debug)]
pub struct PredicateAccessNode {
    pub args: Vec<Exp>,
    pub predicate_name: String,
    pub meta: Metadata,
}
#[derive(Clone, Debug)]
pub struct PredicateAccess(pub Arc<PredicateAccessNode>);
impl PredicateAccess {
    pub fn new(args: Vec<Exp>, predicate_name: String, meta: Metadata) -> Self {
        Self(Arc::new(PredicateAccessNode {
            args,
            predicate_name,
            meta,
        }))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl std::ops::Deref for PredicateAccess {
    type Target = PredicateAccessNode;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl PartialEq for PredicateAccess {
    fn eq(&self, other: &Self) -> bool {
        self.args == other.args && self.predicate_name == other.predicate_name
    }
}
impl Eq for PredicateAccess {}
#[derive(Clone, Debug)]
pub struct TriggerNode {
    pub exps: Vec<Exp>,
    pub meta: Metadata,
}
#[derive(Clone, Debug)]
pub struct Trigger(pub Arc<TriggerNode>);
impl Trigger {
    pub fn new(exps: Vec<Exp>, meta: Metadata) -> Self {
        Self(Arc::new(TriggerNode { exps, meta }))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl std::ops::Deref for Trigger {
    type Target = TriggerNode;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl PartialEq for Trigger {
    fn eq(&self, other: &Self) -> bool {
        self.exps == other.exps
    }
}
impl Eq for Trigger {}

pub trait ExtensionExp: Debug + Send + Sync {
    /// Complete source local check, or an explicit unsupported error.
    fn check(
        &self,
    ) -> Result<
        Vec<crate::verifier::verification_result::FrontendError>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension local consistency",
            ),
        )
    }
    /// Source scope membership and declarations; default deliberately fails closed.
    fn scope_declarations(
        &self,
    ) -> Result<
        Option<Vec<super::program::Declaration>>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Err(crate::verifier::verification_result::DiagnosticError::Unsupported("extension scope"))
    }

    fn metadata(&self) -> &Metadata;
    fn with_metadata(&self, metadata: Metadata) -> ExtensionExpHandle;
    /// First-constructor Node products visited by source checkTransitively; excludes maps.
    fn check_product_nodes(
        &self,
    ) -> Result<
        Vec<super::utility::nodes::Node>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension consistency product traversal",
            ),
        )
    }

    fn as_any(&self) -> &dyn Any;
    fn equals(&self, other: &dyn ExtensionExp) -> bool;
    fn typ(&self) -> Type;
    fn is_pure(&self) -> bool;
    fn is_valid_trigger(&self) -> bool {
        false
    }
    fn is_forbidden_in_trigger(&self) -> bool {
        true
    }
    /// Reconstruct expression children for back-transformation. Extensions with
    /// other rewritable node fields must report unsupported until they can map them.
    fn map_expressions(
        &self,
        _map: &dyn Fn(&Exp) -> Result<Exp, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionExpHandle, crate::verifier::verification_result::DiagnosticError> {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension expression reconstruction",
            ),
        )
    }
    fn subnodes(
        &self,
    ) -> Result<Vec<super::utility::nodes::Node>, super::utility::nodes::TraversalError> {
        Err(super::utility::nodes::TraversalError::Extension(
            "expression subnodes",
        ))
    }
}
#[derive(Clone, Debug)]
pub struct ExtensionExpHandle(pub Arc<dyn ExtensionExp>);
impl PartialEq for ExtensionExpHandle {
    fn eq(&self, other: &Self) -> bool {
        self.0.equals(other.0.as_ref())
    }
}
impl Eq for ExtensionExpHandle {}

/// The source's second constructor lists are preserved here, but excluded from
/// case-class equality. The concrete fields used depend on the expression kind.
#[derive(Clone, Debug, Default)]
pub struct ExpExtra {
    pub typ: Option<Type>,
    pub domain_name: Option<String>,
    pub interpretation: Option<String>,
}
#[derive(Debug)]
pub struct ExpNode {
    pub kind: ExpKind,
    pub meta: Metadata,
    pub extra: ExpExtra,
    pub simplified: RwLock<Option<SimplifiedExp>>,
    pub(crate) auto_triggered: std::sync::Mutex<Option<SimplifiedExp>>,
    implicit_full_permission: OnceLock<Exp>,
}
/// Avoid a strong Arc cycle when the cached simplified expression is itself.
#[derive(Clone, Debug)]
pub enum SimplifiedExp {
    Same,
    Other(Exp),
}
#[derive(Clone, Debug)]
pub struct Exp(pub Arc<ExpNode>);
impl PartialEq for Exp {
    fn eq(&self, other: &Self) -> bool {
        self.0.kind == other.0.kind
    }
}
impl Eq for Exp {}
impl Exp {
    pub fn new(kind: ExpKind, meta: Metadata) -> Self {
        Self::with_extra(kind, meta, ExpExtra::default())
    }
    pub fn with_extra(kind: ExpKind, meta: Metadata, extra: ExpExtra) -> Self {
        // Location accesses already carry their source metadata and identity in
        // their typed handles; use that metadata for the enclosing expression view.
        let meta = match &kind {
            ExpKind::LocalVar(a) => a.meta.clone(),
            ExpKind::PredicateAccessPredicate(a) => a.meta.clone(),
            ExpKind::FieldAccess(a) => a.meta.clone(),
            ExpKind::PredicateAccess(a) => a.meta.clone(),
            ExpKind::Extension(a) => a.0.metadata().clone(),
            _ => meta,
        };
        Self(Arc::new(ExpNode {
            kind,
            meta,
            extra,
            simplified: RwLock::new(None),
            auto_triggered: std::sync::Mutex::new(None),
            implicit_full_permission: OnceLock::new(),
        }))
    }
    pub fn kind(&self) -> &ExpKind {
        &self.0.kind
    }
    pub fn metadata(&self) -> &Metadata {
        &self.0.meta
    }
    pub fn same_node(&self, other: &Self) -> bool {
        match (self.kind(), other.kind()) {
            (ExpKind::LocalVar(a), ExpKind::LocalVar(b)) => a.same_node(b),
            (ExpKind::PredicateAccessPredicate(a), ExpKind::PredicateAccessPredicate(b)) => {
                a.same_node(b)
            }
            (ExpKind::FieldAccess(a), ExpKind::FieldAccess(b)) => a.same_node(b),
            (ExpKind::PredicateAccess(a), ExpKind::PredicateAccess(b)) => a.same_node(b),
            (ExpKind::Extension(a), ExpKind::Extension(b)) => Arc::ptr_eq(&a.0, &b.0),
            _ => Arc::ptr_eq(&self.0, &other.0),
        }
    }
    pub fn top_level_conjuncts(&self) -> Vec<Exp> {
        match self.kind() {
            ExpKind::And(a, b) => {
                let mut out = a.top_level_conjuncts();
                out.extend(b.top_level_conjuncts());
                out
            }
            _ => vec![self.clone()],
        }
    }
    pub fn permission_or_full(&self) -> Option<Exp> {
        match self.kind() {
            ExpKind::FieldAccessPredicate(_, permission) => Some(
                permission
                    .clone()
                    .unwrap_or_else(|| self.implicit_full_permission()),
            ),
            ExpKind::PredicateAccessPredicate(p) => Some(p.permission_or_full()),
            ExpKind::MagicWand(_, _) => Some(self.implicit_full_permission()),
            _ => None,
        }
    }
    fn implicit_full_permission(&self) -> Exp {
        self.0
            .implicit_full_permission
            .get_or_init(|| {
                Self::new(
                    ExpKind::FullPerm,
                    Metadata {
                        position: self.0.meta.position.clone(),
                        ..Metadata::default()
                    },
                )
            })
            .clone()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpKind {
    Add(Exp, Exp),
    Sub(Exp, Exp),
    Mul(Exp, Exp),
    Div(Exp, Exp),
    Mod(Exp, Exp),
    LtCmp(Exp, Exp),
    LeCmp(Exp, Exp),
    GtCmp(Exp, Exp),
    GeCmp(Exp, Exp),
    EqCmp(Exp, Exp),
    NeCmp(Exp, Exp),
    IntLit(BigInt),
    Minus(Exp),
    Or(Exp, Exp),
    And(Exp, Exp),
    Implies(Exp, Exp),
    MagicWand(Exp, Exp),
    Not(Exp),
    TrueLit,
    FalseLit,
    NullLit,
    RefLit(String),
    BackendValueLit(String, Type),
    FieldAccessPredicate(FieldAccess, Option<Exp>),
    PredicateAccessPredicate(PredicateAccessPredicate),
    InhaleExhaleExp(Exp, Exp),
    WildcardPerm,
    FullPerm,
    NoPerm,
    EpsilonPerm,
    FractionalPerm(Exp, Exp),
    PermDiv(Exp, Exp),
    PermPermDiv(Exp, Exp),
    CurrentPerm(Exp),
    PermMinus(Exp),
    PermAdd(Exp, Exp),
    PermSub(Exp, Exp),
    PermMul(Exp, Exp),
    IntPermMul(Exp, Exp),
    DebugPermMin(Exp, Exp),
    PermLtCmp(Exp, Exp),
    PermLeCmp(Exp, Exp),
    PermGtCmp(Exp, Exp),
    PermGeCmp(Exp, Exp),
    FuncApp(String, Vec<Exp>),
    DomainFuncApp(String, Vec<Exp>, TypeSubstitution),
    BackendFuncApp(String, Vec<Exp>),
    FieldAccess(FieldAccess),
    PredicateAccess(PredicateAccess),
    CondExp(Exp, Exp, Exp),
    Unfolding(Exp, Exp),
    Applying(Exp, Exp),
    Asserting(Exp, Exp),
    Old(Exp),
    LabelledOld(Exp, String),
    DebugLabelledOld(Exp, String),
    Let(LocalVarDecl, Exp, Exp),
    Forall(Vec<LocalVarDecl>, Vec<Trigger>, Exp),
    Exists(Vec<LocalVarDecl>, Vec<Trigger>, Exp),
    ForPerm(Vec<LocalVarDecl>, Exp, Exp),
    LocalVar(LocalVar),
    Result(Type),
    LocalVarWithVersion(String, Type),
    EmptySeq(Type),
    ExplicitSeq(Vec<Exp>),
    RangeSeq(Exp, Exp),
    SeqAppend(Exp, Exp),
    SeqIndex(Exp, Exp),
    SeqTake(Exp, Exp),
    SeqDrop(Exp, Exp),
    SeqContains(Exp, Exp),
    SeqUpdate(Exp, Exp, Exp),
    SeqLength(Exp),
    EmptySet(Type),
    ExplicitSet(Vec<Exp>),
    EmptyMultiset(Type),
    ExplicitMultiset(Vec<Exp>),
    AnySetUnion(Exp, Exp),
    AnySetIntersection(Exp, Exp),
    AnySetSubset(Exp, Exp),
    AnySetMinus(Exp, Exp),
    AnySetContains(Exp, Exp),
    AnySetCardinality(Exp),
    EmptyMap(Type, Type),
    ExplicitMap(Vec<Exp>),
    Maplet(Exp, Exp),
    MapUpdate(Exp, Exp, Exp),
    MapLookup(Exp, Exp),
    MapContains(Exp, Exp),
    MapCardinality(Exp),
    MapDomain(Exp),
    MapRange(Exp),
    Extension(ExtensionExpHandle),
}

/// Ill-formed nodes whose upstream type accessor would fail or need extra fields.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpressionTypeError {
    MissingExtraType,
    EmptyCollection,
    ExpectedSequence,
    ExpectedMap,
}
impl Exp {
    /// Compute the same type as the corresponding source node. This is not a
    /// consistency check: malformed child types can still require diagnostics.
    pub fn typ(&self) -> Result<Type, ExpressionTypeError> {
        use ExpKind::*;
        Ok(match self.kind() {
            Add(..)
            | Sub(..)
            | Mul(..)
            | Div(..)
            | Mod(..)
            | IntLit(..)
            | Minus(..)
            | SeqLength(..)
            | AnySetCardinality(..)
            | MapCardinality(..) => Type::Int,
            LtCmp(..)
            | LeCmp(..)
            | GtCmp(..)
            | GeCmp(..)
            | EqCmp(..)
            | NeCmp(..)
            | Or(..)
            | And(..)
            | Implies(..)
            | Not(..)
            | TrueLit
            | FalseLit
            | FieldAccessPredicate(..)
            | PredicateAccessPredicate(..)
            | InhaleExhaleExp(..)
            | PermLtCmp(..)
            | PermLeCmp(..)
            | PermGtCmp(..)
            | PermGeCmp(..)
            | PredicateAccess(..)
            | Forall(..)
            | Exists(..)
            | ForPerm(..)
            | SeqContains(..)
            | AnySetSubset(..)
            | MapContains(..) => Type::Bool,
            NullLit | RefLit(..) => Type::Ref,
            MagicWand(..) => Type::Wand,
            WildcardPerm | FullPerm | NoPerm | EpsilonPerm | FractionalPerm(..) | PermDiv(..)
            | PermPermDiv(..) | CurrentPerm(..) | PermMinus(..) | PermAdd(..) | PermSub(..)
            | PermMul(..) | IntPermMul(..) | DebugPermMin(..) => Type::Perm,
            BackendValueLit(_, t) | Result(t) | LocalVarWithVersion(_, t) => t.clone(),
            LocalVar(v) => v.typ.clone(),
            FieldAccess(v) => v.field.typ.clone(),
            FuncApp(..) | DomainFuncApp(..) | BackendFuncApp(..) => self
                .0
                .extra
                .typ
                .clone()
                .ok_or(ExpressionTypeError::MissingExtraType)?,
            CondExp(_, t, _)
            | Unfolding(_, t)
            | Applying(_, t)
            | Asserting(_, t)
            | Let(_, _, t) => t.typ()?,
            Old(e) | LabelledOld(e, _) | DebugLabelledOld(e, _) => e.typ()?,
            EmptySeq(t) => Type::Seq(Arc::new(t.clone())),
            ExplicitSeq(es) => Type::Seq(Arc::new(
                es.first()
                    .ok_or(ExpressionTypeError::EmptyCollection)?
                    .typ()?,
            )),
            RangeSeq(..) => Type::Seq(Arc::new(Type::Int)),
            SeqAppend(e, _)
            | SeqTake(e, _)
            | SeqDrop(e, _)
            | SeqUpdate(e, _, _)
            | AnySetUnion(e, _)
            | AnySetIntersection(e, _)
            | AnySetMinus(e, _)
            | MapUpdate(e, _, _) => e.typ()?,
            SeqIndex(e, _) => match e.typ()? {
                Type::Seq(t) => (*t).clone(),
                _ => return Err(ExpressionTypeError::ExpectedSequence),
            },
            EmptySet(t) => Type::Set(Arc::new(t.clone())),
            ExplicitSet(es) => Type::Set(Arc::new(
                es.first()
                    .ok_or(ExpressionTypeError::EmptyCollection)?
                    .typ()?,
            )),
            EmptyMultiset(t) => Type::Multiset(Arc::new(t.clone())),
            ExplicitMultiset(es) => Type::Multiset(Arc::new(
                es.first()
                    .ok_or(ExpressionTypeError::EmptyCollection)?
                    .typ()?,
            )),
            AnySetContains(_, s) => {
                if matches!(s.typ()?, Type::Set(_)) {
                    Type::Bool
                } else {
                    Type::Int
                }
            }
            EmptyMap(k, v) => Type::map(k.clone(), v.clone()),
            ExplicitMap(es) => {
                let pair = es
                    .iter()
                    .find_map(|e| match e.kind() {
                        Maplet(k, v) => Some((k, v)),
                        _ => None,
                    })
                    .ok_or(ExpressionTypeError::EmptyCollection)?;
                Type::map(pair.0.typ()?, pair.1.typ()?)
            }
            Maplet(k, v) => Type::map(k.typ()?, v.typ()?),
            MapLookup(e, _) => match e.typ()? {
                Type::Map(pair) => pair.1.clone(),
                _ => return Err(ExpressionTypeError::ExpectedMap),
            },
            MapDomain(e) => match e.typ()? {
                Type::Map(pair) => Type::Set(Arc::new(pair.0.clone())),
                _ => return Err(ExpressionTypeError::ExpectedMap),
            },
            MapRange(e) => match e.typ()? {
                Type::Map(pair) => Type::Set(Arc::new(pair.1.clone())),
                _ => return Err(ExpressionTypeError::ExpectedMap),
            },
            Extension(e) => e.0.typ(),
        })
    }
}

impl Exp {
    /// Mirrors `Expressions.isPure`; collection and application marker families
    /// are treated as pure by that source dispatch without recursively testing children.
    pub fn is_pure(&self) -> bool {
        use ExpKind::*;
        match self.kind() {
            FieldAccessPredicate(..) | PredicateAccessPredicate(..) | MagicWand(..) => false,
            Minus(e)
            | Not(e)
            | PermMinus(e)
            | Old(e)
            | LabelledOld(e, _)
            | DebugLabelledOld(e, _)
            | AnySetCardinality(e) => e.is_pure(),
            Add(a, b)
            | Sub(a, b)
            | Mul(a, b)
            | Div(a, b)
            | Mod(a, b)
            | LtCmp(a, b)
            | LeCmp(a, b)
            | GtCmp(a, b)
            | GeCmp(a, b)
            | EqCmp(a, b)
            | NeCmp(a, b)
            | Or(a, b)
            | And(a, b)
            | Implies(a, b)
            | InhaleExhaleExp(a, b)
            | FractionalPerm(a, b)
            | PermDiv(a, b)
            | PermPermDiv(a, b)
            | PermAdd(a, b)
            | PermSub(a, b)
            | PermMul(a, b)
            | IntPermMul(a, b)
            | DebugPermMin(a, b)
            | PermLtCmp(a, b)
            | PermLeCmp(a, b)
            | PermGtCmp(a, b)
            | PermGeCmp(a, b)
            | AnySetUnion(a, b)
            | AnySetIntersection(a, b)
            | AnySetSubset(a, b)
            | AnySetMinus(a, b)
            | AnySetContains(a, b) => a.is_pure() && b.is_pure(),
            CondExp(c, t, e) => c.is_pure() && t.is_pure() && e.is_pure(),
            Unfolding(_, body)
            | Applying(_, body)
            | Asserting(_, body)
            | Let(_, _, body)
            | Forall(_, _, body)
            | Exists(_, _, body)
            | ForPerm(_, _, body) => body.is_pure(),
            Extension(e) => e.0.is_pure(),
            _ => true,
        }
    }
}

impl Exp {
    /// Rebuild this expression after mapping its direct expression children. Metadata
    /// and the second constructor list are retained. Binding declarations and types
    /// are deliberately not rewritten by this operation. Typed field, predicate,
    /// and trigger children have distinct callbacks. Like withChildren, structural
    /// equality of all mapped children retains the original parent identity.
    /// Extensions are delegated explicitly to the caller.
    pub fn map_expression_children<E>(
        &self,
        f: &mut impl FnMut(&Exp) -> std::result::Result<Exp, E>,
        extension: &mut impl FnMut(&ExtensionExpHandle) -> std::result::Result<ExtensionExpHandle, E>,
        field: &mut impl FnMut(
            &crate::ast::expression::FieldAccess,
        ) -> std::result::Result<crate::ast::expression::FieldAccess, E>,
        predicate: &mut impl FnMut(
            &crate::ast::expression::PredicateAccess,
        )
            -> std::result::Result<crate::ast::expression::PredicateAccess, E>,
        trigger: &mut impl FnMut(&Trigger) -> std::result::Result<Trigger, E>,
    ) -> std::result::Result<Exp, E> {
        self.map_expression_children_impl(f, extension, field, predicate, trigger, false)
    }

    pub fn map_expression_children_by_identity<E>(
        &self,
        f: &mut impl FnMut(&Exp) -> std::result::Result<Exp, E>,
        extension: &mut impl FnMut(&ExtensionExpHandle) -> std::result::Result<ExtensionExpHandle, E>,
        field: &mut impl FnMut(
            &crate::ast::expression::FieldAccess,
        ) -> std::result::Result<crate::ast::expression::FieldAccess, E>,
        predicate: &mut impl FnMut(
            &crate::ast::expression::PredicateAccess,
        )
            -> std::result::Result<crate::ast::expression::PredicateAccess, E>,
        trigger: &mut impl FnMut(&Trigger) -> std::result::Result<Trigger, E>,
    ) -> std::result::Result<Exp, E> {
        self.map_expression_children_impl(f, extension, field, predicate, trigger, true)
    }

    fn map_expression_children_impl<E>(
        &self,
        f: &mut impl FnMut(&Exp) -> std::result::Result<Exp, E>,
        extension: &mut impl FnMut(&ExtensionExpHandle) -> std::result::Result<ExtensionExpHandle, E>,
        field: &mut impl FnMut(
            &crate::ast::expression::FieldAccess,
        ) -> std::result::Result<crate::ast::expression::FieldAccess, E>,
        predicate: &mut impl FnMut(
            &crate::ast::expression::PredicateAccess,
        )
            -> std::result::Result<crate::ast::expression::PredicateAccess, E>,
        trigger: &mut impl FnMut(&Trigger) -> std::result::Result<Trigger, E>,
        preserve_identity_changes: bool,
    ) -> std::result::Result<Exp, E> {
        use ExpKind::*;
        let changed = std::cell::Cell::new(false);
        let mut map_exp = |old: &Exp| {
            let new = f(old)?;
            changed.set(
                changed.get()
                    || if preserve_identity_changes {
                        !new.same_node(old)
                    } else {
                        new != *old
                    },
            );
            Ok(new)
        };
        let mut map_field = |old: &crate::ast::expression::FieldAccess| {
            let new = field(old)?;
            changed.set(
                changed.get()
                    || if preserve_identity_changes {
                        !new.same_node(old)
                    } else {
                        new != *old
                    },
            );
            Ok(new)
        };
        let mut map_predicate = |old: &crate::ast::expression::PredicateAccess| {
            let new = predicate(old)?;
            changed.set(
                changed.get()
                    || if preserve_identity_changes {
                        !new.same_node(old)
                    } else {
                        new != *old
                    },
            );
            Ok(new)
        };
        let mut map_trigger = |old: &Trigger| {
            let new = trigger(old)?;
            changed.set(
                changed.get()
                    || if preserve_identity_changes {
                        !new.same_node(old)
                    } else {
                        new != *old
                    },
            );
            Ok(new)
        };
        let mut map_extension = |old: &ExtensionExpHandle| {
            let new = extension(old)?;
            changed.set(
                changed.get()
                    || if preserve_identity_changes {
                        !std::sync::Arc::ptr_eq(&new.0, &old.0)
                    } else {
                        new != *old
                    },
            );
            Ok(new)
        };
        let f = &mut map_exp;
        let field = &mut map_field;
        let predicate = &mut map_predicate;
        let trigger = &mut map_trigger;
        let extension = &mut map_extension;
        let kind = match self.kind() {
            Add(a, b) => Add(f(a)?, f(b)?),
            Sub(a, b) => Sub(f(a)?, f(b)?),
            Mul(a, b) => Mul(f(a)?, f(b)?),
            Div(a, b) => Div(f(a)?, f(b)?),
            Mod(a, b) => Mod(f(a)?, f(b)?),
            LtCmp(a, b) => LtCmp(f(a)?, f(b)?),
            LeCmp(a, b) => LeCmp(f(a)?, f(b)?),
            GtCmp(a, b) => GtCmp(f(a)?, f(b)?),
            GeCmp(a, b) => GeCmp(f(a)?, f(b)?),
            EqCmp(a, b) => EqCmp(f(a)?, f(b)?),
            NeCmp(a, b) => NeCmp(f(a)?, f(b)?),
            Or(a, b) => Or(f(a)?, f(b)?),
            And(a, b) => And(f(a)?, f(b)?),
            Implies(a, b) => Implies(f(a)?, f(b)?),
            MagicWand(a, b) => MagicWand(f(a)?, f(b)?),
            InhaleExhaleExp(a, b) => InhaleExhaleExp(f(a)?, f(b)?),
            FractionalPerm(a, b) => FractionalPerm(f(a)?, f(b)?),
            PermDiv(a, b) => PermDiv(f(a)?, f(b)?),
            PermPermDiv(a, b) => PermPermDiv(f(a)?, f(b)?),
            PermAdd(a, b) => PermAdd(f(a)?, f(b)?),
            PermSub(a, b) => PermSub(f(a)?, f(b)?),
            PermMul(a, b) => PermMul(f(a)?, f(b)?),
            IntPermMul(a, b) => IntPermMul(f(a)?, f(b)?),
            DebugPermMin(a, b) => DebugPermMin(f(a)?, f(b)?),
            PermLtCmp(a, b) => PermLtCmp(f(a)?, f(b)?),
            PermLeCmp(a, b) => PermLeCmp(f(a)?, f(b)?),
            PermGtCmp(a, b) => PermGtCmp(f(a)?, f(b)?),
            PermGeCmp(a, b) => PermGeCmp(f(a)?, f(b)?),
            Unfolding(a, b) => Unfolding(f(a)?, f(b)?),
            Applying(a, b) => Applying(f(a)?, f(b)?),
            Asserting(a, b) => Asserting(f(a)?, f(b)?),
            RangeSeq(a, b) => RangeSeq(f(a)?, f(b)?),
            SeqAppend(a, b) => SeqAppend(f(a)?, f(b)?),
            SeqIndex(a, b) => SeqIndex(f(a)?, f(b)?),
            SeqTake(a, b) => SeqTake(f(a)?, f(b)?),
            SeqDrop(a, b) => SeqDrop(f(a)?, f(b)?),
            SeqContains(a, b) => SeqContains(f(a)?, f(b)?),
            AnySetUnion(a, b) => AnySetUnion(f(a)?, f(b)?),
            AnySetIntersection(a, b) => AnySetIntersection(f(a)?, f(b)?),
            AnySetSubset(a, b) => AnySetSubset(f(a)?, f(b)?),
            AnySetMinus(a, b) => AnySetMinus(f(a)?, f(b)?),
            AnySetContains(a, b) => AnySetContains(f(a)?, f(b)?),
            Maplet(a, b) => Maplet(f(a)?, f(b)?),
            MapLookup(a, b) => MapLookup(f(a)?, f(b)?),
            MapContains(a, b) => MapContains(f(a)?, f(b)?),
            Minus(a) => Minus(f(a)?),
            Not(a) => Not(f(a)?),
            CurrentPerm(a) => CurrentPerm(f(a)?),
            PermMinus(a) => PermMinus(f(a)?),
            Old(a) => Old(f(a)?),
            SeqLength(a) => SeqLength(f(a)?),
            AnySetCardinality(a) => AnySetCardinality(f(a)?),
            MapCardinality(a) => MapCardinality(f(a)?),
            MapDomain(a) => MapDomain(f(a)?),
            MapRange(a) => MapRange(f(a)?),
            CondExp(a, b, c) => CondExp(f(a)?, f(b)?, f(c)?),
            SeqUpdate(a, b, c) => SeqUpdate(f(a)?, f(b)?, f(c)?),
            MapUpdate(a, b, c) => MapUpdate(f(a)?, f(b)?, f(c)?),
            LabelledOld(a, label) => LabelledOld(f(a)?, label.clone()),
            DebugLabelledOld(a, label) => DebugLabelledOld(f(a)?, label.clone()),
            FieldAccessPredicate(a, p) => {
                FieldAccessPredicate(field(a)?, p.as_ref().map(&mut *f).transpose()?)
            }
            PredicateAccessPredicate(a) => {
                let location = predicate(&a.location)?;
                let permission = a.permission.as_ref().map(&mut *f).transpose()?;
                let permission_same = match (&permission, &a.permission) {
                    (Some(x), Some(y)) => {
                        if preserve_identity_changes {
                            x.same_node(y)
                        } else {
                            x == y
                        }
                    }
                    (None, None) => true,
                    _ => false,
                };
                PredicateAccessPredicate(
                    if (if preserve_identity_changes {
                        location.same_node(&a.location)
                    } else {
                        location == a.location
                    }) && permission_same
                    {
                        a.clone()
                    } else {
                        crate::ast::statement::PredicateAccessPredicate::new(
                            location,
                            permission,
                            a.meta.clone(),
                        )
                    },
                )
            }
            FieldAccess(a) => {
                let receiver = f(&a.receiver)?;
                FieldAccess(
                    if if preserve_identity_changes {
                        receiver.same_node(&a.receiver)
                    } else {
                        receiver == a.receiver
                    } {
                        a.clone()
                    } else {
                        crate::ast::expression::FieldAccess::new(
                            receiver,
                            a.field.clone(),
                            a.meta.clone(),
                        )
                    },
                )
            }
            PredicateAccess(a) => {
                let args = a
                    .args
                    .iter()
                    .map(&mut *f)
                    .collect::<std::result::Result<Vec<_>, _>>()?;
                PredicateAccess(
                    if args.iter().zip(&a.args).all(|(x, y)| {
                        if preserve_identity_changes {
                            x.same_node(y)
                        } else {
                            x == y
                        }
                    }) {
                        a.clone()
                    } else {
                        crate::ast::expression::PredicateAccess::new(
                            args,
                            a.predicate_name.clone(),
                            a.meta.clone(),
                        )
                    },
                )
            }
            FuncApp(n, args) => FuncApp(
                n.clone(),
                args.iter()
                    .map(&mut *f)
                    .collect::<std::result::Result<_, _>>()?,
            ),
            BackendFuncApp(n, args) => BackendFuncApp(
                n.clone(),
                args.iter()
                    .map(&mut *f)
                    .collect::<std::result::Result<_, _>>()?,
            ),
            DomainFuncApp(n, args, types) => DomainFuncApp(
                n.clone(),
                args.iter()
                    .map(&mut *f)
                    .collect::<std::result::Result<_, _>>()?,
                types.clone(),
            ),
            Let(d, a, b) => Let(d.clone(), f(a)?, f(b)?),
            Forall(ds, ts, b) => Forall(
                ds.clone(),
                ts.iter()
                    .map(&mut *trigger)
                    .collect::<std::result::Result<_, _>>()?,
                f(b)?,
            ),
            Exists(ds, ts, b) => Exists(
                ds.clone(),
                ts.iter()
                    .map(&mut *trigger)
                    .collect::<std::result::Result<_, _>>()?,
                f(b)?,
            ),
            ForPerm(ds, a, b) => ForPerm(ds.clone(), f(a)?, f(b)?),
            ExplicitSeq(args) => ExplicitSeq(
                args.iter()
                    .map(&mut *f)
                    .collect::<std::result::Result<_, _>>()?,
            ),
            ExplicitSet(args) => ExplicitSet(
                args.iter()
                    .map(&mut *f)
                    .collect::<std::result::Result<_, _>>()?,
            ),
            ExplicitMultiset(args) => ExplicitMultiset(
                args.iter()
                    .map(&mut *f)
                    .collect::<std::result::Result<_, _>>()?,
            ),
            ExplicitMap(args) => ExplicitMap(
                args.iter()
                    .map(&mut *f)
                    .collect::<std::result::Result<_, _>>()?,
            ),
            Extension(e) => Extension(extension(e)?),
            IntLit(_)
            | TrueLit
            | FalseLit
            | NullLit
            | RefLit(_)
            | BackendValueLit(..)
            | WildcardPerm
            | FullPerm
            | NoPerm
            | EpsilonPerm
            | LocalVar(_)
            | Result(_)
            | LocalVarWithVersion(..)
            | EmptySeq(_)
            | EmptySet(_)
            | EmptyMultiset(_)
            | EmptyMap(..) => self.kind().clone(),
        };
        if !changed.get() {
            return Ok(self.clone());
        }
        Ok(Self::with_extra(
            kind,
            self.0.meta.clone(),
            self.0.extra.clone(),
        ))
    }
}

impl Exp {
    pub fn magic_wand_structure(
        &self,
        program: &super::program::Program,
        unique_names: bool,
    ) -> Result<Exp, super::utility::expressions::MagicWandError> {
        super::utility::expressions::magic_wand_structure(self, program, unique_names)
    }
    pub fn magic_wand_subexpressions(
        &self,
        program: &super::program::Program,
    ) -> Result<Vec<Exp>, super::utility::expressions::MagicWandError> {
        super::utility::expressions::magic_wand_subexpressions(self, program)
    }
}

#[cfg(test)]
mod identity_reconstruction_tests {
    use super::*;

    #[test]
    fn identity_child_mapping_keeps_equal_expression_with_changed_extra_type() {
        let meta = Metadata::default();
        let original = Exp::with_extra(
            ExpKind::FuncApp("f".into(), vec![]),
            meta.clone(),
            ExpExtra {
                typ: Some(Type::Int),
                ..Default::default()
            },
        );
        let replacement = Exp::with_extra(
            original.kind().clone(),
            meta.clone(),
            ExpExtra {
                typ: Some(Type::Bool),
                ..Default::default()
            },
        );
        assert_eq!(original, replacement);
        let parent = Exp::new(ExpKind::Not(original), meta);
        let result: Result<Exp, ()> = parent.map_expression_children_by_identity(
            &mut |_| Ok(replacement.clone()),
            &mut |e| Ok(e.clone()),
            &mut |f| Ok(f.clone()),
            &mut |p| Ok(p.clone()),
            &mut |t| Ok(t.clone()),
        );
        let result = result.unwrap();
        let ExpKind::Not(child) = result.kind() else {
            panic!("expected Not")
        };
        assert!(matches!(child.0.extra.typ, Some(Type::Bool)));
        assert!(!parent.same_node(&result));
    }
}
