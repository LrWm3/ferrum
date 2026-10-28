//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/Translator.scala
//!
//! Purpose:
//! Translate resolved parse AST to verification AST and report translation consistency failures.
//!
//! Planned Rust structure:
//! Port Translator translate, signature/member table, member/stmt/exp/ttyp dispatch,
//! methodCallAssign, havoc and annotation helpers, and position/info conversion.
//!
//! Behavior to preserve:
//! Build domain and extension signatures first, then domain functions and other signatures before
//! bodies. Preserve positions and SourcePNodeInfo/annotations; translate field call targets using
//! receiver temporaries before call and field writes afterward, reporting duplicate fields.
//! Rewrite impure assumes after assembling the program, desugar impure forall quantified
//! permissions, validate forperm and triggers; return None when consistency messages exist.
//! Field targets also receive NodeTrafo back to the original access; duplicate field targets
//! are diagnosed by field identity even if receivers differ. Preserve operator/type-dependent
//! arithmetic, collections, domain substitutions and extensions.
//!
//! Integration:
//! parser::parse_ast and resolver; ast declarations, expression, statement, utility consistency
//! and quantified permissions; plugin::standard::adt and frontend::sil_frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Agree on signature table and AST identity, metadata, extension translation and consistency
//! message ownership with AST and plugins.
//!
//! Status: partial; primitive/collection types and core expression translation are implemented.
//! Member signatures, remaining statements/expressions and program checks remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::parse_ast::{
    PBinaryOp, PExpHandle, PExpressionKind, PIdnRef, PNodeHandle, PNodeKind, PTypeHandle, PTypeKind,
};
use super::parse_ast_keyword::{PKw, PKwOp, PSymOp};
use crate::ast::ast::{Info, Metadata};
use crate::ast::expression::{Exp, ExpKind, LocalVar};
use crate::ast::position::{LineColumn, LineColumnPosition, Position, SourcePosition};
use crate::ast::r#type::Type;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TranslationError {
    Unsupported(&'static str),
    InvalidType,
    UnresolvedIdentifier(String),
    InvalidPosition,
}

/// Preserve SourcePNodeInfo and lift the original parse span into a SourcePosition.
pub fn metadata(node: &PNodeHandle) -> Result<Metadata, TranslationError> {
    let pos = node.read().expect("poisoned parse node").pos.clone();
    let position = match pos {
        (
            Position::LineColumn(LineColumn::File(start)),
            Position::LineColumn(LineColumn::File(end)),
        ) => Position::LineColumn(LineColumn::Source(Box::new(SourcePosition {
            file: Some(start.file),
            start: Box::new(LineColumn::LineColumn(LineColumnPosition::new(
                start.line,
                start.column,
            ))),
            end: Some(Box::new(LineColumn::LineColumn(LineColumnPosition::new(
                end.line, end.column,
            )))),
        }))),
        (Position::LineColumn(LineColumn::File(_)), _) => {
            return Err(TranslationError::InvalidPosition);
        }
        _ => Position::LineColumn(LineColumn::Source(Box::new(SourcePosition {
            file: None,
            start: Box::new(LineColumn::LineColumn(LineColumnPosition::new(0, 0))),
            end: None,
        }))),
    };
    Ok(Metadata {
        position,
        info: Info::SourcePNode(node.clone()),
        ..Metadata::default()
    })
}
/// Translate primitive and collection types; named domains require the signature table.
pub fn translate_type(typ: &PTypeHandle) -> Result<Type, TranslationError> {
    let kind = match &typ.node().read().expect("poisoned parse node").kind {
        PNodeKind::Type(kind) => kind.clone(),
        _ => return Err(TranslationError::InvalidType),
    };
    Ok(match kind {
        PTypeKind::Primitive { name } => match name.value() {
            PKw::Int => Type::Int,
            PKw::Bool => Type::Bool,
            PKw::Perm | PKw::Rational => Type::Perm,
            PKw::Ref => Type::Ref,
            _ => return Err(TranslationError::InvalidType),
        },
        PTypeKind::Seq { element_type, .. } => {
            Type::Seq(std::sync::Arc::new(translate_type(element_type.inner())?))
        }
        PTypeKind::Set { element_type, .. } => {
            Type::Set(std::sync::Arc::new(translate_type(element_type.inner())?))
        }
        PTypeKind::Multiset { element_type, .. } => {
            Type::Multiset(std::sync::Arc::new(translate_type(element_type.inner())?))
        }
        PTypeKind::Map { types, .. } => Type::map(
            translate_type(types.inner().first())?,
            translate_type(types.inner().second())?,
        ),
        PTypeKind::BoolImpure | PTypeKind::BoolPredicate => Type::Bool,
        PTypeKind::BoolWand => Type::Wand,
        PTypeKind::Domain { .. } => {
            return Err(TranslationError::Unsupported(
                "domain signature translation",
            ));
        }
        _ => return Err(TranslationError::InvalidType),
    })
}
/// Translate supported expressions after name and type analysis; unsupported families fail.
pub fn translate_expression(input: &PExpHandle) -> Result<Exp, TranslationError> {
    translate_expression_with_fields(input, None)
}
fn translate_expression_with_fields(
    input: &PExpHandle,
    fields: Option<&std::collections::HashMap<String, crate::ast::program::Field>>,
) -> Result<Exp, TranslationError> {
    let expression = match &input.node().read().expect("poisoned parse node").kind {
        PNodeKind::Expression(e) => e.clone(),
        _ => return Err(TranslationError::Unsupported("not an expression")),
    };
    let meta = metadata(input.node())?;
    let kind = match expression.kind {
        PExpressionKind::IntLit(value) => ExpKind::IntLit(value),
        PExpressionKind::BoolLit(token) => match token.value() {
            PKw::True => ExpKind::TrueLit,
            PKw::False => ExpKind::FalseLit,
            _ => return Err(TranslationError::InvalidType),
        },
        PExpressionKind::NullLit(_) => ExpKind::NullLit,
        PExpressionKind::ResultLit(_) => ExpKind::Result(translate_type(&expression.typ)?),
        PExpressionKind::NoPerm(_) => ExpKind::NoPerm,
        PExpressionKind::FullPerm(_) => ExpKind::FullPerm,
        PExpressionKind::Wildcard(_) => ExpKind::WildcardPerm,
        PExpressionKind::Epsilon(_) => ExpKind::EpsilonPerm,
        PExpressionKind::IdnUse { idnref } => {
            let refs = PIdnRef::decls(&idnref, |_| true);
            let name = match &idnref.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(r) => r.name.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            if refs.len() != 1
                || !matches!(
                    &refs[0].read().expect("poisoned parse node").kind,
                    PNodeKind::Declaration(super::parse_ast::PDeclaration {
                        kind: super::parse_ast::PDeclarationKind::FormalArg
                            | super::parse_ast::PDeclarationKind::FormalReturn
                            | super::parse_ast::PDeclarationKind::LogicalVar
                            | super::parse_ast::PDeclarationKind::LocalVar,
                        ..
                    })
                )
            {
                return Err(TranslationError::UnresolvedIdentifier(name));
            }
            ExpKind::LocalVar(LocalVar::new(
                name,
                translate_type(&expression.typ)?,
                meta.clone(),
            ))
        }
        PExpressionKind::Extension(extension)
            if extension
                .as_any()
                .is::<crate::plugin::standard::arp::arppast_extension::PRdPerm>() =>
        {
            return Ok(
                crate::plugin::standard::arp::arpast_extension::RdPerm { meta }.expression(),
            );
        }
        PExpressionKind::Extension(extension)
            if extension
                .as_any()
                .is::<crate::plugin::sif::sifp_ast_extensions::PSifExpression>() =>
        {
            let sif = extension
                .as_any()
                .downcast_ref::<crate::plugin::sif::sifp_ast_extensions::PSifExpression>()
                .expect("checked SIF type");
            return sif
                .translate(
                    |_| meta,
                    |exp| translate_expression_with_fields(exp, fields),
                )?
                .map_err(|_| TranslationError::InvalidType);
        }
        PExpressionKind::Extension(extension) => {
            let Some(instance) = extension.as_any().downcast_ref::<crate::plugin::standard::predicateinstance::predicate_instance_past_extension::PPredicateInstance>() else { return Err(TranslationError::Unsupported("expression extension translation")); };
            return instance.translate(
                |_| meta,
                |exp| translate_expression_with_fields(exp, fields),
            );
        }
        PExpressionKind::FieldAccess {
            receiver, idnref, ..
        } => {
            let declarations = PIdnRef::decls(&idnref, |_| true);
            if declarations.len() != 1 {
                return Err(TranslationError::Unsupported("unresolved field"));
            }
            let field_handle =
                super::parse_ast::PDeclarationHandle::from_node(declarations[0].clone())
                    .map_err(|_| TranslationError::Unsupported("field declaration"))?;
            let annotations = field_handle.field_annotations();
            let declaration = match &declarations[0].read().expect("poisoned parse node").kind {
                PNodeKind::Declaration(d)
                    if matches!(d.kind, super::parse_ast::PDeclarationKind::Field { .. }) =>
                {
                    d.clone()
                }
                _ => return Err(TranslationError::Unsupported("field declaration")),
            };
            let name = match &declaration.idndef.read().expect("poisoned parse node").kind {
                PNodeKind::IdnDef(id) => id.name.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            let mut field_meta = metadata(field_handle.node())?;
            field_meta.info = annotation_info(&annotations);
            let field = if let Some(fields) = fields {
                fields
                    .get(&name)
                    .cloned()
                    .ok_or_else(|| TranslationError::UnresolvedIdentifier(name.clone()))?
            } else {
                crate::ast::program::Field::new(crate::ast::program::FieldData {
                    name,
                    typ: translate_type(&declaration.typ)?,
                    meta: field_meta,
                })
            };
            ExpKind::FieldAccess(crate::ast::expression::FieldAccess::new(
                translate_expression_with_fields(&receiver, fields)?,
                field,
                meta.clone(),
            ))
        }
        PExpressionKind::Call {
            idnref, call_args, ..
        } => {
            let declarations = PIdnRef::decls(&idnref, |_| true);
            let name = match &idnref.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(reference) => reference.name.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            if declarations.len() != 1 {
                return Err(TranslationError::UnresolvedIdentifier(name));
            }
            let declaration = declarations[0]
                .read()
                .expect("poisoned parse node")
                .kind
                .clone();
            let args = call_args
                .inner()
                .to_seq()
                .into_iter()
                .map(|e| translate_expression_with_fields(e, fields))
                .collect::<Result<Vec<_>, _>>()?;
            if matches!(
                declaration,
                PNodeKind::DomainMember(super::parse_ast::PDomainMember::Function {
                    interpretation: None,
                    ..
                })
            ) {
                let owner = super::parse_ast::get_ancestor(&declarations[0], |node| {
                    matches!(
                        &node.read().expect("poisoned parse node").kind,
                        PNodeKind::Member(super::parse_ast::PMember {
                            kind: super::parse_ast::PMemberKind::Domain { .. },
                            ..
                        })
                    )
                })
                .ok_or(TranslationError::Unsupported("domain function owner"))?;
                let domain_name = match &owner.read().expect("poisoned parse node").kind {
                    PNodeKind::Member(member) => match &member.kind {
                        super::parse_ast::PMemberKind::Domain {
                            idndef, type_vars, ..
                        } if type_vars.as_ref().is_none_or(|v| v.inner().is_empty()) => {
                            declaration_name(idndef)?
                        }
                        _ => return Err(TranslationError::Unsupported("generic domain function")),
                    },
                    _ => unreachable!(),
                };
                return Ok(Exp::with_extra(
                    ExpKind::DomainFuncApp(name, args, Default::default()),
                    meta,
                    crate::ast::expression::ExpExtra {
                        typ: Some(translate_type(&expression.typ)?),
                        domain_name: Some(domain_name),
                        ..Default::default()
                    },
                ));
            }
            let PNodeKind::Member(member) = declaration else {
                return Err(TranslationError::Unsupported("non-function call"));
            };
            match member.kind {
                super::parse_ast::PMemberKind::Function { .. } => {
                    return Ok(Exp::with_extra(
                        ExpKind::FuncApp(name, args),
                        meta,
                        crate::ast::expression::ExpExtra {
                            typ: Some(translate_type(&expression.typ)?),
                            ..Default::default()
                        },
                    ));
                }
                super::parse_ast::PMemberKind::Predicate { .. } => {
                    let location =
                        crate::ast::expression::PredicateAccess::new(args, name, meta.clone());
                    ExpKind::PredicateAccessPredicate(
                        crate::ast::statement::PredicateAccessPredicate::new(
                            location,
                            None,
                            meta.clone(),
                        ),
                    )
                }
                _ => return Err(TranslationError::Unsupported("non-function call")),
            }
        }
        PExpressionKind::AccPred { amount, .. } => {
            let location = translate_expression_with_fields(amount.inner().first(), fields)?;
            let permission = amount
                .inner()
                .second()
                .map(|(_, e)| translate_expression_with_fields(e, fields))
                .transpose()?;
            match location.kind() {
                ExpKind::FieldAccess(field) => {
                    ExpKind::FieldAccessPredicate(field.clone(), permission)
                }
                ExpKind::PredicateAccessPredicate(pred) => ExpKind::PredicateAccessPredicate(
                    crate::ast::statement::PredicateAccessPredicate::new(
                        pred.location.clone(),
                        permission,
                        meta.clone(),
                    ),
                ),
                ExpKind::PredicateAccess(pred) => ExpKind::PredicateAccessPredicate(
                    crate::ast::statement::PredicateAccessPredicate::new(
                        pred.clone(),
                        permission,
                        meta.clone(),
                    ),
                ),
                _ => return Err(TranslationError::InvalidType),
            }
        }
        PExpressionKind::CurrentPerm { resource, .. } => {
            let resource = translate_expression_with_fields(resource.inner(), fields)?;
            let resource = match resource.kind() {
                ExpKind::PredicateAccessPredicate(pred) => Exp::new(
                    ExpKind::PredicateAccess(pred.location.clone()),
                    pred.location.meta.clone(),
                ),
                ExpKind::FieldAccess(_) | ExpKind::PredicateAccess(_) | ExpKind::MagicWand(..) => {
                    resource
                }
                _ => return Err(TranslationError::InvalidType),
            };
            ExpKind::CurrentPerm(resource)
        }
        PExpressionKind::UnExp { op, exp } => {
            let operand = translate_expression_with_fields(&exp, fields)?;
            match op.value() {
                PSymOp::Not => ExpKind::Not(operand),
                PSymOp::Neg => match operand.typ().map_err(|_| TranslationError::InvalidType)? {
                    Type::Int => ExpKind::Minus(operand),
                    Type::Perm => ExpKind::PermMinus(operand),
                    _ => return Err(TranslationError::InvalidType),
                },
                _ => return Err(TranslationError::Unsupported("unary operator")),
            }
        }
        PExpressionKind::BinExp { left, op, right } => {
            let l = translate_expression_with_fields(&left, fields)?;
            let r = translate_expression_with_fields(&right, fields)?;
            match op.value() {
                PBinaryOp::Symbol(PSymOp::Plus) => {
                    match r.typ().map_err(|_| TranslationError::InvalidType)? {
                        Type::Int => ExpKind::Add(l, r),
                        Type::Perm => ExpKind::PermAdd(l, r),
                        _ => return Err(TranslationError::InvalidType),
                    }
                }
                PBinaryOp::Symbol(PSymOp::Minus) => {
                    match r.typ().map_err(|_| TranslationError::InvalidType)? {
                        Type::Int => ExpKind::Sub(l, r),
                        Type::Perm => ExpKind::PermSub(l, r),
                        _ => return Err(TranslationError::InvalidType),
                    }
                }
                PBinaryOp::Symbol(PSymOp::Mul) => match (
                    l.typ().map_err(|_| TranslationError::InvalidType)?,
                    r.typ().map_err(|_| TranslationError::InvalidType)?,
                ) {
                    (Type::Int, Type::Int) => ExpKind::Mul(l, r),
                    (Type::Int, Type::Perm) => ExpKind::IntPermMul(l, r),
                    (Type::Perm, Type::Int) => ExpKind::IntPermMul(r, l),
                    (Type::Perm, Type::Perm) => ExpKind::PermMul(l, r),
                    _ => return Err(TranslationError::InvalidType),
                },
                PBinaryOp::Symbol(PSymOp::Div) => match (
                    l.typ().map_err(|_| TranslationError::InvalidType)?,
                    r.typ().map_err(|_| TranslationError::InvalidType)?,
                ) {
                    (Type::Perm, Type::Int) => ExpKind::PermDiv(l, r),
                    (Type::Perm, Type::Perm) => ExpKind::PermPermDiv(l, r),
                    (Type::Int, Type::Int) => match translate_type(&expression.typ)? {
                        Type::Int => ExpKind::Div(l, r),
                        Type::Perm => ExpKind::FractionalPerm(l, r),
                        _ => return Err(TranslationError::InvalidType),
                    },
                    _ => return Err(TranslationError::InvalidType),
                },
                PBinaryOp::Symbol(PSymOp::ArithDiv) => ExpKind::Div(l, r),
                PBinaryOp::Symbol(PSymOp::Mod) => ExpKind::Mod(l, r),
                PBinaryOp::Symbol(PSymOp::EqEq | PSymOp::Iff) => ExpKind::EqCmp(l, r),
                PBinaryOp::Symbol(PSymOp::Ne) => ExpKind::NeCmp(l, r),
                PBinaryOp::Symbol(PSymOp::AndAnd) => ExpKind::And(l, r),
                PBinaryOp::Symbol(PSymOp::OrOr) => ExpKind::Or(l, r),
                PBinaryOp::Symbol(PSymOp::Implies) => ExpKind::Implies(l, r),
                PBinaryOp::Symbol(PSymOp::Append) => ExpKind::SeqAppend(l, r),
                PBinaryOp::Keyword(PKwOp::Union) => ExpKind::AnySetUnion(l, r),
                PBinaryOp::Keyword(PKwOp::Intersection) => ExpKind::AnySetIntersection(l, r),
                PBinaryOp::Keyword(PKwOp::Setminus) => ExpKind::AnySetMinus(l, r),
                PBinaryOp::Keyword(PKwOp::Subset) => ExpKind::AnySetSubset(l, r),
                PBinaryOp::Keyword(PKwOp::In) => {
                    match r.typ().map_err(|_| TranslationError::InvalidType)? {
                        Type::Seq(_) => ExpKind::SeqContains(l, r),
                        Type::Map(_) => ExpKind::MapContains(l, r),
                        Type::Set(_) | Type::Multiset(_) => ExpKind::AnySetContains(l, r),
                        _ => return Err(TranslationError::InvalidType),
                    }
                }
                PBinaryOp::Symbol(op @ (PSymOp::Lt | PSymOp::Le | PSymOp::Gt | PSymOp::Ge)) => {
                    match (op, l.typ().map_err(|_| TranslationError::InvalidType)?) {
                        (PSymOp::Lt, Type::Int) => ExpKind::LtCmp(l, r),
                        (PSymOp::Le, Type::Int) => ExpKind::LeCmp(l, r),
                        (PSymOp::Gt, Type::Int) => ExpKind::GtCmp(l, r),
                        (PSymOp::Ge, Type::Int) => ExpKind::GeCmp(l, r),
                        (PSymOp::Lt, Type::Perm) => ExpKind::PermLtCmp(l, r),
                        (PSymOp::Le, Type::Perm) => ExpKind::PermLeCmp(l, r),
                        (PSymOp::Gt, Type::Perm) => ExpKind::PermGtCmp(l, r),
                        (PSymOp::Ge, Type::Perm) => ExpKind::PermGeCmp(l, r),
                        _ => return Err(TranslationError::InvalidType),
                    }
                }
                _ => return Err(TranslationError::Unsupported("binary operator")),
            }
        }
        PExpressionKind::Unfolding { acc, exp, .. } => {
            let access = translate_expression_with_fields(&acc, fields)?;
            if !matches!(access.kind(), ExpKind::PredicateAccessPredicate(_)) {
                return Err(TranslationError::Unsupported("unfolding predicate access"));
            }
            ExpKind::Unfolding(access, translate_expression_with_fields(&exp, fields)?)
        }
        PExpressionKind::Applying { wand, exp, .. } => {
            let wand = translate_expression_with_fields(&wand, fields)?;
            if !matches!(wand.kind(), ExpKind::MagicWand(..)) {
                return Err(TranslationError::Unsupported("applying magic wand"));
            }
            ExpKind::Applying(wand, translate_expression_with_fields(&exp, fields)?)
        }
        PExpressionKind::Asserting { assertion, exp, .. } => ExpKind::Asserting(
            translate_expression_with_fields(&assertion, fields)?,
            translate_expression_with_fields(&exp, fields)?,
        ),
        PExpressionKind::MagicWandExp { left, right, .. } => ExpKind::MagicWand(
            translate_expression_with_fields(&left, fields)?,
            translate_expression_with_fields(&right, fields)?,
        ),
        PExpressionKind::CondExp { cond, thn, els, .. } => ExpKind::CondExp(
            translate_expression_with_fields(&cond, fields)?,
            translate_expression_with_fields(&thn, fields)?,
            translate_expression_with_fields(&els, fields)?,
        ),
        PExpressionKind::InhaleExhale { inhale, exhale, .. } => ExpKind::InhaleExhaleExp(
            translate_expression_with_fields(&inhale, fields)?,
            translate_expression_with_fields(&exhale, fields)?,
        ),
        PExpressionKind::Forall(q) | PExpressionKind::Exists(q) => {
            let forall = matches!(q.keyword.value(), PKw::Forall);
            let vars = q
                .vars
                .to_seq()
                .iter()
                .map(|v| formal_declaration(v))
                .collect::<Result<Vec<_>, _>>()?;
            let mut triggers = Vec::new();
            for trigger in &q.triggers {
                let mut expressions = Vec::new();
                for source in trigger.expressions.inner().to_seq() {
                    let value = translate_expression_with_fields(source, fields)?;
                    expressions.push(match value.kind() {
                        ExpKind::PredicateAccessPredicate(access) => Exp::new(
                            ExpKind::PredicateAccess(access.location.clone()),
                            access.location.meta.clone(),
                        ),
                        _ => value,
                    });
                }
                triggers.push(crate::ast::expression::Trigger::new(
                    expressions,
                    metadata(&trigger.node)?,
                ));
            }
            let body = translate_expression_with_fields(&q.body, fields)?;
            if !forall {
                ExpKind::Exists(vars, triggers, body)
            } else {
                let result = Exp::new(ExpKind::Forall(vars, triggers, body), meta.clone());
                if result.is_pure() {
                    return Ok(result);
                }
                let parts = crate::ast::utility::quantified_permissions::desugar_source_quantified_permission_syntax(&result).map_err(|_| TranslationError::Unsupported("quantified permission desugaring"))?;
                let mut parts = parts.into_iter();
                let mut combined = parts.next().ok_or(TranslationError::Unsupported(
                    "empty quantified permission desugaring",
                ))?;
                for part in parts {
                    combined = Exp::new(ExpKind::And(combined, part), meta.clone());
                }
                return Ok(combined);
            }
        }
        PExpressionKind::RangeSeq { low, high, .. } => ExpKind::RangeSeq(
            translate_expression_with_fields(&low, fields)?,
            translate_expression_with_fields(&high, fields)?,
        ),
        PExpressionKind::OldExp { label, exp, .. } => {
            let inner = translate_expression_with_fields(exp.inner(), fields)?;
            match label {
                None => ExpKind::Old(inner),
                Some(label) => {
                    let name = match label.inner() {
                        super::parse_ast::POldLabel::Lhs(_) => "lhs".into(),
                        super::parse_ast::POldLabel::Label(node) => {
                            match &node.read().expect("poisoned parse node").kind {
                                PNodeKind::IdnRef(reference) => reference.name.clone(),
                                _ => return Err(TranslationError::InvalidType),
                            }
                        }
                    };
                    ExpKind::LabelledOld(inner, name)
                }
            }
        }
        PExpressionKind::Lookup { base, index, .. } => {
            let parse_type = match &base.node().read().expect("poisoned parse node").kind {
                PNodeKind::Expression(e) => e.typ.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            let base = translate_expression_with_fields(&base, fields)?;
            let index = translate_expression_with_fields(&index, fields)?;
            match translate_type(&parse_type)? {
                Type::Seq(_) => ExpKind::SeqIndex(base, index),
                Type::Map(_) => ExpKind::MapLookup(base, index),
                _ => return Err(TranslationError::InvalidType),
            }
        }
        PExpressionKind::Update {
            base, key, value, ..
        } => {
            let parse_type = match &base.node().read().expect("poisoned parse node").kind {
                PNodeKind::Expression(e) => e.typ.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            let base = translate_expression_with_fields(&base, fields)?;
            let key = translate_expression_with_fields(&key, fields)?;
            let value = translate_expression_with_fields(&value, fields)?;
            match translate_type(&parse_type)? {
                Type::Seq(_) => ExpKind::SeqUpdate(base, key, value),
                Type::Map(_) => ExpKind::MapUpdate(base, key, value),
                _ => return Err(TranslationError::InvalidType),
            }
        }
        PExpressionKind::Size { seq, .. } => {
            let parse_type = match &seq.node().read().expect("poisoned parse node").kind {
                PNodeKind::Expression(e) => e.typ.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            let base = translate_expression_with_fields(&seq, fields)?;
            match translate_type(&parse_type)? {
                Type::Seq(_) => ExpKind::SeqLength(base),
                Type::Map(_) => ExpKind::MapCardinality(base),
                Type::Set(_) | Type::Multiset(_) => ExpKind::AnySetCardinality(base),
                _ => return Err(TranslationError::InvalidType),
            }
        }
        PExpressionKind::SeqSlice {
            seq, start, end, ..
        } => {
            let mut base = translate_expression_with_fields(&seq, fields)?;
            if let Some(end) = end {
                base = Exp::new(
                    ExpKind::SeqTake(base, translate_expression_with_fields(&end, fields)?),
                    meta.clone(),
                );
            }
            if let Some(start) = start {
                base = Exp::new(
                    ExpKind::SeqDrop(base, translate_expression_with_fields(&start, fields)?),
                    meta,
                );
            }
            return Ok(base);
        }
        _ => return Err(TranslationError::Unsupported("expression translation")),
    };
    Ok(Exp::new(kind, meta))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::fast_parser::{parse_expression, parse_type};
    #[test]
    fn translates_nested_types_and_retains_source_expression_info() {
        let typ = parse_type("Map[Int, Seq[Bool]]", "test.vpr").unwrap().typ;
        assert_eq!(
            translate_type(&typ).unwrap(),
            Type::map(Type::Int, Type::Seq(std::sync::Arc::new(Type::Bool)))
        );
        let parsed = parse_expression("1 + 2 * 3", "test.vpr")
            .unwrap()
            .expression;
        let translated = translate_expression(&parsed).unwrap();
        assert!(matches!(translated.kind(), ExpKind::Add(_, _)));
        assert!(matches!(translated.0.meta.info, Info::SourcePNode(_)));
    }
}

/// Source methodCallAssign saves field receivers before the operation and
/// writes field targets afterward, using one pair of scoped temporaries each.
fn lower_call_targets(
    targets: &[&PExpHandle],
    fields: Option<&std::collections::HashMap<String, crate::ast::program::Field>>,
    operation: impl FnOnce(Vec<LocalVar>) -> crate::ast::statement::Stmt,
) -> Result<crate::ast::statement::Stmt, TranslationError> {
    use crate::ast::ast::{ErrorTrafo, PreviousNode};
    use crate::ast::expression::FieldAccess;
    use crate::ast::program::{Declaration, LocalVarDecl};
    use crate::ast::statement::{Stmt, StmtKind};
    use crate::ast::utility::nodes::Node;
    use std::sync::Arc;
    let mut locals = Vec::new();
    let mut before = Vec::new();
    let mut after = Vec::new();
    let mut declarations = Vec::new();
    let mut target_fields: Vec<crate::ast::program::Field> = Vec::new();
    for (i, target) in targets.iter().enumerate() {
        let value = translate_expression_with_fields(target, fields)?;
        match value.kind() {
            ExpKind::LocalVar(local) => locals.push(local.clone()),
            ExpKind::FieldAccess(field) => {
                if target_fields.contains(&field.field) {
                    return Err(TranslationError::Unsupported(
                        "multiple call targets access the same field",
                    ));
                }
                target_fields.push(field.field.clone());
                let receiver_type = field
                    .receiver
                    .typ()
                    .map_err(|_| TranslationError::InvalidType)?;
                let receiver_decl =
                    LocalVarDecl::new(format!("_receiver{i}"), receiver_type, Metadata::default());
                let target_decl = LocalVarDecl::new(
                    format!("_target{i}"),
                    field.field.typ.clone(),
                    Metadata::default(),
                );
                let receiver_meta = Metadata {
                    position: field.receiver.metadata().position.clone(),
                    ..Default::default()
                };
                let receiver = LocalVar::new(
                    receiver_decl.name.clone(),
                    receiver_decl.typ.clone(),
                    receiver_meta.clone(),
                );
                let target_meta = Metadata {
                    position: field.meta.position.clone(),
                    ..Default::default()
                };
                let temporary = LocalVar::new(
                    target_decl.name.clone(),
                    target_decl.typ.clone(),
                    target_meta,
                );
                before.push(Stmt::new(
                    StmtKind::LocalVarAssign {
                        lhs: receiver.clone(),
                        rhs: field.receiver.clone(),
                    },
                    receiver_meta,
                ));
                let backlink = ErrorTrafo::trafos(
                    vec![],
                    vec![],
                    Some(Arc::new(PreviousNode(Node::FieldAccess(field.clone())))),
                );
                let field_meta = Metadata {
                    error_trafo: backlink.combine(&field.meta.error_trafo),
                    ..field.meta.clone()
                };
                let receiver_exp =
                    Exp::new(ExpKind::LocalVar(receiver.clone()), receiver.meta.clone());
                let location = FieldAccess::new(receiver_exp, field.field.clone(), field_meta);
                let rhs = Exp::new(ExpKind::LocalVar(temporary.clone()), temporary.meta.clone());
                after.push(Stmt::new(
                    StmtKind::FieldAssign { lhs: location, rhs },
                    Metadata {
                        position: field.meta.position.clone(),
                        ..Default::default()
                    },
                ));
                declarations.push(Declaration::Local(receiver_decl));
                declarations.push(Declaration::Local(target_decl));
                locals.push(temporary);
            }
            _ => {
                return Err(TranslationError::Unsupported(
                    "invalid call assignment target",
                ));
            }
        }
    }
    let operation = operation(locals);
    if declarations.is_empty() {
        return Ok(operation);
    }
    let meta = Metadata {
        position: operation.metadata().position.clone(),
        info: operation.metadata().info.clone(),
        ..Default::default()
    };
    before.push(operation);
    before.extend(after);
    Ok(Stmt::new(
        StmtKind::Seqn {
            statements: before,
            declarations,
        },
        meta,
    ))
}

/// Translate supported statements; unsupported call and plugin forms return errors.
pub fn translate_statement(
    input: &super::parse_ast::PStmtHandle,
) -> Result<crate::ast::statement::Stmt, TranslationError> {
    translate_statement_with_fields(input, None, None)
}
fn translate_statement_with_fields(
    input: &super::parse_ast::PStmtHandle,
    fields: Option<&std::collections::HashMap<String, crate::ast::program::Field>>,
    field_order: Option<&[crate::ast::program::Field]>,
) -> Result<crate::ast::statement::Stmt, TranslationError> {
    use super::parse_ast::PStatementKind;
    use crate::ast::program::{Declaration, LocalVarDecl};
    use crate::ast::statement::{Stmt, StmtKind};
    let statement = match &input.node().read().expect("poisoned parse node").kind {
        PNodeKind::Statement(statement) => statement.clone(),
        _ => return Err(TranslationError::Unsupported("statement node")),
    };
    let meta = metadata(input.node())?;
    if let PStatementKind::Assign { targets, rhs, .. } = &statement.kind {
        let rhs_kind = match &rhs.node().read().expect("poisoned parse node").kind {
            PNodeKind::Expression(e) => e.kind.clone(),
            _ => return Err(TranslationError::InvalidType),
        };
        if let PExpressionKind::NewExp {
            fields: selected, ..
        } = rhs_kind
        {
            if targets.len() != 1 {
                return Err(TranslationError::Unsupported(
                    "allocation requires one target",
                ));
            }
            let declared_fields = match selected.inner() {
                super::parse_ast::PNewFields::All(_) => field_order
                    .ok_or(TranslationError::Unsupported(
                        "allocation requires ordered program fields",
                    ))?
                    .to_vec(),
                super::parse_ast::PNewFields::Fields(references) => {
                    let lookup = fields.ok_or(TranslationError::Unsupported(
                        "allocation requires program fields",
                    ))?;
                    let mut selected = Vec::new();
                    for reference in references.to_seq() {
                        let name = match &reference.read().expect("poisoned parse node").kind {
                            PNodeKind::IdnRef(id) => id.name.clone(),
                            _ => return Err(TranslationError::InvalidType),
                        };
                        selected.push(
                            lookup
                                .get(&name)
                                .cloned()
                                .ok_or(TranslationError::UnresolvedIdentifier(name))?,
                        );
                    }
                    selected
                }
            };
            let target_nodes = targets.to_seq();
            return lower_call_targets(&target_nodes, fields, |mut targets| {
                Stmt::new(
                    StmtKind::NewStmt {
                        lhs: targets.remove(0),
                        fields: declared_fields,
                    },
                    meta.clone(),
                )
            });
        }
        let call = match &rhs.node().read().expect("poisoned parse node").kind {
            PNodeKind::Expression(e) => match &e.kind {
                PExpressionKind::Call {
                    idnref,
                    call_args,
                    type_annotated: None,
                    ..
                } => Some((idnref.clone(), call_args.clone())),
                _ => None,
            },
            _ => None,
        };
        if let Some((reference, call_args)) = call {
            let candidates = PIdnRef::decls(&reference, |_| true);
            if candidates.len() == 1
                && matches!(
                    &candidates[0].read().expect("poisoned parse node").kind,
                    PNodeKind::Member(super::parse_ast::PMember {
                        kind: super::parse_ast::PMemberKind::Method { .. },
                        ..
                    })
                )
            {
                let name = match &reference.read().expect("poisoned parse node").kind {
                    PNodeKind::IdnRef(id) => id.name.clone(),
                    _ => return Err(TranslationError::InvalidType),
                };
                let args = call_args
                    .inner()
                    .to_seq()
                    .into_iter()
                    .map(|exp| translate_expression_with_fields(exp, fields))
                    .collect::<Result<Vec<_>, _>>()?;
                let target_nodes = targets.to_seq();
                return lower_call_targets(&target_nodes, fields, |targets| {
                    Stmt::new(
                        StmtKind::MethodCall {
                            method_name: name,
                            args,
                            targets,
                        },
                        meta.clone(),
                    )
                });
            }
        }
    }
    let kind = match statement.kind {
        PStatementKind::Extension(extension) => {
            if let Some(refute) = extension
                .as_any()
                .downcast_ref::<crate::plugin::standard::refute::refute_past_extension::PRefute>(
            ) {
                return Ok(
                    crate::plugin::standard::refute::refute_ast_extension::Refute::new(
                        translate_expression_with_fields(&refute.expression, fields)?,
                        meta,
                    )
                    .statement(),
                );
            }
            if extension
                .as_any()
                .is::<crate::plugin::standard::smoke::unreachable_past_extension::PUnreachable>()
            {
                return Ok(
                    crate::plugin::standard::smoke::unreachable_ast_extension::Unreachable { meta }
                        .statement(),
                );
            }
            return extension.translate_statement(
                &mut |body| translate_statement_with_fields(body, fields, field_order),
                meta,
            );
        }
        ref kind @ (PStatementKind::PackageWand { ref exp, .. }
        | PStatementKind::ApplyWand { ref exp, .. }) => {
            let wand = translate_expression_with_fields(exp, fields)?;
            if !matches!(wand.kind(), ExpKind::MagicWand(..)) {
                return Err(TranslationError::Unsupported("expected magic wand"));
            }
            match kind {
                PStatementKind::PackageWand { proof_script, .. } => {
                    let proof = match proof_script {
                        Some(body) => translate_statement_with_fields(body, fields, field_order)?,
                        None => crate::ast::utility::statements::empty_stmt(),
                    };
                    if !matches!(proof.kind(), StmtKind::Seqn { .. }) {
                        return Err(TranslationError::Unsupported("package proof block"));
                    }
                    StmtKind::Package {
                        wand,
                        proof_script: proof,
                    }
                }
                _ => StmtKind::Apply(wand),
            }
        }
        ref kind @ (PStatementKind::Fold { ref exp, .. }
        | PStatementKind::Unfold { ref exp, .. }) => {
            let fold = matches!(kind, PStatementKind::Fold { .. });
            let access = translate_expression_with_fields(&exp, fields)?;
            let ExpKind::PredicateAccessPredicate(access) = access.kind() else {
                return Err(TranslationError::Unsupported(
                    "fold/unfold predicate access",
                ));
            };
            if fold {
                StmtKind::Fold(access.clone())
            } else {
                StmtKind::Unfold(access.clone())
            }
        }
        PStatementKind::Assert { exp, .. } => {
            StmtKind::Assert(translate_expression_with_fields(&exp, fields)?)
        }
        PStatementKind::Assume { exp, .. } => {
            StmtKind::Assume(translate_expression_with_fields(&exp, fields)?)
        }
        PStatementKind::Inhale { exp, .. } => {
            StmtKind::Inhale(translate_expression_with_fields(&exp, fields)?)
        }
        PStatementKind::Exhale { exp, .. } => {
            StmtKind::Exhale(translate_expression_with_fields(&exp, fields)?)
        }
        PStatementKind::Assign { targets, op, rhs } => {
            if op.is_none() || targets.len() != 1 {
                return Err(TranslationError::Unsupported(
                    "method call or multi-target assignment",
                ));
            }
            let target = targets.head();
            let target_kind = match &target.node().read().expect("poisoned parse node").kind {
                PNodeKind::Expression(expression) => expression.kind.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            if let PExpressionKind::IdnUse { idnref } = target_kind {
                let decls = PIdnRef::decls(&idnref, |_| true);
                if decls.len() != 1
                    || !matches!(
                        &decls[0].read().expect("poisoned parse node").kind,
                        PNodeKind::Declaration(super::parse_ast::PDeclaration {
                            kind: super::parse_ast::PDeclarationKind::FormalReturn
                                | super::parse_ast::PDeclarationKind::LocalVar,
                            ..
                        })
                    )
                {
                    return Err(TranslationError::InvalidType);
                }
            }
            let translated = translate_expression_with_fields(target, fields)?;
            match translated.kind() {
                ExpKind::LocalVar(local) => {
                    let mut local_meta = meta.clone();
                    local_meta.info = Info::SourcePNode(target.node().clone());
                    StmtKind::LocalVarAssign {
                        lhs: LocalVar::new(local.name.clone(), local.typ.clone(), local_meta),
                        rhs: translate_expression_with_fields(&rhs, fields)?,
                    }
                }
                ExpKind::FieldAccess(field) => StmtKind::FieldAssign {
                    lhs: field.clone(),
                    rhs: translate_expression_with_fields(&rhs, fields)?,
                },
                _ => return Err(TranslationError::Unsupported("assignment target")),
            }
        }
        PStatementKind::Vars { init: Some(_), .. } => {
            let generated = input
                .vars_assign()
                .map_err(TranslationError::Unsupported)?
                .ok_or(TranslationError::Unsupported(
                    "missing generated initializer",
                ))?;
            return translate_statement_with_fields(&generated, fields, field_order);
        }
        PStatementKind::Vars { init: None, .. } => {
            return Ok(crate::ast::utility::statements::empty_stmt());
        }
        PStatementKind::Seqn { statements, .. } => {
            let mut result = Vec::new();
            let mut declarations = Vec::new();
            for statement in statements.inner().to_seq() {
                let kind = match &statement.node().read().expect("poisoned parse node").kind {
                    PNodeKind::Statement(statement) => statement.kind.clone(),
                    _ => return Err(TranslationError::Unsupported("block member")),
                };
                if let PStatementKind::Vars { vars, .. } = &kind {
                    for var in vars.to_seq() {
                        let declaration =
                            match &var.node().read().expect("poisoned parse node").kind {
                                PNodeKind::Declaration(d) => d.clone(),
                                _ => return Err(TranslationError::InvalidType),
                            };
                        let name =
                            match &declaration.idndef.read().expect("poisoned parse node").kind {
                                PNodeKind::IdnDef(id) => id.name.clone(),
                                _ => return Err(TranslationError::InvalidType),
                            };
                        let mut decl_meta = metadata(statement.node())?;
                        decl_meta.info = Info::SourcePNode(var.node().clone());
                        declarations.push(Declaration::Local(LocalVarDecl::new(
                            name,
                            translate_type(&declaration.typ)?,
                            decl_meta,
                        )));
                    }
                }
                if !matches!(kind, PStatementKind::Skip) {
                    result.push(translate_statement_with_fields(
                        statement,
                        fields,
                        field_order,
                    )?);
                }
            }
            StmtKind::Seqn {
                statements: result,
                declarations,
            }
        }
        PStatementKind::If { cond, thn, els, .. } => {
            let then_branch = translate_statement_with_fields(&thn, fields, field_order)?;
            let else_branch = match els {
                Some(s) => {
                    let translated = translate_statement_with_fields(&s, fields, field_order)?;
                    if matches!(translated.kind(), StmtKind::Seqn { .. }) {
                        translated
                    } else {
                        Stmt::new(
                            StmtKind::Seqn {
                                statements: vec![translated.clone()],
                                declarations: Vec::new(),
                            },
                            translated.metadata().clone(),
                        )
                    }
                }
                None => crate::ast::utility::statements::empty_stmt(),
            };
            StmtKind::If {
                condition: translate_expression_with_fields(cond.inner(), fields)?,
                then_branch,
                else_branch,
            }
        }
        PStatementKind::Else { els, .. } => {
            return translate_statement_with_fields(&els, fields, field_order);
        }
        PStatementKind::While {
            cond, invs, body, ..
        } => StmtKind::While {
            condition: translate_expression_with_fields(cond.inner(), fields)?,
            invariants: invs
                .specs
                .to_seq()
                .into_iter()
                .map(|spec| translate_expression_with_fields(&spec.exp, fields))
                .collect::<Result<_, _>>()?,
            body: translate_statement_with_fields(&body, fields, field_order)?,
        },
        PStatementKind::Label { idndef, invs, .. } => {
            let name = match &idndef.read().expect("poisoned parse node").kind {
                PNodeKind::IdnDef(id) => id.name.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            StmtKind::Label(crate::ast::program::LabelDeclaration::new(
                crate::ast::program::LabelDeclarationData {
                    name,
                    invariants: invs
                        .to_seq()
                        .into_iter()
                        .map(|spec| translate_expression_with_fields(&spec.exp, fields))
                        .collect::<Result<_, _>>()?,
                    meta: meta.clone(),
                },
            ))
        }
        PStatementKind::Goto { target, .. } => {
            let name = match &target.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(id) => id.name.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            StmtKind::Goto(name)
        }
        _ => return Err(TranslationError::Unsupported("statement translation")),
    };
    Ok(Stmt::new(kind, meta))
}

#[cfg(test)]
mod assignment_validation_tests {
    use super::*;
    use crate::parser::{
        fast_parser::parse_program,
        parse_ast::{PStatementKind, PStmtHandle, subnodes},
        resolver::NameAnalyser,
    };
    fn find_assignment(n: &PNodeHandle) -> Option<PStmtHandle> {
        if matches!(&n.read().unwrap().kind, PNodeKind::Statement(s) if matches!(s.kind,PStatementKind::Assign {..}))
        {
            return PStmtHandle::from_node(n.clone()).ok();
        }
        for child in subnodes(n).unwrap() {
            if let Some(found) = find_assignment(&child) {
                return Some(found);
            }
        }
        None
    }
    #[test]
    fn formal_argument_cannot_be_assignment_target() {
        let program = parse_program("method m(x: Int) { x := 1 }", "test.vpr").unwrap();
        assert!(NameAnalyser::default().run(program.node()).unwrap());
        let assignment = find_assignment(program.node()).unwrap();
        assert!(matches!(
            translate_statement(&assignment),
            Err(TranslationError::InvalidType)
        ));
    }
}

fn annotation_info(annotations: &[super::parse_ast::PAnnotation]) -> Info {
    if annotations.is_empty() {
        return Info::NoInfo;
    }
    let mut values: std::collections::HashMap<String, Vec<String>> =
        std::collections::HashMap::new();
    for annotation in annotations {
        let entry = values
            .entry(annotation.key().text().to_owned())
            .or_default();
        entry.extend(
            annotation
                .values()
                .inner()
                .to_seq()
                .into_iter()
                .map(|value| value.grouped().inner().text().to_owned()),
        );
    }
    Info::Annotation(values)
}
fn declaration_name(id: &PNodeHandle) -> Result<String, TranslationError> {
    match &id.read().expect("poisoned parse node").kind {
        PNodeKind::IdnDef(def) => Ok(def.name.clone()),
        _ => Err(TranslationError::Unsupported("declaration name")),
    }
}
fn formal_declaration(
    handle: &super::parse_ast::PDeclarationHandle,
) -> Result<crate::ast::program::LocalVarDecl, TranslationError> {
    let declaration = match &handle.node().read().expect("poisoned parse node").kind {
        PNodeKind::Declaration(d) => d.clone(),
        _ => return Err(TranslationError::InvalidType),
    };
    let mut meta = metadata(&declaration.idndef)?;
    meta.info = Info::SourcePNode(handle.node().clone());
    Ok(crate::ast::program::LocalVarDecl::new(
        declaration_name(&declaration.idndef)?,
        translate_type(&declaration.typ)?,
        meta,
    ))
}
fn formal_declarations(
    args: &super::parse_ast::PFormalArgs,
) -> Result<Vec<crate::ast::program::LocalVarDecl>, TranslationError> {
    args.inner()
        .to_seq()
        .into_iter()
        .map(formal_declaration)
        .collect()
}
fn specification_expressions(
    specs: &super::parse_ast::PSpecs,
    fields: &std::collections::HashMap<String, crate::ast::program::Field>,
) -> Result<Vec<Exp>, TranslationError> {
    specs
        .specs()
        .to_seq()
        .into_iter()
        .map(|spec| translate_expression_with_fields(spec.exp(), Some(fields)))
        .collect()
}
/// Translate the supported core program after successful name and type analysis. Unsupported
/// members or impure-assume rewrites fail explicitly; no verifier result is synthesized here.
pub fn translate_program_core(
    input: &super::parse_ast::PProgramHandle,
) -> Result<crate::ast::program::Program, TranslationError> {
    use super::parse_ast::{PMemberKind, PStatementKind};
    use crate::ast::program::{
        AnyLocalVarDecl, Domain, DomainAxiom, DomainAxiomKind, DomainData, DomainFunc,
        DomainFuncData, Field, FieldData, Function, FunctionData, Method, MethodData, Predicate,
        PredicateData, Program,
    };
    fn contains_assume(node: &PNodeHandle) -> Result<bool, TranslationError> {
        let kind = node.read().expect("poisoned parse node").kind.clone();
        if matches!(
            kind,
            PNodeKind::Statement(super::parse_ast::PStatement {
                kind: PStatementKind::Assume { .. }
            })
        ) {
            return Ok(true);
        }
        for child in super::parse_ast::subnodes(node)
            .map_err(|_| TranslationError::Unsupported("parse node traversal"))?
        {
            if contains_assume(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    let mut fields = Vec::new();
    let mut field_map = std::collections::HashMap::new();
    for handle in input.all_members() {
        let member = match &handle.node().read().expect("poisoned parse node").kind {
            PNodeKind::Member(member) => member.clone(),
            _ => return Err(TranslationError::Unsupported("program member")),
        };
        if let PMemberKind::Fields {
            fields: declarations,
            ..
        } = &member.kind
        {
            for field in declarations.to_seq() {
                let declaration = match &field.node().read().expect("poisoned parse node").kind {
                    PNodeKind::Declaration(d) => d.clone(),
                    _ => return Err(TranslationError::InvalidType),
                };
                let mut field_meta = metadata(field.node())?;
                field_meta.info = annotation_info(member.annotations());
                let field = Field::new(FieldData {
                    name: declaration_name(&declaration.idndef)?,
                    typ: translate_type(&declaration.typ)?,
                    meta: field_meta,
                });
                field_map.insert(field.name.clone(), field.clone());
                fields.push(field);
            }
        }
    }
    let mut domains = Vec::new();
    let mut functions = Vec::new();
    let mut predicates = Vec::new();
    let mut methods = Vec::new();
    for handle in input.all_members() {
        let member = match &handle.node().read().expect("poisoned parse node").kind {
            PNodeKind::Member(member) => member.clone(),
            _ => return Err(TranslationError::Unsupported("program member")),
        };
        let mut member_meta = metadata(handle.node())?;
        member_meta.info = annotation_info(member.annotations());
        match member.kind {
            PMemberKind::Fields { .. } => {}
            PMemberKind::Domain {
                idndef,
                type_vars,
                interpretations,
                members,
                ..
            } if type_vars.as_ref().is_none_or(|v| v.inner().is_empty())
                && interpretations.is_none()
                && members.inner().to_seq().iter().all(|m| {
                    matches!(
                        &m.node().read().expect("poisoned parse node").kind,
                        PNodeKind::DomainMember(
                            super::parse_ast::PDomainMember::Axiom { .. }
                                | super::parse_ast::PDomainMember::Function {
                                    interpretation: None,
                                    ..
                                }
                        )
                    )
                }) =>
            {
                let domain_name = declaration_name(&idndef)?;
                let mut axioms = Vec::new();
                let mut domain_functions = Vec::new();
                for axiom in members.inner().to_seq() {
                    let kind = axiom
                        .node()
                        .read()
                        .expect("poisoned parse node")
                        .kind
                        .clone();
                    if let PNodeKind::DomainMember(super::parse_ast::PDomainMember::Function {
                        annotations,
                        unique,
                        idndef,
                        args,
                        result_type,
                        ..
                    }) = kind
                    {
                        let mut formal_args = Vec::new();
                        for arg in args.inner().to_seq() {
                            let typ = translate_type(arg.typ())?;
                            let mut meta = metadata(arg.node())?;
                            meta.info = Info::SourcePNode(arg.node().clone());
                            formal_args.push(if let Some(name) = arg.name() {
                                AnyLocalVarDecl::Named(crate::ast::program::LocalVarDecl::new(
                                    declaration_name(name)?,
                                    typ,
                                    meta,
                                ))
                            } else {
                                AnyLocalVarDecl::Unnamed(
                                    crate::ast::program::UnnamedLocalVarDecl::new(
                                        crate::ast::program::UnnamedLocalVarDeclData { typ, meta },
                                    ),
                                )
                            });
                        }
                        let mut meta = metadata(axiom.node())?;
                        meta.info = annotation_info(&annotations);
                        domain_functions.push(DomainFunc::new(DomainFuncData {
                            name: declaration_name(&idndef)?,
                            formal_args,
                            typ: translate_type(&result_type)?,
                            unique: unique.is_some(),
                            interpretation: None,
                            domain_name: domain_name.clone(),
                            meta,
                        }));
                        continue;
                    }
                    let (annotations, idndef, exp) =
                        match &axiom.node().read().expect("poisoned parse node").kind {
                            PNodeKind::DomainMember(super::parse_ast::PDomainMember::Axiom {
                                annotations,
                                idndef,
                                exp,
                                ..
                            }) => (annotations.clone(), idndef.clone(), exp.clone()),
                            _ => unreachable!(),
                        };
                    let mut meta = metadata(axiom.node())?;
                    meta.info = annotation_info(&annotations);
                    let exp =
                        translate_expression_with_fields(exp.exp().inner(), Some(&field_map))?;
                    axioms.push(DomainAxiom::new(if let Some(id) = idndef {
                        DomainAxiomKind::Named {
                            name: declaration_name(&id)?,
                            exp,
                            domain_name: domain_name.clone(),
                            meta,
                        }
                    } else {
                        DomainAxiomKind::Anonymous {
                            exp,
                            domain_name: domain_name.clone(),
                            meta,
                        }
                    }));
                }
                domains.push(Domain::new(DomainData {
                    name: domain_name,
                    functions: domain_functions,
                    axioms,
                    type_vars: vec![],
                    interpretations: None,
                    meta: member_meta,
                }));
            }
            PMemberKind::Function {
                idndef,
                args,
                result_type,
                pres,
                posts,
                body,
                ..
            } => functions.push(Function::new(FunctionData {
                name: declaration_name(&idndef)?,
                formal_args: formal_declarations(&args)?,
                typ: translate_type(&result_type)?,
                pres: specification_expressions(&pres, &field_map)?,
                posts: specification_expressions(&posts, &field_map)?,
                body: body
                    .map(|body| {
                        translate_expression_with_fields(body.exp().inner(), Some(&field_map))
                    })
                    .transpose()?,
                meta: member_meta,
            })),
            PMemberKind::Predicate {
                idndef, args, body, ..
            } => predicates.push(Predicate::new(PredicateData {
                name: declaration_name(&idndef)?,
                formal_args: formal_declarations(&args)?,
                body: body
                    .map(|body| {
                        translate_expression_with_fields(body.exp().inner(), Some(&field_map))
                    })
                    .transpose()?,
                meta: member_meta,
            })),
            PMemberKind::Method {
                idndef,
                args,
                returns,
                pres,
                posts,
                body,
                ..
            } => {
                if let Some(body) = &body {
                    if contains_assume(body.node())? {
                        return Err(TranslationError::Unsupported(
                            "impure assume program rewrite",
                        ));
                    }
                }
                methods.push(Method::new(MethodData {
                    name: declaration_name(&idndef)?,
                    formal_args: formal_declarations(&args)?,
                    formal_returns: returns
                        .map(|r| formal_declarations(r.formal_returns()))
                        .transpose()?
                        .unwrap_or_default(),
                    pres: specification_expressions(&pres, &field_map)?,
                    posts: specification_expressions(&posts, &field_map)?,
                    body: body
                        .map(|body| {
                            translate_statement_with_fields(&body, Some(&field_map), Some(&fields))
                        })
                        .transpose()?,
                    meta: member_meta,
                }));
            }
            PMemberKind::Import { .. } => {}
            _ => {
                return Err(TranslationError::Unsupported(
                    "domain, macro or extension member",
                ));
            }
        }
    }
    let mut meta = metadata(input.node())?;
    meta.info = Info::NoInfo;
    Ok(Program::new(
        domains,
        fields,
        functions,
        predicates,
        methods,
        Vec::new(),
        meta,
    ))
}

#[cfg(test)]
mod program_tests {
    use super::*;
    use crate::parser::fast_parser::parse_program;
    use crate::parser::resolver::{NameAnalyser, check_program_core};
    #[test]
    fn method_calls_translate_multiple_assignable_targets() {
        let source = "method m(x: Int) returns (a: Int, b: Int) method caller() { var x: Int; var y: Int; x, y := m(1); }";
        let parsed = parse_program(source, "test.vpr").unwrap();
        super::super::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        let crate::ast::statement::StmtKind::Seqn { statements, .. } =
            program.methods[1].body.as_ref().unwrap().kind()
        else {
            panic!("caller")
        };
        assert!(
            matches!(statements.last().unwrap().kind(), crate::ast::statement::StmtKind::MethodCall { method_name, args, targets } if method_name == "m" && args.len() == 1 && targets.len() == 2)
        );
    }
    #[test]
    fn sif_low_and_rel_are_parsed_checked_and_translated() {
        use crate::parser::fast_parser::{ParserFeature, parse_program_with_features};
        let parsed = parse_program_with_features(
            "function f(): Bool { low(1) } function g(): Int { rel(1, 0) } function h(): Bool { lowEvent }",
            "test.vpr",
            &[ParserFeature::Sif],
        )
        .unwrap();
        super::super::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        assert!(
            matches!(program.functions[0].body.as_ref().unwrap().kind(), ExpKind::Extension(h) if h.0.as_any().is::<crate::plugin::sif::sif_ast_extensions::SifExpression>())
        );
        let invalid = parse_program_with_features(
            "function f(): Int { rel(1, 2) }",
            "test.vpr",
            &[ParserFeature::Sif],
        )
        .unwrap();
        super::super::parse_ast::init_properties(invalid.node()).unwrap();
        assert!(NameAnalyser::default().run(invalid.node()).unwrap());
        assert!(check_program_core(&invalid, &mut |_, _| {}).is_err());
    }
    #[test]
    fn non_generic_domain_function_call_translates_with_owner() {
        let parsed = parse_program(
            "domain D { function f(Int): Int axiom A { f(1) == 1 } } function g(): Int { f(1) }",
            "test.vpr",
        )
        .unwrap();
        super::super::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        let body = program.functions[0].body.as_ref().unwrap();
        assert!(
            matches!(body.kind(), ExpKind::DomainFuncApp(name, args, types) if name == "f" && args.len() == 1 && types.is_empty())
        );
        assert_eq!(body.0.extra.domain_name.as_deref(), Some("D"));
    }
    #[test]
    fn domain_functions_preserve_named_and_unnamed_arguments() {
        use crate::ast::program::AnyLocalVarDecl;
        let parsed = parse_program(
            "domain D { function f(x: Int, Bool): Ref axiom { true } }",
            "test.vpr",
        )
        .unwrap();
        super::super::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        let function = &program.domains[0].functions[0];
        assert_eq!(function.name, "f");
        assert!(matches!(&function.formal_args[0], AnyLocalVarDecl::Named(d) if d.name == "x"));
        assert!(matches!(
            &function.formal_args[1],
            AnyLocalVarDecl::Unnamed(_)
        ));
        assert_eq!(program.domains[0].axioms.len(), 1);
    }
    #[test]
    fn domain_axioms_are_checked_and_translated_in_order() {
        use crate::ast::program::DomainAxiomKind;
        let parsed =
            parse_program("domain D { axiom A { 1 < 2 } axiom { true } }", "test.vpr").unwrap();
        super::super::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        assert!(
            matches!(program.domains[0].axioms[0].kind(), DomainAxiomKind::Named { name, .. } if name == "A")
        );
        assert!(matches!(
            program.domains[0].axioms[1].kind(),
            DomainAxiomKind::Anonymous { .. }
        ));
    }
    #[test]
    fn predicate_instance_expression_keeps_predicate_reference() {
        use crate::parser::fast_parser::{ParserFeature, parse_program_with_features};
        let parsed = parse_program_with_features(
            "predicate p() function f(): Bool { #p() == #p() }",
            "test.vpr",
            &[ParserFeature::PredicateInstance],
        )
        .unwrap();
        super::super::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        assert!(
            matches!(program.functions[0].body.as_ref().unwrap().kind(), ExpKind::EqCmp(left, _) if matches!(left.kind(), ExpKind::Extension(extension) if extension.0.as_any().is::<crate::plugin::standard::predicateinstance::predicate_instance_ast_extension::PredicateInstance>()))
        );
    }
    #[test]
    fn field_assignments_reuse_program_field_identity() {
        use crate::ast::statement::StmtKind;
        let parsed =
            parse_program("method m(x: Ref) { x.f := 1; } field f: Int", "test.vpr").unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translate_program_core(&parsed).unwrap();
        let StmtKind::Seqn { statements, .. } = program.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!("body")
        };
        let StmtKind::FieldAssign { lhs, .. } = statements[0].kind() else {
            panic!("assignment")
        };
        assert!(lhs.field.same_node(&program.fields[0]));
    }
    #[test]
    fn core_program_pipeline_preserves_methods_and_functions() {
        let source = "function f(x: Int): Int { x + 1 } method m(y: Int) { var z: Int := f(y); assert z > 0; }";
        let parsed = parse_program(source, "test.vpr").unwrap();
        assert!(NameAnalyser::default().run(parsed.node()).unwrap());
        check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let translated = translate_program_core(&parsed).unwrap();
        assert_eq!(translated.functions.len(), 1);
        assert_eq!(translated.methods.len(), 1);
        assert!(translated.methods[0].body.is_some());
    }
}
