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
            Type::Seq(Box::new(translate_type(element_type.inner())?))
        }
        PTypeKind::Set { element_type, .. } => {
            Type::Set(Box::new(translate_type(element_type.inner())?))
        }
        PTypeKind::Multiset { element_type, .. } => {
            Type::Multiset(Box::new(translate_type(element_type.inner())?))
        }
        PTypeKind::Map { types, .. } => Type::Map(
            Box::new(translate_type(types.inner().first())?),
            Box::new(translate_type(types.inner().second())?),
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
        PExpressionKind::UnExp { op, exp } => {
            let operand = translate_expression(&exp)?;
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
            let l = translate_expression(&left)?;
            let r = translate_expression(&right)?;
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
                        Type::Map(_, _) => ExpKind::MapContains(l, r),
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
        PExpressionKind::MagicWandExp { left, right, .. } => {
            ExpKind::MagicWand(translate_expression(&left)?, translate_expression(&right)?)
        }
        PExpressionKind::CondExp { cond, thn, els, .. } => ExpKind::CondExp(
            translate_expression(&cond)?,
            translate_expression(&thn)?,
            translate_expression(&els)?,
        ),
        PExpressionKind::InhaleExhale { inhale, exhale, .. } => ExpKind::InhaleExhaleExp(
            translate_expression(&inhale)?,
            translate_expression(&exhale)?,
        ),
        PExpressionKind::RangeSeq { low, high, .. } => {
            ExpKind::RangeSeq(translate_expression(&low)?, translate_expression(&high)?)
        }
        PExpressionKind::OldExp { label, exp, .. } => {
            let inner = translate_expression(exp.inner())?;
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
            let base = translate_expression(&base)?;
            let index = translate_expression(&index)?;
            match translate_type(&parse_type)? {
                Type::Seq(_) => ExpKind::SeqIndex(base, index),
                Type::Map(_, _) => ExpKind::MapLookup(base, index),
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
            let base = translate_expression(&base)?;
            let key = translate_expression(&key)?;
            let value = translate_expression(&value)?;
            match translate_type(&parse_type)? {
                Type::Seq(_) => ExpKind::SeqUpdate(base, key, value),
                Type::Map(_, _) => ExpKind::MapUpdate(base, key, value),
                _ => return Err(TranslationError::InvalidType),
            }
        }
        PExpressionKind::Size { seq, .. } => {
            let parse_type = match &seq.node().read().expect("poisoned parse node").kind {
                PNodeKind::Expression(e) => e.typ.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            let base = translate_expression(&seq)?;
            match translate_type(&parse_type)? {
                Type::Seq(_) => ExpKind::SeqLength(base),
                Type::Map(_, _) => ExpKind::MapCardinality(base),
                Type::Set(_) | Type::Multiset(_) => ExpKind::AnySetCardinality(base),
                _ => return Err(TranslationError::InvalidType),
            }
        }
        PExpressionKind::SeqSlice {
            seq, start, end, ..
        } => {
            let mut base = translate_expression(&seq)?;
            if let Some(end) = end {
                base = Exp::new(
                    ExpKind::SeqTake(base, translate_expression(&end)?),
                    meta.clone(),
                );
            }
            if let Some(start) = start {
                base = Exp::new(ExpKind::SeqDrop(base, translate_expression(&start)?), meta);
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
            Type::Map(
                Box::new(Type::Int),
                Box::new(Type::Seq(Box::new(Type::Bool)))
            )
        );
        let parsed = parse_expression("1 + 2 * 3", "test.vpr")
            .unwrap()
            .expression;
        let translated = translate_expression(&parsed).unwrap();
        assert!(matches!(translated.kind(), ExpKind::Add(_, _)));
        assert!(matches!(translated.0.meta.info, Info::SourcePNode(_)));
    }
}

/// Translate core statements; method calls, fields, plugins and generated initializers
/// require the member-signature table and remain explicit errors.
pub fn translate_statement(
    input: &super::parse_ast::PStmtHandle,
) -> Result<crate::ast::statement::Stmt, TranslationError> {
    use super::parse_ast::PStatementKind;
    use crate::ast::program::{Declaration, LocalVarDecl};
    use crate::ast::statement::{Stmt, StmtKind};
    let statement = match &input.node().read().expect("poisoned parse node").kind {
        PNodeKind::Statement(statement) => statement.clone(),
        _ => return Err(TranslationError::Unsupported("statement node")),
    };
    let meta = metadata(input.node())?;
    let kind = match statement.kind {
        PStatementKind::Assert { exp, .. } => StmtKind::Assert(translate_expression(&exp)?),
        PStatementKind::Assume { exp, .. } => StmtKind::Assume(translate_expression(&exp)?),
        PStatementKind::Inhale { exp, .. } => StmtKind::Inhale(translate_expression(&exp)?),
        PStatementKind::Exhale { exp, .. } => StmtKind::Exhale(translate_expression(&exp)?),
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
            let translated = translate_expression(target)?;
            let ExpKind::LocalVar(local) = translated.kind() else {
                return Err(TranslationError::Unsupported("field assignment"));
            };
            let mut local_meta = meta.clone();
            local_meta.info = Info::SourcePNode(target.node().clone());
            StmtKind::LocalVarAssign {
                lhs: LocalVar::new(local.name.clone(), local.typ.clone(), local_meta),
                rhs: translate_expression(&rhs)?,
            }
        }
        PStatementKind::Vars { init: Some(_), .. } => {
            return Err(TranslationError::Unsupported(
                "local declaration initializer",
            ));
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
                    result.push(translate_statement(statement)?);
                }
            }
            StmtKind::Seqn {
                statements: result,
                declarations,
            }
        }
        PStatementKind::If { cond, thn, els, .. } => {
            let then_branch = translate_statement(&thn)?;
            let else_branch = match els {
                Some(s) => {
                    let translated = translate_statement(&s)?;
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
                condition: translate_expression(cond.inner())?,
                then_branch,
                else_branch,
            }
        }
        PStatementKind::Else { els, .. } => return translate_statement(&els),
        PStatementKind::While {
            cond, invs, body, ..
        } => StmtKind::While {
            condition: translate_expression(cond.inner())?,
            invariants: invs
                .specs
                .to_seq()
                .into_iter()
                .map(|spec| translate_expression(&spec.exp))
                .collect::<Result<_, _>>()?,
            body: translate_statement(&body)?,
        },
        PStatementKind::Label { idndef, invs, .. } => {
            let name = match &idndef.read().expect("poisoned parse node").kind {
                PNodeKind::IdnDef(id) => id.name.clone(),
                _ => return Err(TranslationError::InvalidType),
            };
            StmtKind::Label {
                name,
                invariants: invs
                    .to_seq()
                    .into_iter()
                    .map(|spec| translate_expression(&spec.exp))
                    .collect::<Result<_, _>>()?,
            }
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
