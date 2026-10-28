//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/MacroExpander.scala
//!
//! Purpose:
//! Expand global and method-local macros hygienically before resolution.
//!
//! Planned Rust structure:
//! Port MacroException, expandDefines, doExpandDefines, ReplaceContext and makeReplacer; group
//! validation, cycle detection, name hygiene, copying, replacement and sequence linearization.
//!
//! Behavior to preserve:
//! Detect duplicate/clashing names, illegal proof-script definitions, unused parameters and
//! recursive macros. Local macros precede globals; remove local definitions and flatten macro
//! sequences without introducing scope. Validate arity and syntactic position, rename clashes
//! using scope identity, deep-copy arguments and bodies, suppress substitution under binders and
//! adapt positions to call sites. Convert failures to parse errors with position fallback.
//!
//! Integration:
//! parser::parse_ast and resolver::NameAnalyser; ast::utility::rewriter, verifier parse reports
//! and fast_parser.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Agree on parse node identity, parent context and reconstruction with parse_ast and rewriter.
//!
//! Status: partial; global binder-free expression macros support declaration parsing, cycle/arity
//! checks, graph duplication, parameter substitution and unused-parameter warnings. Method-local
//! macros use method-wide, local-first lookup; declaration-free statement bodies are spliced
//! without a scope. Type macros, hygienic binder rewriting, other statement products and
//! token-wrapper position adaptation remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2023 ETH Zurich.

use super::parse_ast::{PExpHandle, PMemberHandle, PMemberKind, PNodeKind};
use std::collections::{HashMap, HashSet};

/// Macro lookup is ordered: method-local definitions precede globals when supplied first.
pub fn find_macro<'a>(macros: &'a [PMemberHandle], name: &str) -> Option<&'a PMemberHandle> {
    macros.iter().find(|member| match &member.node().read().expect("poisoned parse node").kind {
        PNodeKind::Member(m) => match &m.kind {
            PMemberKind::Define { idndef, .. } => matches!(&idndef.read().expect("poisoned parse node").kind, PNodeKind::IdnDef(id) if id.name == name),
            _ => false,
        },
        _ => false,
    })
}
/// Actual argument calls match only definitions with an explicit parameter list, and
/// explicitly type-annotated calls are left for ordinary resolution.
pub fn find_call_macro<'a>(
    macros: &'a [PMemberHandle],
    name: &str,
    has_type_annotation: bool,
) -> Option<&'a PMemberHandle> {
    if has_type_annotation {
        return None;
    }
    find_macro(macros, name).filter(|member| matches!(&member.node().read().expect("poisoned parse node").kind, PNodeKind::Member(m) if matches!(m.kind, PMemberKind::Define { parameters: Some(_), .. })))
}
/// `zip(...).toMap` retains the last argument when parameter names repeat.
pub fn map_parameters_to_arguments(
    parameters: &[String],
    arguments: &[PExpHandle],
) -> HashMap<String, PExpHandle> {
    parameters
        .iter()
        .cloned()
        .zip(arguments.iter().cloned())
        .collect()
}
#[derive(Default)]
pub struct FreshMacroNames {
    counters: HashMap<String, i32>,
}
impl FreshMacroNames {
    pub fn fresh(&mut self, name: &str, scope: &HashSet<String>) -> String {
        let mut number = self.counters.get(name).map_or(0, |n| n.wrapping_add(1));
        loop {
            let candidate = format!("{name}${number}");
            if !scope.contains(&candidate) {
                self.counters.insert(name.to_owned(), number);
                return candidate;
            }
            number = number.wrapping_add(1);
        }
    }
}
/// A syntactic macro exception retains the original call or definition span.
#[derive(Clone, Debug)]
pub struct MacroError {
    pub message: String,
    pub pos: super::parse_ast_keyword::Span,
}

/// Validate global macro uniqueness and clashes with domain/function/predicate/method names.
/// Upstream checks duplicate macro declarations first, then checks the set of other names.
pub fn validate_global_names(
    program: &super::parse_ast::PProgramHandle,
) -> Vec<crate::verifier::verification_result::ParseReport> {
    use crate::verifier::verification_result::{ParseError, ParseReport};
    let mut first: HashMap<String, crate::ast::position::Position> = HashMap::new();
    let mut other_names = HashSet::new();
    let mut reports = Vec::new();
    for member in program.all_members() {
        let kind = member
            .node()
            .read()
            .expect("poisoned parse node")
            .kind
            .clone();
        let PNodeKind::Member(member_kind) = kind else {
            continue;
        };
        let (idndef, is_macro) = match member_kind.kind {
            PMemberKind::Define { idndef, .. } => (idndef, true),
            PMemberKind::Domain { idndef, .. }
            | PMemberKind::Function { idndef, .. }
            | PMemberKind::Predicate { idndef, .. }
            | PMemberKind::Method { idndef, .. } => (idndef, false),
            _ => continue,
        };
        let name = match &idndef.read().expect("poisoned parse node").kind {
            PNodeKind::IdnDef(id) => id.name.clone(),
            _ => continue,
        };
        if is_macro {
            let pos = member
                .node()
                .read()
                .expect("poisoned parse node")
                .error_position();
            if let Some(previous) = first.get(&name) {
                reports.push(ParseReport::Error(ParseError::new(
                    format!("another macro named `{name}` already exists at {previous}"),
                    pos,
                )));
            } else {
                first.insert(name, pos);
            }
        } else {
            other_names.insert(name);
        }
    }
    for name in other_names {
        if let Some(pos) = first.get(&name) {
            reports.push(ParseReport::Error(ParseError::new(
                format!("the macro name `{name}` has already been used by another identifier"),
                pos.clone(),
            )));
        }
    }
    reports
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::position::Position;
    use crate::parser::parse_ast::{
        PDefineBody, PDefineInner, PExpression, PExpressionKind, PIdnDef, PMember, PNode, PProgram,
        PProgramHandle,
    };
    use crate::parser::parse_ast_keyword::{PKw, PReserved};
    #[test]
    fn duplicate_macro_and_fresh_names_follow_source_order() {
        let span = (Position::NoPosition, Position::NoPosition);
        let make = || {
            let idndef = PNode::new(
                PNodeKind::IdnDef(PIdnDef { name: "m".into() }),
                span.clone(),
            );
            let body = PExpHandle::new(
                PExpression::from_kind(PExpressionKind::IntLit(1.into())),
                span.clone(),
            );
            PMemberHandle::new(
                PMember::new(
                    vec![],
                    PMemberKind::Define {
                        keyword: PReserved::new(PKw::Define, span.clone()),
                        idndef,
                        parameters: None,
                        body: PDefineInner::new(PDefineBody::Expression(body)),
                    },
                ),
                span.clone(),
            )
        };
        let program = PProgramHandle::new(
            PProgram {
                imported: vec![],
                members: vec![make(), make()],
                local_errors: vec![],
                offsets: vec![],
                raw_program: String::new(),
            },
            span,
        );
        assert_eq!(validate_global_names(&program).len(), 1);
        let mut fresh = FreshMacroNames::default();
        let scope = ["x$0".to_string()].into_iter().collect();
        assert_eq!(fresh.fresh("x", &scope), "x$1");
        assert_eq!(fresh.fresh("x", &scope), "x$2");
    }
}

#[derive(Clone)]
struct ExpressionMacro {
    parameters: Option<Vec<String>>,
    body: super::parse_ast::PDefineBody,
}

fn copy_expression_group(
    group: &super::parse_ast::PExpGroup,
    replacements: &HashMap<String, PExpHandle>,
) -> Result<super::parse_ast::PExpGroup, MacroError> {
    use super::parse_ast_keyword::{PGrouped, PReserved};
    Ok(PGrouped::new(
        PReserved::new(*group.left().value(), group.left().position().clone()),
        copy_expression(group.inner(), replacements)?,
        PReserved::new(*group.right().value(), group.right().position().clone()),
        group.position().clone(),
    ))
}
fn copy_expression_arguments(
    group: &super::parse_ast::PExpArguments,
    replacements: &HashMap<String, PExpHandle>,
) -> Result<super::parse_ast::PExpArguments, MacroError> {
    use super::parse_ast_keyword::{PDelimited, PGrouped, PReserved};
    let old = group.inner();
    let first = old
        .first
        .as_ref()
        .map(|e| copy_expression(e, replacements))
        .transpose()?;
    let rest = old
        .inner
        .iter()
        .map(|(comma, e)| {
            Ok((
                PReserved::new(*comma.value(), comma.position().clone()),
                copy_expression(e, replacements)?,
            ))
        })
        .collect::<Result<Vec<_>, MacroError>>()?;
    let end = old
        .end
        .as_ref()
        .map(|comma| PReserved::new(*comma.value(), comma.position().clone()));
    let args = PDelimited::new(first, rest, end, old.position().clone());
    Ok(PGrouped::new(
        PReserved::new(*group.left().value(), group.left().position().clone()),
        args,
        PReserved::new(*group.right().value(), group.right().position().clone()),
        group.position().clone(),
    ))
}

/// Duplicate the binder-free expression subset without sharing mutable parse nodes.
/// Other expression forms fail explicitly until the full hygienic rewriter is available.
fn copy_expression(
    input: &PExpHandle,
    replacements: &HashMap<String, PExpHandle>,
) -> Result<PExpHandle, MacroError> {
    use super::parse_ast::{PExpression, PExpressionKind as E, PIdnRef, PNode};
    use super::parse_ast_keyword::{PDelimited, PGrouped, PReserved};
    let (expression, pos) = {
        let node = input.node().read().expect("poisoned parse node");
        match &node.kind {
            PNodeKind::Expression(expression) => (expression.clone(), node.pos.clone()),
            _ => {
                return Err(MacroError {
                    message: "macro expression node expected".into(),
                    pos: node.pos.clone(),
                });
            }
        }
    };
    let copy_ref = |node: &super::parse_ast::PNodeHandle| -> Result<_, MacroError> {
        let n = node.read().expect("poisoned parse node");
        let PNodeKind::IdnRef(id) = &n.kind else {
            return Err(MacroError {
                message: "macro identifier expected".into(),
                pos: n.pos.clone(),
            });
        };
        let name = if let Some(replacement) = replacements.get(&id.name) {
            let replacement = replacement.node().read().expect("poisoned parse node");
            let PNodeKind::Expression(super::parse_ast::PExpression {
                kind: E::IdnUse { idnref },
                ..
            }) = &replacement.kind
            else {
                return Err(MacroError {
                    message: "macro expansion requires an identifier in this position".into(),
                    pos: replacement.pos.clone(),
                });
            };
            let reference = idnref.read().expect("poisoned parse node");
            let PNodeKind::IdnRef(reference) = &reference.kind else {
                return Err(MacroError {
                    message: "macro identifier expected".into(),
                    pos: replacement.pos.clone(),
                });
            };
            reference.name.clone()
        } else {
            id.name.clone()
        };
        let mut copy = PIdnRef::with_class(name, id.declaration_class);
        copy.assign_use = id.assign_use;
        Ok(PNode::new(PNodeKind::IdnRef(copy), n.pos.clone()))
    };
    macro_rules! token {
        ($value:expr) => {
            PReserved::new(*$value.value(), $value.position().clone())
        };
    }
    macro_rules! copied {
        ($value:expr) => {
            copy_expression(&$value, replacements)?
        };
    }
    let kind = match expression.kind {
        E::IdnUse { idnref } => {
            let name = match &idnref.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(id) => id.name.clone(),
                _ => {
                    return Err(MacroError {
                        message: "macro identifier expected".into(),
                        pos,
                    });
                }
            };
            if let Some(replacement) = replacements.get(&name) {
                return copy_expression(replacement, &HashMap::new());
            }
            E::IdnUse {
                idnref: copy_ref(&idnref)?,
            }
        }
        E::IntLit(value) => E::IntLit(value),
        E::BoolLit(token) => E::BoolLit(PReserved::new(*token.value(), token.position().clone())),
        E::NullLit(token) => E::NullLit(PReserved::new(*token.value(), token.position().clone())),
        E::NoPerm(token) => E::NoPerm(PReserved::new(*token.value(), token.position().clone())),
        E::FullPerm(token) => E::FullPerm(PReserved::new(*token.value(), token.position().clone())),
        E::Wildcard(token) => E::Wildcard(PReserved::new(*token.value(), token.position().clone())),
        E::Epsilon(token) => E::Epsilon(PReserved::new(*token.value(), token.position().clone())),
        E::ResultLit(token) => {
            E::ResultLit(PReserved::new(*token.value(), token.position().clone()))
        }
        E::UnExp { op, exp } => E::UnExp {
            op: PReserved::new(*op.value(), op.position().clone()),
            exp: copy_expression(&exp, replacements)?,
        },
        E::BinExp { left, op, right } => E::BinExp {
            left: copy_expression(&left, replacements)?,
            op: PReserved::new(op.value().clone(), op.position().clone()),
            right: copy_expression(&right, replacements)?,
        },
        E::MagicWandExp { left, wand, right } => E::MagicWandExp {
            left: copied!(left),
            wand: token!(wand),
            right: copied!(right),
        },
        E::InhaleExhale {
            left,
            inhale,
            comma,
            exhale,
            right,
        } => E::InhaleExhale {
            left: token!(left),
            inhale: copied!(inhale),
            comma: token!(comma),
            exhale: copied!(exhale),
            right: token!(right),
        },
        E::Unfolding {
            unfolding,
            acc,
            in_token,
            exp,
        } => E::Unfolding {
            unfolding: token!(unfolding),
            acc: copied!(acc),
            in_token: token!(in_token),
            exp: copied!(exp),
        },
        E::Applying {
            applying,
            wand,
            in_token,
            exp,
        } => E::Applying {
            applying: token!(applying),
            wand: copied!(wand),
            in_token: token!(in_token),
            exp: copied!(exp),
        },
        E::Asserting {
            asserting,
            assertion,
            in_token,
            exp,
        } => E::Asserting {
            asserting: token!(asserting),
            assertion: copied!(assertion),
            in_token: token!(in_token),
            exp: copied!(exp),
        },
        E::RangeSeq {
            left,
            low,
            dots,
            high,
            right,
        } => E::RangeSeq {
            left: token!(left),
            low: copied!(low),
            dots: token!(dots),
            high: copied!(high),
            right: token!(right),
        },
        E::Lookup {
            base,
            left,
            index,
            right,
        } => E::Lookup {
            base: copied!(base),
            left: token!(left),
            index: copied!(index),
            right: token!(right),
        },
        E::SeqSlice {
            seq,
            left,
            start,
            dots,
            end,
            right,
        } => E::SeqSlice {
            seq: copied!(seq),
            left: token!(left),
            start: start
                .as_ref()
                .map(|e| copy_expression(e, replacements))
                .transpose()?,
            dots: token!(dots),
            end: end
                .as_ref()
                .map(|e| copy_expression(e, replacements))
                .transpose()?,
            right: token!(right),
        },
        E::Update {
            base,
            left,
            key,
            assign,
            value,
            right,
        } => E::Update {
            base: copied!(base),
            left: token!(left),
            key: copied!(key),
            assign: token!(assign),
            value: copied!(value),
            right: token!(right),
        },
        E::Size { left, seq, right } => E::Size {
            left: token!(left),
            seq: copied!(seq),
            right: token!(right),
        },
        E::Maplet { key, assign, value } => E::Maplet {
            key: copied!(key),
            assign: token!(assign),
            value: copied!(value),
        },
        E::CurrentPerm { op, resource } => E::CurrentPerm {
            op: token!(op),
            resource: copy_expression_group(&resource, replacements)?,
        },
        E::OldExp { op, label, exp } => {
            let label = label
                .as_ref()
                .map(|group| {
                    let value = match group.inner() {
                        super::parse_ast::POldLabel::Lhs(token) => {
                            super::parse_ast::POldLabel::Lhs(token!(token))
                        }
                        super::parse_ast::POldLabel::Label(reference) => {
                            super::parse_ast::POldLabel::Label(copy_ref(reference)?)
                        }
                    };
                    Ok(PGrouped::new(
                        token!(group.left()),
                        value,
                        token!(group.right()),
                        group.position().clone(),
                    ))
                })
                .transpose()?;
            E::OldExp {
                op: token!(op),
                label,
                exp: copy_expression_group(&exp, replacements)?,
            }
        }
        E::MapDomain { keyword, base } => E::MapDomain {
            keyword: token!(keyword),
            base: copy_expression_group(&base, replacements)?,
        },
        E::MapRange { keyword, base } => E::MapRange {
            keyword: token!(keyword),
            base: copy_expression_group(&base, replacements)?,
        },
        E::AccPred { op, amount } => {
            let pair = amount.inner();
            let first = copy_expression(pair.first(), replacements)?;
            let second = pair
                .second()
                .map(|(comma, exp)| Ok((token!(comma), copy_expression(exp, replacements)?)))
                .transpose()?;
            let pair =
                super::parse_ast::PMaybePairArgument::new(first, second, pair.position().clone());
            E::AccPred {
                op: token!(op),
                amount: PGrouped::new(
                    token!(amount.left()),
                    pair,
                    token!(amount.right()),
                    amount.position().clone(),
                ),
            }
        }
        E::ExplicitSeq(collection)
        | E::ExplicitSet(collection)
        | E::ExplicitMultiset(collection) => {
            let op = *collection.op().value();
            let collection = super::parse_ast::PExplicitCollection::new(
                token!(collection.op()),
                copy_expression_arguments(collection.call_args(), replacements)?,
            );
            match op {
                super::parse_ast_keyword::PKwOp::Seq => E::ExplicitSeq(collection),
                super::parse_ast_keyword::PKwOp::Set => E::ExplicitSet(collection),
                _ => E::ExplicitMultiset(collection),
            }
        }
        E::ExplicitMap(collection) => E::ExplicitMap(super::parse_ast::PExplicitMap {
            op: token!(collection.op),
            call_args: copy_expression_arguments(&collection.call_args, replacements)?,
        }),
        E::EmptySeq(collection) | E::EmptySet(collection) | E::EmptyMultiset(collection)
            if collection.annotated_type.is_none() =>
        {
            let op = *collection.op.value();
            let collection = super::parse_ast::PEmptyCollection {
                op: token!(collection.op),
                annotated_type: None,
                call_args: copy_expression_arguments(&collection.call_args, replacements)?,
            };
            match op {
                super::parse_ast_keyword::PKwOp::Seq => E::EmptySeq(collection),
                super::parse_ast_keyword::PKwOp::Set => E::EmptySet(collection),
                _ => E::EmptyMultiset(collection),
            }
        }
        E::EmptyMap {
            op,
            annotated_type: None,
            call_args,
        } => E::EmptyMap {
            op: token!(op),
            annotated_type: None,
            call_args: copy_expression_arguments(&call_args, replacements)?,
        },
        E::CondExp {
            cond,
            question,
            thn,
            colon,
            els,
        } => E::CondExp {
            cond: copy_expression(&cond, replacements)?,
            question: PReserved::new(*question.value(), question.position().clone()),
            thn: copy_expression(&thn, replacements)?,
            colon: PReserved::new(*colon.value(), colon.position().clone()),
            els: copy_expression(&els, replacements)?,
        },
        E::FieldAccess {
            receiver,
            dot,
            idnref,
            ..
        } => E::FieldAccess {
            receiver: copy_expression(&receiver, replacements)?,
            dot: PReserved::new(*dot.value(), dot.position().clone()),
            idnref: copy_ref(&idnref)?,
            adt_type_renaming: None,
            adt_substitution: None,
        },
        E::Call {
            idnref,
            call_args,
            type_annotated: None,
            ..
        } => {
            let old = call_args.inner();
            let first = old
                .first
                .as_ref()
                .map(|e| copy_expression(e, replacements))
                .transpose()?;
            let rest = old
                .inner
                .iter()
                .map(|(comma, e)| {
                    Ok((
                        PReserved::new(*comma.value(), comma.position().clone()),
                        copy_expression(e, replacements)?,
                    ))
                })
                .collect::<Result<Vec<_>, MacroError>>()?;
            let end = old
                .end
                .as_ref()
                .map(|comma| PReserved::new(*comma.value(), comma.position().clone()));
            let args = PDelimited::new(first, rest, end, old.position().clone());
            let args = PGrouped::new(
                PReserved::new(
                    *call_args.left().value(),
                    call_args.left().position().clone(),
                ),
                args,
                PReserved::new(
                    *call_args.right().value(),
                    call_args.right().position().clone(),
                ),
                call_args.position().clone(),
            );
            E::Call {
                idnref: copy_ref(&idnref)?,
                call_args: args,
                type_annotated: None,
                extra_local_type_variables: vec![],
                domain_type_renaming: None,
                domain_substitution: None,
            }
        }
        _ => {
            return Err(MacroError {
                message: "unsupported macro expression requiring hygienic reconstruction".into(),
                pos,
            });
        }
    };
    Ok(PExpHandle::new(PExpression::from_kind(kind), pos))
}

/// Reconstruct statement macro bodies only for products without declarations or binders.
/// Declaration-bearing forms require hygienic renaming and are rejected until available.
fn copy_macro_statement(
    input: &super::parse_ast::PStmtHandle,
    replacements: &HashMap<String, PExpHandle>,
    root: bool,
) -> Result<super::parse_ast::PStmtHandle, MacroError> {
    use super::parse_ast::{PStatement, PStatementKind as S, PStmtHandle};
    use super::parse_ast_keyword::{ND, PDelimited, PGrouped, PReserved};
    let (kind, pos) = {
        let node = input.node().read().expect("poisoned parse node");
        let PNodeKind::Statement(stmt) = &node.kind else {
            return Err(MacroError {
                message: "macro statement expected".into(),
                pos: node.pos.clone(),
            });
        };
        (stmt.kind.clone(), node.pos.clone())
    };
    macro_rules! token {
        ($t:expr) => {
            PReserved::new(*$t.value(), $t.position().clone())
        };
    }
    let kind = match kind {
        S::Seqn { statements, .. } => {
            let old = statements.inner();
            let items = old
                .to_seq()
                .into_iter()
                .map(|stmt| copy_macro_statement(stmt, replacements, false))
                .collect::<Result<Vec<_>, _>>()?;
            let mut values = items.into_iter();
            let first = values.next();
            let inner = old
                .inner
                .iter()
                .map(|(delimiter, _)| {
                    let delimiter = ND(delimiter.0.as_ref().map(|t| token!(t)));
                    (delimiter, values.next().expect("matched statement count"))
                })
                .collect();
            let end = old
                .end
                .as_ref()
                .map(|d| ND(d.0.as_ref().map(|t| token!(t))));
            let list = PDelimited::new(first, inner, end, old.position().clone());
            let block = PGrouped::new(
                token!(statements.left()),
                list,
                token!(statements.right()),
                statements.position().clone(),
            );
            if root {
                S::MacroSeqn { statements: block }
            } else {
                S::Seqn {
                    statements: block,
                    scope_id: super::parse_ast::fresh_scope_id(),
                }
            }
        }
        S::Assert { keyword, exp } => S::Assert {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements)?,
        },
        S::Assume { keyword, exp } => S::Assume {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements)?,
        },
        S::Inhale { keyword, exp } => S::Inhale {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements)?,
        },
        S::Exhale { keyword, exp } => S::Exhale {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements)?,
        },
        S::Fold { keyword, exp } => S::Fold {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements)?,
        },
        S::Unfold { keyword, exp } => S::Unfold {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements)?,
        },
        S::ApplyWand { keyword, exp } => S::ApplyWand {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements)?,
        },
        S::Assign { targets, op, rhs } => {
            let first = targets
                .first
                .as_ref()
                .map(|e| copy_expression(e, replacements))
                .transpose()?;
            let inner = targets
                .inner
                .iter()
                .map(|(delimiter, exp)| {
                    Ok((token!(delimiter), copy_expression(exp, replacements)?))
                })
                .collect::<Result<Vec<_>, MacroError>>()?;
            let end = targets.end.as_ref().map(|delimiter| token!(delimiter));
            S::Assign {
                targets: PDelimited::new(first, inner, end, targets.position().clone()),
                op: op.as_ref().map(|t| token!(t)),
                rhs: copy_expression(&rhs, replacements)?,
            }
        }
        S::If {
            keyword,
            cond,
            thn,
            els,
        } => S::If {
            keyword: token!(keyword),
            cond: copy_expression_group(&cond, replacements)?,
            thn: copy_macro_statement(&thn, replacements, false)?,
            els: els
                .as_ref()
                .map(|stmt| copy_macro_statement(stmt, replacements, false))
                .transpose()?,
        },
        S::Else { keyword, els } => S::Else {
            keyword: token!(keyword),
            els: copy_macro_statement(&els, replacements, false)?,
        },
        S::Skip => S::Skip,
        _ => {
            return Err(MacroError {
                message: "statement macro body requires unsupported reconstruction or hygiene"
                    .into(),
                pos,
            });
        }
    };
    Ok(PStmtHandle::new(PStatement { kind }, pos))
}

/// Expand supported global and method-local macros before name analysis. Products requiring
/// hygienic reconstruction fail explicitly when used.
pub fn expand_global_expression_macros(
    program: &super::parse_ast::PProgramHandle,
) -> Result<(), MacroError> {
    use super::parse_ast::{PDefineBody, PExpressionKind, PNodeHandle, subnodes};
    let reports = validate_global_names(program);
    if let Some(report) = reports.first() {
        return Err(MacroError {
            message: report.readable_message(),
            pos: (report.pos().clone(), report.pos().clone()),
        });
    }
    fn free_names(
        node: &PNodeHandle,
        bound: &HashSet<String>,
        free: &mut HashSet<String>,
    ) -> Result<(), MacroError> {
        let (kind, pos) = {
            let node = node.read().expect("poisoned parse node");
            (node.kind.clone(), node.pos.clone())
        };
        let mut inner_bound = bound.clone();
        if let PNodeKind::Expression(expression) = &kind {
            let vars = match &expression.kind {
                PExpressionKind::Forall(q) | PExpressionKind::Exists(q) => Some(&q.vars),
                PExpressionKind::ForPerm { vars, .. } => Some(vars),
                _ => None,
            };
            if let Some(vars) = vars {
                for var in vars.to_seq() {
                    let kind = var.node().read().expect("poisoned parse node").kind.clone();
                    if let PNodeKind::Declaration(declaration) = kind {
                        if let PNodeKind::IdnDef(id) =
                            &declaration.idndef.read().expect("poisoned parse node").kind
                        {
                            inner_bound.insert(id.name.clone());
                        }
                    }
                }
            }
        }
        if let PNodeKind::IdnRef(id) = kind {
            if !inner_bound.contains(&id.name) {
                free.insert(id.name);
            }
        }
        for child in subnodes(node).map_err(|e| MacroError {
            message: format!("macro free-variable traversal: {e:?}"),
            pos: pos.clone(),
        })? {
            free_names(&child, &inner_bound, free)?;
        }
        Ok(())
    }
    fn register(
        member: PMemberHandle,
        definitions: &mut HashMap<String, ExpressionMacro>,
        warnings: &mut Vec<crate::verifier::verification_result::ParseReport>,
        keep_first: bool,
    ) -> Result<(), MacroError> {
        let error_position = member
            .node()
            .read()
            .expect("poisoned parse node")
            .error_position();
        let kind = member
            .node()
            .read()
            .expect("poisoned parse node")
            .kind
            .clone();
        if let PNodeKind::Member(member) = kind {
            if let PMemberKind::Define {
                idndef,
                parameters,
                body,
                ..
            } = member.kind
            {
                let name = match &idndef.read().expect("poisoned parse node").kind {
                    PNodeKind::IdnDef(id) => id.name.clone(),
                    _ => {
                        return Err(MacroError {
                            message: "macro name expected".into(),
                            pos: idndef.read().expect("poisoned parse node").pos.clone(),
                        });
                    }
                };
                let parameters = parameters
                    .map(|p| {
                        p.inner()
                            .to_seq()
                            .into_iter()
                            .map(
                                |node| match &node.read().expect("poisoned parse node").kind {
                                    PNodeKind::DefineParam { children } => {
                                        match &children[0].read().expect("poisoned parse node").kind
                                        {
                                            PNodeKind::IdnDef(id) => Ok(id.name.clone()),
                                            _ => Err(MacroError {
                                                message: "macro parameter name expected".into(),
                                                pos: node
                                                    .read()
                                                    .expect("poisoned parse node")
                                                    .pos
                                                    .clone(),
                                            }),
                                        }
                                    }
                                    _ => Err(MacroError {
                                        message: "macro parameter expected".into(),
                                        pos: node.read().expect("poisoned parse node").pos.clone(),
                                    }),
                                },
                            )
                            .collect::<Result<Vec<_>, _>>()
                    })
                    .transpose()?;
                {
                    let mut free = HashSet::new();
                    let body_node = match body.body() {
                        PDefineBody::Expression(e) => e.node(),
                        PDefineBody::Statement(s) => s.node(),
                    };
                    free_names(body_node, &HashSet::new(), &mut free)?;
                    let unused: HashSet<_> = parameters
                        .as_ref()
                        .into_iter()
                        .flatten()
                        .filter(|param| !free.contains(*param))
                        .cloned()
                        .collect();
                    if !unused.is_empty() {
                        warnings.push(crate::verifier::verification_result::ParseReport::Warning(crate::verifier::verification_result::ParseWarning::new(format!("in macro `{name}`, the following parameters were defined but not used: {}", unused.into_iter().collect::<Vec<_>>().join(", ")), error_position)));
                    }
                    let definition = ExpressionMacro {
                        parameters,
                        body: body.body().clone(),
                    };
                    if keep_first {
                        definitions.entry(name).or_insert(definition);
                    } else {
                        definitions.insert(name, definition);
                    }
                }
            }
        }
        Ok(())
    }
    let mut definitions = HashMap::new();
    let mut warnings = Vec::new();
    for member in program.all_members() {
        register(member, &mut definitions, &mut warnings, false)?;
    }
    fn adapt_position(
        node: &PNodeHandle,
        pos: &super::parse_ast_keyword::Span,
    ) -> Result<(), MacroError> {
        for child in subnodes(node).map_err(|e| MacroError {
            message: format!("macro position traversal: {e:?}"),
            pos: pos.clone(),
        })? {
            adapt_position(&child, pos)?;
        }
        node.write().expect("poisoned parse node").pos = pos.clone();
        Ok(())
    }
    fn walk(
        node: &PNodeHandle,
        definitions: &HashMap<String, ExpressionMacro>,
        stack: &mut Vec<String>,
        warnings: &mut Vec<crate::verifier::verification_result::ParseReport>,
    ) -> Result<(), MacroError> {
        let (kind, pos) = {
            let node = node.read().expect("poisoned parse node");
            (node.kind.clone(), node.pos.clone())
        };
        if matches!(
            &kind,
            PNodeKind::Member(super::parse_ast::PMember {
                kind: PMemberKind::Define { .. },
                ..
            })
        ) {
            return Ok(());
        }
        if matches!(
            &kind,
            PNodeKind::Member(super::parse_ast::PMember {
                kind: PMemberKind::Method { .. },
                ..
            })
        ) {
            fn collect_local(
                node: &PNodeHandle,
                inside_wand: bool,
                definitions: &mut HashMap<String, ExpressionMacro>,
                warnings: &mut Vec<crate::verifier::verification_result::ParseReport>,
            ) -> Result<(), MacroError> {
                let (kind, pos) = {
                    let node = node.read().expect("poisoned parse node");
                    (node.kind.clone(), node.pos.clone())
                };
                if let PNodeKind::Statement(super::parse_ast::PStatement {
                    kind: super::parse_ast::PStatementKind::MacroDefinition(member),
                }) = &kind
                {
                    if inside_wand {
                        return Err(MacroError {
                            message: "macros cannot be defined inside magic wands proof scripts"
                                .into(),
                            pos,
                        });
                    }
                    register(member.clone(), definitions, warnings, true)?;
                    node.write().expect("poisoned parse node").kind =
                        PNodeKind::Statement(super::parse_ast::PStatement {
                            kind: super::parse_ast::PStatementKind::Skip,
                        });
                    return Ok(());
                }
                let inside_wand = inside_wand
                    || matches!(
                        kind,
                        PNodeKind::Statement(super::parse_ast::PStatement {
                            kind: super::parse_ast::PStatementKind::PackageWand { .. }
                        })
                    );
                for child in subnodes(node).map_err(|e| MacroError {
                    message: format!("macro traversal: {e:?}"),
                    pos: pos.clone(),
                })? {
                    collect_local(&child, inside_wand, definitions, warnings)?;
                }
                Ok(())
            }
            let mut locals = HashMap::new();
            collect_local(node, false, &mut locals, warnings)?;
            for (name, definition) in definitions {
                locals
                    .entry(name.clone())
                    .or_insert_with(|| definition.clone());
            }
            for child in subnodes(node).map_err(|e| MacroError {
                message: format!("macro traversal: {e:?}"),
                pos: pos.clone(),
            })? {
                walk(&child, &locals, stack, warnings)?;
            }
            return Ok(());
        }
        if let PNodeKind::Statement(super::parse_ast::PStatement {
            kind:
                super::parse_ast::PStatementKind::Assign {
                    targets,
                    op: None,
                    rhs,
                },
        }) = &kind
        {
            if targets.is_empty() {
                let rhs_kind = rhs.node().read().expect("poisoned parse node").kind.clone();
                let use_call = match rhs_kind {
                    PNodeKind::Expression(super::parse_ast::PExpression {
                        kind: PExpressionKind::IdnUse { idnref },
                        ..
                    }) => Some((idnref, None)),
                    PNodeKind::Expression(super::parse_ast::PExpression {
                        kind:
                            PExpressionKind::Call {
                                idnref,
                                call_args,
                                type_annotated: None,
                                ..
                            },
                        ..
                    }) => Some((
                        idnref,
                        Some(
                            call_args
                                .inner()
                                .to_seq()
                                .into_iter()
                                .cloned()
                                .collect::<Vec<_>>(),
                        ),
                    )),
                    _ => None,
                };
                if let Some((reference, args)) = use_call {
                    let name = match &reference.read().expect("poisoned parse node").kind {
                        PNodeKind::IdnRef(id) => id.name.clone(),
                        _ => {
                            return Err(MacroError {
                                message: "macro identifier expected".into(),
                                pos,
                            });
                        }
                    };
                    if let Some(def) = definitions
                        .get(&name)
                        .filter(|d| args.is_none() || d.parameters.is_some())
                    {
                        if stack.contains(&name) {
                            return Err(MacroError {
                                message: format!("recursive macro `{name}`"),
                                pos,
                            });
                        }
                        if args.is_some() != def.parameters.is_some()
                            || args.as_ref().map(Vec::len) != def.parameters.as_ref().map(Vec::len)
                        {
                            return Err(MacroError {
                                message: format!("wrong number of arguments to macro `{name}`"),
                                pos,
                            });
                        }
                        let PDefineBody::Statement(body) = &def.body else {
                            return Err(MacroError {
                                message: format!(
                                    "expression macro `{name}` cannot be used as a statement"
                                ),
                                pos,
                            });
                        };
                        let replacements = map_parameters_to_arguments(
                            def.parameters.as_deref().unwrap_or_default(),
                            args.as_deref().unwrap_or_default(),
                        );
                        let copy = copy_macro_statement(body, &replacements, true)?;
                        adapt_position(copy.node(), &pos)?;
                        stack.push(name);
                        walk(copy.node(), definitions, stack, warnings)?;
                        stack.pop();
                        node.write().expect("poisoned parse node").kind = copy
                            .node()
                            .read()
                            .expect("poisoned parse node")
                            .kind
                            .clone();
                        return Ok(());
                    }
                }
            }
        }
        if let PNodeKind::Type(super::parse_ast::PTypeKind::Domain {
            domain, args: None, ..
        }) = &kind
        {
            let name = match &domain.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(id) => id.name.clone(),
                _ => {
                    return Err(MacroError {
                        message: "macro type identifier expected".into(),
                        pos,
                    });
                }
            };
            if let Some(definition) = definitions.get(&name) {
                if definition.parameters.is_some() {
                    return Err(MacroError {
                        message: format!(
                            "macro `{name}` is defined with parameters but referenced without arguments"
                        ),
                        pos,
                    });
                }
                return Err(MacroError {
                    message: format!("macro `{name}` does not have a type body"),
                    pos,
                });
            }
        }
        let invocation = match &kind {
            PNodeKind::Expression(expression) => match &expression.kind {
                PExpressionKind::Call {
                    idnref,
                    call_args,
                    type_annotated: None,
                    ..
                } => {
                    let name = match &idnref.read().expect("poisoned parse node").kind {
                        PNodeKind::IdnRef(id) => id.name.clone(),
                        _ => {
                            return Err(MacroError {
                                message: "macro call identifier expected".into(),
                                pos,
                            });
                        }
                    };
                    definitions.get(&name).and_then(|def| {
                        def.parameters.as_ref().map(|_| {
                            (
                                name,
                                call_args
                                    .inner()
                                    .to_seq()
                                    .into_iter()
                                    .cloned()
                                    .collect::<Vec<_>>(),
                            )
                        })
                    })
                }
                PExpressionKind::IdnUse { idnref } => {
                    let name = match &idnref.read().expect("poisoned parse node").kind {
                        PNodeKind::IdnRef(id) => id.name.clone(),
                        _ => {
                            return Err(MacroError {
                                message: "macro identifier expected".into(),
                                pos,
                            });
                        }
                    };
                    match definitions.get(&name) {
                        Some(def) if def.parameters.is_some() => {
                            return Err(MacroError {
                                message: format!(
                                    "macro `{name}` is defined with parameters but referenced without arguments"
                                ),
                                pos,
                            });
                        }
                        Some(_) => Some((name, Vec::new())),
                        None => None,
                    }
                }
                _ => None,
            },
            _ => None,
        };
        if let Some((name, args)) = invocation {
            if stack.contains(&name) {
                return Err(MacroError {
                    message: format!("recursive macro `{name}`"),
                    pos,
                });
            }
            let def = &definitions[&name];
            let params = def.parameters.as_deref().unwrap_or_default();
            if params.len() != args.len() {
                return Err(MacroError {
                    message: format!("wrong number of arguments to macro `{name}`"),
                    pos,
                });
            }
            let replacements = map_parameters_to_arguments(params, &args);
            let PDefineBody::Expression(body) = &def.body else {
                return Err(MacroError {
                    message: format!("statement macro `{name}` cannot be used as an expression"),
                    pos,
                });
            };
            let copy = copy_expression(body, &replacements)?;
            adapt_position(copy.node(), &pos)?;
            stack.push(name);
            walk(copy.node(), definitions, stack, warnings)?;
            stack.pop();
            let replacement = copy
                .node()
                .read()
                .expect("poisoned parse node")
                .kind
                .clone();
            node.write().expect("poisoned parse node").kind = replacement;
            return Ok(());
        }
        for child in subnodes(node).map_err(|e| MacroError {
            message: format!("macro traversal: {e:?}"),
            pos: pos.clone(),
        })? {
            walk(&child, definitions, stack, warnings)?;
        }
        // Source linearization splices macro sequences into their containing block without
        // introducing a lexical scope; the macro's own delimiters are retained.
        let current = node.read().expect("poisoned parse node").kind.clone();
        if let PNodeKind::Statement(super::parse_ast::PStatement {
            kind: statement_kind,
        }) = current
        {
            use super::parse_ast::PStatementKind as S;
            let (block, scope) = match statement_kind {
                S::Seqn {
                    statements,
                    scope_id,
                } => (statements, Some(scope_id)),
                S::MacroSeqn { statements } => (statements, None),
                _ => return Ok(()),
            };
            let mut pairs = Vec::new();
            let old = block.inner();
            if old.to_seq().len() != old.delimiters().count() {
                return Err(MacroError {
                    message: "macro block delimiter is missing".into(),
                    pos,
                });
            }
            for (stmt, delimiter) in old.to_seq().into_iter().zip(old.delimiters()) {
                let child = stmt
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .kind
                    .clone();
                if let PNodeKind::Statement(super::parse_ast::PStatement {
                    kind: S::MacroSeqn { statements },
                }) = child
                {
                    let list = statements.inner();
                    if list.to_seq().len() != list.delimiters().count() {
                        return Err(MacroError {
                            message: "macro block delimiter is missing".into(),
                            pos,
                        });
                    }
                    pairs.extend(
                        list.to_seq()
                            .into_iter()
                            .cloned()
                            .zip(list.delimiters().cloned()),
                    );
                } else {
                    pairs.push((stmt.clone(), delimiter.clone()));
                }
            }
            let list =
                super::parse_ast_keyword::PDelimited::from_pairs(pairs, old.position().clone());
            let block = block.clone().update(list);
            let kind = if let Some(scope_id) = scope {
                S::Seqn {
                    statements: block,
                    scope_id,
                }
            } else {
                S::MacroSeqn { statements: block }
            };
            node.write().expect("poisoned parse node").kind =
                PNodeKind::Statement(super::parse_ast::PStatement { kind });
        }
        Ok(())
    }
    walk(program.node(), &definitions, &mut Vec::new(), &mut warnings)?;
    if let PNodeKind::Program(program) =
        &mut program.node().write().expect("poisoned parse node").kind
    {
        program.local_errors.extend(warnings);
    }
    Ok(())
}
