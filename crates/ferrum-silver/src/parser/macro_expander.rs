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
//! checks, graph duplication and parameter substitution. Statement/local macros, hygienic binder
//! rewriting, token-wrapper position adaptation and unused-parameter warnings remain pending.

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
    body: PExpHandle,
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

/// Expand global binder-free expression macros before name analysis. Definitions with
/// statement bodies and expression families needing binder hygiene fail explicitly when used.
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
    let mut definitions = HashMap::new();
    for member in program.all_members() {
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
                if let PDefineBody::Expression(body) = body.body() {
                    definitions.insert(
                        name,
                        ExpressionMacro {
                            parameters,
                            body: body.clone(),
                        },
                    );
                } else {
                    return Err(MacroError {
                        message: "statement macro expansion is not implemented".into(),
                        pos: idndef.read().expect("poisoned parse node").pos.clone(),
                    });
                }
            }
        }
    }
    if definitions.is_empty() {
        return Ok(());
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
            let copy = copy_expression(&def.body, &replacements)?;
            adapt_position(copy.node(), &pos)?;
            stack.push(name);
            walk(copy.node(), definitions, stack)?;
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
            walk(&child, definitions, stack)?;
        }
        Ok(())
    }
    walk(program.node(), &definitions, &mut Vec::new())
}
