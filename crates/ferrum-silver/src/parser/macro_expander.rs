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
//! Status: partial; global and method-local macros use local-first lookup, validate declarations,
//! duplicate supported expression and statement products, rename declarations and splice blocks.
//! Unknown plugin products, some statements and token-wrapper position adaptation remain pending;
//! global name seeding is conservative for unknown extension declarations.

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
#[derive(Default, Clone)]
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

fn non_expression_substitution(
    value: &PExpHandle,
    target: &crate::ast::position::Position,
) -> Option<String> {
    let rendered = super::reformat_pretty_printer::show_node(
        value.node(),
        &super::reformat_pretty_printer::LeafReformatAdapter,
    )
    .ok()?;
    let position = value.node().read().ok()?.pos.0.clone();
    Some(format!(
        "macro expansion cannot substitute expression `{rendered}` at {position} in non-expression position at {target}."
    ))
}

impl MacroError {
    /// Source MacroExpander uses the exception span when file-backed, then the
    /// enclosing program span, finally the exception start position.
    pub fn error_position(
        &self,
        program: &super::parse_ast::PProgramHandle,
    ) -> crate::ast::position::Position {
        use crate::ast::position::{LineColumn, Position, SourcePosition};
        fn source(span: &super::parse_ast_keyword::Span) -> Option<Position> {
            match span {
                (
                    Position::LineColumn(LineColumn::File(start)),
                    Position::LineColumn(LineColumn::File(end)),
                ) => Some(Position::LineColumn(LineColumn::Source(Box::new(
                    SourcePosition {
                        file: Some(start.file.clone()),
                        start: Box::new(LineColumn::File(start.clone())),
                        end: Some(Box::new(LineColumn::File(end.clone()))),
                    },
                )))),
                _ => None,
            }
        }
        source(&self.pos)
            .or_else(|| source(&program.node().read().expect("poisoned parse node").pos))
            .unwrap_or_else(|| self.pos.0.clone())
    }
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
    fn versioned_identifiers_follow_renaming_but_are_not_parameter_expressions() {
        use crate::parser::parse_ast::{PDeclarationClass, PIdnRef};
        let pos = (Position::NoPosition, Position::NoPosition);
        let expression = PExpHandle::new(
            PExpression::from_kind(PExpressionKind::VersionedIdnUse {
                idnref: PIdnRef::with_class("x", PDeclarationClass::TypedVar),
                version: "3".into(),
                separator: "@".into(),
            }),
            pos.clone(),
        );
        let scope = std::cell::RefCell::new(MacroCopyScope {
            renames: [("x".into(), "x$0".into())].into(),
            ..Default::default()
        });
        let replacement = PExpHandle::new(
            PExpression::from_kind(PExpressionKind::IntLit(42.into())),
            pos,
        );
        let output =
            copy_expression(&expression, &[("x$0".into(), replacement)].into(), &scope).unwrap();
        let node = output.node().read().unwrap();
        assert!(
            matches!(&node.kind, PNodeKind::Expression(PExpression { kind: PExpressionKind::VersionedIdnUse { idnref, version, separator }, .. }) if idnref.name == "x$0" && version == "3" && separator == "@")
        );
    }

    #[test]
    fn copying_macro_sequence_preserves_scope_free_product() {
        use crate::parser::parse_ast::{PStatement, PStatementKind, PStmtHandle};
        use crate::parser::parse_ast_keyword::{ND, PDelimited, PGrouped, PSym};
        let pos = (Position::NoPosition, Position::NoPosition);
        let skip = PStmtHandle::new(
            PStatement {
                kind: PStatementKind::Skip,
            },
            pos.clone(),
        );
        let block = PGrouped::new(
            PReserved::new(PSym::LBrace, pos.clone()),
            PDelimited::new(Some(skip), vec![], Some(ND(None)), pos.clone()),
            PReserved::new(PSym::RBrace, pos.clone()),
            pos.clone(),
        );
        let statement = PStmtHandle::new(
            PStatement {
                kind: PStatementKind::MacroSeqn { statements: block },
            },
            pos,
        );
        let output = copy_macro_statement(
            &statement,
            &HashMap::new(),
            false,
            &std::cell::RefCell::new(MacroCopyScope::default()),
        )
        .unwrap();
        assert!(matches!(
            &output.node().read().unwrap().kind,
            PNodeKind::Statement(PStatement {
                kind: PStatementKind::MacroSeqn { .. }
            })
        ));
    }

    #[test]
    fn macro_error_uses_program_span_when_exception_is_not_file_backed() {
        use crate::ast::position::{FilePosition, LineColumn};
        let file = std::path::PathBuf::from("test.vpr");
        let span = (
            Position::LineColumn(LineColumn::File(FilePosition {
                file: file.clone(),
                line: 1,
                column: 1,
            })),
            Position::LineColumn(LineColumn::File(FilePosition {
                file,
                line: 2,
                column: 3,
            })),
        );
        let program = PProgramHandle::new(
            PProgram {
                imported: vec![],
                members: vec![],
                local_errors: vec![],
                offsets: vec![],
                raw_program: String::new(),
            },
            span,
        );
        let error = MacroError {
            message: "bad".into(),
            pos: (Position::NoPosition, Position::NoPosition),
        };
        assert!(
            matches!(error.error_position(&program), Position::LineColumn(LineColumn::Source(source)) if source.end.is_some())
        );
    }

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
    pos: super::parse_ast_keyword::Span,
}

fn missing_macro_arguments(name: &str, parameters: &[String]) -> String {
    format!(
        "macro `{name}` is defined with parameters but referenced without, try adding `({})`",
        parameters.join(", ")
    )
}

#[derive(Default)]
struct MacroCopyScope {
    names: HashSet<String>,
    fresh: FreshMacroNames,
    renames: HashMap<String, String>,
    preserve_names: bool,
    expression_call_position: Option<crate::ast::position::Position>,
}

fn copy_expression_group(
    group: &super::parse_ast::PExpGroup,
    replacements: &HashMap<String, PExpHandle>,
    scope: &std::cell::RefCell<MacroCopyScope>,
) -> Result<super::parse_ast::PExpGroup, MacroError> {
    copy_extension_expression_group(group, &|child| copy_expression(child, replacements, scope))
}
/// Rebuild a grouped expression in a plugin macro-copy hook, preserving delimiter
/// and group positions while using the caller's hygienic child copier.
pub fn copy_extension_expression_group(
    group: &super::parse_ast::PExpGroup,
    copy: &dyn Fn(&PExpHandle) -> Result<PExpHandle, MacroError>,
) -> Result<super::parse_ast::PExpGroup, MacroError> {
    use super::parse_ast_keyword::{PGrouped, PReserved};
    Ok(PGrouped::new(
        PReserved::new(*group.left().value(), group.left().position().clone()),
        copy(group.inner())?,
        PReserved::new(*group.right().value(), group.right().position().clone()),
        group.position().clone(),
    ))
}
fn copy_expression_arguments(
    group: &super::parse_ast::PExpArguments,
    replacements: &HashMap<String, PExpHandle>,
    scope: &std::cell::RefCell<MacroCopyScope>,
) -> Result<super::parse_ast::PExpArguments, MacroError> {
    use super::parse_ast_keyword::{PDelimited, PGrouped, PReserved};
    let old = group.inner();
    let first = old
        .first
        .as_ref()
        .map(|e| copy_expression(e, replacements, scope))
        .transpose()?;
    let rest = old
        .inner
        .iter()
        .map(|(comma, e)| {
            Ok((
                PReserved::new(*comma.value(), comma.position().clone()),
                copy_expression(e, replacements, scope)?,
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

fn copy_macro_annotation(
    annotation: &super::parse_ast::PAnnotation,
) -> super::parse_ast::PAnnotation {
    use super::parse_ast::{PAnnotation, PRawString, PStringLiteral};
    use super::parse_ast_keyword::{PDelimited, PGrouped, PReserved};
    macro_rules! token {
        ($t:expr) => {
            PReserved::new(*$t.value(), $t.position().clone())
        };
    }
    let copy_string = |literal: &PStringLiteral| {
        let group = literal.grouped();
        let raw = PRawString::new(
            group.inner().text().into(),
            group.inner().position().clone(),
        );
        let group = PGrouped::new(
            token!(group.left()),
            raw,
            token!(group.right()),
            group.position().clone(),
        );
        PStringLiteral::new(group, literal.position().clone())
    };
    let group = annotation.values();
    let old = group.inner();
    let first = old.first.as_ref().map(copy_string);
    let inner = old
        .inner
        .iter()
        .map(|(comma, literal)| (token!(comma), copy_string(literal)))
        .collect();
    let end = old.end.as_ref().map(|comma| token!(comma));
    let values = PDelimited::new(first, inner, end, old.position().clone());
    let values = PGrouped::new(
        token!(group.left()),
        values,
        token!(group.right()),
        group.position().clone(),
    );
    let key = PRawString::new(
        annotation.key().text().into(),
        annotation.key().position().clone(),
    );
    PAnnotation::new(
        token!(annotation.at()),
        key,
        values,
        annotation.position().clone(),
    )
}

/// Duplicate source type products rather than sharing their mutable parser graph.
fn copy_macro_type(
    input: &super::parse_ast::PTypeHandle,
    replacements: &HashMap<String, PExpHandle>,
    scope: &std::cell::RefCell<MacroCopyScope>,
) -> Result<super::parse_ast::PTypeHandle, MacroError> {
    use super::parse_ast::{PNode, PPairArgument, PTypeHandle, PTypeKind as T};
    use super::parse_ast_keyword::{PDelimited, PGrouped, PReserved};
    let (kind, pos) = {
        let node = input.node().read().expect("poisoned parse node");
        let PNodeKind::Type(kind) = &node.kind else {
            return Err(MacroError {
                message: "macro type node expected".into(),
                pos: node.pos.clone(),
            });
        };
        (kind.clone(), node.pos.clone())
    };
    macro_rules! token {
        ($t:expr) => {
            PReserved::new(*$t.value(), $t.position().clone())
        };
    }
    let kind = match kind {
        T::Primitive { name } => T::Primitive { name: token!(name) },
        T::ExtensionPrimitive { name } => T::ExtensionPrimitive {
            name: PReserved::new(name.value().clone(), name.position().clone()),
        },
        T::Domain { domain, args, kind } => {
            let domain_node = domain.read().expect("poisoned parse node");
            let PNodeKind::IdnRef(id) = &domain_node.kind else {
                return Err(MacroError {
                    message: "macro type identifier expected".into(),
                    pos: domain_node.pos.clone(),
                });
            };
            let mut id = id.clone();
            id.name = scope
                .borrow()
                .renames
                .get(&id.name)
                .cloned()
                .unwrap_or(id.name);
            if let Some(value) = replacements.get(&id.name) {
                let value = value.node().read().expect("poisoned parse node");
                let PNodeKind::Expression(super::parse_ast::PExpression {
                    kind: super::parse_ast::PExpressionKind::IdnUse { idnref },
                    ..
                }) = &value.kind
                else {
                    return Err(MacroError {
                        message: "macro expansion requires an identifier in type position".into(),
                        pos: value.pos.clone(),
                    });
                };
                let reference = idnref.read().expect("poisoned parse node");
                let PNodeKind::IdnRef(reference) = &reference.kind else {
                    return Err(MacroError {
                        message: "macro identifier expected".into(),
                        pos: reference.pos.clone(),
                    });
                };
                id.name = reference.name.clone();
            }
            let domain = PNode::new(PNodeKind::IdnRef(id), domain_node.pos.clone());
            let args = args
                .map(|group| {
                    let old = group.inner();
                    let first = old
                        .first
                        .as_ref()
                        .map(|typ| copy_macro_type(typ, replacements, scope))
                        .transpose()?;
                    let inner = old
                        .inner
                        .iter()
                        .map(|(comma, typ)| {
                            Ok((token!(comma), copy_macro_type(typ, replacements, scope)?))
                        })
                        .collect::<Result<Vec<_>, MacroError>>()?;
                    let end = old.end.as_ref().map(|comma| token!(comma));
                    let list = PDelimited::new(first, inner, end, old.position().clone());
                    Ok::<_, MacroError>(PGrouped::new(
                        token!(group.left()),
                        list,
                        token!(group.right()),
                        group.position().clone(),
                    ))
                })
                .transpose()?;
            T::Domain { domain, args, kind }
        }
        T::Seq {
            keyword,
            element_type,
        }
        | T::Set {
            keyword,
            element_type,
        }
        | T::Multiset {
            keyword,
            element_type,
        } => {
            let kw = *keyword.value();
            let item = copy_macro_type(element_type.inner(), replacements, scope)?;
            let group = PGrouped::new(
                token!(element_type.left()),
                item,
                token!(element_type.right()),
                element_type.position().clone(),
            );
            let keyword = token!(keyword);
            match kw {
                super::parse_ast_keyword::PKw::Seq => T::Seq {
                    keyword,
                    element_type: group,
                },
                super::parse_ast_keyword::PKw::Set => T::Set {
                    keyword,
                    element_type: group,
                },
                _ => T::Multiset {
                    keyword,
                    element_type: group,
                },
            }
        }
        T::Map { keyword, types } => {
            let pair = types.inner();
            let copy = PPairArgument::new(
                copy_macro_type(pair.first(), replacements, scope)?,
                token!(pair.comma()),
                copy_macro_type(pair.second(), replacements, scope)?,
                pair.position().clone(),
            );
            T::Map {
                keyword: token!(keyword),
                types: PGrouped::new(
                    token!(types.left()),
                    copy,
                    token!(types.right()),
                    types.position().clone(),
                ),
            }
        }
        _ => {
            return Err(MacroError {
                message: "macro type product requires unsupported reconstruction".into(),
                pos,
            });
        }
    };
    Ok(PTypeHandle::new(kind, pos))
}

fn copy_macro_bound_variables(
    vars: &super::parse_ast::PLogicalVars,
    replacements: &HashMap<String, PExpHandle>,
    scope: &std::cell::RefCell<MacroCopyScope>,
    binder: bool,
) -> Result<(super::parse_ast::PLogicalVars, HashMap<String, PExpHandle>), MacroError> {
    use super::parse_ast::{PDeclaration, PDeclarationHandle, PIdnDef, PNode};
    use super::parse_ast_keyword::{PDelimited, PReserved};
    let mut inner = replacements.clone();
    let mut copies = Vec::new();
    for var in vars.to_seq() {
        let (decl, pos) = {
            let node = var.node().read().expect("poisoned parse node");
            let PNodeKind::Declaration(decl) = &node.kind else {
                return Err(MacroError {
                    message: "macro binder declaration expected".into(),
                    pos: node.pos.clone(),
                });
            };
            (decl.clone(), node.pos.clone())
        };
        let (old_name, name_pos) = {
            let node = decl.idndef.read().expect("poisoned parse node");
            let PNodeKind::IdnDef(id) = &node.kind else {
                return Err(MacroError {
                    message: "macro binder name expected".into(),
                    pos: node.pos.clone(),
                });
            };
            (id.name.clone(), node.pos.clone())
        };
        let new_name = {
            let mut state = scope.borrow_mut();
            let name = if !state.preserve_names && state.names.contains(&old_name) {
                let names = state.names.clone();
                state.fresh.fresh(&old_name, &names)
            } else {
                old_name.clone()
            };
            state.names.insert(name.clone());
            if name != old_name {
                state.renames.insert(old_name.clone(), name.clone());
            }
            name
        };
        if binder {
            inner.remove(&new_name);
        }
        let idndef = PNode::new(PNodeKind::IdnDef(PIdnDef { name: new_name }), name_pos);
        copies.push((decl, idndef, pos, scope.borrow().renames.clone()));
    }
    let copies = copies
        .into_iter()
        .map(|(decl, idndef, pos, renames)| {
            let type_scope = std::cell::RefCell::new(MacroCopyScope {
                renames,
                preserve_names: true,
                ..Default::default()
            });
            Ok(PDeclarationHandle::new(
                PDeclaration {
                    kind: decl.kind,
                    idndef,
                    colon: PReserved::new(*decl.colon.value(), decl.colon.position().clone()),
                    typ: copy_macro_type(&decl.typ, &inner, &type_scope)?,
                },
                pos,
            ))
        })
        .collect::<Result<Vec<_>, MacroError>>()?;
    let mut items = copies.into_iter();
    let first = items.next();
    let rest = vars
        .inner
        .iter()
        .map(|(comma, _)| {
            (
                PReserved::new(*comma.value(), comma.position().clone()),
                items.next().expect("binder count"),
            )
        })
        .collect();
    let end = vars
        .end
        .as_ref()
        .map(|comma| PReserved::new(*comma.value(), comma.position().clone()));
    Ok((
        PDelimited::new(first, rest, end, vars.position().clone()),
        inner,
    ))
}

/// Duplicate expression products without sharing mutable parse nodes. Quantifier binders
/// are copied with fresh names; unsupported products fail explicitly.
fn copy_expression(
    input: &PExpHandle,
    replacements: &HashMap<String, PExpHandle>,
    scope: &std::cell::RefCell<MacroCopyScope>,
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
        let renamed = scope
            .borrow()
            .renames
            .get(&id.name)
            .cloned()
            .unwrap_or_else(|| id.name.clone());
        let name = if let Some(replacement) = replacements.get(&renamed) {
            let original = replacement.clone();
            let replacement = replacement.node().read().expect("poisoned parse node");
            let PNodeKind::Expression(super::parse_ast::PExpression {
                kind: E::IdnUse { idnref },
                ..
            }) = &replacement.kind
            else {
                return Err(MacroError {
                    message: non_expression_substitution(
                        &original,
                        scope
                            .borrow()
                            .expression_call_position
                            .as_ref()
                            .unwrap_or(&n.pos.0),
                    )
                    .unwrap_or_else(|| {
                        "macro expansion requires an identifier in this position".into()
                    }),
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
            renamed
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
            copy_expression(&$value, replacements, scope)?
        };
    }
    let kind = match expression.kind {
        E::Extension(extension) => {
            use crate::plugin::sif::sifp_ast_extensions::{PSifExpression, PSifKind};
            use crate::plugin::standard::predicateinstance::predicate_instance_past_extension::PPredicateInstance;
            if let Some(instance) = extension.as_any().downcast_ref::<PPredicateInstance>() {
                return Ok(PPredicateInstance {
                    marker: PReserved::new(
                        instance.marker.value().clone(),
                        instance.marker.position().clone(),
                    ),
                    idnuse: copy_ref(&instance.idnuse)?,
                    args: copy_expression_arguments(&instance.args, replacements, scope)?,
                    pos: instance.pos.clone(),
                }
                .expression());
            }
            if let Some(clause) = extension.as_any().downcast_ref::<crate::plugin::standard::termination::termination_past_extension::PDecreasesClause>() {
                use crate::plugin::standard::termination::termination_past_extension::{PDecreasesClause, PDecreasesKind};
                let copy_condition = |condition: &Option<(PReserved<crate::plugin::standard::termination::termination_past_extension::PIfKeyword>, PExpHandle)>| -> Result<_, MacroError> {
                    condition.as_ref().map(|(keyword, exp)| Ok((PReserved::new(keyword.value().clone(), keyword.position().clone()), copy_expression(exp, replacements, scope)?))).transpose()
                };
                let kind = match &clause.kind {
                    PDecreasesKind::Tuple { tuple, condition } => {
                        let first = tuple.first.as_ref().map(|e| copy_expression(e, replacements, scope)).transpose()?;
                        let rest = tuple.inner.iter().map(|(comma, exp)| Ok((PReserved::new(*comma.value(), comma.position().clone()), copy_expression(exp, replacements, scope)?))).collect::<Result<Vec<_>, MacroError>>()?;
                        let end = tuple.end.as_ref().map(|comma| PReserved::new(*comma.value(), comma.position().clone()));
                        PDecreasesKind::Tuple { tuple: PDelimited::new(first, rest, end, tuple.position().clone()), condition: copy_condition(condition)? }
                    }
                    PDecreasesKind::Wildcard { wildcard, condition } => PDecreasesKind::Wildcard { wildcard: PReserved::new(wildcard.value().clone(), wildcard.position().clone()), condition: copy_condition(condition)? },
                    PDecreasesKind::Star { star } => PDecreasesKind::Star { star: PReserved::new(*star.value(), star.position().clone()) },
                };
                return Ok(PDecreasesClause { kind, pos: clause.pos.clone() }.expression());
            }
            if let Some(sif) = extension.as_any().downcast_ref::<PSifExpression>() {
                let kind = match &sif.kind {
                    PSifKind::Low(e) => PSifKind::Low(copy_expression(e, replacements, scope)?),
                    PSifKind::LowEvent => PSifKind::LowEvent,
                    PSifKind::Rel { exp, index } => PSifKind::Rel {
                        exp: copy_expression(exp, replacements, scope)?,
                        index: copy_expression(index, replacements, scope)?,
                    },
                };
                return Ok(PSifExpression {
                    kind,
                    pos: sif.pos.clone(),
                }
                .expression());
            }
            if let Some(expression) = extension.copy_macro_expression(
                &|child| copy_expression(child, replacements, scope),
                &copy_ref,
            )? {
                return Ok(expression);
            }
            return Err(MacroError {
                message: "extension expression in macro requires reconstruction".into(),
                pos,
            });
        }
        E::AnnotatedExp {
            annotation,
            expression,
        } => E::AnnotatedExp {
            annotation: copy_macro_annotation(&annotation),
            expression: copy_expression(&expression, replacements, scope)?,
        },
        E::Let {
            keyword,
            variable,
            eq,
            exp,
            in_token,
            nested_scope,
            ..
        } => {
            let (old_name, name_pos) = {
                let n = variable.read().expect("poisoned parse node");
                let PNodeKind::IdnDef(id) = &n.kind else {
                    return Err(MacroError {
                        message: "let macro binder name expected".into(),
                        pos: n.pos.clone(),
                    });
                };
                (id.name.clone(), n.pos.clone())
            };
            let new_name = {
                let mut state = scope.borrow_mut();
                let name = if !state.preserve_names && state.names.contains(&old_name) {
                    let names = state.names.clone();
                    state.fresh.fresh(&old_name, &names)
                } else {
                    old_name.clone()
                };
                state.names.insert(name.clone());
                if name != old_name {
                    state.renames.insert(old_name.clone(), name.clone());
                }
                name
            };
            let inner = replacements.clone();
            let variable = PNode::new(
                PNodeKind::IdnDef(super::parse_ast::PIdnDef { name: new_name }),
                name_pos,
            );
            let (body, nested_pos) = {
                let nested = nested_scope.read().expect("poisoned parse node");
                let PNodeKind::LetNestedScope { body } = &nested.kind else {
                    return Err(MacroError {
                        message: "let macro nested scope expected".into(),
                        pos: nested.pos.clone(),
                    });
                };
                (body.clone(), nested.pos.clone())
            };
            let exp = copy_expression_group(&exp, &inner, scope)?;
            let body = copy_expression(&body, &inner, scope)?;
            let nested_scope = PNode::new(PNodeKind::LetNestedScope { body }, nested_pos);
            E::Let {
                keyword: token!(keyword),
                variable,
                eq: token!(eq),
                exp,
                in_token: token!(in_token),
                nested_scope,
                scope_id: super::parse_ast::fresh_scope_id(),
            }
        }
        E::Forall(q) | E::Exists(q) => {
            let is_forall = *q.keyword.value() == super::parse_ast_keyword::PKw::Forall;
            let (vars, inner) = copy_macro_bound_variables(&q.vars, replacements, scope, true)?;
            let triggers = q
                .triggers
                .iter()
                .map(|trigger| {
                    Ok(super::parse_ast::PTrigger::new(
                        copy_expression_arguments(trigger.expressions(), &inner, scope)?,
                        trigger.position().clone(),
                    ))
                })
                .collect::<Result<Vec<_>, MacroError>>()?;
            let q = super::parse_ast::PQuantifier {
                keyword: token!(q.keyword),
                vars,
                colons: token!(q.colons),
                triggers,
                body: copy_expression(&q.body, &inner, scope)?,
                scope_id: super::parse_ast::fresh_scope_id(),
            };
            if is_forall {
                E::Forall(q)
            } else {
                E::Exists(q)
            }
        }
        E::ForPerm {
            keyword,
            vars,
            trigger,
            colons,
            body,
            ..
        } => {
            let (vars, inner) = copy_macro_bound_variables(&vars, replacements, scope, true)?;
            E::ForPerm {
                keyword: token!(keyword),
                vars,
                trigger: super::parse_ast::PPermTrigger::new(copy_expression_group(
                    trigger.access(),
                    &inner,
                    scope,
                )?),
                colons: token!(colons),
                body: copy_expression(&body, &inner, scope)?,
                scope_id: super::parse_ast::fresh_scope_id(),
            }
        }
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
            let name = scope.borrow().renames.get(&name).cloned().unwrap_or(name);
            if let Some(replacement) = replacements.get(&name) {
                return copy_expression(
                    replacement,
                    &HashMap::new(),
                    &std::cell::RefCell::new(MacroCopyScope {
                        preserve_names: true,
                        ..Default::default()
                    }),
                );
            }
            E::IdnUse {
                idnref: copy_ref(&idnref)?,
            }
        }
        E::VersionedIdnUse {
            mut idnref,
            version,
            separator,
        } => {
            // Scala's renamer visits PIdnUse, but its expression replacer only
            // substitutes PIdnUseExp, not PVersionedIdnUseExp.
            if let Some(name) = scope.borrow().renames.get(&idnref.name) {
                idnref.name = name.clone();
            }
            let mut fresh = PIdnRef::with_class(idnref.name, idnref.declaration_class);
            fresh.assign_use = idnref.assign_use;
            E::VersionedIdnUse {
                idnref: fresh,
                version,
                separator,
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
            exp: copy_expression(&exp, replacements, scope)?,
        },
        E::BinExp { left, op, right } => E::BinExp {
            left: copy_expression(&left, replacements, scope)?,
            op: PReserved::new(op.value().clone(), op.position().clone()),
            right: copy_expression(&right, replacements, scope)?,
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
                .map(|e| copy_expression(e, replacements, scope))
                .transpose()?,
            dots: token!(dots),
            end: end
                .as_ref()
                .map(|e| copy_expression(e, replacements, scope))
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
            resource: copy_expression_group(&resource, replacements, scope)?,
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
                exp: copy_expression_group(&exp, replacements, scope)?,
            }
        }
        E::DebugLabelledOldExp { op, label, exp } => E::DebugLabelledOldExp {
            op: token!(op),
            label: copied!(label),
            exp: copied!(exp),
        },
        E::NewExp { keyword, fields } => {
            use super::parse_ast::PNewFields;
            let contents = match fields.inner() {
                PNewFields::All(star) => PNewFields::All(token!(star)),
                PNewFields::Fields(old) => {
                    let first = old.first.as_ref().map(&copy_ref).transpose()?;
                    let inner = old
                        .inner
                        .iter()
                        .map(|(comma, field)| Ok((token!(comma), copy_ref(field)?)))
                        .collect::<Result<Vec<_>, MacroError>>()?;
                    let end = old.end.as_ref().map(|comma| token!(comma));
                    PNewFields::Fields(PDelimited::new(first, inner, end, old.position().clone()))
                }
            };
            E::NewExp {
                keyword: token!(keyword),
                fields: PGrouped::new(
                    token!(fields.left()),
                    contents,
                    token!(fields.right()),
                    fields.position().clone(),
                ),
            }
        }
        E::MapDomain { keyword, base } => E::MapDomain {
            keyword: token!(keyword),
            base: copy_expression_group(&base, replacements, scope)?,
        },
        E::MapRange { keyword, base } => E::MapRange {
            keyword: token!(keyword),
            base: copy_expression_group(&base, replacements, scope)?,
        },
        E::AccPred { op, amount } => {
            let pair = amount.inner();
            let first = copy_expression(pair.first(), replacements, scope)?;
            let second = pair
                .second()
                .map(|(comma, exp)| Ok((token!(comma), copy_expression(exp, replacements, scope)?)))
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
                copy_expression_arguments(collection.call_args(), replacements, scope)?,
            );
            match op {
                super::parse_ast_keyword::PKwOp::Seq => E::ExplicitSeq(collection),
                super::parse_ast_keyword::PKwOp::Set => E::ExplicitSet(collection),
                _ => E::ExplicitMultiset(collection),
            }
        }
        E::ExplicitMap(collection) => E::ExplicitMap(super::parse_ast::PExplicitMap {
            op: token!(collection.op),
            call_args: copy_expression_arguments(&collection.call_args, replacements, scope)?,
        }),
        E::EmptySeq(collection) | E::EmptySet(collection) | E::EmptyMultiset(collection) => {
            let op = *collection.op.value();
            let collection = super::parse_ast::PEmptyCollection {
                op: token!(collection.op),
                annotated_type: collection
                    .annotated_type
                    .map(|group| {
                        Ok::<_, MacroError>(PGrouped::new(
                            token!(group.left()),
                            copy_macro_type(group.inner(), replacements, scope)?,
                            token!(group.right()),
                            group.position().clone(),
                        ))
                    })
                    .transpose()?,
                call_args: copy_expression_arguments(&collection.call_args, replacements, scope)?,
            };
            match op {
                super::parse_ast_keyword::PKwOp::Seq => E::EmptySeq(collection),
                super::parse_ast_keyword::PKwOp::Set => E::EmptySet(collection),
                _ => E::EmptyMultiset(collection),
            }
        }
        E::EmptyMap {
            op,
            annotated_type,
            call_args,
        } => E::EmptyMap {
            op: token!(op),
            annotated_type: annotated_type
                .map(|group| {
                    let pair = group.inner();
                    let pair = super::parse_ast::PPairArgument::new(
                        copy_macro_type(pair.first(), replacements, scope)?,
                        token!(pair.comma()),
                        copy_macro_type(pair.second(), replacements, scope)?,
                        pair.position().clone(),
                    );
                    Ok::<_, MacroError>(PGrouped::new(
                        token!(group.left()),
                        pair,
                        token!(group.right()),
                        group.position().clone(),
                    ))
                })
                .transpose()?,
            call_args: copy_expression_arguments(&call_args, replacements, scope)?,
        },
        E::CondExp {
            cond,
            question,
            thn,
            colon,
            els,
        } => E::CondExp {
            cond: copy_expression(&cond, replacements, scope)?,
            question: PReserved::new(*question.value(), question.position().clone()),
            thn: copy_expression(&thn, replacements, scope)?,
            colon: PReserved::new(*colon.value(), colon.position().clone()),
            els: copy_expression(&els, replacements, scope)?,
        },
        E::FieldAccess {
            receiver,
            dot,
            idnref,
            ..
        } => E::FieldAccess {
            receiver: copy_expression(&receiver, replacements, scope)?,
            dot: PReserved::new(*dot.value(), dot.position().clone()),
            idnref: copy_ref(&idnref)?,
            adt_type_renaming: None,
            adt_substitution: None,
        },
        E::Call {
            idnref,
            call_args,
            type_annotated,
            ..
        } => {
            let old = call_args.inner();
            let first = old
                .first
                .as_ref()
                .map(|e| copy_expression(e, replacements, scope))
                .transpose()?;
            let rest = old
                .inner
                .iter()
                .map(|(comma, e)| {
                    Ok((
                        PReserved::new(*comma.value(), comma.position().clone()),
                        copy_expression(e, replacements, scope)?,
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
                type_annotated: type_annotated
                    .map(|(colon, typ)| {
                        Ok::<_, MacroError>((
                            token!(colon),
                            copy_macro_type(&typ, replacements, scope)?,
                        ))
                    })
                    .transpose()?,
                extra_local_type_variables: vec![],
                domain_type_renaming: None,
                domain_substitution: None,
            }
        }
    };
    Ok(PExpHandle::new(PExpression::from_kind(kind), pos))
}

fn copy_macro_reference(
    input: &super::parse_ast::PNodeHandle,
    replacements: &HashMap<String, PExpHandle>,
    scope: &std::cell::RefCell<MacroCopyScope>,
) -> Result<super::parse_ast::PNodeHandle, MacroError> {
    use super::parse_ast::PNode;
    let node = input.read().expect("poisoned parse node");
    let PNodeKind::IdnRef(reference) = &node.kind else {
        return Err(MacroError {
            message: "macro identifier expected".into(),
            pos: node.pos.clone(),
        });
    };
    let mut reference = reference.clone();
    reference.name = scope
        .borrow()
        .renames
        .get(&reference.name)
        .cloned()
        .unwrap_or(reference.name);
    if let Some(value) = replacements.get(&reference.name) {
        let original = value.clone();
        let value = value.node().read().expect("poisoned parse node");
        let PNodeKind::Expression(super::parse_ast::PExpression {
            kind: super::parse_ast::PExpressionKind::IdnUse { idnref },
            ..
        }) = &value.kind
        else {
            return Err(MacroError {
                message: non_expression_substitution(&original, &node.pos.0).unwrap_or_else(|| {
                    "macro expansion requires an identifier in this position".into()
                }),
                pos: value.pos.clone(),
            });
        };
        let idn = idnref.read().expect("poisoned parse node");
        let PNodeKind::IdnRef(idn) = &idn.kind else {
            return Err(MacroError {
                message: "macro identifier expected".into(),
                pos: value.pos.clone(),
            });
        };
        reference.name = idn.name.clone();
    }
    Ok(PNode::new(PNodeKind::IdnRef(reference), node.pos.clone()))
}

fn copy_macro_specs(
    old: &super::parse_ast_keyword::PDelimited<
        super::parse_ast::PSpecification,
        super::parse_ast::OptionalSemi,
    >,
    replacements: &HashMap<String, PExpHandle>,
    scope: &std::cell::RefCell<MacroCopyScope>,
) -> Result<
    super::parse_ast_keyword::PDelimited<
        super::parse_ast::PSpecification,
        super::parse_ast::OptionalSemi,
    >,
    MacroError,
> {
    use super::parse_ast::{PSpecification, PSpecificationKeyword};
    use super::parse_ast_keyword::{ND, PDelimited, PReserved};
    let mut copies = Vec::new();
    for spec in old.to_seq() {
        let key = match &spec.keyword {
            PSpecificationKeyword::Builtin(token) => PSpecificationKeyword::Builtin(
                PReserved::new(*token.value(), token.position().clone()),
            ),
            PSpecificationKeyword::Extension(token) => PSpecificationKeyword::Extension(
                PReserved::new(token.value().clone(), token.position().clone()),
            ),
        };
        copies.push(PSpecification::new(
            key,
            copy_expression(&spec.exp, replacements, scope)?,
            spec.pos.clone(),
        ));
    }
    let mut items = copies.into_iter();
    let first = items.next();
    let rest = old
        .inner
        .iter()
        .map(|(d, _)| {
            (
                ND(d.0
                    .as_ref()
                    .map(|t| PReserved::new(*t.value(), t.position().clone()))),
                items.next().expect("specification count"),
            )
        })
        .collect();
    let end = old.end.as_ref().map(|d| {
        ND(d.0
            .as_ref()
            .map(|t| PReserved::new(*t.value(), t.position().clone())))
    });
    Ok(PDelimited::new(first, rest, end, old.position().clone()))
}

/// Reconstruct supported statement products, freshening declared names as they enter scope.
fn copy_macro_statement(
    input: &super::parse_ast::PStmtHandle,
    replacements: &HashMap<String, PExpHandle>,
    root: bool,
    scope: &std::cell::RefCell<MacroCopyScope>,
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
    let is_macro_sequence = matches!(&kind, S::MacroSeqn { .. });
    let kind = match kind {
        S::Extension(extension) => {
            use crate::plugin::standard::refute::refute_past_extension::PRefute;
            use crate::plugin::standard::smoke::unreachable_past_extension::PUnreachable;
            if let Some(refute) = extension.as_any().downcast_ref::<PRefute>() {
                return Ok(PRefute {
                    keyword: PReserved::new(
                        refute.keyword.value().clone(),
                        refute.keyword.position().clone(),
                    ),
                    expression: copy_expression(&refute.expression, replacements, scope)?,
                    pos: refute.pos.clone(),
                }
                .statement());
            }
            if let Some(unreachable) = extension.as_any().downcast_ref::<PUnreachable>() {
                return Ok(PUnreachable {
                    keyword: PReserved::new(
                        unreachable.keyword.value().clone(),
                        unreachable.keyword.position().clone(),
                    ),
                    pos: unreachable.pos.clone(),
                }
                .statement());
            }
            if let Some(statement) = extension.copy_macro_statement(&|child| {
                copy_macro_statement(child, replacements, false, scope)
            })? {
                return Ok(statement);
            }
            return Err(MacroError {
                message: "extension statement in macro requires reconstruction".into(),
                pos,
            });
        }
        S::Annotated { annotation, stmt } => S::Annotated {
            annotation: copy_macro_annotation(&annotation),
            stmt: copy_macro_statement(&stmt, replacements, false, scope)?,
        },
        S::Vars {
            keyword,
            vars,
            init,
        } => {
            let (vars, inner) = copy_macro_bound_variables(&vars, replacements, scope, false)?;
            let init = init
                .map(|(op, exp)| Ok((token!(op), copy_expression(&exp, &inner, scope)?)))
                .transpose()?;
            S::Vars {
                keyword: token!(keyword),
                vars,
                init,
            }
        }
        S::Label {
            keyword,
            idndef,
            invs,
        } => {
            use super::parse_ast::{PExpression, PExpressionKind, PIdnDef, PNode};
            let (old_name, name_pos) = {
                let n = idndef.read().expect("poisoned parse node");
                let PNodeKind::IdnDef(id) = &n.kind else {
                    return Err(MacroError {
                        message: "label name expected".into(),
                        pos: n.pos.clone(),
                    });
                };
                (id.name.clone(), n.pos.clone())
            };
            let mut name = {
                let mut state = scope.borrow_mut();
                let name = if !state.preserve_names && state.names.contains(&old_name) {
                    let names = state.names.clone();
                    state.fresh.fresh(&old_name, &names)
                } else {
                    old_name.clone()
                };
                state.names.insert(name.clone());
                if name != old_name {
                    state.renames.insert(old_name.clone(), name.clone());
                }
                name
            };
            let mut label_replacements = replacements.clone();
            if let Some(value) = replacements.get(&name) {
                let original = value.clone();
                let value = value.node().read().expect("poisoned parse node");
                let PNodeKind::Expression(PExpression {
                    kind: PExpressionKind::IdnUse { idnref },
                    ..
                }) = &value.kind
                else {
                    return Err(MacroError {
                        message: non_expression_substitution(&original, &name_pos.0)
                            .unwrap_or_else(|| {
                                "macro label replacement requires an identifier".into()
                            }),
                        pos: value.pos.clone(),
                    });
                };
                let id = idnref.read().expect("poisoned parse node");
                let PNodeKind::IdnRef(id) = &id.kind else {
                    return Err(MacroError {
                        message: "macro identifier expected".into(),
                        pos: value.pos.clone(),
                    });
                };
                name = id.name.clone();
                label_replacements.clear();
            }
            let idndef = PNode::new(PNodeKind::IdnDef(PIdnDef { name }), name_pos);
            let invs = copy_macro_specs(&invs, &label_replacements, scope)?;
            S::Label {
                keyword: token!(keyword),
                idndef,
                invs,
            }
        }
        S::Seqn { statements, .. } | S::MacroSeqn { statements } => {
            let old = statements.inner();
            let items = old
                .to_seq()
                .into_iter()
                .map(|stmt| copy_macro_statement(stmt, replacements, false, scope))
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
            if root || is_macro_sequence {
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
            exp: copy_expression(&exp, replacements, scope)?,
        },
        S::Assume { keyword, exp } => S::Assume {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements, scope)?,
        },
        S::Inhale { keyword, exp } => S::Inhale {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements, scope)?,
        },
        S::Exhale { keyword, exp } => S::Exhale {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements, scope)?,
        },
        S::Fold { keyword, exp } => S::Fold {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements, scope)?,
        },
        S::Unfold { keyword, exp } => S::Unfold {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements, scope)?,
        },
        S::PackageWand {
            keyword,
            exp,
            proof_script,
        } => S::PackageWand {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements, scope)?,
            proof_script: proof_script
                .as_ref()
                .map(|body| copy_macro_statement(body, replacements, false, scope))
                .transpose()?,
        },
        S::ApplyWand { keyword, exp } => S::ApplyWand {
            keyword: token!(keyword),
            exp: copy_expression(&exp, replacements, scope)?,
        },
        S::Quasihavoc { keyword, lhs, exp } => S::Quasihavoc {
            keyword: token!(keyword),
            lhs: lhs
                .as_ref()
                .map(|(guard, op)| Ok((copy_expression(guard, replacements, scope)?, token!(op))))
                .transpose()?,
            exp: copy_expression(&exp, replacements, scope)?,
        },
        S::Quasihavocall {
            keyword,
            vars,
            colons,
            lhs,
            exp,
            ..
        } => {
            let (vars, inner) = copy_macro_bound_variables(&vars, replacements, scope, true)?;
            S::Quasihavocall {
                keyword: token!(keyword),
                vars,
                colons: token!(colons),
                lhs: lhs
                    .as_ref()
                    .map(|(guard, op)| Ok((copy_expression(guard, &inner, scope)?, token!(op))))
                    .transpose()?,
                exp: copy_expression(&exp, &inner, scope)?,
                scope_id: super::parse_ast::fresh_scope_id(),
            }
        }
        S::Assign { targets, op, rhs } => {
            let first = targets
                .first
                .as_ref()
                .map(|e| copy_expression(e, replacements, scope))
                .transpose()?;
            let inner = targets
                .inner
                .iter()
                .map(|(delimiter, exp)| {
                    Ok((
                        token!(delimiter),
                        copy_expression(exp, replacements, scope)?,
                    ))
                })
                .collect::<Result<Vec<_>, MacroError>>()?;
            let end = targets.end.as_ref().map(|delimiter| token!(delimiter));
            S::Assign {
                targets: PDelimited::new(first, inner, end, targets.position().clone()),
                op: op.as_ref().map(|t| token!(t)),
                rhs: copy_expression(&rhs, replacements, scope)?,
            }
        }
        S::If {
            keyword,
            cond,
            thn,
            els,
        } => S::If {
            keyword: token!(keyword),
            cond: copy_expression_group(&cond, replacements, scope)?,
            thn: copy_macro_statement(&thn, replacements, false, scope)?,
            els: els
                .as_ref()
                .map(|stmt| copy_macro_statement(stmt, replacements, false, scope))
                .transpose()?,
        },
        S::While {
            keyword,
            cond,
            invs,
            body,
        } => {
            let cond = copy_expression_group(&cond, replacements, scope)?;
            let invs = super::parse_ast::PSpecs::new(
                copy_macro_specs(&invs.specs, replacements, scope)?,
                invs.pos.clone(),
            );
            S::While {
                keyword: token!(keyword),
                cond,
                invs,
                body: copy_macro_statement(&body, replacements, false, scope)?,
            }
        }
        S::Else { keyword, els } => S::Else {
            keyword: token!(keyword),
            els: copy_macro_statement(&els, replacements, false, scope)?,
        },
        S::Goto { keyword, target } => S::Goto {
            keyword: token!(keyword),
            target: copy_macro_reference(&target, replacements, scope)?,
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
    if let PNodeKind::Program(root) = &mut program.node().write().expect("poisoned parse node").kind
    {
        root.local_errors.extend(reports);
    }
    fn collect_proof_script_definitions(
        node: &PNodeHandle,
        inside_wand: bool,
        reports: &mut Vec<crate::verifier::verification_result::ParseReport>,
    ) -> Result<(), MacroError> {
        let (kind, pos) = {
            let node = node.read().expect("poisoned parse node");
            (node.kind.clone(), node.pos.clone())
        };
        if inside_wand {
            if let PNodeKind::Statement(super::parse_ast::PStatement {
                kind: super::parse_ast::PStatementKind::MacroDefinition(member),
            }) = &kind
            {
                let position = member
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .error_position();
                reports.push(crate::verifier::verification_result::ParseReport::Error(
                    crate::verifier::verification_result::ParseError::new(
                        "macros cannot be defined inside magic wands proof scripts",
                        position,
                    ),
                ));
            }
        }
        let inside_wand = inside_wand
            || matches!(
                kind,
                PNodeKind::Statement(super::parse_ast::PStatement {
                    kind: super::parse_ast::PStatementKind::PackageWand { .. }
                })
            );
        for child in subnodes(node).map_err(|e| MacroError {
            message: format!("macro validation traversal: {e:?}"),
            pos: pos.clone(),
        })? {
            collect_proof_script_definitions(&child, inside_wand, reports)?;
        }
        Ok(())
    }
    let mut proof_reports = Vec::new();
    collect_proof_script_definitions(program.node(), false, &mut proof_reports)?;
    if let PNodeKind::Program(root) = &mut program.node().write().expect("poisoned parse node").kind
    {
        root.local_errors.extend(proof_reports);
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
        if let PNodeKind::Statement(super::parse_ast::PStatement {
            kind: super::parse_ast::PStatementKind::Label { idndef, .. },
        }) = &kind
        {
            if let PNodeKind::IdnDef(id) = &idndef.read().expect("poisoned parse node").kind {
                if !inner_bound.contains(&id.name) {
                    free.insert(id.name.clone());
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
        let definition_pos = member
            .node()
            .read()
            .expect("poisoned parse node")
            .pos
            .clone();
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
                    // Scala's small immutable sets preserve insertion order; use a
                    // deterministic native order for the erased larger-set case too.
                    let mut unused = Vec::new();
                    for parameter in parameters.as_ref().into_iter().flatten() {
                        if !free.contains(parameter) && !unused.contains(parameter) {
                            unused.push(parameter.clone());
                        }
                    }
                    if !unused.is_empty() {
                        warnings.push(crate::verifier::verification_result::ParseReport::Warning(crate::verifier::verification_result::ParseWarning::new(format!("in macro `{name}`, the following parameters were defined but not used: {}", unused.join(", ")), error_position)));
                    }
                    let definition = ExpressionMacro {
                        parameters,
                        body: body.body().clone(),
                        pos: definition_pos,
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
        register(member, &mut definitions, &mut warnings, true)?;
    }
    fn adapt_position(
        node: &PNodeHandle,
        pos: &super::parse_ast_keyword::Span,
    ) -> Result<(), MacroError> {
        // Silver's adaptation follows direct product children. Quantifier
        // triggers are held in a sequence, so their original positions survive.
        if matches!(
            &node.read().expect("poisoned parse node").kind,
            PNodeKind::Trigger { .. }
        ) {
            return Ok(());
        }
        for child in subnodes(node).map_err(|e| MacroError {
            message: format!("macro position traversal: {e:?}"),
            pos: pos.clone(),
        })? {
            adapt_position(&child, pos)?;
        }
        node.write().expect("poisoned parse node").pos = pos.clone();
        Ok(())
    }
    fn collect_scope_names(
        node: &PNodeHandle,
        names: &mut HashSet<String>,
    ) -> Result<(), MacroError> {
        let (kind, pos) = {
            let node = node.read().expect("poisoned parse node");
            (node.kind.clone(), node.pos.clone())
        };
        if matches!(
            kind,
            PNodeKind::Member(super::parse_ast::PMember {
                kind: PMemberKind::Define { .. },
                ..
            })
        ) {
            return Ok(());
        }
        if let PNodeKind::IdnDef(id) = kind {
            names.insert(id.name);
        }
        for child in subnodes(node).map_err(|e| MacroError {
            message: format!("macro scope traversal: {e:?}"),
            pos: pos.clone(),
        })? {
            collect_scope_names(&child, names)?;
        }
        Ok(())
    }
    fn walk(
        node: &PNodeHandle,
        definitions: &HashMap<String, ExpressionMacro>,
        stack: &mut Vec<String>,
        warnings: &mut Vec<crate::verifier::verification_result::ParseReport>,
        scope: &std::cell::RefCell<MacroCopyScope>,
    ) -> Result<(), MacroError> {
        let (kind, pos) = {
            let node = node.read().expect("poisoned parse node");
            (node.kind.clone(), node.pos.clone())
        };
        // These operands have narrower source AST types than arbitrary expressions.
        let constrained_macro_operand = if let PNodeKind::Expression(expression) = &kind {
            let (operand, location) = match &expression.kind {
                PExpressionKind::CurrentPerm { resource, .. } => (Some(resource.inner()), true),
                PExpressionKind::AccPred { amount, .. } => (Some(amount.inner().first()), true),
                PExpressionKind::Unfolding { acc, .. } => (Some(acc), false),
                _ => (None, false),
            };
            operand.and_then(|operand| {
                let kind = operand.node().read().expect("poisoned parse node").kind.clone();
                let reference = match kind {
                    PNodeKind::Expression(super::parse_ast::PExpression { kind: PExpressionKind::Call { idnref, .. } | PExpressionKind::IdnUse { idnref }, .. }) => idnref,
                    _ => return None,
                };
                let is_macro = match &reference.read().expect("poisoned parse node").kind {
                    PNodeKind::IdnRef(id) => definitions.contains_key(&id.name),
                    _ => false,
                };
                is_macro.then(|| (operand.clone(), location))
            })
        } else {
            None
        };
        if let PNodeKind::Program(program) = &kind {
            // Scala expands imported PPrograms independently and catches each
            // MacroException at that program boundary before processing siblings.
            for imported in &program.imported {
                let mut imported_warnings = Vec::new();
                let result = walk(
                    imported.node(),
                    definitions,
                    &mut Vec::new(),
                    &mut imported_warnings,
                    scope,
                );
                let error_report = result.err().map(|error| {
                    let position = error.error_position(imported);
                    crate::verifier::verification_result::ParseReport::Error(
                        crate::verifier::verification_result::ParseError::new(
                            error.message,
                            position,
                        ),
                    )
                });
                if let PNodeKind::Program(child) =
                    &mut imported.node().write().expect("poisoned parse node").kind
                {
                    child.local_errors.extend(imported_warnings);
                    child.local_errors.extend(error_report);
                }
            }
            for member in &program.members {
                walk(member.node(), definitions, stack, warnings, scope)?;
            }
            return Ok(());
        }
        if matches!(
            &kind,
            PNodeKind::Member(super::parse_ast::PMember {
                kind: PMemberKind::Define { .. },
                ..
            })
        ) {
            return Ok(());
        }
        // Upstream expands only domains, functions, predicates and methods; other
        // member families are carried through unchanged.
        if matches!(
            &kind,
            PNodeKind::Member(super::parse_ast::PMember {
                kind: PMemberKind::Import { .. }
                    | PMemberKind::Fields { .. }
                    | PMemberKind::Extension(_),
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
            let mut method_names = scope.borrow().names.clone();
            collect_scope_names(node, &mut method_names)?;
            let method_scope = std::cell::RefCell::new(MacroCopyScope {
                names: method_names,
                fresh: FreshMacroNames::default(),
                preserve_names: false,
                renames: HashMap::new(),
                expression_call_position: None,
            });
            for (name, definition) in definitions {
                locals
                    .entry(name.clone())
                    .or_insert_with(|| definition.clone());
            }
            for child in subnodes(node).map_err(|e| MacroError {
                message: format!("macro traversal: {e:?}"),
                pos: pos.clone(),
            })? {
                walk(&child, &locals, stack, warnings, &method_scope)?;
            }
            return Ok(());
        }
        if matches!(
            &kind,
            PNodeKind::Member(super::parse_ast::PMember {
                kind: PMemberKind::Function { .. }
                    | PMemberKind::Predicate { .. }
                    | PMemberKind::Domain { .. },
                ..
            })
        ) {
            let mut member_names = scope.borrow().names.clone();
            collect_scope_names(node, &mut member_names)?;
            let member_scope = std::cell::RefCell::new(MacroCopyScope {
                names: member_names,
                fresh: FreshMacroNames::default(),
                preserve_names: false,
                renames: HashMap::new(),
                expression_call_position: None,
            });
            for child in subnodes(node).map_err(|e| MacroError {
                message: format!("macro traversal: {e:?}"),
                pos: pos.clone(),
            })? {
                walk(&child, definitions, stack, warnings, &member_scope)?;
            }
            return Ok(());
        }
        // The source MacroExpander validates calls in assignment targets before
        // ordinary expression expansion and before resolver/typechecker phases.
        if let PNodeKind::Statement(super::parse_ast::PStatement {
            kind:
                super::parse_ast::PStatementKind::Assign {
                    targets,
                    op: Some(_),
                    ..
                },
        }) = &kind
        {
            for target in targets.to_seq() {
                let (target_kind, call_pos) = {
                    let target = target.node().read().expect("poisoned parse node");
                    (target.kind.clone(), target.pos.clone())
                };
                let PNodeKind::Expression(super::parse_ast::PExpression {
                    kind:
                        PExpressionKind::Call {
                            idnref,
                            type_annotated,
                            ..
                        },
                    ..
                }) = target_kind
                else {
                    continue;
                };
                let name = match &idnref.read().expect("poisoned parse node").kind {
                    PNodeKind::IdnRef(reference) => reference.name.clone(),
                    _ => {
                        return Err(MacroError {
                            message: "macro identifier expected".into(),
                            pos: call_pos,
                        });
                    }
                };
                let is_macro = type_annotated.is_none()
                    && definitions
                        .get(&name)
                        .is_some_and(|definition| definition.parameters.is_some());
                if !is_macro {
                    return Err(MacroError { message: "The only calls that can be on the left-hand side of an assignment statement are calls to macros".into(), pos: call_pos });
                }
                walk(target.node(), definitions, stack, warnings, scope)?;
                let valid = matches!(
                    &target.node().read().expect("poisoned parse node").kind,
                    PNodeKind::Expression(super::parse_ast::PExpression {
                        kind: PExpressionKind::IdnUse { .. }
                            | PExpressionKind::FieldAccess { .. }
                            | PExpressionKind::Call { .. },
                        ..
                    })
                );
                if !valid {
                    return Err(MacroError { message: "The body of this macro is not a suitable left-hand side for an assignment statement".into(), pos: call_pos });
                }
            }
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
                                message: format!("Recursive macro declaration found: {name}"),
                                pos: def.pos.clone(),
                            });
                        }
                        if args.is_none() {
                            if let Some(parameters) = def.parameters.as_deref() {
                                return Err(MacroError {
                                    message: missing_macro_arguments(&name, parameters),
                                    pos,
                                });
                            }
                        }
                        if args.is_some() != def.parameters.is_some()
                            || args.as_ref().map(Vec::len) != def.parameters.as_ref().map(Vec::len)
                        {
                            return Err(MacroError {
                                message: "Number of macro arguments does not match".into(),
                                pos,
                            });
                        }
                        let PDefineBody::Statement(body) = &def.body else {
                            return Err(MacroError {
                                message: "Expression macro used in statement position".into(),
                                pos,
                            });
                        };
                        let replacements = map_parameters_to_arguments(
                            def.parameters.as_deref().unwrap_or_default(),
                            args.as_deref().unwrap_or_default(),
                        );
                        scope.borrow_mut().renames.clear();
                        let copy = copy_macro_statement(body, &replacements, true, scope)?;
                        adapt_position(copy.node(), &pos)?;
                        stack.push(name);
                        walk(copy.node(), definitions, stack, warnings, scope)?;
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
                        message: missing_macro_arguments(
                            &name,
                            definition
                                .parameters
                                .as_deref()
                                .expect("checked parameters"),
                        ),
                        pos,
                    });
                }
                return Err(MacroError {
                    message: match &definition.body {
                        PDefineBody::Expression(_) => "Expression macro used in type position",
                        PDefineBody::Statement(_) => "Statement macro used in type position",
                    }
                    .into(),
                    pos,
                });
            }
        }
        if let PNodeKind::IdnRef(reference) = &kind {
            if let Some(definition) = definitions.get(&reference.name) {
                let name = reference.name.clone();
                if definition.parameters.is_some() {
                    return Err(MacroError {
                        message: missing_macro_arguments(
                            &name,
                            definition
                                .parameters
                                .as_deref()
                                .expect("checked parameters"),
                        ),
                        pos,
                    });
                }
                if stack.contains(&name) {
                    return Err(MacroError {
                        message: format!("Recursive macro declaration found: {name}"),
                        pos: definition.pos.clone(),
                    });
                }
                let PDefineBody::Expression(body) = &definition.body else {
                    return Err(MacroError {
                        message: format!(
                            "statement macro `{name}` cannot be used as an identifier"
                        ),
                        pos,
                    });
                };
                scope.borrow_mut().renames.clear();
                let copy = copy_expression(body, &HashMap::new(), scope)?;
                stack.push(name.clone());
                walk(copy.node(), definitions, stack, warnings, scope)?;
                stack.pop();
                let copy = copy.node().read().expect("poisoned parse node");
                let PNodeKind::Expression(super::parse_ast::PExpression {
                    kind: PExpressionKind::IdnUse { idnref },
                    ..
                }) = &copy.kind
                else {
                    return Err(MacroError {
                        message: "Expression macro used in identifier position".into(),
                        pos,
                    });
                };
                let replacement = idnref.read().expect("poisoned parse node");
                let PNodeKind::IdnRef(replacement) = &replacement.kind else {
                    return Err(MacroError {
                        message: "macro identifier expected".into(),
                        pos,
                    });
                };
                let mut updated = reference.clone();
                updated.name = replacement.name.clone();
                node.write().expect("poisoned parse node").kind = PNodeKind::IdnRef(updated);
                return Ok(());
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
                                message: missing_macro_arguments(
                                    &name,
                                    def.parameters.as_deref().expect("checked parameters"),
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
                    message: format!("Recursive macro declaration found: {name}"),
                    pos: definitions[&name].pos.clone(),
                });
            }
            let def = &definitions[&name];
            let params = def.parameters.as_deref().unwrap_or_default();
            if params.len() != args.len() {
                return Err(MacroError {
                    message: "Number of macro arguments does not match".into(),
                    pos,
                });
            }
            // Arguments belong to the caller, not the expanded macro body. Expand
            // them before entering this declaration so Q(Q(x)) is not recursive.
            for arg in &args {
                walk(arg.node(), definitions, stack, warnings, scope)?;
            }
            let replacements = map_parameters_to_arguments(params, &args);
            let PDefineBody::Expression(body) = &def.body else {
                return Err(MacroError {
                    message: "Statement macro used in expression position".into(),
                    pos,
                });
            };
            scope.borrow_mut().renames.clear();
            let previous_position = scope
                .borrow_mut()
                .expression_call_position
                .replace(pos.0.clone());
            let copy = copy_expression(body, &replacements, scope);
            scope.borrow_mut().expression_call_position = previous_position;
            let copy = copy?;
            adapt_position(copy.node(), &pos)?;
            stack.push(name);
            walk(copy.node(), definitions, stack, warnings, scope)?;
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
        // Generated names in a nested source scope do not leak into siblings; the
        // fresh-number counter still belongs to the whole member expansion.
        let nested_scope = matches!(
            &kind,
            PNodeKind::Statement(super::parse_ast::PStatement {
                kind: super::parse_ast::PStatementKind::Seqn { .. }
                    | super::parse_ast::PStatementKind::Quasihavocall { .. }
            }) | PNodeKind::Expression(super::parse_ast::PExpression {
                kind: PExpressionKind::Forall(_)
                    | PExpressionKind::Exists(_)
                    | PExpressionKind::ForPerm { .. }
                    | PExpressionKind::Let { .. },
                ..
            }) | PNodeKind::DomainMember(_)
        )
        .then(|| {
            let parent = scope.borrow();
            std::cell::RefCell::new(MacroCopyScope {
                names: parent.names.clone(),
                fresh: parent.fresh.clone(),
                renames: parent.renames.clone(),
                preserve_names: parent.preserve_names,
                expression_call_position: parent.expression_call_position.clone(),
            })
        });
        let child_scope = nested_scope.as_ref().unwrap_or(scope);
        for child in subnodes(node).map_err(|e| MacroError {
            message: format!("macro traversal: {e:?}"),
            pos: pos.clone(),
        })? {
            walk(&child, definitions, stack, warnings, child_scope)?;
        }
        if let Some((operand, location)) = constrained_macro_operand {
            let kind = operand
                .node()
                .read()
                .expect("poisoned parse node")
                .kind
                .clone();
            let valid = matches!(
                kind,
                PNodeKind::Expression(super::parse_ast::PExpression {
                    kind: PExpressionKind::Call { .. },
                    ..
                })
            ) || location
                && matches!(
                    kind,
                    PNodeKind::Expression(super::parse_ast::PExpression {
                        kind: PExpressionKind::FieldAccess { .. },
                        ..
                    })
                )
                || !location
                    && matches!(
                        kind,
                        PNodeKind::Expression(super::parse_ast::PExpression {
                            kind: PExpressionKind::AccPred { .. },
                            ..
                        })
                    );
            if !valid {
                return Err(MacroError {
                    message:
                        "Macro expansion would result in invalid code: expected a resource access"
                            .into(),
                    pos,
                });
            }
        }
        if let Some(child) = nested_scope {
            scope.borrow_mut().fresh = child.into_inner().fresh;
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
    let mut globals = HashSet::new();
    for member in program.all_members() {
        let kind = member
            .node()
            .read()
            .expect("poisoned parse node")
            .kind
            .clone();
        if let PNodeKind::Member(member_kind) = kind {
            match member_kind.kind {
                PMemberKind::Domain {
                    idndef, members, ..
                } => {
                    collect_scope_names(&idndef, &mut globals)?;
                    for function in members.inner().to_seq() {
                        let kind = function
                            .node()
                            .read()
                            .expect("poisoned parse node")
                            .kind
                            .clone();
                        if let PNodeKind::DomainMember(
                            super::parse_ast::PDomainMember::Function { idndef, .. },
                        ) = kind
                        {
                            collect_scope_names(&idndef, &mut globals)?;
                        }
                    }
                }
                PMemberKind::Extension(extension) => {
                    if let Some(adt) = extension
                        .as_any()
                        .downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdt>(
                    ) {
                        collect_scope_names(&adt.idndef, &mut globals)?;
                        for constructor in &adt.constructors {
                            let kind = constructor
                                .read()
                                .expect("poisoned parse node")
                                .kind
                                .clone();
                            if let PNodeKind::Extension(extension) = kind {
                                if let Some(constructor) = extension.as_any().downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>() {
                                    collect_scope_names(&constructor.idndef, &mut globals)?;
                                    for field in constructor.formal_args() { collect_scope_names(field.node(), &mut globals)?; }
                                } else { collect_scope_names(constructor, &mut globals)?; }
                            }
                        }
                    } else {
                        collect_scope_names(member.node(), &mut globals)?;
                    }
                }
                PMemberKind::Function { idndef, .. }
                | PMemberKind::Predicate { idndef, .. }
                | PMemberKind::Method { idndef, .. } => {
                    if let PNodeKind::IdnDef(id) = &idndef.read().expect("poisoned parse node").kind
                    {
                        globals.insert(id.name.clone());
                    }
                }
                PMemberKind::Fields { fields, .. } => {
                    for field in fields.to_seq() {
                        collect_scope_names(field.node(), &mut globals)?;
                    }
                }
                _ => {}
            }
        }
    }
    let scope = std::cell::RefCell::new(MacroCopyScope {
        names: globals,
        fresh: FreshMacroNames::default(),
        preserve_names: false,
        renames: HashMap::new(),
        expression_call_position: None,
    });
    let result = walk(
        program.node(),
        &definitions,
        &mut Vec::new(),
        &mut warnings,
        &scope,
    );
    if let PNodeKind::Program(program) =
        &mut program.node().write().expect("poisoned parse node").kind
    {
        program.local_errors.extend(warnings);
    }
    result
}

#[cfg(test)]
mod macro_source_diagnostic_tests {
    use super::*;
    use crate::parser::{fast_parser, parse_ast};
    fn expand(text: &str) -> MacroError {
        let program = fast_parser::parse_program(text, "test.vpr").unwrap();
        parse_ast::init_properties(program.node()).unwrap();
        expand_global_expression_macros(&program).unwrap_err()
    }
    #[test]
    fn unused_macro_parameters_follow_source_small_set_order() {
        let program = fast_parser::parse_program(
            "define B(x, res) true\nmethod m(x: Ref) ensures B(x)",
            "test.vpr",
        )
        .unwrap();
        parse_ast::init_properties(program.node()).unwrap();
        let error = expand_global_expression_macros(&program).unwrap_err();
        assert_eq!(error.message, "Number of macro arguments does not match");
        let reports = program.errors();
        assert_eq!(reports.len(), 1);
        assert_eq!(
            reports[0].message(),
            "in macro `B`, the following parameters were defined but not used: x, res"
        );
    }
    #[test]
    fn label_macro_parameter_counts_as_used() {
        let program = fast_parser::parse_program(
            "method main() { m(3) }\ndefine m(label_name) { label label_name }",
            "test.vpr",
        )
        .unwrap();
        parse_ast::init_properties(program.node()).unwrap();
        let error = expand_global_expression_macros(&program).unwrap_err();
        assert!(
            error
                .message
                .contains("macro expansion cannot substitute expression `3`")
        );
        assert!(
            program.errors().is_empty(),
            "label parameter is used and must not produce an unused warning"
        );
    }
    #[test]
    fn rejects_invalid_assignment_calls_during_macro_expansion() {
        let error = expand("method f(x: Int) {} method m() { f(1) := 2 }");
        assert_eq!(
            error.message,
            "The only calls that can be on the left-hand side of an assignment statement are calls to macros"
        );
        assert_eq!(error.pos.0.to_string(), "test.vpr@1.34");
        let error = expand("define nonlhs() 3\nmethod m() { nonlhs() := 4 }");
        assert_eq!(
            error.message,
            "The body of this macro is not a suitable left-hand side for an assignment statement"
        );
        assert_eq!(error.pos.0.to_string(), "test.vpr@2.14");
        let program = fast_parser::parse_program(
            "define target(x) x\nmethod m() { var x: Int; target(x) := 1 }",
            "test.vpr",
        )
        .unwrap();
        parse_ast::init_properties(program.node()).unwrap();
        expand_global_expression_macros(&program).unwrap();
        let program = fast_parser::parse_program(
            "define deref(x) x.f\nfield f: Int\nmethod m(r: Ref) { deref(r) := 1 }",
            "test.vpr",
        )
        .unwrap();
        parse_ast::init_properties(program.node()).unwrap();
        expand_global_expression_macros(&program).unwrap();
    }
    #[test]
    fn reports_source_identifier_substitution_errors() {
        let error = expand("define b 2\nmethod a() { b() }");
        assert_eq!(
            error.message,
            "Expression macro used in identifier position"
        );
        let error =
            expand("define checkThis(check) check(x)\nmethod foo() ensures checkThis(true)");
        assert_eq!(
            error.message,
            "macro expansion cannot substitute expression `true` at test.vpr@2.32 in non-expression position at test.vpr@2.22."
        );
        let error = expand("method main() { m(3) }\ndefine m(label_name) { label label_name }");
        assert_eq!(
            error.message,
            "macro expansion cannot substitute expression `3` at test.vpr@1.19 in non-expression position at test.vpr@2.30."
        );
    }
}
