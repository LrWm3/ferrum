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
//! Status: partial; ordered lookup, argument mapping and fresh-name allocation implemented.
//! Cyclic checking, graph duplication, substitution and complete expansion remain pending.

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
