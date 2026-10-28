//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/DebugParser.scala
//!
//! Purpose:
//! Parse and translate versioned debugger expressions and debug old labels.
//!
//! Planned Rust structure:
//! Port DebugParser versioned identifiers/debugOld syntax and DebugTranslator expInternal
//! overrides.
//!
//! Behavior to preserve:
//! Register debug old and versioned identifier start extensions; parse numeric @ versions and
//! debug labels, translate to LocalVarWithVersion and DebugLabelledOld with source metadata;
//! delegate other expressions.
//!
//! Integration:
//! debugger::{debug_typechecker,silicon_debugger} and ferrum_silver::parser::{fast_parser,translator}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for parser strategy, source positions and extension registration.
//!
//! Open decisions:
//! Agree on debug label syntax and parser ownership with Silver frontend.
//!
//! Status: partial; source debug tokens, typed nodes and translation/check callbacks exist.
//! General parser/resolver override registration and debugger-session integration remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright notice: the pinned upstream file does not carry an individual notice.

use ferrum_silver::{
    ast::{
        ast::Metadata,
        expression::{Exp, ExpKind},
        position::Position,
    },
    parser::{
        parse_ast::{PExpHandle, PExpression, PExpressionKind, PIdnRef, PNodeKind},
        parse_ast_keyword::{PKwOp, PReserved},
        translator::{self, TranslationError},
    },
};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DebugParseError {
    InvalidVersionedIdentifier,
    InvalidOldLabel,
    EmptyOldVersion,
}
/// Return the source token and consumed byte count. All accepted characters are ASCII.
pub fn versioned_identifier(input: &str) -> Result<(&str, usize), DebugParseError> {
    let bytes = input.as_bytes();
    let first = |b: u8| b.is_ascii_alphabetic() || b == b'$' || b == b'_';
    if !bytes.first().copied().is_some_and(first) {
        return Err(DebugParseError::InvalidVersionedIdentifier);
    }
    let mut end = 1;
    while bytes
        .get(end)
        .copied()
        .is_some_and(|b| first(b) || b.is_ascii_digit())
    {
        end += 1;
    }
    if bytes.get(end) != Some(&b'@') {
        return Err(DebugParseError::InvalidVersionedIdentifier);
    }
    end += 1;
    let start = end;
    while bytes.get(end).is_some_and(u8::is_ascii_digit) {
        end += 1;
    }
    if end == start {
        return Err(DebugParseError::InvalidVersionedIdentifier);
    }
    Ok((&input[..end], end))
}
/// The source token grammar accepts `debug@` but its split-index construction
/// subsequently throws. Native code reports that case explicitly below.
pub fn debug_old_label(input: &str) -> Result<(&str, usize), DebugParseError> {
    if !input.starts_with("debug@") {
        return Err(DebugParseError::InvalidOldLabel);
    }
    let mut end = 6;
    while input
        .as_bytes()
        .get(end)
        .copied()
        .is_some_and(|b| b.is_ascii_alphanumeric() || b"#$_.:".contains(&b))
    {
        end += 1;
    }
    Ok((&input[..end], end))
}
pub fn versioned_use(
    token: &str,
    position: (Position, Position),
) -> Result<PExpHandle, DebugParseError> {
    let (name, version) = token
        .split_once('@')
        .ok_or(DebugParseError::InvalidVersionedIdentifier)?;
    if version.is_empty() {
        return Err(DebugParseError::EmptyOldVersion);
    }
    Ok(PExpHandle::new(
        PExpression::from_kind(PExpressionKind::VersionedIdnUse {
            idnref: PIdnRef::new(name),
            version: version.into(),
            separator: "@".into(),
        }),
        position,
    ))
}
pub fn debug_old(
    label: PExpHandle,
    expression: PExpHandle,
    position: (Position, Position),
) -> PExpHandle {
    PExpHandle::new(
        PExpression::from_kind(PExpressionKind::DebugLabelledOldExp {
            op: PReserved::implied(PKwOp::Old),
            label,
            exp: expression,
        }),
        position,
    )
}
pub fn versioned_name(expression: &PExpHandle) -> Result<String, TranslationError> {
    let node = expression.node().read().expect("poisoned parse node");
    match &node.kind {
        PNodeKind::Expression(PExpression {
            kind:
                PExpressionKind::VersionedIdnUse {
                    idnref,
                    version,
                    separator,
                },
            ..
        }) => Ok(format!("{}{separator}{version}", idnref.name)),
        _ => Err(TranslationError::Unsupported(
            "expected versioned identifier",
        )),
    }
}
/// Source debug translation at a recursion boundary. The caller must install this
/// override in the general translator so nested debug expressions use it too.
pub fn translate_debug_expression(
    expression: &PExpHandle,
    metadata: Metadata,
    recurse: &mut impl FnMut(&PExpHandle) -> Result<Exp, TranslationError>,
) -> Result<Exp, TranslationError> {
    let value = match &expression.node().read().expect("poisoned parse node").kind {
        PNodeKind::Expression(value) => value.clone(),
        _ => return Err(TranslationError::Unsupported("expected expression")),
    };
    match value.kind {
        PExpressionKind::VersionedIdnUse { .. } => Ok(Exp::new(
            ExpKind::LocalVarWithVersion(
                versioned_name(expression)?,
                translator::translate_type(&value.typ)?,
            ),
            metadata,
        )),
        PExpressionKind::DebugLabelledOldExp { label, exp, .. } => Ok(Exp::new(
            ExpKind::DebugLabelledOld(recurse(&exp)?, versioned_name(&label)?),
            metadata,
        )),
        _ => recurse(expression),
    }
}
