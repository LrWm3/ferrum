//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/FastParser.scala
//!
//! Purpose:
//! Parse source into a position-bearing parse tree, recursively load imports and optionally
//! expand macros.
//!
//! Planned Rust structure:
//! Port FastParser, ParserData, RecParser, SuffixedExpressionGenerator and companion
//! lexical/trivia/grouping helpers. Organize grammar by expressions and precedence, types,
//! statements, declarations/specifications and ParserExtension hooks.
//!
//! Behavior to preserve:
//! Normalize and deduplicate local and standard import paths separately; local imports inside
//! standard imports become standard. Apply beforeParse to imports and report failures at import
//! positions. Parse full file first, then recover member by member with errors and warnings;
//! retain raw source and offsets on success. Preserve operator precedence, chained comparisons,
//! delimiters, source spans, extension order and deprecated call whitespace and Rational
//! warnings. Chained comparisons copy the middle operand into conjunctions; suffix and
//! arithmetic chains fold left, while implication and Boolean chains recurse right. Call type
//! annotations require parentheses.
//!
//! Integration:
//! parser::parse_ast, parse_ast_keyword, macro_expander; plugin parser hooks, ast::utility
//! file_loader and verifier parse reports; frontend::sil_frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Parser strategy, extension API, position encoding and mutable parser ownership require
//! agreement with parse_ast, plugin and reformatter.
//!
//! Status: partial; native expression parsing is implemented for a subset. Program parsing,
//! imports, macro expansion, extensions, recovery and remaining expression forms are pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use std::path::{Path, PathBuf};

use super::parse_ast::{
    PBinaryOp, PDeclarationClass, PDomainTypeKind, PExpHandle, PExpression, PExpressionBrackets,
    PExpressionKind, PIdnRef, PNode, PNodeKind, PPairArgument, PTypeHandle, PTypeKind,
};
use super::parse_ast_keyword::{PDelimited, PGrouped, PKw, PKwOp, PReserved, PSym, PSymOp, Span};
use crate::ast::position::{FilePosition, LineColumn, Position, SourcePosition};
use crate::verifier::verification_result::ParseWarning;

/// A syntax failure at the point where the native parser stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SyntaxError {
    pub message: String,
    pub position: Position,
}

/// A parsed expression and its ordered, non-fatal diagnostics.
#[derive(Clone, Debug)]
pub struct ParsedExpression {
    pub expression: PExpHandle,
    pub warnings: Vec<ParseWarning>,
}

/// Parse a complete expression. Unsupported forms and trailing input are errors.
pub fn parse_expression(
    source: &str,
    file: impl AsRef<Path>,
) -> Result<ParsedExpression, SyntaxError> {
    let mut parser = ExpressionParser {
        source,
        file: file.as_ref().to_owned(),
        cursor: 0,
        warnings: Vec::new(),
    };
    let result = parser.expression(0)?;
    parser.trivia()?;
    if parser.cursor != source.len() {
        return Err(parser.error("unexpected trailing input"));
    }
    Ok(ParsedExpression {
        expression: result,
        warnings: parser.warnings,
    })
}

/// A parsed source type and ordered deprecation warnings.
#[derive(Clone, Debug)]
pub struct ParsedType {
    pub typ: PTypeHandle,
    pub warnings: Vec<ParseWarning>,
}

/// Parse a complete source type.
pub fn parse_type(source: &str, file: impl AsRef<Path>) -> Result<ParsedType, SyntaxError> {
    let mut parser = ExpressionParser {
        source,
        file: file.as_ref().to_owned(),
        cursor: 0,
        warnings: Vec::new(),
    };
    let typ = parser.typ()?;
    parser.trivia()?;
    if parser.cursor != source.len() {
        return Err(parser.error("unexpected trailing input"));
    }
    Ok(ParsedType {
        typ,
        warnings: parser.warnings,
    })
}

struct ExpressionParser<'a> {
    source: &'a str,
    file: PathBuf,
    cursor: usize,
    warnings: Vec<ParseWarning>,
}

impl ExpressionParser<'_> {
    fn position(&self, offset: usize) -> Position {
        let prefix = &self.source[..offset];
        let mut line = 1i32;
        let mut column = 1i32;
        let mut chars = prefix.chars().peekable();
        while let Some(ch) = chars.next() {
            match ch {
                '\r' => {
                    if chars.peek() == Some(&'\n') {
                        chars.next();
                    }
                    line += 1;
                    column = 1;
                }
                '\n' => {
                    line += 1;
                    column = 1;
                }
                _ => column += ch.len_utf16() as i32,
            }
        }
        Position::LineColumn(LineColumn::File(FilePosition {
            file: self.file.clone(),
            line,
            column,
        }))
    }
    fn span(&self, start: usize, end: usize) -> Span {
        (self.position(start), self.position(end))
    }
    fn error(&self, message: impl Into<String>) -> SyntaxError {
        SyntaxError {
            message: message.into(),
            position: self.position(self.cursor),
        }
    }
    fn trivia(&mut self) -> Result<(), SyntaxError> {
        loop {
            let rest = &self.source[self.cursor..];
            if rest.starts_with("//") {
                self.cursor += rest.find('\n').map_or(rest.len(), |i| i + 1);
            } else if rest.starts_with("/*") {
                if let Some(end) = rest[2..].find("*/") {
                    self.cursor += end + 4;
                } else {
                    return Err(self.error("unterminated block comment"));
                }
            } else if let Some(ch) = rest
                .chars()
                .next()
                .filter(|c| matches!(c, ' ' | '\t' | '\r' | '\n'))
            {
                self.cursor += ch.len_utf8();
            } else {
                return Ok(());
            }
        }
    }
    fn identifier_end(&self, start: usize) -> usize {
        let bytes = self.source.as_bytes();
        let mut end = start;
        while end < bytes.len()
            && (bytes[end].is_ascii_alphanumeric() || matches!(bytes[end], b'_' | b'$'))
        {
            end += 1;
        }
        end
    }
    fn take(&mut self, text: &str) -> Result<Option<Span>, SyntaxError> {
        let before_trivia = self.cursor;
        self.trivia()?;
        let start = self.cursor;
        if self.source[start..].starts_with(text) {
            self.cursor += text.len();
            Ok(Some(self.span(start, self.cursor)))
        } else {
            self.cursor = before_trivia;
            Ok(None)
        }
    }
    fn expr_node(&self, kind: PExpressionKind, start: Position, end: Position) -> PExpHandle {
        PExpHandle::new(PExpression::from_kind(kind), (start, end))
    }
    fn expression(&mut self, minimum: u8) -> Result<PExpHandle, SyntaxError> {
        let mut left = self.atom()?;
        let mut seen_comparison = false;
        loop {
            self.trivia()?;
            let start = self.cursor;
            if minimum <= 1 && self.source[start..].starts_with('?') {
                self.cursor += 1;
                let question = PReserved::new(PSymOp::Question, self.span(start, self.cursor));
                let thn = self.expression(0)?;
                let colon = self
                    .take(":")?
                    .ok_or_else(|| self.error("expected ':' in conditional expression"))?;
                let els = self.expression(1)?;
                let begin = left
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .pos
                    .0
                    .clone();
                let end = els
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .pos
                    .1
                    .clone();
                left = self.expr_node(
                    PExpressionKind::CondExp {
                        cond: left,
                        question,
                        thn,
                        colon: PReserved::new(PSymOp::Colon, colon),
                        els,
                    },
                    begin,
                    end,
                );
                continue;
            }
            let Some((op, precedence, right_assoc, comparison, length)) = self.binary_operator()
            else {
                break;
            };
            if precedence < minimum {
                break;
            }
            if comparison && seen_comparison {
                return Err(self.error(
                    "chained comparisons require parse-tree copying, which is not implemented yet",
                ));
            }
            seen_comparison |= comparison;
            self.cursor += length;
            let operator_span = self.span(start, self.cursor);
            let right = self.expression(if matches!(op, PBinaryOp::Symbol(PSymOp::Wand)) {
                0
            } else if right_assoc {
                precedence
            } else {
                precedence + 1
            })?;
            let begin = left
                .node()
                .read()
                .expect("poisoned parse node")
                .pos
                .0
                .clone();
            let end = right
                .node()
                .read()
                .expect("poisoned parse node")
                .pos
                .1
                .clone();
            let kind = if matches!(op, PBinaryOp::Symbol(PSymOp::Wand)) {
                PExpressionKind::MagicWandExp {
                    left,
                    wand: PReserved::new(PSymOp::Wand, operator_span),
                    right,
                }
            } else {
                PExpressionKind::BinExp {
                    left,
                    op: PReserved::new(op, operator_span),
                    right,
                }
            };
            left = self.expr_node(kind, begin, end);
        }
        Ok(left)
    }
    fn binary_operator(&self) -> Option<(PBinaryOp, u8, bool, bool, usize)> {
        use PSymOp::*;
        let text = &self.source[self.cursor..];
        let symbols = [
            ("<==>", Iff, 2, true, false),
            ("==>", Implies, 3, true, false),
            ("--*", Wand, 4, true, false),
            ("||", OrOr, 5, true, false),
            ("&&", AndAnd, 6, true, false),
            ("==", EqEq, 7, true, false),
            ("!=", Ne, 7, true, false),
            ("<=", Le, 8, false, true),
            (">=", Ge, 8, false, true),
            ("<", Lt, 8, false, true),
            (">", Gt, 8, false, true),
            ("++", Append, 9, false, false),
            ("+", Plus, 9, false, false),
            ("-", Minus, 9, false, false),
            ("*", Mul, 10, false, false),
            ("/", Div, 10, false, false),
            ("\\", ArithDiv, 10, false, false),
            ("%", Mod, 10, false, false),
        ];
        for (spelling, op, precedence, right, comparison) in symbols {
            if text.starts_with(spelling) {
                return Some((
                    PBinaryOp::Symbol(op),
                    precedence,
                    right,
                    comparison,
                    spelling.len(),
                ));
            }
        }
        for (spelling, op, precedence, comparison) in [
            ("intersection", PKwOp::Intersection, 9, false),
            ("setminus", PKwOp::Setminus, 9, false),
            ("subset", PKwOp::Subset, 9, false),
            ("union", PKwOp::Union, 9, false),
            ("in", PKwOp::In, 8, true),
        ] {
            if text.starts_with(spelling)
                && self.identifier_end(self.cursor) == self.cursor + spelling.len()
            {
                return Some((
                    PBinaryOp::Keyword(op),
                    precedence,
                    false,
                    comparison,
                    spelling.len(),
                ));
            }
        }
        None
    }
    fn typ(&mut self) -> Result<PTypeHandle, SyntaxError> {
        self.trivia()?;
        let start = self.cursor;
        let bytes = self.source.as_bytes();
        if start >= bytes.len()
            || !(bytes[start].is_ascii_alphabetic() || matches!(bytes[start], b'_' | b'$'))
        {
            return Err(self.error("expected type"));
        }
        self.cursor = self.identifier_end(start);
        let name = &self.source[start..self.cursor];
        let name_span = self.span(start, self.cursor);
        let keyword = match name {
            "Int" => Some(PKw::Int),
            "Bool" => Some(PKw::Bool),
            "Perm" => Some(PKw::Perm),
            "Ref" => Some(PKw::Ref),
            "Rational" => Some(PKw::Rational),
            "Seq" => Some(PKw::Seq),
            "Set" => Some(PKw::Set),
            "Multiset" => Some(PKw::Multiset),
            "Map" => Some(PKw::Map),
            _ => None,
        };
        let kind = if let Some(keyword) = keyword {
            let token = PReserved::new(keyword, name_span.clone());
            if keyword == PKw::Rational {
                let (Position::LineColumn(start), Position::LineColumn(end)) = name_span.clone()
                else {
                    unreachable!()
                };
                self.warnings.push(ParseWarning::new(
                    "Rational is deprecated, use Perm instead",
                    Position::LineColumn(LineColumn::Source(Box::new(SourcePosition {
                        file: Some(self.file.clone()),
                        start: Box::new(start),
                        end: Some(Box::new(end)),
                    }))),
                ));
            }
            match keyword {
                PKw::Seq | PKw::Set | PKw::Multiset | PKw::Map => {
                    let left_span = self
                        .take("[")?
                        .ok_or_else(|| self.error("expected '[' after collection type"))?;
                    let group_start = left_span.0.clone();
                    let left = PReserved::new(PSym::LBracket, left_span);
                    let first = self.typ()?;
                    if keyword == PKw::Map {
                        let comma = self
                            .take(",")?
                            .ok_or_else(|| self.error("expected ',' in map type"))?;
                        let second = self.typ()?;
                        let pair_start = first
                            .node()
                            .read()
                            .expect("poisoned parse node")
                            .pos
                            .0
                            .clone();
                        let pair_end = second
                            .node()
                            .read()
                            .expect("poisoned parse node")
                            .pos
                            .1
                            .clone();
                        let pair = PPairArgument::new(
                            first,
                            PReserved::new(PSym::Comma, comma),
                            second,
                            (pair_start, pair_end),
                        );
                        let right_span = self
                            .take("]")?
                            .ok_or_else(|| self.error("expected ']' after map type"))?;
                        let group_end = right_span.1.clone();
                        let types = PGrouped::new(
                            left,
                            pair,
                            PReserved::new(PSym::RBracket, right_span),
                            (group_start, group_end),
                        );
                        PTypeKind::Map {
                            keyword: token,
                            types,
                        }
                    } else {
                        let right_span = self
                            .take("]")?
                            .ok_or_else(|| self.error("expected ']' after collection type"))?;
                        let group_end = right_span.1.clone();
                        let element_type = PGrouped::new(
                            left,
                            first,
                            PReserved::new(PSym::RBracket, right_span),
                            (group_start, group_end),
                        );
                        match keyword {
                            PKw::Seq => PTypeKind::Seq {
                                keyword: token,
                                element_type,
                            },
                            PKw::Set => PTypeKind::Set {
                                keyword: token,
                                element_type,
                            },
                            PKw::Multiset => PTypeKind::Multiset {
                                keyword: token,
                                element_type,
                            },
                            _ => unreachable!(),
                        }
                    }
                }
                _ => PTypeKind::Primitive { name: token },
            }
        } else {
            // Only identifiers may denote domain types. Reserved words are rejected.
            if is_keyword(name) {
                return Err(self.error(format!("expected type, found keyword '{name}'")));
            }
            let domain = PNode::new(
                PNodeKind::IdnRef(PIdnRef::with_class(
                    name,
                    PDeclarationClass::TypeDeclaration,
                )),
                name_span,
            );
            let args = if let Some(left_span) = self.take("[")? {
                let group_start = left_span.0.clone();
                let left = PReserved::new(PSym::LBracket, left_span);
                self.trivia()?;
                let list_start = self.position(self.cursor);
                let first = if self.source[self.cursor..].starts_with(']') {
                    None
                } else {
                    Some(self.typ()?)
                };
                let mut rest = Vec::new();
                if first.is_some() {
                    while let Some(comma) = self.take(",")? {
                        rest.push((PReserved::new(PSym::Comma, comma), self.typ()?));
                    }
                }
                let list_end = if let Some((_, last)) = rest.last() {
                    last.node()
                        .read()
                        .expect("poisoned parse node")
                        .pos
                        .1
                        .clone()
                } else if let Some(first) = &first {
                    first
                        .node()
                        .read()
                        .expect("poisoned parse node")
                        .pos
                        .1
                        .clone()
                } else {
                    list_start.clone()
                };
                let list = PDelimited::new(first, rest, None, (list_start, list_end));
                let right_span = self
                    .take("]")?
                    .ok_or_else(|| self.error("expected ']' after type arguments"))?;
                let group_end = right_span.1.clone();
                Some(PGrouped::new(
                    left,
                    list,
                    PReserved::new(PSym::RBracket, right_span),
                    (group_start, group_end),
                ))
            } else {
                None
            };
            PTypeKind::Domain {
                domain,
                args,
                kind: PDomainTypeKind::Unresolved,
            }
        };
        Ok(PTypeHandle::new(kind, self.span(start, self.cursor)))
    }
    fn atom(&mut self) -> Result<PExpHandle, SyntaxError> {
        self.trivia()?;
        let start = self.cursor;
        if self.take("(")?.is_some() {
            let left = PReserved::new(PSym::LParen, self.span(start, start + 1));
            let expression = self.expression(0)?;
            let right = self.take(")")?.ok_or_else(|| self.error("expected ')'"))?;
            let group = PExpressionBrackets::new(
                left,
                &expression,
                PReserved::new(PSym::RParen, right),
                self.span(start, self.cursor),
            );
            expression.set_brackets(group);
            return self.suffix(expression);
        }
        if self.source[start..].starts_with('-') || self.source[start..].starts_with('!') {
            self.cursor += 1;
            let op = if self.source.as_bytes()[start] == b'-' {
                PSymOp::Neg
            } else {
                PSymOp::Not
            };
            let operator = PReserved::new(op, self.span(start, self.cursor));
            let inner = self.atom()?;
            let end = inner
                .node()
                .read()
                .expect("poisoned parse node")
                .pos
                .1
                .clone();
            return Ok(self.expr_node(
                PExpressionKind::UnExp {
                    op: operator,
                    exp: inner,
                },
                self.position(start),
                end,
            ));
        }
        let bytes = self.source.as_bytes();
        if start < bytes.len() && bytes[start].is_ascii_digit() {
            while self.cursor < bytes.len() && bytes[self.cursor].is_ascii_digit() {
                self.cursor += 1;
            }
            let number = self.source[start..self.cursor]
                .parse()
                .expect("decimal digits are a BigInt");
            let expression = self.expr_node(
                PExpressionKind::IntLit(number),
                self.position(start),
                self.position(self.cursor),
            );
            return self.suffix(expression);
        }
        if start < bytes.len()
            && (bytes[start].is_ascii_alphabetic() || matches!(bytes[start], b'_' | b'$'))
        {
            self.cursor = self.identifier_end(start);
            let name = &self.source[start..self.cursor];
            let span = self.span(start, self.cursor);
            let keyword = match name {
                "true" => Some(PKw::True),
                "false" => Some(PKw::False),
                "null" => Some(PKw::Null),
                "result" => Some(PKw::Result),
                "none" => Some(PKw::None),
                "wildcard" => Some(PKw::Wildcard),
                "write" => Some(PKw::Write),
                "epsilon" => Some(PKw::Epsilon),
                _ => None,
            };
            let kind = if let Some(kw) = keyword {
                let token = PReserved::new(kw, span.clone());
                match kw {
                    PKw::True | PKw::False => PExpressionKind::BoolLit(token),
                    PKw::Null => PExpressionKind::NullLit(token),
                    PKw::Result => PExpressionKind::ResultLit(token),
                    PKw::None => PExpressionKind::NoPerm(token),
                    PKw::Wildcard => PExpressionKind::Wildcard(token),
                    PKw::Write => PExpressionKind::FullPerm(token),
                    PKw::Epsilon => PExpressionKind::Epsilon(token),
                    _ => unreachable!(),
                }
            } else {
                if is_keyword(name) {
                    return Err(
                        self.error(format!("expression form '{name}' is not yet implemented"))
                    );
                }
                let mut call_start = self.cursor;
                while self.source.as_bytes().get(call_start) == Some(&b' ') {
                    call_start += 1;
                }
                let is_call = self.source[call_start..].starts_with('(');
                let class = if is_call {
                    PDeclarationClass::Callable
                } else {
                    PDeclarationClass::TypedVar
                };
                let idnref = PNode::new(
                    PNodeKind::IdnRef(PIdnRef::with_class(name, class)),
                    span.clone(),
                );
                if is_call {
                    if call_start > self.cursor {
                        let (start_pos, end_pos) = self.span(self.cursor, call_start);
                        let (Position::LineColumn(start), Position::LineColumn(end)) =
                            (start_pos, end_pos)
                        else {
                            unreachable!()
                        };
                        self.warnings.push(ParseWarning::new(
                            "Whitespace between a function identifier and the opening paren is deprecated, remove the spaces",
                            Position::LineColumn(LineColumn::Source(Box::new(SourcePosition { file: Some(self.file.clone()), start: Box::new(start), end: Some(Box::new(end)) }))),
                        ));
                    }
                    self.cursor = call_start + 1;
                    let left = PReserved::new(PSym::LParen, self.span(call_start, self.cursor));
                    self.trivia()?;
                    let list_start = self.cursor;
                    let first = if self.source[self.cursor..].starts_with(')') {
                        None
                    } else {
                        Some(self.expression(0)?)
                    };
                    let mut rest = Vec::new();
                    if first.is_some() {
                        while let Some(comma) = self.take(",")? {
                            rest.push((PReserved::new(PSym::Comma, comma), self.expression(0)?));
                        }
                    }
                    let list_end = if let Some((_, last)) = rest.last() {
                        last.node()
                            .read()
                            .expect("poisoned parse node")
                            .pos
                            .1
                            .clone()
                    } else if let Some(first) = &first {
                        first
                            .node()
                            .read()
                            .expect("poisoned parse node")
                            .pos
                            .1
                            .clone()
                    } else {
                        self.position(list_start)
                    };
                    let list =
                        PDelimited::new(first, rest, None, (self.position(list_start), list_end));
                    let right = self
                        .take(")")?
                        .ok_or_else(|| self.error("expected ')' after arguments"))?;
                    let args = PGrouped::new(
                        left,
                        list,
                        PReserved::new(PSym::RParen, right),
                        self.span(call_start, self.cursor),
                    );
                    let call = PExpressionKind::Call {
                        idnref,
                        call_args: args,
                        type_annotated: None,
                        extra_local_type_variables: Vec::new(),
                        domain_type_renaming: None,
                        domain_substitution: None,
                    };
                    let expression =
                        self.expr_node(call, self.position(start), self.position(self.cursor));
                    return self.suffix(expression);
                }
                PExpressionKind::IdnUse { idnref }
            };
            let expression = PExpHandle::new(PExpression::from_kind(kind), span);
            return self.suffix(expression);
        }
        Err(self.error("expected expression"))
    }
    fn suffix(&mut self, mut base: PExpHandle) -> Result<PExpHandle, SyntaxError> {
        loop {
            self.trivia()?;
            let start = self.cursor;
            if !self.source[start..].starts_with('.') || self.source[start..].starts_with("..") {
                return Ok(base);
            }
            self.cursor += 1;
            let dot = PReserved::new(PSymOp::Dot, self.span(start, self.cursor));
            self.trivia()?;
            let name_start = self.cursor;
            let bytes = self.source.as_bytes();
            if name_start >= bytes.len()
                || !(bytes[name_start].is_ascii_alphabetic()
                    || matches!(bytes[name_start], b'_' | b'$'))
            {
                return Err(self.error("expected field name"));
            }
            self.cursor = self.identifier_end(name_start);
            if is_keyword(&self.source[name_start..self.cursor]) {
                return Err(self.error("expected field identifier"));
            }
            let idnref = PNode::new(
                PNodeKind::IdnRef(PIdnRef::with_class(
                    &self.source[name_start..self.cursor],
                    PDeclarationClass::Field,
                )),
                self.span(name_start, self.cursor),
            );
            let begin = base
                .node()
                .read()
                .expect("poisoned parse node")
                .pos
                .0
                .clone();
            base = self.expr_node(
                PExpressionKind::FieldAccess {
                    receiver: base,
                    dot,
                    idnref,
                },
                begin,
                self.position(self.cursor),
            );
        }
    }
}

fn is_keyword(name: &str) -> bool {
    const KEYWORDS: &[&str] = &[
        "Int",
        "Perm",
        "Bool",
        "Ref",
        "Rational",
        "import",
        "method",
        "function",
        "predicate",
        "domain",
        "axiom",
        "var",
        "returns",
        "field",
        "define",
        "interpretation",
        "requires",
        "ensures",
        "invariant",
        "fold",
        "unfold",
        "inhale",
        "exhale",
        "new",
        "assert",
        "assume",
        "package",
        "apply",
        "quasihavoc",
        "quasihavocall",
        "while",
        "if",
        "elseif",
        "else",
        "goto",
        "label",
        "Seq",
        "Set",
        "Multiset",
        "Map",
        "union",
        "intersection",
        "setminus",
        "subset",
        "range",
        "domain",
        "unfolding",
        "in",
        "applying",
        "asserting",
        "old",
        "lhs",
        "let",
        "forall",
        "exists",
        "forperm",
        "acc",
        "perm",
        "unique",
    ];
    KEYWORDS.contains(&name)
        || matches!(
            name,
            "true" | "false" | "null" | "result" | "none" | "wildcard" | "write" | "epsilon"
        )
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn operator_associativity_and_deprecated_call_spacing() {
        let parsed = parse_expression("a ==> f (1 + 2 * 3) ==> b", "test.vpr").unwrap();
        assert_eq!(parsed.warnings.len(), 1);
        let PNodeKind::Expression(expression) =
            parsed.expression.node().read().unwrap().kind.clone()
        else {
            panic!("expected expression")
        };
        let PExpressionKind::BinExp { op, right, .. } = expression.kind else {
            panic!("expected implication")
        };
        assert_eq!(op.display(), "==>");
        assert!(matches!(
            right.node().read().unwrap().kind,
            PNodeKind::Expression(PExpression {
                kind: PExpressionKind::BinExp { .. },
                ..
            })
        ));
        assert!(parse_expression("a < b < c", "test.vpr").is_err());
    }
    #[test]
    fn nested_types_and_rational_warning() {
        let parsed = parse_type("Map[Int, Seq[Rational]]", "test.vpr").unwrap();
        assert!(matches!(
            parsed.typ.node().read().unwrap().kind,
            PNodeKind::Type(PTypeKind::Map { .. })
        ));
        assert_eq!(parsed.warnings.len(), 1);
        assert!(parse_type("Map[Int]", "test.vpr").is_err());
        assert!(parse_type("true", "test.vpr").is_err());
    }
    #[test]
    fn delimited_lists_reject_a_leading_comma() {
        assert!(parse_expression("f(,1)", "test.vpr").is_err());
        assert!(parse_type("Domain[,Int]", "test.vpr").is_err());
        assert!(parse_expression("f()", "test.vpr").is_ok());
        assert!(parse_type("D[]", "test.vpr").is_ok());
    }
}
