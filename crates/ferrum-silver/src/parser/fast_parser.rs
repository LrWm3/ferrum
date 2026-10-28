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
//! Status: partial; common expressions, types, fields, functions, predicates and methods are
//! implemented. Imports, macro expansion, extensions, recovery and remaining forms are pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use std::path::{Path, PathBuf};

use super::parse_ast::{
    PBinaryOp, PDeclarationClass, PDomainTypeKind, PExpHandle, PExpression, PExpressionBrackets,
    PExpressionKind, PIdnRef, PNode, PNodeKind, PPairArgument, PTypeHandle, PTypeKind,
};
use super::parse_ast::{
    PBracedExp, PDeclarationHandle, PDeclarationKind, PIdnDef, PIdnTypeBinding, PMember,
    PMemberHandle, PMemberKind, PNodeHandle, PProgram, PProgramHandle, PSpecification, PSpecs,
};
use super::parse_ast::{
    PExpGroup, PMethodReturns, PStatement, PStatementKind, PStmtHandle, fresh_scope_id,
};
use super::parse_ast::{PMaybePairArgument, POldLabel};
use super::parse_ast::{PQuantifier, PTrigger};
use super::parse_ast_keyword::{
    ND, PDelimited, PGrouped, PKw, PKwOp, PReserved, PSym, PSymOp, Span,
};
use crate::ast::position::{FilePosition, LineColumn, Position, SourcePosition};
use crate::verifier::verification_result::ParseReport;
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

/// Parse a complete program containing the currently supported declarations.
/// Imports, domains and macros are rejected until their grammar and processing
/// are connected, so an unsupported program is never accepted as a partial program.
pub fn parse_program(source: &str, file: impl AsRef<Path>) -> Result<PProgramHandle, SyntaxError> {
    let mut parser = ExpressionParser {
        source,
        file: file.as_ref().to_owned(),
        cursor: 0,
        warnings: Vec::new(),
    };
    let mut members = Vec::new();
    loop {
        parser.trivia()?;
        if parser.cursor == source.len() {
            break;
        }
        members.push(parser.member()?);
    }
    let mut offsets = Vec::new();
    if !source.is_empty() {
        offsets.push(0);
        let mut utf16 = 0i32;
        let mut chars = source.chars().peekable();
        while let Some(ch) = chars.next() {
            utf16 = utf16.wrapping_add(ch.len_utf16() as i32);
            if ch == '\r' {
                if chars.peek() == Some(&'\n') {
                    chars.next();
                    utf16 = utf16.wrapping_add(1);
                }
                if chars.peek().is_some() {
                    offsets.push(utf16);
                }
            } else if ch == '\n' && chars.peek().is_some() {
                offsets.push(utf16);
            }
        }
    }
    let pos = parser.span(0, source.len());
    Ok(PProgramHandle::new(
        PProgram {
            imported: Vec::new(),
            members,
            local_errors: parser
                .warnings
                .into_iter()
                .map(|w| ParseReport::Warning(w))
                .collect(),
            offsets,
            raw_program: source.into(),
        },
        pos,
    ))
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
    fn identifier_definition(&mut self) -> Result<PNodeHandle, SyntaxError> {
        self.trivia()?;
        let start = self.cursor;
        let bytes = self.source.as_bytes();
        if start >= bytes.len()
            || !(bytes[start].is_ascii_alphabetic() || matches!(bytes[start], b'_' | b'$'))
        {
            return Err(self.error("expected identifier"));
        }
        self.cursor = self.identifier_end(start);
        let name = &self.source[start..self.cursor];
        if is_keyword(name) {
            return Err(self.error("expected identifier"));
        }
        Ok(PNode::new(
            PNodeKind::IdnDef(PIdnDef { name: name.into() }),
            self.span(start, self.cursor),
        ))
    }
    fn binding(&mut self, kind: PDeclarationKind) -> Result<PDeclarationHandle, SyntaxError> {
        let idndef = self.identifier_definition()?;
        let start = idndef.read().expect("poisoned parse node").pos.0.clone();
        let colon = self
            .take(":")?
            .ok_or_else(|| self.error("expected ':' after declaration name"))?;
        let typ = self.typ()?;
        let end = typ
            .node()
            .read()
            .expect("poisoned parse node")
            .pos
            .1
            .clone();
        Ok(PDeclarationHandle::from_binding(
            kind,
            PIdnTypeBinding {
                idndef,
                colon: PReserved::new(PSym::Colon, colon),
                typ,
                pos: (start, end),
            },
        ))
    }
    fn formal_args(
        &mut self,
        kind: PDeclarationKind,
    ) -> Result<super::parse_ast::PFormalArgs, SyntaxError> {
        let left_span = self
            .take("(")?
            .ok_or_else(|| self.error("expected '(' before arguments"))?;
        let start = left_span.0.clone();
        self.trivia()?;
        let list_start = self.position(self.cursor);
        let first = if self.source[self.cursor..].starts_with(')') {
            None
        } else {
            Some(self.binding(kind.clone())?)
        };
        let mut rest = Vec::new();
        if first.is_some() {
            while let Some(comma) = self.take(",")? {
                rest.push((
                    PReserved::new(PSym::Comma, comma),
                    self.binding(kind.clone())?,
                ));
            }
        }
        let end = if let Some((_, last)) = rest.last() {
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
        let list = PDelimited::new(first, rest, None, (list_start, end));
        let right_span = self
            .take(")")?
            .ok_or_else(|| self.error("expected ')' after arguments"))?;
        let group_end = right_span.1.clone();
        Ok(PGrouped::new(
            PReserved::new(PSym::LParen, left_span),
            list,
            PReserved::new(PSym::RParen, right_span),
            (start, group_end),
        ))
    }
    fn specifications(&mut self, name: &str, keyword: PKw) -> Result<PSpecs, SyntaxError> {
        self.trivia()?;
        let start = self.position(self.cursor);
        let mut pairs = Vec::new();
        loop {
            self.trivia()?;
            let at = self.cursor;
            if !self.source[at..].starts_with(name) || self.identifier_end(at) != at + name.len() {
                break;
            }
            self.cursor += name.len();
            let token = PReserved::new(keyword, self.span(at, self.cursor));
            let expression = self.expression(0)?;
            let end = expression
                .node()
                .read()
                .expect("poisoned parse node")
                .pos
                .1
                .clone();
            let spec = PSpecification::new(token, expression, (self.position(at), end));
            let semi = self.take(";")?.map(|span| PReserved::new(PSym::Semi, span));
            pairs.push((spec, ND(semi)));
        }
        let end = self.position(self.cursor);
        let span = (start, end);
        Ok(PSpecs::new(
            PDelimited::from_pairs(pairs, span.clone()),
            span,
        ))
    }
    fn braced_expression(&mut self) -> Result<Option<PBracedExp>, SyntaxError> {
        let Some(left_span) = self.take("{")? else {
            return Ok(None);
        };
        let start = left_span.0.clone();
        let expression = self.expression(0)?;
        let right_span = self
            .take("}")?
            .ok_or_else(|| self.error("expected '}' after expression"))?;
        let end = right_span.1.clone();
        let group = PGrouped::new(
            PReserved::new(PSym::LBrace, left_span),
            expression,
            PReserved::new(PSym::RBrace, right_span),
            (start.clone(), end.clone()),
        );
        Ok(Some(PBracedExp::new(group, (start, end))))
    }
    fn parenthesized_expression(&mut self) -> Result<PExpGroup, SyntaxError> {
        let left = self.take("(")?.ok_or_else(|| self.error("expected '('"))?;
        let start = left.0.clone();
        let exp = self.expression(0)?;
        let right = self.take(")")?.ok_or_else(|| self.error("expected ')'"))?;
        let end = right.1.clone();
        Ok(PGrouped::new(
            PReserved::new(PSym::LParen, left),
            exp,
            PReserved::new(PSym::RParen, right),
            (start, end),
        ))
    }
    fn statement_block(&mut self) -> Result<Option<PStmtHandle>, SyntaxError> {
        let Some(left) = self.take("{")? else {
            return Ok(None);
        };
        let start = left.0.clone();
        self.trivia()?;
        let list_start = self.position(self.cursor);
        let mut pairs = Vec::new();
        while !self.source[self.cursor..].starts_with('}') {
            if self.cursor >= self.source.len() {
                return Err(self.error("expected '}' after statements"));
            }
            let statement = self.statement()?;
            let semi = self.take(";")?.map(|span| PReserved::new(PSym::Semi, span));
            pairs.push((statement, ND(semi)));
            self.trivia()?;
        }
        let list_end = self.position(self.cursor);
        let list = PDelimited::from_pairs(pairs, (list_start, list_end));
        let right = self
            .take("}")?
            .ok_or_else(|| self.error("expected '}' after statements"))?;
        let end = right.1.clone();
        let group = PGrouped::new(
            PReserved::new(PSym::LBrace, left),
            list,
            PReserved::new(PSym::RBrace, right),
            (start.clone(), end.clone()),
        );
        Ok(Some(PStmtHandle::new(
            PStatement {
                kind: PStatementKind::Seqn {
                    statements: group,
                    scope_id: fresh_scope_id(),
                },
            },
            (start, end),
        )))
    }
    fn statement(&mut self) -> Result<PStmtHandle, SyntaxError> {
        self.trivia()?;
        let start = self.cursor;
        if self.source[start..].starts_with('{') {
            return self
                .statement_block()?
                .ok_or_else(|| self.error("expected block"));
        }
        let end = self.identifier_end(start);
        let name = &self.source[start..end];
        let keyword = match name {
            "assert" => Some(PKw::Assert),
            "assume" => Some(PKw::Assume),
            "inhale" => Some(PKw::Inhale),
            "exhale" => Some(PKw::Exhale),
            "var" => Some(PKw::Var),
            "if" => Some(PKw::If),
            "while" => Some(PKw::While),
            "goto" => Some(PKw::Goto),
            "label" => Some(PKw::Label),
            _ => None,
        };
        let kind = if let Some(keyword) = keyword {
            self.cursor = end;
            let token = PReserved::new(keyword, self.span(start, end));
            match keyword {
                PKw::Assert | PKw::Assume | PKw::Inhale | PKw::Exhale => {
                    let exp = self.expression(0)?;
                    match keyword {
                        PKw::Assert => PStatementKind::Assert {
                            keyword: token,
                            exp,
                        },
                        PKw::Assume => PStatementKind::Assume {
                            keyword: token,
                            exp,
                        },
                        PKw::Inhale => PStatementKind::Inhale {
                            keyword: token,
                            exp,
                        },
                        _ => PStatementKind::Exhale {
                            keyword: token,
                            exp,
                        },
                    }
                }
                PKw::Var => {
                    let first = self.binding(PDeclarationKind::LocalVar)?;
                    let list_start = first
                        .node()
                        .read()
                        .expect("poisoned parse node")
                        .pos
                        .0
                        .clone();
                    let mut rest = Vec::new();
                    while let Some(comma) = self.take(",")? {
                        rest.push((
                            PReserved::new(PSym::Comma, comma),
                            self.binding(PDeclarationKind::LocalVar)?,
                        ));
                    }
                    let list_end = rest
                        .last()
                        .map(|(_, n)| n)
                        .unwrap_or(&first)
                        .node()
                        .read()
                        .expect("poisoned parse node")
                        .pos
                        .1
                        .clone();
                    let vars = PDelimited::new(Some(first), rest, None, (list_start, list_end));
                    let init = if let Some(assign) = self.take(":=")? {
                        Some((PReserved::new(PSymOp::Assign, assign), self.expression(0)?))
                    } else {
                        None
                    };
                    PStatementKind::Vars {
                        keyword: token,
                        vars,
                        init,
                    }
                }
                PKw::If => {
                    let cond = self.parenthesized_expression()?;
                    let thn = self
                        .statement_block()?
                        .ok_or_else(|| self.error("expected if body"))?;
                    self.trivia()?;
                    let at = self.cursor;
                    let els = if self.source[at..].starts_with("else")
                        && self.identifier_end(at) == at + 4
                    {
                        self.cursor += 4;
                        let else_token = PReserved::new(PKw::Else, self.span(at, self.cursor));
                        let body = self
                            .statement_block()?
                            .ok_or_else(|| self.error("expected else body"))?;
                        Some(PStmtHandle::new(
                            PStatement {
                                kind: PStatementKind::Else {
                                    keyword: else_token,
                                    els: body,
                                },
                            },
                            self.span(at, self.cursor),
                        ))
                    } else {
                        None
                    };
                    PStatementKind::If {
                        keyword: token,
                        cond,
                        thn,
                        els,
                    }
                }
                PKw::While => {
                    let cond = self.parenthesized_expression()?;
                    let invs = self.specifications("invariant", PKw::Invariant)?;
                    let body = self
                        .statement_block()?
                        .ok_or_else(|| self.error("expected while body"))?;
                    PStatementKind::While {
                        keyword: token,
                        cond,
                        invs,
                        body,
                    }
                }
                PKw::Goto => {
                    let idndef = self.identifier_definition()?;
                    let node = idndef.read().expect("poisoned parse node");
                    let PNodeKind::IdnDef(id) = &node.kind else {
                        unreachable!()
                    };
                    let target = PNode::new(
                        PNodeKind::IdnRef(PIdnRef::with_class(&id.name, PDeclarationClass::Label)),
                        node.pos.clone(),
                    );
                    PStatementKind::Goto {
                        keyword: token,
                        target,
                    }
                }
                PKw::Label => {
                    let idndef = self.identifier_definition()?;
                    let invs = self.specifications("invariant", PKw::Invariant)?.specs;
                    PStatementKind::Label {
                        keyword: token,
                        idndef,
                        invs,
                    }
                }
                _ => unreachable!(),
            }
        } else {
            let first = self.atom()?;
            let first_kind = first
                .node()
                .read()
                .expect("poisoned parse node")
                .kind
                .clone();
            if !matches!(
                &first_kind,
                PNodeKind::Expression(PExpression {
                    kind: PExpressionKind::IdnUse { .. }
                        | PExpressionKind::FieldAccess { .. }
                        | PExpressionKind::Call { .. },
                    ..
                })
            ) {
                return Err(self.error("expected assignment target or call"));
            }
            let list_start = first
                .node()
                .read()
                .expect("poisoned parse node")
                .pos
                .0
                .clone();
            let mut rest = Vec::new();
            while let Some(comma) = self.take(",")? {
                let target = self.atom()?;
                if !matches!(
                    &target.node().read().expect("poisoned parse node").kind,
                    PNodeKind::Expression(PExpression {
                        kind: PExpressionKind::IdnUse { .. }
                            | PExpressionKind::FieldAccess { .. }
                            | PExpressionKind::Call { .. },
                        ..
                    })
                ) {
                    return Err(self.error("expected assignment target"));
                }
                rest.push((PReserved::new(PSym::Comma, comma), target));
            }
            if let Some(assign) = self.take(":=")? {
                let list_end = rest
                    .last()
                    .map(|(_, n)| n)
                    .unwrap_or(&first)
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .pos
                    .1
                    .clone();
                let targets = PDelimited::new(Some(first), rest, None, (list_start, list_end));
                PStatementKind::Assign {
                    targets,
                    op: Some(PReserved::new(PSymOp::Assign, assign)),
                    rhs: self.expression(0)?,
                }
            } else {
                if !rest.is_empty()
                    || matches!(
                        first_kind,
                        PNodeKind::Expression(PExpression {
                            kind: PExpressionKind::FieldAccess { .. },
                            ..
                        })
                    )
                {
                    return Err(self.error("expected ':=' after assignment targets"));
                }
                PStatementKind::Assign {
                    targets: PDelimited::empty(),
                    op: None,
                    rhs: first,
                }
            }
        };
        Ok(PStmtHandle::new(
            PStatement { kind },
            self.span(start, self.cursor),
        ))
    }
    fn member(&mut self) -> Result<PMemberHandle, SyntaxError> {
        self.trivia()?;
        let start = self.cursor;
        let end = self.identifier_end(start);
        if end == start {
            return Err(self.error("expected declaration"));
        }
        let name = &self.source[start..end];
        self.cursor = end;
        let keyword_span = self.span(start, end);
        let kind = match name {
            "field" => {
                let keyword = PReserved::new(PKw::Field, keyword_span);
                let first = self.binding(PDeclarationKind::field())?;
                let list_start = first
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .pos
                    .0
                    .clone();
                let mut rest = Vec::new();
                while let Some(comma) = self.take(",")? {
                    rest.push((
                        PReserved::new(PSym::Comma, comma),
                        self.binding(PDeclarationKind::field())?,
                    ));
                }
                let list_end = rest
                    .last()
                    .map(|(_, n)| n)
                    .unwrap_or(&first)
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .pos
                    .1
                    .clone();
                let fields = PDelimited::new(Some(first), rest, None, (list_start, list_end));
                let semi = self.take(";")?.map(|span| PReserved::new(PSym::Semi, span));
                PMemberKind::Fields {
                    keyword,
                    fields,
                    semi,
                }
            }
            "function" => {
                let keyword = PReserved::new(PKw::Function, keyword_span);
                let idndef = self.identifier_definition()?;
                let args = self.formal_args(PDeclarationKind::FormalArg)?;
                let colon = self
                    .take(":")?
                    .ok_or_else(|| self.error("expected ':' before return type"))?;
                let result_type = self.typ()?;
                let pres = self.specifications("requires", PKw::Requires)?;
                let posts = self.specifications("ensures", PKw::Ensures)?;
                let body = self.braced_expression()?;
                PMemberKind::Function {
                    keyword,
                    idndef,
                    args,
                    colon: PReserved::new(PSym::Colon, colon),
                    result_type,
                    pres,
                    posts,
                    body,
                }
            }
            "method" => {
                let keyword = PReserved::new(PKw::Method, keyword_span);
                let idndef = self.identifier_definition()?;
                let args = self.formal_args(PDeclarationKind::FormalArg)?;
                self.trivia()?;
                let at = self.cursor;
                let returns = if self.source[at..].starts_with("returns")
                    && self.identifier_end(at) == at + 7
                {
                    self.cursor += 7;
                    let token = PReserved::new(PKw::Returns, self.span(at, self.cursor));
                    let formal_returns = self.formal_args(PDeclarationKind::FormalReturn)?;
                    Some(PMethodReturns::new(
                        token,
                        formal_returns,
                        self.span(at, self.cursor),
                    ))
                } else {
                    None
                };
                let pres = self.specifications("requires", PKw::Requires)?;
                let posts = self.specifications("ensures", PKw::Ensures)?;
                let body = self.statement_block()?;
                PMemberKind::Method {
                    keyword,
                    idndef,
                    args,
                    returns,
                    pres,
                    posts,
                    body,
                }
            }
            "predicate" => {
                let keyword = PReserved::new(PKw::Predicate, keyword_span);
                let idndef = self.identifier_definition()?;
                let args = self.formal_args(PDeclarationKind::FormalArg)?;
                let body = self.braced_expression()?;
                PMemberKind::Predicate {
                    keyword,
                    idndef,
                    args,
                    body,
                }
            }
            _ => {
                return Err(self.error(format!("declaration form '{name}' is not yet implemented")));
            }
        };
        Ok(PMemberHandle::new(
            PMember::new(Vec::new(), kind),
            self.span(start, self.cursor),
        ))
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
        if self.source[start..].starts_with('|') && !self.source[start..].starts_with("||") {
            self.cursor += 1;
            let left = PReserved::new(PSymOp::Or, self.span(start, self.cursor));
            let seq = self.expression(0)?;
            let right_span = self
                .take("|")?
                .ok_or_else(|| self.error("expected '|' after size expression"))?;
            let expression = self.expr_node(
                PExpressionKind::Size {
                    left,
                    seq,
                    right: PReserved::new(PSymOp::Or, right_span),
                },
                self.position(start),
                self.position(self.cursor),
            );
            return self.suffix(expression);
        }
        if self.source[start..].starts_with('[') {
            self.cursor += 1;
            let left = PReserved::new(PSymOp::LBracket, self.span(start, self.cursor));
            let first = self.expression(0)?;
            let kind = if let Some(comma) = self.take(",")? {
                let exhale = self.expression(0)?;
                let right = self
                    .take("]")?
                    .ok_or_else(|| self.error("expected ']' after inhale/exhale expression"))?;
                PExpressionKind::InhaleExhale {
                    left,
                    inhale: first,
                    comma: PReserved::new(PSymOp::Comma, comma),
                    exhale,
                    right: PReserved::new(PSymOp::RBracket, right),
                }
            } else if let Some(dots) = self.take("..")? {
                let high = self.expression(0)?;
                let right = self
                    .take(")")?
                    .ok_or_else(|| self.error("expected ')' after sequence range"))?;
                PExpressionKind::RangeSeq {
                    left,
                    low: first,
                    dots: PReserved::new(PSymOp::DotDot, dots),
                    high,
                    right: PReserved::new(PSymOp::RParen, right),
                }
            } else {
                return Err(self.error("expected ',' or '..' in bracket expression"));
            };
            let expression = self.expr_node(kind, self.position(start), self.position(self.cursor));
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
            if matches!(name, "forall" | "exists") {
                let first = self.binding(PDeclarationKind::LogicalVar)?;
                let list_start = first
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .pos
                    .0
                    .clone();
                let mut rest = Vec::new();
                while let Some(comma) = self.take(",")? {
                    rest.push((
                        PReserved::new(PSym::Comma, comma),
                        self.binding(PDeclarationKind::LogicalVar)?,
                    ));
                }
                let list_end = rest
                    .last()
                    .map(|(_, n)| n)
                    .unwrap_or(&first)
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .pos
                    .1
                    .clone();
                let vars = PDelimited::new(Some(first), rest, None, (list_start, list_end));
                let colons = self
                    .take("::")?
                    .ok_or_else(|| self.error("expected '::' after quantifier variables"))?;
                let mut triggers = Vec::new();
                while let Some(left) = self.take("{")? {
                    let group_start = left.0.clone();
                    self.trivia()?;
                    let list_start = self.position(self.cursor);
                    let first = if self.source[self.cursor..].starts_with('}') {
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
                    let list_end = rest
                        .last()
                        .map(|(_, e)| e)
                        .or(first.as_ref())
                        .map(|e| e.node().read().expect("poisoned parse node").pos.1.clone())
                        .unwrap_or(list_start.clone());
                    let list = PDelimited::new(first, rest, None, (list_start, list_end));
                    let right = self
                        .take("}")?
                        .ok_or_else(|| self.error("expected '}' after trigger"))?;
                    let group_end = right.1.clone();
                    let group = PGrouped::new(
                        PReserved::new(PSym::LBrace, left),
                        list,
                        PReserved::new(PSym::RBrace, right),
                        (group_start.clone(), group_end.clone()),
                    );
                    triggers.push(PTrigger::new(group, (group_start, group_end)));
                }
                let body = self.expression(0)?;
                let quantifier = PQuantifier {
                    keyword: PReserved::new(
                        if name == "forall" {
                            PKw::Forall
                        } else {
                            PKw::Exists
                        },
                        span.clone(),
                    ),
                    vars,
                    colons: PReserved::new(PSym::ColonColon, colons),
                    triggers,
                    body,
                    scope_id: fresh_scope_id(),
                };
                let kind = if name == "forall" {
                    PExpressionKind::Forall(quantifier)
                } else {
                    PExpressionKind::Exists(quantifier)
                };
                let expression =
                    self.expr_node(kind, self.position(start), self.position(self.cursor));
                return self.suffix(expression);
            }
            if matches!(name, "acc" | "perm" | "old") {
                let kind = if name == "old" {
                    let op = PReserved::new(PKwOp::Old, span.clone());
                    let label = if let Some(left) = self.take("[")? {
                        let group_start = left.0.clone();
                        self.trivia()?;
                        let at = self.cursor;
                        let end = self.identifier_end(at);
                        let first = self.source.as_bytes().get(at).copied();
                        if !first
                            .is_some_and(|b| b.is_ascii_alphabetic() || matches!(b, b'_' | b'$'))
                        {
                            return Err(self.error("expected old label"));
                        }
                        self.cursor = end;
                        let label_span = self.span(at, end);
                        let label = if &self.source[at..end] == "lhs" {
                            POldLabel::Lhs(PReserved::new(PKw::Lhs, label_span))
                        } else {
                            if is_keyword(&self.source[at..end]) {
                                return Err(self.error("expected old label"));
                            }
                            POldLabel::Label(PNode::new(
                                PNodeKind::IdnRef(PIdnRef::with_class(
                                    &self.source[at..end],
                                    PDeclarationClass::Label,
                                )),
                                label_span,
                            ))
                        };
                        let right = self
                            .take("]")?
                            .ok_or_else(|| self.error("expected ']' after old label"))?;
                        let group_end = right.1.clone();
                        Some(PGrouped::new(
                            PReserved::new(PSym::LBracket, left),
                            label,
                            PReserved::new(PSym::RBracket, right),
                            (group_start, group_end),
                        ))
                    } else {
                        None
                    };
                    PExpressionKind::OldExp {
                        op,
                        label,
                        exp: self.parenthesized_expression()?,
                    }
                } else {
                    let left = self
                        .take("(")?
                        .ok_or_else(|| self.error("expected '(' after permission operator"))?;
                    let group_start = left.0.clone();
                    let resource = self.expression(0)?;
                    let resource_kind = resource
                        .node()
                        .read()
                        .expect("poisoned parse node")
                        .kind
                        .clone();
                    let valid = matches!(
                        &resource_kind,
                        PNodeKind::Expression(PExpression {
                            kind: PExpressionKind::FieldAccess { .. }
                                | PExpressionKind::Call { .. },
                            ..
                        })
                    ) || (name == "perm"
                        && matches!(
                            &resource_kind,
                            PNodeKind::Expression(PExpression {
                                kind: PExpressionKind::MagicWandExp { .. },
                                ..
                            })
                        ));
                    if !valid {
                        return Err(self.error("expected resource access"));
                    }
                    if name == "acc" {
                        let pair_start = resource
                            .node()
                            .read()
                            .expect("poisoned parse node")
                            .pos
                            .0
                            .clone();
                        let second = if let Some(comma) = self.take(",")? {
                            Some((PReserved::new(PSym::Comma, comma), self.expression(0)?))
                        } else {
                            None
                        };
                        let pair_end = second
                            .as_ref()
                            .map(|(_, e)| e)
                            .unwrap_or(&resource)
                            .node()
                            .read()
                            .expect("poisoned parse node")
                            .pos
                            .1
                            .clone();
                        let pair =
                            PMaybePairArgument::new(resource, second, (pair_start, pair_end));
                        let right = self
                            .take(")")?
                            .ok_or_else(|| self.error("expected ')' after access predicate"))?;
                        let group_end = right.1.clone();
                        let amount = PGrouped::new(
                            PReserved::new(PSym::LParen, left),
                            pair,
                            PReserved::new(PSym::RParen, right),
                            (group_start, group_end),
                        );
                        PExpressionKind::AccPred {
                            op: PReserved::new(PKwOp::Acc, span.clone()),
                            amount,
                        }
                    } else {
                        let right = self.take(")")?.ok_or_else(|| {
                            self.error("expected ')' after permission expression")
                        })?;
                        let group_end = right.1.clone();
                        let resource = PGrouped::new(
                            PReserved::new(PSym::LParen, left),
                            resource,
                            PReserved::new(PSym::RParen, right),
                            (group_start, group_end),
                        );
                        PExpressionKind::CurrentPerm {
                            op: PReserved::new(PKwOp::Perm, span.clone()),
                            resource,
                        }
                    }
                };
                let expression =
                    self.expr_node(kind, self.position(start), self.position(self.cursor));
                return self.suffix(expression);
            }
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
            if self.source[start..].starts_with('[') {
                self.cursor += 1;
                let left = PReserved::new(PSymOp::LBracket, self.span(start, self.cursor));
                let begin = base
                    .node()
                    .read()
                    .expect("poisoned parse node")
                    .pos
                    .0
                    .clone();
                let kind = if let Some(dots) = self.take("..")? {
                    let end = self.expression(0)?;
                    let right = self
                        .take("]")?
                        .ok_or_else(|| self.error("expected ']' after slice"))?;
                    PExpressionKind::SeqSlice {
                        seq: base,
                        left,
                        start: None,
                        dots: PReserved::new(PSymOp::DotDot, dots),
                        end: Some(end),
                        right: PReserved::new(PSymOp::RBracket, right),
                    }
                } else {
                    let key = self.expression(0)?;
                    if let Some(assign) = self.take(":=")? {
                        let value = self.expression(0)?;
                        let right = self
                            .take("]")?
                            .ok_or_else(|| self.error("expected ']' after update"))?;
                        PExpressionKind::Update {
                            base,
                            left,
                            key,
                            assign: PReserved::new(PSymOp::Assign, assign),
                            value,
                            right: PReserved::new(PSymOp::RBracket, right),
                        }
                    } else if let Some(dots) = self.take("..")? {
                        self.trivia()?;
                        let end = if self.source[self.cursor..].starts_with(']') {
                            None
                        } else {
                            Some(self.expression(0)?)
                        };
                        let right = self
                            .take("]")?
                            .ok_or_else(|| self.error("expected ']' after slice"))?;
                        PExpressionKind::SeqSlice {
                            seq: base,
                            left,
                            start: Some(key),
                            dots: PReserved::new(PSymOp::DotDot, dots),
                            end,
                            right: PReserved::new(PSymOp::RBracket, right),
                        }
                    } else {
                        let right = self
                            .take("]")?
                            .ok_or_else(|| self.error("expected ']' after index"))?;
                        PExpressionKind::Lookup {
                            base,
                            left,
                            index: key,
                            right: PReserved::new(PSymOp::RBracket, right),
                        }
                    }
                };
                base = self.expr_node(kind, begin, self.position(self.cursor));
                continue;
            }
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
    #[test]
    fn bracket_forms_preserve_typed_expression_nodes() {
        for (text, tag) in [
            ("a[1]", 0),
            ("a[1 := 2]", 1),
            ("a[..3]", 2),
            ("a[1..]", 2),
            ("[1..3)", 3),
            ("[true, false]", 4),
            ("|a|", 5),
        ] {
            let parsed = parse_expression(text, "test.vpr").unwrap();
            let PNodeKind::Expression(exp) = parsed.expression.node().read().unwrap().kind.clone()
            else {
                panic!("expression")
            };
            assert!(
                match tag {
                    0 => matches!(exp.kind, PExpressionKind::Lookup { .. }),
                    1 => matches!(exp.kind, PExpressionKind::Update { .. }),
                    2 => matches!(exp.kind, PExpressionKind::SeqSlice { .. }),
                    3 => matches!(exp.kind, PExpressionKind::RangeSeq { .. }),
                    4 => matches!(exp.kind, PExpressionKind::InhaleExhale { .. }),
                    _ => matches!(exp.kind, PExpressionKind::Size { .. }),
                },
                "{text}"
            );
        }
        assert!(parse_expression("a[..]", "test.vpr").is_err());
    }
    #[test]
    fn programs_retain_fields_functions_predicates_and_warnings() {
        let program = parse_program("field f: Int, g: Ref;\nfunction foo(x: Rational): Int requires x > 0 ensures result > 0 { 1 }\npredicate p()", "test.vpr").unwrap();
        let PNodeKind::Program(p) = program.node().read().unwrap().kind.clone() else {
            panic!("program")
        };
        assert_eq!(p.members.len(), 3);
        assert_eq!(p.local_errors.len(), 1);
        assert!(matches!(
            p.members[0].node().read().unwrap().kind,
            PNodeKind::Member(PMember {
                kind: PMemberKind::Fields { .. },
                ..
            })
        ));
        assert!(parse_program("field f: Int domain D {}", "test.vpr").is_err());
    }
    #[test]
    fn method_with_statements_is_a_typed_parse_tree() {
        let text = "method m(x: Int) returns (y: Int) requires x > 0 ensures y > 0 { var z: Int := x; y := z; if (y > 1) { assert true; } else { inhale false; } while (y > 0) invariant y >= 0 { y := y - 1; } }";
        let p = parse_program(text, "test.vpr").unwrap();
        let PNodeKind::Program(p) = p.node().read().unwrap().kind.clone() else {
            panic!("program")
        };
        assert_eq!(p.members.len(), 1);
        assert!(matches!(
            p.members[0].node().read().unwrap().kind,
            PNodeKind::Member(PMember {
                kind: PMemberKind::Method { body: Some(_), .. },
                ..
            })
        ));
    }
    #[test]
    fn permissions_and_old_expressions_require_resources() {
        for text in [
            "acc(x.f)",
            "acc(x.f, write)",
            "perm(x.f)",
            "old[lhs](x.f)",
            "old[here](x)",
        ] {
            parse_expression(text, "test.vpr").unwrap();
        }
        assert!(parse_expression("acc(x)", "test.vpr").is_err());
        assert!(parse_expression("old[123](x)", "test.vpr").is_err());
    }
    #[test]
    fn quantifiers_retain_variables_and_ordered_triggers() {
        let parsed = parse_expression(
            "forall x: Int, y: Ref :: {f(x), g(y)} {h(x)} x > 0",
            "test.vpr",
        )
        .unwrap();
        let PNodeKind::Expression(exp) = parsed.expression.node().read().unwrap().kind.clone()
        else {
            panic!("expression")
        };
        let PExpressionKind::Forall(q) = exp.kind else {
            panic!("quantifier")
        };
        assert_eq!(q.vars.len(), 2);
        assert_eq!(q.triggers.len(), 2);
        assert!(parse_expression("forall :: true", "test.vpr").is_err());
    }
}
