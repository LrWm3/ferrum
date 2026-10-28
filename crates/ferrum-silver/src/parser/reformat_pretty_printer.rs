//! Parse-tree reformatting and trivia preservation.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/ReformatPrettyPrinter.scala
//! Status: partial; trivia scanning, whitespace merging, grouping, nesting and
//! typed parser adapter and concrete leaf/group/program dispatch are implemented.
//! Other parse-node `reformatSuper` rules and exact upstream layout remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2024 ETH Zurich.

use super::{
    parse_ast::{PComment, PNodeHandle, PNodeKind},
    parse_ast_keyword::{Formatting, Pad},
};
use crate::ast::{
    position::Position,
    pretty::pretty_printer::{Doc, pretty},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RWhitespace {
    Space,
    Line,
    LineBreak,
    DoubleLineBreak,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RCommentFragment {
    Whitespace(RWhitespace),
    Comment(PComment),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RTrivia(pub Vec<RCommentFragment>);
impl RTrivia {
    pub fn has_comment(&self) -> bool {
        self.0
            .iter()
            .any(|x| matches!(x, RCommentFragment::Comment(_)))
    }
    pub fn trimmed_lw(&self) -> Self {
        if matches!(self.0.first(), Some(RCommentFragment::Whitespace(_))) {
            Self(self.0[1..].to_vec())
        } else {
            self.clone()
        }
    }
    pub fn replaced_lw(&self, value: RWhitespace) -> Self {
        let mut result = self.clone();
        if matches!(result.0.first(), Some(RCommentFragment::Whitespace(_))) {
            result.0[0] = RCommentFragment::Whitespace(value)
        }
        result
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RNode {
    Text(String),
    Trivia(RTrivia),
    Nest(Vec<RNode>),
    Group(Vec<RNode>),
    Whitespace(RWhitespace),
}
impl RNode {
    pub fn is_nil(&self) -> bool {
        match self {
            Self::Text(s) => s.is_empty(),
            Self::Trivia(t) => t.0.is_empty(),
            Self::Nest(v) | Self::Group(v) => v.iter().all(Self::is_nil),
            Self::Whitespace(_) => false,
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReformatError<E> {
    Adapter(E),
    InvalidPosition,
    InvalidUtf16Offset,
    NotProgram,
    PoisonedNode,
}
/// Positions and offsets follow Java String UTF-16 units, not Rust UTF-8 bytes.
pub struct ReformatterContext<'a> {
    pub program: &'a str,
    pub offsets: Option<&'a [i32]>,
    pub current_offset: usize,
}
impl<'a> ReformatterContext<'a> {
    pub fn new(program: &'a str, offsets: Option<&'a [i32]>) -> Self {
        Self {
            program,
            offsets,
            current_offset: 0,
        }
    }
    fn byte_offset<E>(&self, offset: usize) -> Result<usize, ReformatError<E>> {
        let mut units = 0;
        for (index, ch) in self.program.char_indices() {
            if units == offset {
                return Ok(index);
            }
            units += ch.len_utf16();
            if units > offset {
                return Err(ReformatError::InvalidUtf16Offset);
            }
        }
        if units == offset {
            Ok(self.program.len())
        } else {
            Err(ReformatError::InvalidPosition)
        }
    }
    pub fn get_byte_offset<E>(
        &self,
        position: &Position,
    ) -> Result<Option<usize>, ReformatError<E>> {
        let (Some(offsets), Some(pos)) = (self.offsets, position.line_column()) else {
            return Ok(None);
        };
        let row = pos
            .line()
            .checked_sub(1)
            .and_then(|v| usize::try_from(v).ok())
            .ok_or(ReformatError::InvalidPosition)?;
        let start = *offsets.get(row).ok_or(ReformatError::InvalidPosition)?;
        let result = pos
            .column()
            .checked_sub(1)
            .and_then(|column| start.checked_add(column))
            .and_then(|v| usize::try_from(v).ok())
            .ok_or(ReformatError::InvalidPosition)?;
        Ok(Some(result))
    }
    pub fn get_trivia<E>(
        &mut self,
        start: &Position,
        end: &Position,
    ) -> Result<Option<RTrivia>, ReformatError<E>> {
        match (self.get_byte_offset(start)?, self.get_byte_offset(end)?) {
            (Some(start), Some(end)) => self.get_trivia_by_offset(start, end),
            _ => Ok(None),
        }
    }
    pub fn get_trivia_by_offset<E>(
        &mut self,
        end: usize,
        update: usize,
    ) -> Result<Option<RTrivia>, ReformatError<E>> {
        if self.current_offset > end {
            return Ok(None);
        }
        let a = self.byte_offset(self.current_offset)?;
        let b = self.byte_offset(end)?;
        let input = &self.program[a..b];
        self.current_offset = update;
        Ok(parse_trivia(input))
    }
}
/// `pTrivia` is a prefix parser: nontrivia ends the repetition without error.
fn parse_trivia(input: &str) -> Option<RTrivia> {
    let mut cursor = 0;
    let mut spaces = 0;
    let mut newlines = 0;
    let mut result = Vec::new();
    fn flush(result: &mut Vec<RCommentFragment>, spaces: usize, newlines: usize) {
        if newlines > 1 {
            result.push(RCommentFragment::Whitespace(RWhitespace::DoubleLineBreak));
        } else if newlines > 0 {
            result.push(RCommentFragment::Whitespace(RWhitespace::LineBreak));
        } else if spaces > 0 {
            result.push(RCommentFragment::Whitespace(RWhitespace::Space));
        }
    }
    while cursor < input.len() {
        let rest = &input[cursor..];
        if rest.starts_with("//") {
            let length = rest.find('\n').map_or(rest.len(), |i| i + 1);
            flush(&mut result, spaces, newlines);
            let comment = PComment::new(&rest[..length]);
            newlines = usize::from(comment.trimmed);
            spaces = 0;
            result.push(RCommentFragment::Comment(comment));
            cursor += length;
        } else if rest.starts_with("/*") {
            let Some(end) = rest[2..].find("*/") else {
                break;
            };
            let length = end + 4;
            flush(&mut result, spaces, newlines);
            let comment = PComment::new(&rest[..length]);
            newlines = usize::from(comment.trimmed);
            spaces = 0;
            result.push(RCommentFragment::Comment(comment));
            cursor += length;
        } else if rest.starts_with("\r\n") {
            newlines += 1;
            cursor += 2;
        } else if rest.starts_with('\n') || rest.starts_with('\r') {
            newlines += 1;
            cursor += 1;
        } else if rest.starts_with(' ') || rest.starts_with('\t') {
            spaces += 1;
            cursor += 1;
        } else {
            break;
        }
    }
    flush(&mut result, spaces, newlines);
    if result.is_empty() {
        None
    } else {
        Some(RTrivia(result))
    }
}
#[derive(Default)]
pub struct PrettyPrintContext {
    pub whitespace: Option<RWhitespace>,
}
impl PrettyPrintContext {
    pub fn register(&mut self, value: RWhitespace) {
        match self.whitespace {
            None => self.whitespace = Some(value),
            Some(RWhitespace::LineBreak) => {
                if matches!(value, RWhitespace::LineBreak | RWhitespace::DoubleLineBreak) {
                    self.whitespace = Some(RWhitespace::DoubleLineBreak)
                }
            }
            Some(_) => self.whitespace = Some(value),
        }
    }
}
fn whitespace_doc(w: RWhitespace) -> Doc {
    match w {
        RWhitespace::Space => Doc::text(" "),
        RWhitespace::Line => Doc::line(),
        RWhitespace::LineBreak => Doc::Line("\n".into()),
        RWhitespace::DoubleLineBreak => {
            Doc::concat([Doc::Line("\n".into()), Doc::Line("\n".into())])
        }
    }
}
fn flush(pc: &mut PrettyPrintContext) -> Doc {
    pc.whitespace.take().map(whitespace_doc).unwrap_or(Doc::Nil)
}
fn leading(nodes: &[RNode]) -> bool {
    match nodes.first() {
        Some(RNode::Group(v) | RNode::Nest(v)) => leading(v),
        Some(RNode::Whitespace(_)) => true,
        _ => false,
    }
}
fn trivia_doc(trivia: &RTrivia) -> Doc {
    Doc::concat(trivia.0.iter().map(|v| match v {
        RCommentFragment::Whitespace(w) => whitespace_doc(*w),
        RCommentFragment::Comment(c) => Doc::text(c.str()),
    }))
}
/// Convert the intermediate source tree to the native width-aware document.
pub fn show_list(nodes: &[RNode], pc: &mut PrettyPrintContext) -> Doc {
    let mut result = Vec::new();
    for node in nodes {
        let doc = match node {
            RNode::Whitespace(w) => {
                pc.register(*w);
                Doc::Nil
            }
            RNode::Text(text) => Doc::concat([flush(pc), Doc::text(text)]),
            RNode::Trivia(t) => {
                let body = if t.has_comment() {
                    match pc.whitespace {
                        None => trivia_doc(t),
                        Some(RWhitespace::LineBreak)
                            if matches!(
                                t.0.first(),
                                Some(RCommentFragment::Whitespace(RWhitespace::DoubleLineBreak))
                            ) =>
                        {
                            trivia_doc(&t.replaced_lw(RWhitespace::LineBreak))
                        }
                        Some(RWhitespace::LineBreak) => trivia_doc(&t.trimmed_lw()),
                        Some(RWhitespace::Space)
                            if matches!(
                                t.0.first(),
                                Some(RCommentFragment::Whitespace(RWhitespace::Space))
                            ) =>
                        {
                            trivia_doc(&t.trimmed_lw())
                        }
                        Some(RWhitespace::Space) => trivia_doc(t),
                        Some(_) => trivia_doc(&t.trimmed_lw()),
                    }
                } else {
                    let breaks: usize =
                        t.0.iter()
                            .map(|v| match v {
                                RCommentFragment::Whitespace(RWhitespace::LineBreak) => 1,
                                RCommentFragment::Whitespace(RWhitespace::DoubleLineBreak) => 2,
                                _ => 0,
                            })
                            .sum();
                    if pc.whitespace == Some(RWhitespace::LineBreak) && breaks > 1 {
                        whitespace_doc(RWhitespace::LineBreak)
                    } else {
                        Doc::Nil
                    }
                };
                Doc::concat([flush(pc), body])
            }
            RNode::Group(v) | RNode::Nest(v) => {
                let before = flush(pc);
                let body = show_list(v, pc);
                let body = if matches!(node, RNode::Group(_)) {
                    body.group()
                } else {
                    body.nest(4)
                };
                if leading(v) {
                    body
                } else {
                    Doc::concat([before, body])
                }
            }
        };
        result.push(doc);
    }
    Doc::concat(result)
}
/// Concrete parse nodes must supply their source product/reformat dispatch.
/// Implementations snapshot fields and release parse-node locks before callbacks.
pub trait ReformatAdapter {
    type Error;
    fn formatting(&self, node: &PNodeHandle) -> Result<Formatting, Self::Error>;
    fn reformat(
        &self,
        node: &PNodeHandle,
        context: &mut ReformatterContext<'_>,
    ) -> Result<Vec<RNode>, Self::Error>;
}
fn pad(value: Pad) -> RNode {
    RNode::Whitespace(match value {
        Pad::Space => RWhitespace::Space,
        Pad::Line => RWhitespace::Line,
    })
}
pub fn reformat_subnodes<A: ReformatAdapter>(
    nodes: &[PNodeHandle],
    end_linebreak: bool,
    context: &mut ReformatterContext<'_>,
    adapter: &A,
) -> Result<Vec<RNode>, ReformatError<A::Error>> {
    let mut out = Vec::new();
    let mut index = 0;
    while index < nodes.len() {
        let node = &nodes[index];
        let formatting = adapter.formatting(node).map_err(ReformatError::Adapter)?;
        if let Some(left) = formatting.left {
            out.push(pad(left));
        }
        out.extend(
            adapter
                .reformat(node, context)
                .map_err(ReformatError::Adapter)?,
        );
        index += 1;
        if formatting.right_nest || formatting.right_group {
            let mut rest = reformat_subnodes(&nodes[index..], false, context, adapter)?;
            if let Some(right) = formatting.right {
                rest.insert(0, pad(right));
            }
            if formatting.right_group {
                rest = vec![RNode::Group(rest)];
            }
            if formatting.right_nest {
                rest = vec![RNode::Nest(rest)];
            }
            out.extend(rest);
            return Ok(out);
        }
        if let Some(right) = formatting.right {
            out.push(pad(right));
        }
    }
    if end_linebreak {
        out.push(RNode::Whitespace(RWhitespace::LineBreak));
    }
    Ok(out)
}
pub fn show_node<A: ReformatAdapter>(
    node: &PNodeHandle,
    adapter: &A,
) -> Result<String, ReformatError<A::Error>> {
    let mut context = ReformatterContext::new("", None);
    let nodes = adapter
        .reformat(node, &mut context)
        .map_err(ReformatError::Adapter)?;
    Ok(pretty(
        75,
        &show_list(&nodes, &mut PrettyPrintContext::default()),
    ))
}
pub fn show_program<A: ReformatAdapter>(
    node: &PNodeHandle,
    adapter: &A,
) -> Result<String, ReformatError<A::Error>> {
    let (source, offsets) = {
        let guard = node.read().map_err(|_| ReformatError::PoisonedNode)?;
        let PNodeKind::Program(program) = &guard.kind else {
            return Err(ReformatError::NotProgram);
        };
        (program.raw_program.clone(), program.offsets.clone())
    };
    let mut context = ReformatterContext::new(&source, Some(&offsets));
    let mut nodes = adapter
        .reformat(node, &mut context)
        .map_err(ReformatError::Adapter)?;
    let end = source.encode_utf16().count();
    if let Some(trivia) = context.get_trivia_by_offset(end, end)? {
        nodes.push(RNode::Trivia(trivia));
    }
    nodes.retain(|n| !n.is_nil());
    Ok(pretty(
        75,
        &show_list(&nodes, &mut PrettyPrintContext::default()),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn trivia_keeps_comments_and_restores_line_comment_break() {
        let mut context = ReformatterContext::new("  // note\n\nnext", None);
        let trivia = context.get_trivia_by_offset::<()>(11, 11).unwrap().unwrap();
        assert!(trivia.has_comment());
        assert!(matches!(
            trivia.0.as_slice(),
            [
                RCommentFragment::Whitespace(RWhitespace::Space),
                RCommentFragment::Comment(_),
                RCommentFragment::Whitespace(RWhitespace::DoubleLineBreak)
            ]
        ));
    }
    #[test]
    fn leaf_adapter_preserves_brace_group_nesting() {
        use crate::parser::parse_ast::{PIdnDef, PNode};
        use crate::parser::parse_ast_keyword::{PSym, PToken};
        let pos = (Position::NoPosition, Position::NoPosition);
        let left = PNode::new(
            PNodeKind::Reserved(PToken::Symbol(PSym::LBrace)),
            pos.clone(),
        );
        let id = PNode::new(PNodeKind::IdnDef(PIdnDef { name: "x".into() }), pos.clone());
        let right = PNode::new(
            PNodeKind::Reserved(PToken::Symbol(PSym::RBrace)),
            pos.clone(),
        );
        let node = PNode::new(
            PNodeKind::Grouped {
                children: vec![left, id, right],
            },
            pos,
        );
        assert_eq!(
            show_node(&node, &LeafReformatAdapter).unwrap(),
            "{\n    x\n}"
        );
    }
    #[test]
    fn newline_delimiters_keep_logical_item_boundaries() {
        use crate::parser::parse_ast::{PIdnDef, PNode};
        use crate::parser::parse_ast_keyword::{ND, PDelimited, PReserved, PSym};
        let pos = (Position::NoPosition, Position::NoPosition);
        let first = PNode::new(PNodeKind::IdnDef(PIdnDef { name: "a".into() }), pos.clone());
        let second = PNode::new(PNodeKind::IdnDef(PIdnDef { name: "b".into() }), pos.clone());
        let values = PDelimited::new(
            Some(first),
            vec![(ND(None::<PReserved<PSym>>), second)],
            None,
            pos,
        );
        assert_eq!(
            show_node(values.node(), &LeafReformatAdapter).unwrap(),
            "a\nb"
        );
    }
    #[test]
    fn utf16_offsets_reject_half_of_a_surrogate_pair() {
        let mut context = ReformatterContext::new("😀 ", None);
        assert!(matches!(
            context.get_trivia_by_offset::<()>(1, 1),
            Err(ReformatError::InvalidUtf16Offset)
        ));
        assert!(context.get_trivia_by_offset::<()>(2, 2).unwrap().is_none());
    }
}

/// Concrete dispatch for source leaf nodes and the program member list. Other
/// parse-node families return Unsupported until their custom reformat rules land.
pub struct LeafReformatAdapter;
#[derive(Debug)]
pub enum LeafReformatError {
    Unsupported(&'static str),
    InvalidPosition,
    InvalidUtf16Offset,
    PoisonedNode,
    NotProgram,
}
fn leaf_error(error: ReformatError<LeafReformatError>) -> LeafReformatError {
    match error {
        ReformatError::Adapter(e) => e,
        ReformatError::InvalidPosition => LeafReformatError::InvalidPosition,
        ReformatError::InvalidUtf16Offset => LeafReformatError::InvalidUtf16Offset,
        ReformatError::PoisonedNode => LeafReformatError::PoisonedNode,
        ReformatError::NotProgram => LeafReformatError::NotProgram,
    }
}
impl ReformatAdapter for LeafReformatAdapter {
    type Error = LeafReformatError;
    fn formatting(&self, node: &PNodeHandle) -> Result<Formatting, Self::Error> {
        use super::parse_ast_keyword::{PFormatting, PSym, PToken};
        enum Kind {
            Token(PToken),
            Group(Option<PNodeHandle>),
            Other,
        }
        let kind = {
            let guard = node.read().map_err(|_| LeafReformatError::PoisonedNode)?;
            match &guard.kind {
                PNodeKind::Reserved(token) => Kind::Token(token.clone()),
                PNodeKind::Grouped { children } => Kind::Group(children.first().cloned()),
                _ => Kind::Other,
            }
        };
        Ok(match kind {
            Kind::Token(token) => match token {
                PToken::Keyword(v) => v.formatting(),
                PToken::Symbol(v) => v.formatting(),
                PToken::SymbolOperator(v) => v.formatting(),
                PToken::KeywordOperator(v) => v.formatting(),
                PToken::ExtensionKeyword(v) => v.formatting(),
                PToken::ExtensionSymbol(v) => v.formatting(),
            },
            Kind::Group(Some(left)) => {
                let guard = left.read().map_err(|_| LeafReformatError::PoisonedNode)?;
                Formatting {
                    left: if matches!(
                        guard.kind,
                        PNodeKind::Reserved(PToken::Symbol(PSym::LBrace))
                    ) {
                        Some(Pad::Space)
                    } else {
                        None
                    },
                    ..Default::default()
                }
            }
            _ => Formatting::default(),
        })
    }
    fn reformat(
        &self,
        node: &PNodeHandle,
        context: &mut ReformatterContext<'_>,
    ) -> Result<Vec<RNode>, Self::Error> {
        use super::parse_ast_keyword::{PReservedString, PToken};
        enum Work {
            Leaf(String, (Position, Position)),
            Program(Vec<PNodeHandle>),
            Group(Vec<PNodeHandle>),
            Delimited(super::parse_ast::PDelimitedNewlineParts),
            Children(Vec<PNodeHandle>, bool),
            Unsupported,
        }
        let work = {
            let guard = node.read().map_err(|_| LeafReformatError::PoisonedNode)?;
            match &guard.kind {
                PNodeKind::IdnDef(v) => Work::Leaf(v.name.clone(), guard.pos.clone()),
                PNodeKind::IdnRef(v) => Work::Leaf(v.name.clone(), guard.pos.clone()),
                PNodeKind::RawString(v) => Work::Leaf(v.clone(), guard.pos.clone()),
                PNodeKind::Reserved(token) => Work::Leaf(
                    match token {
                        PToken::Keyword(v) => v.token(),
                        PToken::Symbol(v) => v.token(),
                        PToken::SymbolOperator(v) => v.token(),
                        PToken::KeywordOperator(v) => v.token(),
                        PToken::ExtensionKeyword(v) => v.token(),
                        PToken::ExtensionSymbol(v) => v.token(),
                    }
                    .into(),
                    guard.pos.clone(),
                ),
                PNodeKind::Program(program) => {
                    Work::Program(program.members.iter().map(|m| m.node().clone()).collect())
                }
                PNodeKind::Grouped { children } => Work::Group(children.clone()),
                PNodeKind::Delimited {
                    children,
                    newline_parts,
                } => match newline_parts {
                    Some(parts) => Work::Delimited(parts.clone()),
                    None => Work::Children(children.clone(), false),
                },
                PNodeKind::Annotation { children } => Work::Children(children.clone(), true),
                PNodeKind::PairArgument { children }
                | PNodeKind::MaybePairArgument { children }
                | PNodeKind::StringLiteral { children }
                | PNodeKind::BracedExp { children }
                | PNodeKind::Specification { children }
                | PNodeKind::PermTrigger { children }
                | PNodeKind::DomainFunctionArg { children }
                | PNodeKind::DomainFunctionInterpretation { children }
                | PNodeKind::DomainInterpretation { children }
                | PNodeKind::MethodReturns { children }
                | PNodeKind::DefineInner { children }
                | PNodeKind::DefineParam { children }
                | PNodeKind::TypeVarDecl { children } => Work::Children(children.clone(), false),
                _ => Work::Unsupported,
            }
        };
        match work {
            Work::Leaf(text, (start, end)) => {
                let mut result = Vec::new();
                if let Some(trivia) = context
                    .get_trivia::<Self::Error>(&start, &end)
                    .map_err(leaf_error)?
                {
                    result.push(RNode::Trivia(trivia));
                }
                result.push(RNode::Text(text));
                Ok(result)
            }
            Work::Program(nodes) => {
                reformat_subnodes(&nodes, false, context, self).map_err(leaf_error)
            }
            Work::Delimited(parts) => {
                let mut out =
                    reformat_subnodes(&parts.first, false, context, self).map_err(leaf_error)?;
                for (delimiter, item) in &parts.inner {
                    out.extend(
                        reformat_subnodes(delimiter, false, context, self).map_err(leaf_error)?,
                    );
                    out.push(RNode::Whitespace(RWhitespace::LineBreak));
                    out.extend(reformat_subnodes(item, false, context, self).map_err(leaf_error)?);
                }
                out.extend(
                    reformat_subnodes(&parts.end, false, context, self).map_err(leaf_error)?,
                );
                Ok(out)
            }
            Work::Children(children, end_linebreak) => {
                reformat_subnodes(&children, end_linebreak, context, self).map_err(leaf_error)
            }
            Work::Group(children) => {
                use super::parse_ast_keyword::{PSym, PToken};
                if children.len() < 2 {
                    return Err(LeafReformatError::Unsupported("invalid grouped node"));
                }
                let is_brace = {
                    let guard = children[0]
                        .read()
                        .map_err(|_| LeafReformatError::PoisonedNode)?;
                    matches!(
                        guard.kind,
                        PNodeKind::Reserved(PToken::Symbol(PSym::LBrace))
                    )
                };
                let mut out = self.reformat(&children[0], context)?;
                let inner =
                    reformat_subnodes(&children[1..children.len() - 1], false, context, self)
                        .map_err(leaf_error)?;
                let right = self.reformat(children.last().unwrap(), context)?;
                if !inner.is_empty() {
                    if is_brace {
                        let mut nested = vec![RNode::Whitespace(RWhitespace::Line)];
                        nested.extend(inner);
                        out.push(RNode::Nest(nested));
                        out.push(RNode::Whitespace(RWhitespace::Line));
                    } else {
                        out.push(RNode::Nest(inner));
                    }
                }
                out.extend(right);
                Ok(out)
            }
            Work::Unsupported => Err(LeafReformatError::Unsupported("parse-node reformat rule")),
        }
    }
}
