//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/ParseAstKeyword.scala
//!
//! Purpose:
//! Represent source tokens, delimiters and operator typing and formatting rules.
//!
//! Planned Rust structure:
//! Port PReserved, PGrouped, PDelimited, ND, PKw, PSym, PSymOp, PKwOp and operator signature
//! categories. Retain grouping/delimiter helpers, update and implied constructors.
//!
//! Behavior to preserve:
//! Keep position-independent PDelimited equality/hash, delimiter order and update length
//! assertion. Preserve each token spelling, formatting pads and ordered overload signatures,
//! including integer versus permission division and collection membership return types.
//!
//! Integration:
//! parser::parse_ast, fast_parser, resolver and reformat_pretty_printer; utility::common hash
//! helper.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Choose token and generic grouping representation consistent with parser and formatter without
//! changing signatures.
//!
//! Status: partial; token, delimiter, formatting metadata and signature patterns implemented; formatter and parse-type integration pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::position::Position;
use std::hash::{Hash, Hasher};

pub type Span = (Position, Position);

/// Source product fields expose their actual parse-node handles in traversal order.
pub trait PGraphElement {
    fn graph_nodes(&self) -> Vec<super::parse_ast::PNodeHandle>;
}
impl<T: PGraphElement> PGraphElement for Option<T> {
    fn graph_nodes(&self) -> Vec<super::parse_ast::PNodeHandle> {
        self.as_ref()
            .map(PGraphElement::graph_nodes)
            .unwrap_or_default()
    }
}
impl<T: PGraphElement> PGraphElement for Vec<T> {
    fn graph_nodes(&self) -> Vec<super::parse_ast::PNodeHandle> {
        self.iter().flat_map(PGraphElement::graph_nodes).collect()
    }
}

pub trait PReservedString {
    fn token(&self) -> &'static str;
}

#[derive(Clone, Debug)]
pub enum PToken {
    Keyword(PKw),
    Symbol(PSym),
    SymbolOperator(PSymOp),
    KeywordOperator(PKwOp),
}
pub trait PTokenValue: Clone {
    fn graph_token(&self) -> PToken;
}
impl PTokenValue for PKw {
    fn graph_token(&self) -> PToken {
        PToken::Keyword(*self)
    }
}
impl PTokenValue for PSym {
    fn graph_token(&self) -> PToken {
        PToken::Symbol(*self)
    }
}
impl PTokenValue for PSymOp {
    fn graph_token(&self) -> PToken {
        PToken::SymbolOperator(*self)
    }
}
impl PTokenValue for PKwOp {
    fn graph_token(&self) -> PToken {
        PToken::KeywordOperator(*self)
    }
}
impl PTokenValue for super::parse_ast::PBinaryOp {
    fn graph_token(&self) -> PToken {
        match self {
            Self::Symbol(op) => PToken::SymbolOperator(*op),
            Self::Keyword(op) => PToken::KeywordOperator(*op),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PReserved<T> {
    pub(crate) rs: T,
    pub(crate) pos: Span,
    pub(crate) node: super::parse_ast::PNodeHandle,
}
impl<T> PReserved<T> {
    pub fn value(&self) -> &T {
        &self.rs
    }
    pub fn position(&self) -> &Span {
        &self.pos
    }
    pub fn node(&self) -> &super::parse_ast::PNodeHandle {
        &self.node
    }
}
impl<T> PGraphElement for PReserved<T> {
    fn graph_nodes(&self) -> Vec<super::parse_ast::PNodeHandle> {
        vec![self.node.clone()]
    }
}
impl<T: PartialEq> PartialEq for PReserved<T> {
    fn eq(&self, other: &Self) -> bool {
        self.rs == other.rs
    }
}
impl<T: Eq> Eq for PReserved<T> {}
impl<T: Hash> Hash for PReserved<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.rs.hash(state);
    }
}
impl<T: PTokenValue> PReserved<T> {
    pub fn new(rs: T, pos: Span) -> Self {
        let node = super::parse_ast::PNode::new(
            super::parse_ast::PNodeKind::Reserved(rs.graph_token()),
            pos.clone(),
        );
        Self { rs, pos, node }
    }
    pub fn implied(rs: T) -> Self {
        Self::new(rs, (Position::NoPosition, Position::NoPosition))
    }
}
impl<T: PReservedString> PReserved<T> {
    pub fn display(&self) -> &'static str {
        self.rs.token()
    }
}

#[derive(Clone, Debug)]
pub struct PGrouped<L, T, R> {
    pub(crate) left: PReserved<L>,
    pub(crate) inner: T,
    pub(crate) right: PReserved<R>,
    pub(crate) pos: Span,
    pub(crate) node: super::parse_ast::PNodeHandle,
}
impl<L, T, R> PGrouped<L, T, R> {
    pub fn left(&self) -> &PReserved<L> {
        &self.left
    }
    pub fn inner(&self) -> &T {
        &self.inner
    }
    pub fn right(&self) -> &PReserved<R> {
        &self.right
    }
    pub fn position(&self) -> &Span {
        &self.pos
    }
    pub fn node(&self) -> &super::parse_ast::PNodeHandle {
        &self.node
    }
}
impl<L, T, R> PGraphElement for PGrouped<L, T, R> {
    fn graph_nodes(&self) -> Vec<super::parse_ast::PNodeHandle> {
        vec![self.node.clone()]
    }
}
impl<L: PartialEq, T: PartialEq, R: PartialEq> PartialEq for PGrouped<L, T, R> {
    fn eq(&self, other: &Self) -> bool {
        self.left == other.left && self.inner == other.inner && self.right == other.right
    }
}
impl<L: Eq, T: Eq, R: Eq> Eq for PGrouped<L, T, R> {}
impl<L: Hash, T: Hash, R: Hash> Hash for PGrouped<L, T, R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.left.hash(state);
        self.inner.hash(state);
        self.right.hash(state);
    }
}
impl<L, T, R> PGrouped<L, T, R> {
    pub fn new(left: PReserved<L>, inner: T, right: PReserved<R>, pos: Span) -> Self
    where
        T: PGraphElement,
    {
        let mut children = left.graph_nodes();
        children.extend(inner.graph_nodes());
        children.extend(right.graph_nodes());
        let node = super::parse_ast::PNode::new(
            super::parse_ast::PNodeKind::Grouped { children },
            pos.clone(),
        );
        Self {
            left,
            inner,
            right,
            pos,
            node,
        }
    }
    pub fn update<U: PGraphElement>(self, replacement: U) -> PGrouped<L, U, R> {
        PGrouped::new(self.left, replacement, self.right, self.pos)
    }
    pub fn implied(left: L, inner: T, right: R) -> Self
    where
        L: PTokenValue,
        R: PTokenValue,
        T: PGraphElement,
    {
        Self::new(
            PReserved::implied(left),
            inner,
            PReserved::implied(right),
            (Position::NoPosition, Position::NoPosition),
        )
    }
}

#[derive(Clone, Debug)]
pub struct PDelimited<T, D> {
    pub(crate) first: Option<T>,
    pub(crate) inner: Vec<(D, T)>,
    pub(crate) end: Option<D>,
    pub(crate) pos: Span,
    pub(crate) node: super::parse_ast::PNodeHandle,
}
impl<T, D> PDelimited<T, D> {
    pub fn position(&self) -> &Span {
        &self.pos
    }
    pub fn node(&self) -> &super::parse_ast::PNodeHandle {
        &self.node
    }
    pub fn end(&self) -> Option<&D> {
        self.end.as_ref()
    }
}
impl<T, D> PGraphElement for PDelimited<T, D> {
    fn graph_nodes(&self) -> Vec<super::parse_ast::PNodeHandle> {
        vec![self.node.clone()]
    }
}
impl<T: PartialEq, D: PartialEq> PartialEq for PDelimited<T, D> {
    fn eq(&self, other: &Self) -> bool {
        self.first == other.first && self.inner == other.inner && self.end == other.end
    }
}
impl<T: Eq, D: Eq> Eq for PDelimited<T, D> {}
impl<T: Hash, D: Hash> Hash for PDelimited<T, D> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.first.hash(state);
        self.inner.hash(state);
        self.end.hash(state);
    }
}
impl<T, D> PDelimited<T, D> {
    pub fn new(first: Option<T>, inner: Vec<(D, T)>, end: Option<D>, pos: Span) -> Self
    where
        T: PGraphElement,
        D: PGraphElement,
    {
        let mut children = first.graph_nodes();
        for (delimiter, item) in &inner {
            children.extend(delimiter.graph_nodes());
            children.extend(item.graph_nodes());
        }
        children.extend(end.graph_nodes());
        let node = super::parse_ast::PNode::new(
            super::parse_ast::PNodeKind::Delimited { children },
            pos.clone(),
        );
        Self {
            first,
            inner,
            end,
            pos,
            node,
        }
    }
    pub fn len(&self) -> usize {
        if self.first.is_some() {
            1 + self.inner.len()
        } else {
            0
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn head_option(&self) -> Option<&T> {
        self.first.as_ref()
    }
    pub fn head(&self) -> &T {
        self.first.as_ref().expect("empty PDelimited")
    }
    pub fn tail(&self) -> impl Iterator<Item = &T> {
        self.inner.iter().map(|(_, item)| item)
    }
    pub fn to_seq(&self) -> Vec<&T> {
        self.first.iter().chain(self.tail()).collect()
    }
    pub fn delimiters(&self) -> impl Iterator<Item = &D> {
        self.inner
            .iter()
            .map(|(delimiter, _)| delimiter)
            .chain(self.end.iter())
    }
    pub fn update<U: PGraphElement>(self, mut replacement: Vec<U>) -> PDelimited<U, D>
    where
        D: PGraphElement,
    {
        assert!(
            (self.first.is_none() && replacement.is_empty())
                || (self.first.is_some() && self.inner.len() + 1 == replacement.len())
        );
        if replacement.is_empty() {
            PDelimited::new(None, Vec::new(), self.end, self.pos)
        } else {
            let first = replacement.remove(0);
            let inner = self
                .inner
                .into_iter()
                .map(|(d, _)| d)
                .zip(replacement)
                .collect();
            PDelimited::new(Some(first), inner, self.end, self.pos)
        }
    }
    pub fn empty() -> Self
    where
        T: PGraphElement,
        D: PGraphElement,
    {
        Self::new(
            None,
            Vec::new(),
            None,
            (Position::NoPosition, Position::NoPosition),
        )
    }
    pub fn from_pairs(pairs: Vec<(T, D)>, pos: Span) -> Self
    where
        T: PGraphElement,
        D: PGraphElement,
    {
        let mut pairs = pairs.into_iter();
        let Some((first, mut previous_delimiter)) = pairs.next() else {
            return Self::new(None, Vec::new(), None, pos);
        };
        let mut inner = Vec::new();
        for (item, delimiter) in pairs {
            inner.push((previous_delimiter, item));
            previous_delimiter = delimiter;
        }
        Self::new(Some(first), inner, Some(previous_delimiter), pos)
    }
}
impl<T: PGraphElement, D: Clone + PGraphElement> PDelimited<T, D> {
    pub fn implied(items: Vec<T>, delimiter: D) -> Self {
        let mut items = items.into_iter();
        let first = items.next();
        let end = first.as_ref().map(|_| delimiter.clone());
        Self::new(
            first,
            items.map(|item| (delimiter.clone(), item)).collect(),
            end,
            (Position::NoPosition, Position::NoPosition),
        )
    }
}
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ND<T>(pub T);
impl<T: PGraphElement> PGraphElement for ND<T> {
    fn graph_nodes(&self) -> Vec<super::parse_ast::PNodeHandle> {
        self.0.graph_nodes()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PKw {
    Import,
    Define,
    Field,
    Method,
    Function,
    FunctionD,
    Predicate,
    Domain,
    Interpretation,
    Axiom,
    Returns,
    Unique,
    Requires,
    Ensures,
    Invariant,
    Result,
    Exists,
    Forall,
    Forperm,
    New,
    Lhs,
    If,
    Elseif,
    Else,
    While,
    Fold,
    Unfold,
    Inhale,
    Exhale,
    Package,
    Apply,
    Assert,
    Assume,
    Var,
    Label,
    Goto,
    Quasihavoc,
    Quasihavocall,
    True,
    False,
    Null,
    None,
    Wildcard,
    Write,
    Epsilon,
    Int,
    Bool,
    Perm,
    Ref,
    Rational,
    Set,
    Seq,
    Map,
    Multiset,
}
impl PReservedString for PKw {
    fn token(&self) -> &'static str {
        match self {
            Self::Import => "import",
            Self::Define => "define",
            Self::Field => "field",
            Self::Method => "method",
            Self::Function => "function",
            Self::FunctionD => "function",
            Self::Predicate => "predicate",
            Self::Domain => "domain",
            Self::Interpretation => "interpretation",
            Self::Axiom => "axiom",
            Self::Returns => "returns",
            Self::Unique => "unique",
            Self::Requires => "requires",
            Self::Ensures => "ensures",
            Self::Invariant => "invariant",
            Self::Result => "result",
            Self::Exists => "exists",
            Self::Forall => "forall",
            Self::Forperm => "forperm",
            Self::New => "new",
            Self::Lhs => "lhs",
            Self::If => "if",
            Self::Elseif => "elseif",
            Self::Else => "else",
            Self::While => "while",
            Self::Fold => "fold",
            Self::Unfold => "unfold",
            Self::Inhale => "inhale",
            Self::Exhale => "exhale",
            Self::Package => "package",
            Self::Apply => "apply",
            Self::Assert => "assert",
            Self::Assume => "assume",
            Self::Var => "var",
            Self::Label => "label",
            Self::Goto => "goto",
            Self::Quasihavoc => "quasihavoc",
            Self::Quasihavocall => "quasihavocall",
            Self::True => "true",
            Self::False => "false",
            Self::Null => "null",
            Self::None => "none",
            Self::Wildcard => "wildcard",
            Self::Write => "write",
            Self::Epsilon => "epsilon",
            Self::Int => "Int",
            Self::Bool => "Bool",
            Self::Perm => "Perm",
            Self::Ref => "Ref",
            Self::Rational => "Rational",
            Self::Set => "Set",
            Self::Seq => "Seq",
            Self::Map => "Map",
            Self::Multiset => "Multiset",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PSym {
    LParen,
    RParen,
    LAngle,
    RAngle,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Quote,
    Comma,
    Semi,
    Colon,
    ColonColon,
    At,
    Star,
    Newline,
}
impl PReservedString for PSym {
    fn token(&self) -> &'static str {
        match self {
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LAngle => "<",
            Self::RAngle => ">",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::Quote => "\"",
            Self::Comma => ",",
            Self::Semi => ";",
            Self::Colon => ":",
            Self::ColonColon => "::",
            Self::At => "@",
            Self::Star => "*",
            Self::Newline => "\n",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PSymOp {
    Wand,
    EqEq,
    Ne,
    Le,
    Ge,
    Lt,
    Gt,
    AndAnd,
    OrOr,
    Implies,
    Iff,
    Mul,
    Div,
    ArithDiv,
    Mod,
    Plus,
    Minus,
    Append,
    Neg,
    Not,
    Assign,
    Dot,
    DotDot,
    Comma,
    RParen,
    LBracket,
    RBracket,
    Question,
    Colon,
    Or,
}
impl PReservedString for PSymOp {
    fn token(&self) -> &'static str {
        match self {
            Self::Wand => "--*",
            Self::EqEq => "==",
            Self::Ne => "!=",
            Self::Le => "<=",
            Self::Ge => ">=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::AndAnd => "&&",
            Self::OrOr => "||",
            Self::Implies => "==>",
            Self::Iff => "<==>",
            Self::Mul => "*",
            Self::Div => "/",
            Self::ArithDiv => "\\",
            Self::Mod => "%",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Append => "++",
            Self::Neg => "-",
            Self::Not => "!",
            Self::Assign => ":=",
            Self::Dot => ".",
            Self::DotDot => "..",
            Self::Comma => ",",
            Self::RParen => ")",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::Question => "?",
            Self::Colon => ":",
            Self::Or => "|",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PKwOp {
    In,
    Union,
    Intersection,
    Setminus,
    Subset,
    Unfolding,
    Applying,
    Asserting,
    Let,
    Perm,
    Acc,
    Old,
    Domain,
    Range,
    Seq,
    Set,
    Multiset,
    Map,
}
impl PReservedString for PKwOp {
    fn token(&self) -> &'static str {
        match self {
            Self::In => "in",
            Self::Union => "union",
            Self::Intersection => "intersection",
            Self::Setminus => "setminus",
            Self::Subset => "subset",
            Self::Unfolding => "unfolding",
            Self::Applying => "applying",
            Self::Asserting => "asserting",
            Self::Let => "let",
            Self::Perm => "perm",
            Self::Acc => "acc",
            Self::Old => "old",
            Self::Domain => "domain",
            Self::Range => "range",
            Self::Seq => "Seq",
            Self::Set => "Set",
            Self::Multiset => "Multiset",
            Self::Map => "Map",
        }
    }
}

/// Symbolic types in an operator's upstream type-substitution signatures.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SignatureType {
    Int,
    Bool,
    Perm,
    Ref,
    Impure,
    Wand,
    Predicate,
    Var(&'static str),
    Seq(Box<SignatureType>),
    Set(Box<SignatureType>),
    Multiset(Box<SignatureType>),
    Map(Box<SignatureType>, Box<SignatureType>),
}
pub type OperatorSignature = Vec<(&'static str, SignatureType)>;

fn signature(args: &[SignatureType], result: SignatureType) -> OperatorSignature {
    let keys = ["#T0", "#T1"];
    let mut bindings: OperatorSignature = args
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, t)| (keys[i], t))
        .collect();
    bindings.push(("#R", result));
    bindings
}
fn collection(t: SignatureType, kind: u8) -> SignatureType {
    match kind {
        0 => SignatureType::Seq(Box::new(t)),
        1 => SignatureType::Set(Box::new(t)),
        _ => SignatureType::Multiset(Box::new(t)),
    }
}
impl PSymOp {
    /// None means the punctuation is not a typed unary/binary operator.
    pub fn signatures(self) -> Option<Vec<OperatorSignature>> {
        use PSymOp::*;
        use SignatureType::*;
        let binary = |a, b, r| signature(&[a, b], r);
        Some(match self {
            PSymOp::Wand => vec![binary(Impure, Impure, SignatureType::Wand)],
            EqEq | Ne => vec![vec![("#T1", Var("#T0")), ("#R", Bool)]],
            Le | Ge | Lt | Gt => vec![binary(Perm, Perm, Bool), binary(Int, Int, Bool)],
            AndAnd => vec![binary(Bool, Bool, Bool), binary(Impure, Impure, Impure)],
            OrOr | Iff => vec![binary(Bool, Bool, Bool)],
            Implies => vec![binary(Bool, Bool, Bool), binary(Bool, Impure, Impure)],
            Mul => vec![
                binary(Perm, Perm, Perm),
                binary(Int, Perm, Perm),
                binary(Perm, Int, Perm),
                binary(Int, Int, Int),
            ],
            Div => vec![
                binary(Perm, Perm, Perm),
                binary(Perm, Int, Perm),
                binary(Int, Int, Perm),
                binary(Int, Int, Int),
            ],
            ArithDiv | Mod => vec![binary(Int, Int, Int)],
            Plus | Minus => vec![binary(Perm, Perm, Perm), binary(Int, Int, Int)],
            Append => {
                let t = collection(Var("#E"), 0);
                vec![binary(t.clone(), t.clone(), t)]
            }
            Neg => vec![signature(&[Perm], Perm), signature(&[Int], Int)],
            Not => vec![signature(&[Bool], Bool)],
            _ => return None,
        })
    }
    pub fn require_pure_args(self) -> bool {
        matches!(self, Self::EqEq | Self::Ne)
    }
}
impl PKwOp {
    pub fn signatures(self) -> Option<Vec<OperatorSignature>> {
        use SignatureType::*;
        let binary = |a, b, r| signature(&[a, b], r);
        Some(match self {
            Self::Union | Self::Intersection | Self::Setminus | Self::Subset => (1..=2)
                .map(|kind| {
                    let t = collection(Var("#E"), kind);
                    let result = if self == Self::Subset {
                        Bool
                    } else {
                        t.clone()
                    };
                    binary(t.clone(), t, result)
                })
                .collect(),
            Self::In => vec![
                vec![("#T1", collection(Var("#T0"), 1)), ("#R", Bool)],
                vec![("#T1", collection(Var("#T0"), 0)), ("#R", Bool)],
                vec![("#T1", collection(Var("#T0"), 2)), ("#R", Int)],
                vec![
                    ("#T1", Map(Box::new(Var("#T0")), Box::new(Var("#E")))),
                    ("#R", Bool),
                ],
            ],
            _ => return None,
        })
    }
}

/// Padding decisions consumed by the source reformatter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pad {
    Space,
    Line,
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Formatting {
    pub left: Option<Pad>,
    pub right: Option<Pad>,
    pub right_nest: bool,
    pub right_group: bool,
}
pub trait PFormatting {
    fn formatting(&self) -> Formatting;
}
impl<T: PFormatting> PFormatting for PReserved<T> {
    fn formatting(&self) -> Formatting {
        self.rs.formatting()
    }
}
impl<L: PReservedString, T, R> PFormatting for PGrouped<L, T, R> {
    fn formatting(&self) -> Formatting {
        Formatting {
            left: if matches!(self.left.rs.token(), "{" | "}") {
                Some(Pad::Space)
            } else {
                None
            },
            ..Formatting::default()
        }
    }
}

impl PFormatting for PKw {
    fn formatting(&self) -> Formatting {
        match self {
            Self::Import => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Define => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Field => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Method => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Function => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::FunctionD => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Predicate => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Domain => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Interpretation => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Axiom => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Returns => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Unique => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Requires => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Ensures => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Invariant => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Result => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Exists => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Forall => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Forperm => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::New => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Lhs => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::If => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Elseif => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Else => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::While => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Fold => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Unfold => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Inhale => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Exhale => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Package => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Apply => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Assert => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Assume => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Var => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Label => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Goto => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Quasihavoc => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Quasihavocall => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::True => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::False => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Null => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::None => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Wildcard => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Write => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Epsilon => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Int => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Bool => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Perm => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Ref => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Rational => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Set => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Seq => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Map => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Multiset => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
        }
    }
}

impl PFormatting for PSym {
    fn formatting(&self) -> Formatting {
        match self {
            Self::LParen => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::RParen => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::LAngle => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::RAngle => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::LBrace => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::RBrace => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::LBracket => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::RBracket => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Quote => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Comma => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Semi => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Colon => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::ColonColon => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Line),
                right_nest: true,
                right_group: true,
            },
            Self::At => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Star => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Newline => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
        }
    }
}

impl PFormatting for PSymOp {
    fn formatting(&self) -> Formatting {
        match self {
            Self::Wand => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::EqEq => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Line),
                right_nest: true,
                right_group: false,
            },
            Self::Ne => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Le => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Ge => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Lt => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Gt => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::AndAnd => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::OrOr => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Implies => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Line),
                right_nest: true,
                right_group: false,
            },
            Self::Iff => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Line),
                right_nest: true,
                right_group: false,
            },
            Self::Mul => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Div => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::ArithDiv => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Mod => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Plus => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Minus => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Append => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Neg => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Not => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Assign => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Line),
                right_nest: true,
                right_group: true,
            },
            Self::Dot => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::DotDot => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Comma => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::RParen => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::LBracket => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::RBracket => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Question => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Line),
                right_nest: true,
                right_group: true,
            },
            Self::Colon => Formatting {
                left: Some(Pad::Space),
                right: Some(Pad::Line),
                right_nest: false,
                right_group: true,
            },
            Self::Or => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
        }
    }
}

impl PFormatting for PKwOp {
    fn formatting(&self) -> Formatting {
        match self {
            Self::In => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Line),
                right_nest: true,
                right_group: true,
            },
            Self::Union => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Intersection => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Setminus => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Subset => Formatting {
                left: Some(Pad::Line),
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Unfolding => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Applying => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Asserting => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Let => Formatting {
                left: None,
                right: Some(Pad::Space),
                right_nest: false,
                right_group: false,
            },
            Self::Perm => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Acc => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Old => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Domain => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Range => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Seq => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Set => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Multiset => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
            Self::Map => Formatting {
                left: None,
                right: None,
                right_nest: false,
                right_group: false,
            },
        }
    }
}
