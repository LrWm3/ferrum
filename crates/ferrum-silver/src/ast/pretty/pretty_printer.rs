//! Width-aware document primitives and Silver AST rendering.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/pretty/PrettyPrinter.scala
//! Status: partial; document composition, parenthesis decisions, type rendering and a
//! basic expression subset are implemented. Full expression/statement/member dispatch,
//! metadata annotations and exact source layout engine remain pending; unsupported cases fail.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    expression::{Exp, ExpKind},
    program::{BuiltinOp, OperatorFixity},
    r#type::Type,
};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Doc {
    Nil,
    Text(String),
    Line(String),
    Concat(Vec<Doc>),
    Nest(usize, Box<Doc>),
    Group(Box<Doc>),
}
impl Doc {
    pub fn text(s: impl Into<String>) -> Self {
        let s = s.into();
        if s.is_empty() {
            Self::Nil
        } else {
            Self::Text(s)
        }
    }
    pub fn line() -> Self {
        Self::Line(" ".into())
    }
    pub fn concat(items: impl IntoIterator<Item = Doc>) -> Self {
        Self::Concat(items.into_iter().collect())
    }
    pub fn nest(self, n: usize) -> Self {
        Self::Nest(n, Box::new(self))
    }
    pub fn group(self) -> Self {
        Self::Group(Box::new(self))
    }
    pub fn parens(self) -> Self {
        Self::concat([Self::text("("), self, Self::text(")")])
    }
}
/// Rendering uses JVM-compatible UTF-16 widths; exact source queue/trampoline layout is pending.
pub fn pretty(width: usize, doc: &Doc) -> String {
    fn flat_width(doc: &Doc) -> Option<usize> {
        match doc {
            Doc::Nil => Some(0),
            Doc::Text(s) => Some(s.encode_utf16().count()),
            Doc::Line(s) => Some(s.encode_utf16().count()),
            Doc::Concat(ds) => ds
                .iter()
                .try_fold(0usize, |sum, d| Some(sum.saturating_add(flat_width(d)?))),
            Doc::Nest(_, d) | Doc::Group(d) => flat_width(d),
        }
    }
    fn write(
        doc: &Doc,
        width: usize,
        indent: usize,
        flat: bool,
        column: &mut usize,
        out: &mut String,
    ) {
        match doc {
            Doc::Nil => {}
            Doc::Text(s) => {
                out.push_str(s);
                *column += s.encode_utf16().count();
            }
            Doc::Line(s) if flat => {
                out.push_str(s);
                *column += s.encode_utf16().count();
            }
            Doc::Line(_) => {
                out.push('\n');
                out.extend(std::iter::repeat_n(' ', indent));
                *column = indent;
            }
            Doc::Concat(ds) => {
                for d in ds {
                    write(d, width, indent, flat, column, out);
                }
            }
            Doc::Nest(n, d) => write(d, width, indent.saturating_add(*n), flat, column, out),
            Doc::Group(d) => {
                let fit = flat || flat_width(d).is_some_and(|n| n <= width.saturating_sub(*column));
                write(d, width, indent, fit, column, out);
            }
        }
    }
    let mut out = String::new();
    let mut column = 0;
    write(doc, width, 0, false, &mut column, &mut out);
    out
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
    NonAssociative,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fixity {
    Prefix,
    Postfix,
    Infix(Associativity),
}
pub fn no_parentheses(
    inner_priority: u8,
    inner: Fixity,
    outer_priority: u8,
    outer: Fixity,
    side: Associativity,
) -> bool {
    inner_priority > outer_priority
        || match (inner, side) {
            (Fixity::Postfix, Associativity::Left) | (Fixity::Prefix, Associativity::Right) => true,
            (Fixity::Infix(Associativity::Left), Associativity::Left) => {
                inner_priority == outer_priority && outer == Fixity::Infix(Associativity::Left)
            }
            (Fixity::Infix(Associativity::Right), Associativity::Right) => {
                inner_priority == outer_priority && outer == Fixity::Infix(Associativity::Right)
            }
            (_, Associativity::NonAssociative) => inner == outer,
            _ => false,
        }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrintError {
    Unsupported(&'static str),
    MissingExpressionType,
}
pub fn show_type(t: &Type) -> Result<String, PrintError> {
    Ok(match t {
        Type::Bool => "Bool".into(),
        Type::Int => "Int".into(),
        Type::Ref => "Ref".into(),
        Type::Perm => "Perm".into(),
        Type::InternalType => "InternalType".into(),
        Type::Wand => "$WandType".into(),
        Type::Seq(x) => format!("Seq[{}]", show_type(x)?),
        Type::Set(x) => format!("Set[{}]", show_type(x)?),
        Type::Multiset(x) => format!("Multiset[{}]", show_type(x)?),
        Type::Map(k, v) => format!("Map[{},{}]", show_type(k)?, show_type(v)?),
        Type::Var(v) => v.name.clone(),
        Type::Domain(d) => {
            let args = d
                .type_arguments()
                .iter()
                .map(show_type)
                .collect::<Result<Vec<_>, _>>()?;
            if args.is_empty() {
                d.domain_name.clone()
            } else {
                format!("{}[{}]", d.domain_name, args.join(", "))
            }
        }
        Type::Backend(b) => b.viper_name.clone(),
        Type::Extension(e) => e
            .pretty_print()
            .map_err(|_| PrintError::Unsupported("extension type pretty printer"))?,
    })
}
fn fixity(f: OperatorFixity) -> Fixity {
    match f {
        OperatorFixity::Prefix => Fixity::Prefix,
        OperatorFixity::InfixLeft => Fixity::Infix(Associativity::Left),
        OperatorFixity::InfixRight => Fixity::Infix(Associativity::Right),
        OperatorFixity::InfixNonAssociative => Fixity::Infix(Associativity::NonAssociative),
    }
}
fn operator(e: &Exp) -> Option<(u8, Fixity)> {
    use ExpKind::*;
    let op = match e.kind() {
        Add(..) => BuiltinOp::Add,
        Sub(..) => BuiltinOp::Sub,
        Mul(..) => BuiltinOp::Mul,
        Div(..) => BuiltinOp::Div,
        Mod(..) => BuiltinOp::Mod,
        LtCmp(..) => BuiltinOp::Lt,
        LeCmp(..) => BuiltinOp::Le,
        GtCmp(..) => BuiltinOp::Gt,
        GeCmp(..) => BuiltinOp::Ge,
        Minus(..) => BuiltinOp::Neg,
        Or(..) => BuiltinOp::Or,
        And(..) => BuiltinOp::And,
        Implies(..) => BuiltinOp::Implies,
        MagicWand(..) => BuiltinOp::MagicWand,
        Not(..) => BuiltinOp::Not,
        PermAdd(..) => BuiltinOp::PermAdd,
        PermSub(..) => BuiltinOp::PermSub,
        PermMul(..) => BuiltinOp::PermMul,
        IntPermMul(..) => BuiltinOp::IntPermMul,
        PermDiv(..) | PermPermDiv(..) => BuiltinOp::PermDiv,
        FractionalPerm(..) => BuiltinOp::Frac,
        PermMinus(..) => BuiltinOp::PermNeg,
        PermLtCmp(..) => BuiltinOp::PermLt,
        PermLeCmp(..) => BuiltinOp::PermLe,
        PermGtCmp(..) => BuiltinOp::PermGt,
        PermGeCmp(..) => BuiltinOp::PermGe,
        EqCmp(..) | NeCmp(..) => return Some((6, Fixity::Infix(Associativity::NonAssociative))),
        _ => return None,
    };
    Some((op.priority(), fixity(op.fixity())))
}
fn operand(e: &Exp, outer: (u8, Fixity), side: Associativity) -> Result<Doc, PrintError> {
    let doc = show_exp(e)?;
    Ok(
        if operator(e).is_some_and(|(p, f)| !no_parentheses(p, f, outer.0, outer.1, side)) {
            doc.parens()
        } else {
            doc
        },
    )
}
pub fn show_exp(e: &Exp) -> Result<Doc, PrintError> {
    if e.metadata()
        .info
        .find(&|i| matches!(i, crate::ast::ast::Info::Annotation(_)))
        .is_some()
    {
        return Err(PrintError::Unsupported("expression annotations"));
    }
    use ExpKind::*;
    let atom = |s: String| Ok(Doc::text(s));
    match e.kind() {
        IntLit(n) => atom(n.to_string()),
        TrueLit => atom("true".into()),
        FalseLit => atom("false".into()),
        NullLit => atom("null".into()),
        RefLit(s) | BackendValueLit(s, _) => atom(s.clone()),
        LocalVar(v) => atom(v.name.clone()),
        Result(_) => atom("result".into()),
        WildcardPerm => atom("wildcard".into()),
        FullPerm => atom("write".into()),
        NoPerm => atom("none".into()),
        EpsilonPerm => atom("epsilon".into()),
        Minus(a) | Not(a) | PermMinus(a) => {
            let outer = operator(e).unwrap();
            let symbol = if matches!(e.kind(), Not(_)) { "!" } else { "-" };
            Ok(Doc::concat([
                Doc::text(symbol),
                operand(a, outer, Associativity::NonAssociative)?,
            ]))
        }
        Add(a, b)
        | Sub(a, b)
        | Mul(a, b)
        | Div(a, b)
        | Mod(a, b)
        | LtCmp(a, b)
        | LeCmp(a, b)
        | GtCmp(a, b)
        | GeCmp(a, b)
        | EqCmp(a, b)
        | NeCmp(a, b)
        | Or(a, b)
        | And(a, b)
        | Implies(a, b)
        | MagicWand(a, b)
        | FractionalPerm(a, b)
        | PermDiv(a, b)
        | PermPermDiv(a, b)
        | PermAdd(a, b)
        | PermSub(a, b)
        | PermMul(a, b)
        | IntPermMul(a, b)
        | PermLtCmp(a, b)
        | PermLeCmp(a, b)
        | PermGtCmp(a, b)
        | PermGeCmp(a, b) => {
            let symbol = match e.kind() {
                Add(..) | PermAdd(..) => "+",
                Sub(..) | PermSub(..) => "-",
                Mul(..) | PermMul(..) | IntPermMul(..) => "*",
                Div(..) => "\\",
                Mod(..) => "%",
                LtCmp(..) | PermLtCmp(..) => "<",
                LeCmp(..) | PermLeCmp(..) => "<=",
                GtCmp(..) | PermGtCmp(..) => ">",
                GeCmp(..) | PermGeCmp(..) => ">=",
                EqCmp(..) => "==",
                NeCmp(..) => "!=",
                Or(..) => "||",
                And(..) => "&&",
                Implies(..) => "==>",
                MagicWand(..) => "--*",
                _ => "/",
            };
            let outer = operator(e).unwrap();
            Ok(Doc::concat([
                operand(a, outer, Associativity::Left)?,
                Doc::text(format!(" {symbol}")),
                Doc::line(),
                operand(b, outer, Associativity::Right)?,
            ])
            .group())
        }
        _ => Err(PrintError::Unsupported("expression pretty printer")),
    }
}
pub fn pretty_expression(e: &Exp) -> Result<String, PrintError> {
    Ok(pretty(75, &show_exp(e)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ast::Metadata;
    #[test]
    fn preserves_operator_grouping() {
        let m = Metadata::default();
        let one = Exp::new(ExpKind::IntLit(1.into()), m.clone());
        let two = Exp::new(ExpKind::IntLit(2.into()), m.clone());
        let three = Exp::new(ExpKind::IntLit(3.into()), m.clone());
        let inner = Exp::new(ExpKind::Add(two, three), m.clone());
        let root = Exp::new(ExpKind::Mul(one, inner), m);
        assert_eq!(pretty_expression(&root).unwrap(), "1 * (2 + 3)");
    }
}
