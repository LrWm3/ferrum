//! Width-aware document primitives and Silver AST rendering.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/pretty/PrettyPrinter.scala
//! Status: partial; built-in expression, statement, member, program, type and
//! metadata rendering are implemented. Plugin-specific printers remain fallible;
//! layout follows the source group scan and UTF-16 width rules.

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
/// Render source document groups, counting UTF-16 text units and one scan unit per line.
pub fn pretty(width: usize, doc: &Doc) -> String {
    fn flat_width(doc: &Doc) -> Option<usize> {
        match doc {
            Doc::Nil => Some(0),
            Doc::Text(s) => Some(s.encode_utf16().count()),
            Doc::Line(_) => Some(1),
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
        remaining: &mut i64,
        out: &mut String,
    ) {
        match doc {
            Doc::Nil => {}
            Doc::Text(s) => {
                out.push_str(s);
                *remaining -= s.encode_utf16().count() as i64;
            }
            Doc::Line(s) if flat => {
                out.push_str(s);
                *remaining -= s.encode_utf16().count() as i64;
            }
            Doc::Line(_) => {
                out.push('\n');
                out.extend(std::iter::repeat_n(' ', indent));
                *remaining = width as i64 - indent as i64;
            }
            Doc::Concat(ds) => {
                for d in ds {
                    write(d, width, indent, flat, remaining, out);
                }
            }
            Doc::Nest(n, d) => write(d, width, indent.saturating_add(*n), flat, remaining, out),
            Doc::Group(d) => {
                let fit = flat_width(d).is_some_and(|n| n as i64 <= *remaining);
                write(d, width, indent, fit, remaining, out);
            }
        }
    }
    let mut out = String::new();
    let mut remaining = width as i64;
    write(doc, width, 0, false, &mut remaining, &mut out);
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
        Type::Map(pair) => format!("Map[{},{}]", show_type(&pair.0)?, show_type(&pair.1)?),
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
        SeqAppend(..) => return Some((8, Fixity::Infix(Associativity::Left))),
        SeqIndex(..) | SeqTake(..) | SeqDrop(..) => {
            return Some((10, Fixity::Infix(Associativity::Left)));
        }
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
    let result = show_exp_inner(e)?;
    let annotation = e
        .metadata()
        .info
        .find(&|i| matches!(i, crate::ast::ast::Info::Annotation(_)));
    if let Some(crate::ast::ast::Info::Annotation(values)) = annotation {
        if !values.is_empty() {
            let docs = values
                .iter()
                .map(|(key, items)| {
                    Doc::text(format!(
                        "@{}({})",
                        key,
                        items
                            .iter()
                            .map(|v| format!("\"{}\"", v))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                })
                .collect::<Vec<_>>();
            return Ok(Doc::concat([
                join_docs(docs, Doc::text(" ")),
                Doc::line(),
                result.parens(),
            ]));
        }
    }
    Ok(result)
}
fn join_docs(docs: Vec<Doc>, separator: Doc) -> Doc {
    let mut result = Vec::new();
    for (i, doc) in docs.into_iter().enumerate() {
        if i > 0 {
            result.push(separator.clone());
        }
        result.push(doc);
    }
    Doc::concat(result)
}
fn arguments(args: &[Exp]) -> Result<Doc, PrintError> {
    Ok(join_docs(
        args.iter().map(show_exp).collect::<Result<Vec<_>, _>>()?,
        Doc::concat([Doc::text(","), Doc::line()]).group(),
    )
    .parens())
}
fn bracketed(value: Doc) -> Doc {
    Doc::concat([Doc::text("["), value, Doc::text("]")])
}
fn named_call(name: &str, args: &[Exp]) -> Result<Doc, PrintError> {
    Ok(Doc::concat([Doc::text(name), arguments(args)?]))
}
fn variable_list(vars: &[crate::ast::program::LocalVarDecl]) -> Result<Doc, PrintError> {
    Ok(join_docs(
        vars.iter()
            .map(|v| Ok(Doc::text(format!("{}: {}", v.name, show_type(&v.typ)?))))
            .collect::<Result<Vec<_>, PrintError>>()?,
        Doc::concat([Doc::text(","), Doc::line()]).group(),
    ))
}
fn trigger_list(triggers: &[crate::ast::expression::Trigger]) -> Result<Vec<Doc>, PrintError> {
    triggers
        .iter()
        .map(|t| {
            Ok(Doc::concat([
                Doc::text("{ "),
                join_docs(
                    t.exps.iter().map(show_exp).collect::<Result<Vec<_>, _>>()?,
                    Doc::concat([Doc::text(","), Doc::line()]).group(),
                ),
                Doc::text(" }"),
            ]))
        })
        .collect()
}
fn show_exp_inner(e: &Exp) -> Result<Doc, PrintError> {
    use ExpKind::*;
    let atom = |s: String| Ok(Doc::text(s));
    match e.kind() {
        IntLit(n) => atom(n.to_string()),
        TrueLit => atom("true".into()),
        FalseLit => atom("false".into()),
        NullLit => atom("null".into()),
        RefLit(s) | BackendValueLit(s, _) => atom(s.clone()),
        LocalVar(v) => atom(v.name.clone()),
        LocalVarWithVersion(name, _) => atom(name.clone()),
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
        | SeqAppend(a, b)
        | PermLtCmp(a, b)
        | PermLeCmp(a, b)
        | PermGtCmp(a, b)
        | PermGeCmp(a, b) => {
            let symbol = match e.kind() {
                Add(..) | PermAdd(..) => "+",
                Sub(..) | PermSub(..) => "-",
                Mul(..) | PermMul(..) | IntPermMul(..) => "*",
                Div(..) => "\\",
                SeqAppend(..) => "++",
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
        FieldAccess(a) => Ok(Doc::concat([
            show_exp(&a.receiver)?,
            Doc::text(format!(".{}", a.field.name)),
        ])),
        PredicateAccess(a) => named_call(&a.predicate_name, &a.args),
        FieldAccessPredicate(a, _) => {
            let loc = show_exp(&Exp::new(FieldAccess(a.clone()), a.meta.clone()))?;
            let perm = e.permission_or_full().expect("field permission");
            Ok(Doc::concat([
                Doc::text("acc"),
                Doc::concat([loc, Doc::text(", "), show_exp(&perm)?]).parens(),
            ]))
        }
        PredicateAccessPredicate(a) => {
            let loc = show_exp(&Exp::new(
                PredicateAccess(a.location.clone()),
                a.meta.clone(),
            ))?;
            let perm = e.permission_or_full().expect("predicate permission");
            Ok(Doc::concat([
                Doc::text("acc"),
                Doc::concat([loc, Doc::text(", "), show_exp(&perm)?]).parens(),
            ]))
        }
        FuncApp(name, args) | BackendFuncApp(name, args) => named_call(name, args),
        DomainFuncApp(name, args, types) => {
            let app = named_call(name, args)?;
            if types.is_empty() {
                Ok(app)
            } else {
                Ok(Doc::concat([
                    app,
                    Doc::text(": "),
                    Doc::text(show_type(
                        &e.typ().map_err(|_| PrintError::MissingExpressionType)?,
                    )?),
                ])
                .parens())
            }
        }
        Old(inner) => named_call("old", std::slice::from_ref(inner)),
        LabelledOld(inner, label) | DebugLabelledOld(inner, label) => Ok(Doc::concat([
            Doc::text("old"),
            bracketed(Doc::text(label)),
            show_exp(inner)?.parens(),
        ])),
        CurrentPerm(inner) => named_call("perm", std::slice::from_ref(inner)),
        Unfolding(access, body) | Applying(access, body) | Asserting(access, body) => {
            let keyword = match e.kind() {
                Unfolding(..) => "unfolding",
                Applying(..) => "applying",
                _ => "asserting",
            };
            let access = if matches!(e.kind(), Asserting(..)) {
                show_exp(access)?.parens()
            } else {
                show_exp(access)?
            };
            let result = Doc::concat([
                Doc::text(format!("{keyword} ")),
                access.nest(2),
                Doc::text(" in"),
                Doc::concat([Doc::line(), show_exp(body)?]).nest(2),
            ])
            .parens();
            Ok(if matches!(e.kind(), Unfolding(..)) {
                result.group()
            } else {
                result
            })
        }
        Let(v, value, body) => Ok(Doc::concat([
            Doc::text(format!("let {} ==", v.name)),
            Doc::concat([Doc::line(), show_exp(value)?.parens()]).nest(2),
            Doc::text(" in"),
            Doc::concat([Doc::line(), show_exp(body)?]).nest(2),
        ])
        .parens()),
        CondExp(condition, yes, no) => Ok(Doc::concat([
            show_exp(condition)?,
            Doc::text(" ?"),
            Doc::concat([
                Doc::line(),
                show_exp(yes)?,
                Doc::text(" :"),
                Doc::line(),
                show_exp(no)?,
            ])
            .nest(2),
        ])
        .parens()
        .group()),
        Forall(vars, triggers, body) | Exists(vars, triggers, body) => {
            let forall = matches!(e.kind(), Forall(..));
            let trigger_docs = trigger_list(triggers)?;
            let triggers_doc = if trigger_docs.is_empty() {
                Doc::Nil
            } else {
                Doc::concat([
                    if forall { Doc::line() } else { Doc::text(" ") },
                    join_docs(
                        trigger_docs,
                        if forall { Doc::line() } else { Doc::text(" ") },
                    ),
                ])
            };
            let separator = if forall && triggers.is_empty() {
                Doc::Nil
            } else if forall {
                Doc::line()
            } else {
                Doc::text(" ")
            };
            let nested = Doc::concat([triggers_doc, separator, show_exp(body)?]).nest(2);
            let result = Doc::concat([
                Doc::text(if forall { "forall " } else { "exists " }),
                variable_list(vars)?,
                Doc::text(" ::"),
                nested,
            ])
            .parens();
            Ok(if forall { result.group() } else { result })
        }
        ForPerm(vars, resource, body) => Ok(Doc::concat([
            Doc::text("forperm"),
            Doc::concat([
                Doc::line(),
                variable_list(vars)?,
                Doc::text(" "),
                bracketed(show_exp(resource)?),
                Doc::text(" :: "),
                show_exp(body)?,
            ])
            .nest(2),
        ])
        .parens()
        .group()),
        InhaleExhaleExp(a, b) => Ok(bracketed(Doc::concat([
            show_exp(a)?,
            Doc::text(","),
            Doc::line(),
            show_exp(b)?,
        ]))
        .group()),
        DebugPermMin(a, b) => Ok(Doc::concat([
            Doc::text("min"),
            Doc::concat([show_exp(a)?, Doc::text(", "), show_exp(b)?]).parens(),
        ])),
        EmptySeq(t) | EmptySet(t) | EmptyMultiset(t) => {
            let name = match e.kind() {
                EmptySeq(_) => "Seq",
                EmptySet(_) => "Set",
                _ => "Multiset",
            };
            atom(format!("{name}[{}]()", show_type(t)?))
        }
        ExplicitSeq(args) | ExplicitSet(args) | ExplicitMultiset(args) | ExplicitMap(args) => {
            let name = match e.kind() {
                ExplicitSeq(_) => "Seq",
                ExplicitSet(_) => "Set",
                ExplicitMultiset(_) => "Multiset",
                _ => "Map",
            };
            named_call(name, args)
        }
        EmptyMap(k, v) => atom(format!("Map[{},{}]()", show_type(k)?, show_type(v)?)),
        RangeSeq(a, b) => Ok(Doc::concat([
            Doc::text("["),
            show_exp(a)?,
            Doc::text(".."),
            show_exp(b)?,
            Doc::text(")"),
        ])),
        SeqIndex(base, index) | SeqTake(base, index) | SeqDrop(base, index) => {
            let (base, inner) = if let SeqDrop(taken, drop) = e.kind() {
                if let SeqTake(original, take) = taken.kind() {
                    (
                        original,
                        Doc::concat([show_exp(drop)?, Doc::text(".."), show_exp(take)?]),
                    )
                } else {
                    (base, Doc::concat([show_exp(index)?, Doc::text("..")]))
                }
            } else if matches!(e.kind(), SeqTake(..)) {
                (base, Doc::concat([Doc::text(".."), show_exp(index)?]))
            } else {
                (base, show_exp(index)?)
            };
            let source_base = if matches!(e.kind(), SeqDrop(taken, _) if !matches!(taken.kind(), SeqTake(..)))
            {
                show_exp(base)?
            } else {
                operand(
                    base,
                    (10, Fixity::Infix(Associativity::Left)),
                    Associativity::Left,
                )?
            };
            Ok(Doc::concat([source_base, bracketed(inner)]))
        }
        SeqUpdate(base, index, value) | MapUpdate(base, index, value) => Ok(Doc::concat([
            show_exp(base)?,
            bracketed(Doc::concat([
                show_exp(index)?,
                Doc::text(" :="),
                Doc::line(),
                show_exp(value)?,
            ]))
            .group(),
        ])),
        SeqLength(inner) | AnySetCardinality(inner) | MapCardinality(inner) => Ok(Doc::concat([
            Doc::text("|"),
            show_exp(inner)?,
            Doc::text("|"),
        ])),
        SeqContains(a, b)
        | AnySetContains(a, b)
        | MapContains(a, b)
        | AnySetUnion(a, b)
        | AnySetIntersection(a, b)
        | AnySetSubset(a, b)
        | AnySetMinus(a, b) => {
            let op = match e.kind() {
                AnySetUnion(..) => "union",
                AnySetIntersection(..) => "intersection",
                AnySetSubset(..) => "subset",
                AnySetMinus(..) => "setminus",
                _ => "in",
            };
            Ok(Doc::concat([
                show_exp(a)?,
                Doc::text(format!(" {op}")),
                Doc::line(),
                show_exp(b)?,
            ])
            .parens()
            .group())
        }
        Maplet(k, v) => Ok(Doc::concat([show_exp(k)?, Doc::text(" := "), show_exp(v)?])),
        MapLookup(base, key) => Ok(Doc::concat([show_exp(base)?, bracketed(show_exp(key)?)])),
        MapDomain(base) => named_call("domain", std::slice::from_ref(base)),
        MapRange(base) => named_call("range", std::slice::from_ref(base)),
        Extension(extension) => Ok(Doc::text(extension.0.pretty_print()?)),
    }
}
pub fn pretty_expression(e: &Exp) -> Result<String, PrintError> {
    Ok(pretty(75, &show_exp(e)?))
}

fn doc_empty(doc: &Doc) -> bool {
    match doc {
        Doc::Nil => true,
        Doc::Text(s) => s.is_empty(),
        Doc::Concat(v) => v.iter().all(doc_empty),
        Doc::Nest(_, v) | Doc::Group(v) => doc_empty(v),
        Doc::Line(_) => false,
    }
}
fn line_join(a: Doc, b: Doc) -> Doc {
    if doc_empty(&a) {
        b
    } else if doc_empty(&b) {
        a
    } else {
        Doc::concat([a, Doc::line(), b])
    }
}
fn comments(info: &crate::ast::ast::Info) -> Doc {
    join_docs(
        info.comments()
            .into_iter()
            .map(|v| {
                if v.is_empty() {
                    Doc::Nil
                } else {
                    Doc::text(format!("// {v}"))
                }
            })
            .collect(),
        Doc::line(),
    )
}
fn annotations(info: &crate::ast::ast::Info) -> Doc {
    match info.find(&|i| matches!(i, crate::ast::ast::Info::Annotation(_))) {
        Some(crate::ast::ast::Info::Annotation(values)) => join_docs(
            values
                .iter()
                .map(|(key, values)| {
                    Doc::text(format!(
                        "@{}({})",
                        key,
                        values
                            .iter()
                            .map(|v| format!("\"{v}\""))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ))
                })
                .collect(),
            Doc::line(),
        ),
        _ => Doc::Nil,
    }
}
fn with_info(info: &crate::ast::ast::Info, doc: Doc) -> Doc {
    line_join(line_join(comments(info), annotations(info)), doc)
}
fn braced(doc: Doc) -> Doc {
    Doc::concat([Doc::text("{"), doc, Doc::text("}")])
}
fn local_var(v: &crate::ast::expression::LocalVar) -> Doc {
    Doc::text(v.name.clone())
}
fn field_doc(v: &crate::ast::expression::FieldAccess) -> Result<Doc, PrintError> {
    show_exp(&Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone()))
}
fn predicate_perm_doc(
    v: &crate::ast::statement::PredicateAccessPredicate,
) -> Result<Doc, PrintError> {
    show_exp(&Exp::new(
        ExpKind::PredicateAccessPredicate(v.clone()),
        v.meta.clone(),
    ))
}
fn resource_doc(v: &crate::ast::statement::ResourceAccess) -> Result<Doc, PrintError> {
    use crate::ast::statement::ResourceAccess;
    match v {
        ResourceAccess::Field(f) => field_doc(f),
        ResourceAccess::Predicate(p) => show_exp(&Exp::new(
            ExpKind::PredicateAccess(p.clone()),
            p.meta.clone(),
        )),
        ResourceAccess::MagicWand(e) => show_exp(e),
    }
}
fn is_decreases(e: &Exp) -> bool {
    matches!(e.kind(),ExpKind::Extension(v) if v.0.as_any().is::<crate::plugin::standard::termination::termination_ast_extension::DecreasesClause>())
}
fn contracts(name: &str, items: &[Exp]) -> Result<Doc, PrintError> {
    if items.is_empty() {
        return Ok(Doc::Nil);
    }
    Ok(Doc::concat([
        Doc::line(),
        join_docs(
            items
                .iter()
                .map(|e| {
                    Ok(Doc::concat([
                        Doc::text(format!("{name} ")),
                        show_exp(e)?.nest(2),
                    ]))
                })
                .collect::<Result<Vec<_>, PrintError>>()?,
            Doc::line(),
        ),
    ]))
}
fn contracts_with_decreases(name: &str, items: &[Exp]) -> Result<(Doc, Vec<Exp>), PrintError> {
    let (measures, ordinary): (Vec<_>, Vec<_>) = items.iter().cloned().partition(is_decreases);
    Ok((contracts(name, &ordinary)?, measures))
}
fn decreases(items: &[Exp]) -> Result<Doc, PrintError> {
    if items.is_empty() {
        Ok(Doc::Nil)
    } else {
        Ok(Doc::concat([
            Doc::line(),
            join_docs(
                items
                    .iter()
                    .map(|e| show_exp(e).map(|d| d.nest(2)))
                    .collect::<Result<Vec<_>, _>>()?,
                Doc::line(),
            ),
        ]))
    }
}
fn empty_sequence_without_comments(s: &crate::ast::statement::Stmt) -> bool {
    matches!(s.kind(),crate::ast::statement::StmtKind::Seqn{statements,declarations} if statements.is_empty() && declarations.is_empty())
        && s.metadata().info.comments().is_empty()
}
fn locals_in(declarations: &[crate::ast::program::Declaration]) -> Result<Vec<Doc>, PrintError> {
    use crate::ast::program::Declaration;
    declarations
        .iter()
        .filter_map(|d| {
            if let Declaration::Local(v) = d {
                Some(v)
            } else {
                None
            }
        })
        .map(|v| Ok(Doc::text(format!("var {}: {}", v.name, show_type(&v.typ)?))))
        .collect()
}
pub fn show_block(statement: &crate::ast::statement::Stmt) -> Result<Doc, PrintError> {
    use crate::ast::statement::StmtKind;
    match statement.kind() {
        StmtKind::Seqn {
            statements,
            declarations,
        } => {
            let nonempty = statements
                .iter()
                .filter(|s| !empty_sequence_without_comments(s))
                .collect::<Vec<_>>();
            let mut content = locals_in(declarations)?;
            for s in &nonempty {
                content.push(show_stmt(s)?);
            }
            let prefix = if declarations.is_empty() && nonempty.is_empty() {
                Doc::Nil
            } else {
                Doc::line()
            };
            Ok(braced(Doc::concat([
                Doc::concat([prefix, join_docs(content, Doc::line())]).nest(2),
                Doc::line(),
            ])))
        }
        _ => Ok(braced(
            Doc::concat([Doc::line(), show_stmt(statement)?]).nest(2),
        )),
    }
}
fn show_else(statement: &crate::ast::statement::Stmt) -> Result<Doc, PrintError> {
    use crate::ast::statement::StmtKind;
    match statement.kind() {
        StmtKind::Seqn {
            statements,
            declarations,
        } if statements.is_empty() && declarations.is_empty() => Ok(Doc::Nil),
        StmtKind::Seqn {
            statements,
            declarations,
        } if statements.len() == 1 && declarations.is_empty() => show_else(&statements[0]),
        StmtKind::If {
            condition,
            then_branch,
            else_branch,
        } => Ok(Doc::concat([
            Doc::text(" elseif "),
            show_exp(condition)?.parens(),
            Doc::text(" "),
            show_block(then_branch)?,
            show_else(else_branch)?,
        ])),
        _ => Ok(Doc::concat([Doc::text(" else "), show_block(statement)?])),
    }
}
pub fn show_stmt(statement: &crate::ast::statement::Stmt) -> Result<Doc, PrintError> {
    use crate::ast::statement::StmtKind;
    let body = match statement.kind() {
        StmtKind::NewStmt { lhs, fields } => Doc::concat([
            local_var(lhs),
            Doc::text(format!(
                " := new({})",
                fields
                    .iter()
                    .map(|f| f.name.as_str())
                    .collect::<Vec<_>>()
                    .join(", ")
            )),
        ]),
        StmtKind::LocalVarAssign { lhs, rhs } => {
            Doc::concat([local_var(lhs), Doc::text(" := "), show_exp(rhs)?.nest(2)])
        }
        StmtKind::FieldAssign { lhs, rhs } => {
            Doc::concat([field_doc(lhs)?, Doc::text(" := "), show_exp(rhs)?.nest(2)])
        }
        StmtKind::Fold(p) | StmtKind::Unfold(p) => Doc::concat([
            Doc::text(if matches!(statement.kind(), StmtKind::Fold(_)) {
                "fold "
            } else {
                "unfold "
            }),
            predicate_perm_doc(p)?.nest(2),
        ]),
        StmtKind::Package { wand, proof_script } => Doc::concat([
            Doc::text("package "),
            show_exp(wand)?,
            Doc::text(" "),
            show_block(proof_script)?,
        ]),
        StmtKind::Apply(e)
        | StmtKind::Inhale(e)
        | StmtKind::Exhale(e)
        | StmtKind::Assert(e)
        | StmtKind::Assume(e) => {
            let keyword = match statement.kind() {
                StmtKind::Apply(_) => "apply",
                StmtKind::Inhale(_) => "inhale",
                StmtKind::Exhale(_) => "exhale",
                StmtKind::Assert(_) => "assert",
                _ => "assume",
            };
            Doc::concat([Doc::text(format!("{keyword} ")), show_exp(e)?.nest(2)])
        }
        StmtKind::MethodCall {
            method_name,
            args,
            targets,
        } => {
            let call = Doc::concat([Doc::text(method_name), arguments(args)?.nest(2)]);
            if targets.is_empty() {
                call
            } else {
                Doc::concat([
                    join_docs(targets.iter().map(local_var).collect(), Doc::text(", ")),
                    Doc::text(" := "),
                    call,
                ])
            }
        }
        StmtKind::Seqn {
            statements,
            declarations,
        } if !declarations.is_empty() => {
            let mut docs = locals_in(declarations)?;
            let nonempty = statements
                .iter()
                .filter(|s| !empty_sequence_without_comments(s))
                .collect::<Vec<_>>();
            if statements.is_empty() && docs.is_empty() {
                Doc::Nil
            } else {
                for item in nonempty {
                    docs.push(show_stmt(item)?);
                }
                braced(Doc::concat([
                    Doc::concat([Doc::line(), join_docs(docs, Doc::line())]).nest(2),
                    Doc::line(),
                ]))
            }
        }
        StmtKind::Seqn { statements, .. } => {
            if statements.is_empty() && statement.metadata().info.comments().is_empty() {
                Doc::Nil
            } else {
                join_docs(
                    statements
                        .iter()
                        .filter(|s| !empty_sequence_without_comments(s))
                        .map(|s| show_stmt(s))
                        .collect::<Result<Vec<_>, _>>()?,
                    Doc::line(),
                )
            }
        }
        StmtKind::While {
            condition,
            invariants,
            body,
        } => {
            let (invariants_doc, measures) = contracts_with_decreases("invariant", invariants)?;
            Doc::concat([
                Doc::text("while "),
                show_exp(condition)?.parens(),
                Doc::concat([invariants_doc, decreases(&measures)?]).nest(2),
                Doc::text(" "),
                if invariants.is_empty() {
                    Doc::Nil
                } else {
                    Doc::line()
                },
                show_block(body)?,
            ])
        }
        StmtKind::If {
            condition,
            then_branch,
            else_branch,
        } => Doc::concat([
            Doc::text("if "),
            show_exp(condition)?.parens(),
            Doc::text(" "),
            show_block(then_branch)?,
            show_else(else_branch)?,
        ]),
        StmtKind::Label(label) => Doc::concat([
            Doc::text(format!("label {}", label.name)),
            contracts("invariant", &label.invariants)?.nest(2),
        ]),
        StmtKind::Goto(name) => Doc::text(format!("goto {name}")),
        StmtKind::LocalVarDeclStmt(v) => {
            Doc::text(format!("var {}: {}", v.name, show_type(&v.typ)?))
        }
        StmtKind::Quasihavoc { guard, resource } => {
            let guard = match guard {
                Some(g) => Doc::concat([show_exp(g)?, Doc::text(" ==> ")]),
                None => Doc::Nil,
            };
            Doc::concat([Doc::text("quasihavoc "), guard, resource_doc(resource)?])
        }
        StmtKind::Quasihavocall {
            variables,
            guard,
            resource,
        } => {
            let guard = match guard {
                Some(g) => Doc::concat([show_exp(g)?, Doc::text(" ==> ")]),
                None => Doc::Nil,
            };
            Doc::concat([
                Doc::text("quasihavocall "),
                join_docs(
                    variables
                        .iter()
                        .map(|v| Ok(Doc::text(format!("{}: {}", v.name, show_type(&v.typ)?))))
                        .collect::<Result<Vec<_>, PrintError>>()?,
                    Doc::text(", "),
                ),
                Doc::text(" :: "),
                guard,
                resource_doc(resource)?,
            ])
        }
        StmtKind::Extension(v) => Doc::text(v.0.pretty_print()?),
    };
    Ok(with_info(&statement.metadata().info, body))
}

fn domain_function(function: &crate::ast::program::DomainFunc) -> Result<Doc, PrintError> {
    use crate::ast::program::AnyLocalVarDecl;
    let args = function
        .formal_args
        .iter()
        .map(|arg| match arg {
            AnyLocalVarDecl::Named(v) => {
                Ok(Doc::text(format!("{}: {}", v.name, show_type(&v.typ)?)))
            }
            AnyLocalVarDecl::Unnamed(v) => Ok(Doc::text(show_type(&v.typ)?)),
        })
        .collect::<Result<Vec<_>, PrintError>>()?;
    let args = join_docs(args, Doc::concat([Doc::text(","), Doc::line()]).group()).parens();
    let interpretation = function
        .interpretation
        .as_ref()
        .map(|v| Doc::text(format!("interpretation \"{v}\"")))
        .unwrap_or(Doc::Nil);
    Ok(with_info(
        &function.meta.info,
        Doc::concat([
            Doc::text(if function.unique {
                "unique function "
            } else {
                "function "
            }),
            Doc::text(&function.name),
            args,
            Doc::text(format!(": {} ", show_type(&function.typ)?)),
            interpretation,
        ]),
    ))
}
fn domain_axiom(axiom: &crate::ast::program::DomainAxiom) -> Result<Doc, PrintError> {
    use crate::ast::program::DomainAxiomKind;
    let (name, expression, meta) = match axiom.kind() {
        DomainAxiomKind::Named {
            name, exp, meta, ..
        } => (Some(name), exp, meta),
        DomainAxiomKind::Anonymous { exp, meta, .. } => (None, exp, meta),
    };
    let head = match name {
        Some(name) => format!("axiom {name} "),
        None => "axiom ".into(),
    };
    Ok(with_info(
        &meta.info,
        Doc::concat([
            Doc::text(head),
            braced(Doc::concat([
                Doc::concat([Doc::line(), show_exp(expression)?]).nest(2),
                Doc::line(),
            ])),
        ]),
    ))
}
fn domain_doc(domain: &crate::ast::program::Domain) -> Result<Doc, PrintError> {
    let parameters = if domain.type_vars.is_empty() {
        String::new()
    } else {
        format!(
            "[{}]",
            domain
                .type_vars
                .iter()
                .map(|v| v.name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    let interpretation = match &domain.interpretations {
        None => String::new(),
        Some(values) => format!(
            "interpretation ({})",
            values
                .iter()
                .map(|(k, v)| format!("{k}: \"{v}\""))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    };
    let mut members = domain
        .functions
        .iter()
        .map(domain_function)
        .collect::<Result<Vec<_>, _>>()?;
    members.extend(
        domain
            .axioms
            .iter()
            .map(domain_axiom)
            .collect::<Result<Vec<_>, _>>()?,
    );
    Ok(Doc::concat([
        Doc::text(format!(
            "domain {}{} {} ",
            domain.name, parameters, interpretation
        )),
        braced(Doc::concat([
            Doc::concat([
                Doc::line(),
                Doc::line(),
                join_docs(members, Doc::concat([Doc::line(), Doc::line()])),
            ])
            .nest(2),
            Doc::line(),
        ])),
    ]))
}
pub fn show_member(member: &crate::ast::program::Member) -> Result<Doc, PrintError> {
    use crate::ast::program::Member;
    let (doc, info) = match member {
        Member::Field(v) => (
            Doc::text(format!("field {}: {}", v.name, show_type(&v.typ)?)),
            &v.meta.info,
        ),
        Member::Domain(v) => (domain_doc(v)?, &v.meta.info),
        Member::Predicate(v) => {
            let body = match &v.body {
                Some(e) => braced(Doc::concat([
                    Doc::concat([Doc::line(), show_exp(e)?]).nest(2),
                    Doc::line(),
                ])),
                None => Doc::Nil,
            };
            (
                Doc::concat([
                    Doc::text(format!("predicate {}", v.name)),
                    variable_list(&v.formal_args)?.parens().nest(2),
                    Doc::text(" "),
                    body,
                ]),
                &v.meta.info,
            )
        }
        Member::Function(v) => {
            let (pre, mut measures) = contracts_with_decreases("requires", &v.pres)?;
            let (post, post_measures) = contracts_with_decreases("ensures", &v.posts)?;
            measures.extend(post_measures);
            let body = match &v.body {
                Some(e) => braced(Doc::concat([
                    Doc::concat([Doc::line(), show_exp(e)?]).nest(2),
                    Doc::line(),
                ])),
                None => Doc::Nil,
            };
            (
                Doc::concat([
                    Doc::text(format!("function {}", v.name)),
                    variable_list(&v.formal_args)?.parens().nest(2),
                    Doc::text(format!(": {}", show_type(&v.typ)?)),
                    Doc::concat([pre, post, decreases(&measures)?]).nest(2),
                    Doc::line(),
                    body,
                ]),
                &v.meta.info,
            )
        }
        Member::Method(v) => {
            let (pre, mut measures) = contracts_with_decreases("requires", &v.pres)?;
            let (post, post_measures) = contracts_with_decreases("ensures", &v.posts)?;
            measures.extend(post_measures);
            let returns = if v.formal_returns.is_empty() {
                Doc::Nil
            } else {
                Doc::concat([
                    Doc::line(),
                    Doc::text("returns "),
                    variable_list(&v.formal_returns)?.parens(),
                ])
                .nest(2)
            };
            let head = Doc::concat([
                Doc::text(format!("method {}", v.name)),
                variable_list(&v.formal_args)?.parens().nest(2),
                returns,
            ])
            .group();
            let body = match &v.body {
                Some(s) => show_block(s)?,
                None => Doc::Nil,
            };
            (
                Doc::concat([
                    head,
                    Doc::concat([pre, post, decreases(&measures)?]).nest(2),
                    Doc::line(),
                    body,
                ]),
                &v.meta.info,
            )
        }
        Member::Extension(v) => {
            let metadata =
                v.0.metadata()
                    .map_err(|_| PrintError::Unsupported("extension member metadata"))?;
            (Doc::text(v.0.pretty_print()?), &metadata.info)
        }
    };
    Ok(with_info(info, doc))
}
pub fn show_program(program: &crate::ast::program::Program) -> Result<Doc, PrintError> {
    let members = program
        .members()
        .iter()
        .map(show_member)
        .collect::<Result<Vec<_>, _>>()?;
    Ok(line_join(
        comments(&program.meta.info),
        join_docs(members, Doc::concat([Doc::line(), Doc::line()])),
    ))
}
pub fn show_node(node: &crate::ast::utility::nodes::Node) -> Result<Doc, PrintError> {
    use crate::ast::{statement::StmtKind, utility::nodes::Node};
    match node {
        Node::Exp(e) => show_exp(e),
        Node::LocalVar(v) => show_exp(&Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone())),
        Node::FieldAccess(v) => field_doc(v),
        Node::PredicateAccess(v) => show_exp(&Exp::new(
            ExpKind::PredicateAccess(v.clone()),
            v.meta.clone(),
        )),
        Node::PredicateAccessPredicate(v) => predicate_perm_doc(v),
        Node::Stmt(v) => show_stmt(v),
        Node::LabelDecl(v) => show_stmt(&crate::ast::statement::Stmt::new(
            StmtKind::Label(v.clone()),
            v.meta.clone(),
        )),
        Node::LocalDecl(v) => Ok(Doc::text(format!("{}: {}", v.name, show_type(&v.typ)?))),
        Node::UnnamedLocalDecl(v) => Ok(Doc::text(show_type(&v.typ)?)),
        Node::Type(v) => Ok(Doc::text(show_type(v)?)),
        Node::DomainFunc(v) => domain_function(v),
        Node::DomainAxiom(v) => domain_axiom(v),
        Node::Member(v) => show_member(v),
        Node::Program(v) => show_program(v),
        Node::Trigger(v) => Ok(trigger_list(std::slice::from_ref(v))?
            .into_iter()
            .next()
            .unwrap_or(Doc::Nil)),
    }
}
pub fn pretty_node(node: &crate::ast::utility::nodes::Node) -> Result<String, PrintError> {
    Ok(pretty(75, &show_node(node)?))
}
/// Scala Exp.toString removes pretty-printer linebreaks and following JVM-regex whitespace.
pub fn expression_to_string(expression: &Exp) -> Result<String, PrintError> {
    let input = pretty_expression(expression)?;
    let mut result = String::new();
    let mut iter = input.chars().peekable();
    while let Some(ch) = iter.next() {
        if ch == '\n' {
            result.push(' ');
            while iter
                .peek()
                .is_some_and(|c| matches!(c, ' ' | '\t' | '\n' | '\r' | '\u{000b}' | '\u{000c}'))
            {
                iter.next();
            }
        } else {
            result.push(ch);
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    #[test]
    fn source_nested_groups_scan_line_as_one_unit() {
        use super::{Doc, pretty};
        let nested = Doc::concat([Doc::text("b"), Doc::line(), Doc::text("c")]).group();
        let wide_replacement =
            Doc::concat([Doc::text("a"), Doc::Line("LONG".into()), nested.clone()]).group();
        assert_eq!(pretty(5, &wide_replacement), "aLONGb\nc");
        let regular = Doc::concat([Doc::text("a"), Doc::line(), nested]).group();
        assert_eq!(pretty(3, &regular), "a\nb c");
        assert_eq!(
            pretty(
                2,
                &Doc::concat([
                    Doc::text("long"),
                    Doc::concat([Doc::line(), Doc::text("x")]).group()
                ])
            ),
            "long\nx"
        );
    }
    use super::*;
    use crate::ast::ast::Metadata;
    #[test]
    fn prints_method_with_assertion_and_contract() {
        use crate::ast::{
            program::{Method, MethodData, Program},
            statement::{Stmt, StmtKind},
            utility::nodes::Node,
        };
        let m = Metadata::default();
        let yes = Exp::new(ExpKind::TrueLit, m.clone());
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![Stmt::new(StmtKind::Assert(yes.clone()), m.clone())],
                declarations: vec![],
            },
            m.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![yes],
            posts: vec![],
            body: Some(body),
            meta: m.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], m);
        assert_eq!(
            pretty_node(&Node::Program(program)).unwrap(),
            "method m()\n  requires true\n{\n  assert true\n}"
        );
    }
    #[test]
    fn expression_to_string_flattens_annotation_linebreaks() {
        use crate::ast::ast::Info;
        let m = Metadata {
            info: Info::Annotation(std::collections::HashMap::from([(
                "tag".into(),
                vec!["v".into()],
            )])),
            ..Default::default()
        };
        let e = Exp::new(ExpKind::TrueLit, m);
        assert_eq!(expression_to_string(&e).unwrap(), "@tag(\"v\") (true)");
    }
    #[test]
    fn prints_heap_access_and_collection_forms() {
        use crate::ast::{
            expression::{FieldAccess, LocalVar},
            program::{Field, FieldData},
        };
        let m = Metadata::default();
        let receiver = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Ref, m.clone())),
            m.clone(),
        );
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: m.clone(),
        });
        let access = FieldAccess::new(receiver, field, m.clone());
        let permission = Exp::new(ExpKind::FieldAccessPredicate(access, None), m.clone());
        assert_eq!(pretty_expression(&permission).unwrap(), "acc(x.f, write)");
        let seq = Exp::new(
            ExpKind::ExplicitSeq(vec![
                Exp::new(ExpKind::IntLit(1.into()), m.clone()),
                Exp::new(ExpKind::IntLit(2.into()), m.clone()),
            ]),
            m.clone(),
        );
        let index = Exp::new(
            ExpKind::SeqIndex(seq, Exp::new(ExpKind::IntLit(0.into()), m.clone())),
            m,
        );
        assert_eq!(pretty_expression(&index).unwrap(), "Seq(1, 2)[0]");
    }
    #[test]
    fn prints_domain_application_with_explicit_result_type() {
        use crate::ast::{expression::ExpExtra, r#type::TypeVar};
        let e = Exp::with_extra(
            ExpKind::DomainFuncApp(
                "f".into(),
                vec![],
                std::collections::HashMap::from([(TypeVar::new("T"), Type::Int)]),
            ),
            Metadata::default(),
            ExpExtra {
                typ: Some(Type::Int),
                ..Default::default()
            },
        );
        assert_eq!(pretty_expression(&e).unwrap(), "(f(): Int)");
    }
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
