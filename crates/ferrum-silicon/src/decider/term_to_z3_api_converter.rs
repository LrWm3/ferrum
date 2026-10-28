// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Native API conversion, adapted from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/TermToZ3APIConverter.scala.
//!
//! Status: source sort and major term dispatch are implemented against an explicit native
//! context contract. A linked Z3 context adapter and the API prover remain pending. Unsupported
//! upstream cases and incomplete substitution return errors, never fabricated solver objects.

use crate::decider::term_to_smt_lib2_converter::{
    ConversionError as SmtError, TermToSmtLib2Converter,
};
use crate::state::identifiers::Identifier;
use crate::state::terms::{
    ApplicableKind, ApplicationTarget, Declaration, DeclarationKind, Quantifier, Sort, Term,
    TermFactory, TermKind, sort_wrapper_id,
};
use std::collections::HashMap;

/// Native adapter must keep handles valid for its context lifetime, lazily create the recursive
/// `$Snap` datatype, and resolve SMT builtins by parsing their source signature as upstream does.
pub trait Z3NativeContext {
    type Sort: Clone + Eq;
    type Expr: Clone + Eq;
    type Function: Clone + Eq;
    type Error;
    fn function(
        &mut self,
        name: &str,
        args: &[Self::Sort],
        result: &Self::Sort,
    ) -> Result<Self::Function, Self::Error>;
    fn sort(&mut self, spec: NativeSort) -> Result<Self::Sort, Self::Error>;
    fn literal(
        &mut self,
        literal: NativeLiteral,
        sort: &Self::Sort,
    ) -> Result<Self::Expr, Self::Error>;
    fn constant(&mut self, name: &str, sort: &Self::Sort) -> Result<Self::Expr, Self::Error>;
    fn builtin(&mut self, op: NativeOp, args: &[Self::Expr]) -> Result<Self::Expr, Self::Error>;
    /// `smt_builtin` requests parse-based builtin lookup, not an uninterpreted declaration.
    fn application(
        &mut self,
        name: &str,
        arg_sorts: &[Self::Sort],
        result: &Self::Sort,
        args: &[Self::Expr],
        smt_builtin: bool,
    ) -> Result<Self::Expr, Self::Error>;
    fn quantifier(
        &mut self,
        quantifier: Quantifier,
        vars: &[Self::Expr],
        body: &Self::Expr,
        patterns: &[Vec<Self::Expr>],
        name: &str,
        weight: i32,
    ) -> Result<Self::Expr, Self::Error>;
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeSort {
    Int,
    Bool,
    Real,
    Snap,
    Uninterpreted(String),
    ParsedSmt(String),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NativeLiteral {
    Integer(String),
    Real(i32),
    Bool(bool),
    SnapUnit,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeOp {
    Neg,
    Not,
    And,
    Or,
    Implies,
    Equal,
    Distinct,
    Ite,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    ToReal,
    SnapCombine,
    SnapFirst,
    SnapSecond,
}
#[derive(Debug)]
pub enum NativeConversionError<E> {
    Context(E),
    Name(SmtError),
    Unsupported(&'static str),
    MacroArity,
    Substitution,
}
impl<E> From<SmtError> for NativeConversionError<E> {
    fn from(e: SmtError) -> Self {
        Self::Name(e)
    }
}
type ResultFor<C, T> = Result<T, NativeConversionError<<C as Z3NativeContext>::Error>>;

/// Declarations needed when parsing the buffered textual preamble. Macro declarations are
/// expanded on Silicon terms and thus have no native symbol in the source's default mode.
pub enum NativeDeclaration<C: Z3NativeContext> {
    Sort { name: Option<String>, sort: C::Sort },
    Function { name: String, function: C::Function },
    ExpandedMacro,
}
pub struct TermToZ3ApiConverter<C: Z3NativeContext> {
    pub context: C,
    factory: TermFactory,
    names: TermToSmtLib2Converter,
    sorts: HashMap<Sort, C::Sort>,
    terms: HashMap<Term, C::Expr>,
    macros: HashMap<String, (Vec<Term>, Term)>,
}
impl<C: Z3NativeContext> TermToZ3ApiConverter<C> {
    pub fn new(context: C, factory: TermFactory) -> Self {
        Self {
            context,
            names: TermToSmtLib2Converter::new(factory.clone()),
            factory,
            sorts: HashMap::new(),
            terms: HashMap::new(),
            macros: HashMap::new(),
        }
    }
    /// Drop all cached context handles and macros before reusing or replacing the context.
    pub fn reset(&mut self) {
        self.sorts.clear();
        self.terms.clear();
        self.macros.clear();
        self.names.reset();
    }
    pub fn register_macro(&mut self, name: String, vars: Vec<Term>, body: Term) {
        self.macros.insert(name, (vars, body));
        self.terms.clear();
    }
    pub fn convert_declaration(
        &mut self,
        declaration: &Declaration,
    ) -> ResultFor<C, NativeDeclaration<C>> {
        match declaration.kind() {
            DeclarationKind::Sort(sort) => {
                let name = match sort {
                    Sort::Int | Sort::Bool | Sort::Perm => None,
                    Sort::SmtSort(_) => {
                        return Err(NativeConversionError::Unsupported("SMT sort symbol"));
                    }
                    _ => Some(self.names.convert_sort(sort)?),
                };
                let sort = self.convert_sort(sort)?;
                Ok(NativeDeclaration::Sort { name, sort })
            }
            DeclarationKind::Function(target) => {
                let name = self.names.convert_identifier(target.id())?;
                let args = match target {
                    ApplicationTarget::Function(f) => f.data().arg_sorts.clone(),
                    ApplicationTarget::Variable(_) => Vec::new(),
                };
                self.function_declaration(name, &args, target.result_sort())
            }
            DeclarationKind::SortWrapper(from, to) => {
                let name = self
                    .names
                    .convert_identifier(&sort_wrapper_id(from.clone(), to.clone()))?;
                self.function_declaration(name, std::slice::from_ref(from), to)
            }
            DeclarationKind::Macro { id, args, body } => {
                self.register_macro(id.name(), args.clone(), body.clone());
                Ok(NativeDeclaration::ExpandedMacro)
            }
        }
    }
    fn function_declaration(
        &mut self,
        name: String,
        args: &[Sort],
        result: &Sort,
    ) -> ResultFor<C, NativeDeclaration<C>> {
        let mut converted = Vec::new();
        for arg in args {
            if *arg != Sort::Unit {
                converted.push(self.convert_sort(arg)?);
            }
        }
        let result = self.convert_sort(result)?;
        let function = self
            .context
            .function(&name, &converted, &result)
            .map_err(NativeConversionError::Context)?;
        Ok(NativeDeclaration::Function { name, function })
    }
    pub fn convert_sort(&mut self, sort: &Sort) -> ResultFor<C, C::Sort> {
        if let Some(value) = self.sorts.get(sort) {
            return Ok(value.clone());
        }
        let spec = match sort {
            Sort::Int => NativeSort::Int,
            Sort::Bool => NativeSort::Bool,
            Sort::Perm => NativeSort::Real,
            Sort::Snap => NativeSort::Snap,
            Sort::Ref => NativeSort::Uninterpreted("$Ref".into()),
            Sort::SmtSort(id) => NativeSort::ParsedSmt(id.name()),
            Sort::Unit => return Err(NativeConversionError::Unsupported("Unit sort")),
            Sort::Heap(_) | Sort::WandHeap | Sort::PredHeap | Sort::PredMask => {
                return Err(NativeConversionError::Unsupported("mask heap sort"));
            }
            _ => NativeSort::Uninterpreted(self.names.convert_sort(sort)?),
        };
        let value = self
            .context
            .sort(spec)
            .map_err(NativeConversionError::Context)?;
        self.sorts.insert(sort.clone(), value.clone());
        Ok(value)
    }
    fn literal(&mut self, value: NativeLiteral, sort: &Sort) -> ResultFor<C, C::Expr> {
        let sort = self.convert_sort(sort)?;
        self.context
            .literal(value, &sort)
            .map_err(NativeConversionError::Context)
    }
    fn op(&mut self, op: NativeOp, args: &[C::Expr]) -> ResultFor<C, C::Expr> {
        self.context
            .builtin(op, args)
            .map_err(NativeConversionError::Context)
    }
    fn app(
        &mut self,
        name: &str,
        args: &[Term],
        output: &Sort,
        smt: bool,
    ) -> ResultFor<C, C::Expr> {
        let mut sorts = Vec::with_capacity(args.len());
        let mut values = Vec::with_capacity(args.len());
        for arg in args {
            sorts.push(self.convert_sort(arg.sort())?);
            values.push(self.convert_term(arg)?);
        }
        let out = self.convert_sort(output)?;
        self.context
            .application(name, &sorts, &out, &values, smt)
            .map_err(NativeConversionError::Context)
    }
    fn raw_identifier(&mut self, id: &Identifier) -> ResultFor<C, String> {
        Ok(match id {
            Identifier::Simple(name) => name.clone(),
            Identifier::Suffixed {
                prefix,
                separator,
                suffix,
            } => format!("{}{}{}", self.raw_identifier(prefix)?, separator, suffix),
            Identifier::SortBased { template, sorts } => {
                let mut out = String::new();
                let mut chars = template.chars();
                let mut sorts = sorts.iter();
                while let Some(c) = chars.next() {
                    if c != '%' {
                        out.push(c);
                        continue;
                    }
                    match chars.next() {
                        Some('%') => out.push('%'),
                        Some('s') => out.push_str(&self.names.convert_sort(
                            sorts.next().ok_or(SmtError::InvalidIdentifierTemplate)?,
                        )?),
                        _ => {
                            return Err(NativeConversionError::Name(
                                SmtError::InvalidIdentifierTemplate,
                            ));
                        }
                    }
                }
                out
            }
        })
    }
    fn integer(&mut self, value: &str) -> ResultFor<C, C::Expr> {
        if let Some(positive) = value.strip_prefix('-') {
            let n = self.literal(NativeLiteral::Integer(positive.into()), &Sort::Int)?;
            self.op(NativeOp::Neg, &[n])
        } else {
            self.literal(NativeLiteral::Integer(value.into()), &Sort::Int)
        }
    }
    fn to_real(&mut self, t: &Term) -> ResultFor<C, C::Expr> {
        let v = self.convert_term(t)?;
        if *t.sort() == Sort::Int {
            self.op(NativeOp::ToReal, &[v])
        } else {
            Ok(v)
        }
    }
    pub fn convert_term(&mut self, term: &Term) -> ResultFor<C, C::Expr> {
        if let Some(value) = self.terms.get(term) {
            return Ok(value.clone());
        }
        use TermKind::*;
        macro_rules! op { ($op:ident, $($arg:expr),* $(,)?) => {{
            let mut args = Vec::new(); $(args.push(self.convert_term($arg)?);)*
            self.op(NativeOp::$op, &args)?
        }} }
        macro_rules! app { ($name:expr $(, $arg:expr)* $(,)?) => {{
            let args = vec![$($arg.clone()),*]; self.app($name, &args, term.sort(), false)?
        }} }
        let value = match term.kind() {
            Unit => self.literal(NativeLiteral::SnapUnit, &Sort::Snap)?,
            True => self.literal(NativeLiteral::Bool(true), &Sort::Bool)?,
            False => self.literal(NativeLiteral::Bool(false), &Sort::Bool)?,
            IntLiteral(n) => {
                let s = n.to_string();
                if let Some(pos) = s.strip_prefix('-') {
                    let n = self.literal(NativeLiteral::Integer(pos.into()), &Sort::Int)?;
                    self.op(NativeOp::Neg, &[n])?
                } else {
                    self.literal(NativeLiteral::Integer(s), &Sort::Int)?
                }
            }
            Null => {
                let s = self.convert_sort(&Sort::Ref)?;
                self.context
                    .constant("$Ref.null", &s)
                    .map_err(NativeConversionError::Context)?
            }
            Var(v) => {
                let name = self.names.convert_identifier(&v.id)?;
                let s = self.convert_sort(&v.sort)?;
                self.context
                    .constant(&name, &s)
                    .map_err(NativeConversionError::Context)?
            }
            App { applicable, args } => {
                let id = applicable.id();
                let macro_name = id.name();
                let smt = matches!(applicable, ApplicationTarget::Function(f) if f.data().kind == ApplicableKind::SmtFun);
                if !smt && self.macros.contains_key(&macro_name) {
                    let (vars, body) = self.macros.get(&macro_name).cloned().unwrap();
                    if vars.len() != args.len() {
                        return Err(NativeConversionError::MacroArity);
                    }
                    let substitutions = vars.into_iter().zip(args.iter().cloned()).collect();
                    let replaced = self
                        .factory
                        .replace(&body, &substitutions)
                        .map_err(|_| NativeConversionError::Substitution)?;
                    self.convert_term(&replaced)?
                } else {
                    let name = if smt {
                        self.raw_identifier(id)?
                    } else {
                        self.names.convert_identifier(id)?
                    };
                    self.app(&name, args, term.sort(), smt)?
                }
            }
            Let(bindings, body) => {
                let substitutions = bindings.iter().cloned().collect();
                let replaced = self
                    .factory
                    .replace(body, &substitutions)
                    .map_err(|_| NativeConversionError::Substitution)?;
                self.convert_term(&replaced)?
            }
            Quantification {
                quantifier,
                vars,
                body,
                triggers,
                name,
                weight,
                ..
            } => {
                if vars.is_empty() {
                    self.convert_term(body)?
                } else {
                    let vars = vars
                        .iter()
                        .map(|v| self.convert_term(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let body = self.convert_term(body)?;
                    let mut patterns = Vec::new();
                    for trigger in triggers {
                        if !trigger.terms.is_empty() {
                            patterns.push(
                                trigger
                                    .terms
                                    .iter()
                                    .map(|v| self.convert_term(v))
                                    .collect::<Result<Vec<_>, _>>()?,
                            );
                        }
                    }
                    self.context
                        .quantifier(
                            *quantifier,
                            &vars,
                            &body,
                            &patterns,
                            name,
                            weight.unwrap_or(1),
                        )
                        .map_err(NativeConversionError::Context)?
                }
            }
            Iff(a, b) => {
                let a = self.convert_term(a)?;
                let b = self.convert_term(b)?;
                let ab = self.op(NativeOp::Implies, &[a.clone(), b.clone()])?;
                let ba = self.op(NativeOp::Implies, &[b, a])?;
                self.op(NativeOp::And, &[ab, ba])?
            }
            And(ts) | Or(ts) => {
                let op = if matches!(term.kind(), And(_)) {
                    NativeOp::And
                } else {
                    NativeOp::Or
                };
                let vals = ts
                    .iter()
                    .map(|t| self.convert_term(t))
                    .collect::<Result<Vec<_>, _>>()?;
                self.op(op, &vals)?
            }
            CustomEquals(a, b) => {
                let name = match a.sort() {
                    Sort::Seq(_) => "Seq_equal",
                    Sort::Set(_) => "Set_equal",
                    Sort::Multiset(_) => "Multiset_equal",
                    Sort::Map(_, _) => "Map_equal",
                    _ => return Err(NativeConversionError::Unsupported("custom equality sort")),
                };
                app!(name, a, b)
            }
            NoPerm => self.literal(NativeLiteral::Real(0), &Sort::Perm)?,
            FullPerm => self.literal(NativeLiteral::Real(1), &Sort::Perm)?,
            FractionPermLiteral(r) => {
                let n = self.integer(&r.numerator().to_string())?;
                let d = self.integer(&r.denominator().to_string())?;
                let n = self.op(NativeOp::ToReal, &[n])?;
                let d = self.op(NativeOp::ToReal, &[d])?;
                self.op(NativeOp::Div, &[n, d])?
            }
            FractionPerm(a, b) | PermIntDiv(a, b) | PermPermDiv(a, b) => {
                let a = self.to_real(a)?;
                let b = self.to_real(b)?;
                self.op(NativeOp::Div, &[a, b])?
            }
            PermMin(a, b) => {
                let a = self.convert_term(a)?;
                let b = self.convert_term(b)?;
                let cond = self.op(NativeOp::LessEqual, &[a.clone(), b.clone()])?;
                self.op(NativeOp::Ite, &[cond, a, b])?
            }
            IsValidPermVal(a) | IsReadPermVar(a) => {
                let zero = self.literal(NativeLiteral::Real(0), &Sort::Perm)?;
                let val = self.convert_term(a)?;
                let op = if matches!(term.kind(), IsValidPermVal(_)) {
                    NativeOp::LessEqual
                } else {
                    NativeOp::Less
                };
                self.op(op, &[zero, val])?
            }
            SeqNil(_) => app!("Seq_empty"),
            EmptySet(_) => app!("Set_empty"),
            EmptyMultiset(_) => app!("Multiset_empty"),
            EmptyMap(_, _) => app!("Map_empty"),
            Not(a) => op!(Not, a),
            PermNegation(a) => op!(Neg, a),
            First(a) => op!(SnapFirst, a),
            Second(a) => op!(SnapSecond, a),
            Plus(a, b) => op!(Add, a, b),
            Minus(a, b) => op!(Sub, a, b),
            Times(a, b) => op!(Mul, a, b),
            Div(a, b) => op!(Div, a, b),
            Mod(a, b) => op!(Mod, a, b),
            Implies(a, b) => op!(Implies, a, b),
            BuiltinEquals(a, b) => op!(Equal, a, b),
            Less(a, b) => op!(Less, a, b),
            AtMost(a, b) => op!(LessEqual, a, b),
            Greater(a, b) => op!(Greater, a, b),
            AtLeast(a, b) => op!(GreaterEqual, a, b),
            PermTimes(a, b) => op!(Mul, a, b),
            IntPermTimes(a, b) => op!(Mul, a, b),
            PermPlus(a, b) => op!(Add, a, b),
            PermMinus(a, b) => op!(Sub, a, b),
            PermLess(a, b) => op!(Less, a, b),
            PermAtMost(a, b) => op!(LessEqual, a, b),
            Combine(a, b) => op!(SnapCombine, a, b),
            SeqRanged(a, b) => app!("Seq_range", a, b),
            SeqSingleton(a) => app!("Seq_singleton", a),
            SeqAppend(a, b) => app!("Seq_append", a, b),
            SeqDrop(a, b) => app!("Seq_drop", a, b),
            SeqTake(a, b) => app!("Seq_take", a, b),
            SeqLength(a) => app!("Seq_length", a),
            SeqAt(a, b) => app!("Seq_index", a, b),
            SeqIn(a, b) => app!("Seq_contains", a, b),
            SeqInTrigger(a, b) => app!("Seq_contains_trigger", a, b),
            SeqUpdate(a, b, c) => app!("Seq_update", a, b, c),
            SingletonSet(a) => app!("Set_singleton", a),
            SetAdd(a, b) => app!("Set_unionone", a, b),
            SetUnion(a, b) => app!("Set_union", a, b),
            SetIntersection(a, b) => app!("Set_intersection", a, b),
            SetSubset(a, b) => app!("Set_subset", a, b),
            SetDisjoint(a, b) => app!("Set_disjoint", a, b),
            SetDifference(a, b) => app!("Set_difference", a, b),
            SetIn(a, b) => app!("Set_in", a, b),
            SetCardinality(a) => app!("Set_card", a),
            SingletonMultiset(a) => app!("Multiset_singleton", a),
            MultisetAdd(a, b) => app!("Multiset_unionone", a, b),
            MultisetUnion(a, b) => app!("Multiset_union", a, b),
            MultisetIntersection(a, b) => app!("Multiset_intersection", a, b),
            MultisetSubset(a, b) => app!("Multiset_subset", a, b),
            MultisetDifference(a, b) => app!("Multiset_difference", a, b),
            MultisetCardinality(a) => app!("Multiset_card", a),
            MultisetCount(a, b) => app!("Multiset_count", a, b),
            MapLookup(a, b) => app!("Map_apply", a, b),
            MapCardinality(a) => app!("Map_card", a),
            MapUpdate(a, b, c) => app!("Map_update", a, b, c),
            MapDomain(a) => app!("Map_domain", a),
            MapRange(a) => app!("Map_values", a),
            MwsfLookup(a, b) => app!("MWSF_apply", a, b),
            MagicWandToken(a, b) => app!("MW_token", a, b),
            Ite(a, b, c) => op!(Ite, a, b, c),
            Domain(id, a) => app!(&format!("$FVF.domain_{id}"), a),
            HasDomain(id, a, _) => app!(&format!("$FVF.has_domain_{id}"), a),
            Lookup(id, a, b) => app!(&format!("$FVF.lookup_{id}"), a, b),
            PermLookup(id, a, b) => app!(&format!("$FVF.perm_{id}"), a, b),
            FieldTrigger(id, a, b) => {
                let v = if matches!(a.sort(), Sort::FieldValueFunction { .. }) {
                    self.factory.lookup(id.clone(), a.clone(), b.clone())
                } else {
                    a.clone()
                };
                app!(&format!("$FVF.loc_{id}"), v, b)
            }
            PredicateDomain(id, a) => app!(&format!("$PSF.domain_{id}"), a),
            HasPredicateDomain(id, a, _) => app!(&format!("$PSF.has_domain_{id}"), a),
            PredicateLookup(id, a, args) | PredicatePermLookup(id, a, args) => {
                let snap = self.factory.to_snap_tree(args.clone());
                let op = if matches!(term.kind(), PredicateLookup(..)) {
                    "lookup"
                } else {
                    "perm"
                };
                app!(&format!("$PSF.{op}_{id}"), a, snap)
            }
            PredicateTrigger(id, a, args) => {
                let snap = self.factory.to_snap_tree(args.clone());
                let lookup = self
                    .factory
                    .predicate_lookup(id.clone(), a.clone(), args.clone());
                app!(&format!("$PSF.loc_{id}"), lookup, snap)
            }
            SortWrapper(a, to) => {
                let id = sort_wrapper_id(a.sort().clone(), to.clone());
                let name = self.names.convert_identifier(&id)?;
                app!(&name, a)
            }
            Distinct(symbols) => {
                let mut values = Vec::new();
                for f in symbols.iter() {
                    let name = self.names.convert_identifier(&f.data().id)?;
                    let sort = self.convert_sort(&f.data().result_sort)?;
                    values.push(
                        self.context
                            .constant(&name, &sort)
                            .map_err(NativeConversionError::Context)?,
                    );
                }
                self.op(NativeOp::Distinct, &values)?
            }
            _ => {
                return Err(NativeConversionError::Unsupported(
                    "term has no upstream native API conversion",
                ));
            }
        };
        self.terms.insert(term.clone(), value.clone());
        Ok(value)
    }
}
