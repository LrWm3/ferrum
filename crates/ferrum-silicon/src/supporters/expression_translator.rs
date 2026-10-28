//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/ExpressionTranslator.scala
//!
//! Purpose:
//! Translate heap-independent Silver expressions to symbolic terms.
//!
//! Planned Rust structure:
//! Port ExpressionTranslator translate with quantifier, Boolean/arithmetic,
//! function/domain/backend, permissions, sequence, set/multiset, map and let dispatch.
//!
//! Behavior to preserve:
//! Translate forall/exists triggers using limited heap-dependent function versions; preserve
//! quantifier weights and builtin-domain naming mode. Pure functions receive snapshot arguments;
//! collections preserve operand orientation, literals fold in source order, maps desugar.
//! Explicitly reject unexpected heap-dependent/extension expressions rather than assume them.
//!
//! Integration:
//! supporters::domains and functions::heap_access_replacing_expression_translator,
//! rules::{function_supporter,evaluator}, state::terms and Silver AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact arithmetic, term identity, trigger order and explicit
//! context.
//!
//! Open decisions:
//! Reconcile builtin mode and pure-function snapshot argument conventions with domain and function
//! encoders.
//!
//! Status: partial; source pure-expression translation implemented, with source sort rendering
//! explicitly supplied by the caller. Concrete consumers and unsupported AST variants remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::identifiers::Identifier;
use crate::state::symbol_converter::{DefaultSymbolConverter, SymbolConversionError};
use crate::state::terms::{
    ApplicableData, ApplicableKind, ApplicationTarget, Quantifier, Sort, Term, TermFactory,
    TermKind, Trigger, UnsupportedTriggerTransform,
};
use ferrum_silver::ast::ast::Info;
use ferrum_silver::ast::expression::{Exp, ExpKind, ExpressionTypeError};
use ferrum_silver::ast::r#type::Type;

#[derive(Debug)]
pub enum ExpressionTranslationError<E> {
    UnsupportedExpression,
    InvalidCollection,
    MissingInterpretation,
    MissingFunction(String),
    Traversal(crate::state::terms::UnsupportedSubterms),
    Projection(ferrum_silver::ast::utility::expressions::UnsupportedExtensionProjection),
    Service(E),
    Type(ExpressionTypeError),
    Sort(SymbolConversionError),
    Render(E),
    Quantifier(UnsupportedTriggerTransform),
}
/// Pure Silver expression translator; sort rendering is supplied by the Silicon
/// source renderer for polymorphic domain-function identifiers.
pub struct ExpressionTranslator<'a, R> {
    pub factory: &'a TermFactory,
    pub converter: &'a DefaultSymbolConverter,
    pub render_sort: R,
    pub builtin: bool,
    pub pure_function_snapshots: Vec<Term>,
    /// Optional source domain instantiation applied before every sort conversion.
    pub type_substitution: Option<&'a ferrum_silver::ast::r#type::TypeSubstitution>,
}
/// Override source-specific expression cases while retaining recursive pure translation.
pub trait ExpressionOverrides<R, E>
where
    R: Fn(&Sort) -> Result<String, E>,
{
    fn translate_special(
        &mut self,
        translator: &ExpressionTranslator<'_, R>,
        expression: &Exp,
    ) -> Option<Result<Term, ExpressionTranslationError<E>>>;
}
pub struct NoExpressionOverrides;
impl<R, E> ExpressionOverrides<R, E> for NoExpressionOverrides
where
    R: Fn(&Sort) -> Result<String, E>,
{
    fn translate_special(
        &mut self,
        _: &ExpressionTranslator<'_, R>,
        _: &Exp,
    ) -> Option<Result<Term, ExpressionTranslationError<E>>> {
        None
    }
}
impl<'a, R, E> ExpressionTranslator<'a, R>
where
    R: Fn(&Sort) -> Result<String, E>,
{
    pub fn new(
        factory: &'a TermFactory,
        converter: &'a DefaultSymbolConverter,
        render_sort: R,
    ) -> Self {
        ExpressionTranslator {
            factory,
            converter,
            render_sort,
            builtin: false,
            pure_function_snapshots: vec![factory.unit()],
            type_substitution: None,
        }
    }
    pub fn translate(&self, expression: &Exp) -> Result<Term, ExpressionTranslationError<E>> {
        self.translate_with(expression, &mut NoExpressionOverrides)
    }
    pub fn translate_with<H: ExpressionOverrides<R, E>>(
        &self,
        expression: &Exp,
        overrides: &mut H,
    ) -> Result<Term, ExpressionTranslationError<E>> {
        if let Some(result) = overrides.translate_special(self, expression) {
            return result;
        }
        self.translate_without_override(expression, overrides)
    }
    /// Translate this node's pure form while still applying overrides to its children.
    pub fn translate_without_override<H: ExpressionOverrides<R, E>>(
        &self,
        expression: &Exp,
        overrides: &mut H,
    ) -> Result<Term, ExpressionTranslationError<E>> {
        use ExpKind::*;
        let f = self.factory;
        let mut t = |exp: &Exp| self.translate_with(exp, overrides);
        let sort = |typ: &Type| {
            let concrete = self
                .type_substitution
                .map_or_else(|| typ.clone(), |map| typ.substitute(map));
            self.converter
                .to_sort(&concrete)
                .map_err(ExpressionTranslationError::Sort)
        };
        let result = match expression.kind() {
            TrueLit => f.boolean(true),
            FalseLit => f.boolean(false),
            NullLit => f.null(),
            IntLit(n) => f.int_literal(n.clone()),
            LocalVar(v) => f.var(Identifier::Simple(v.name.clone()), sort(&v.typ)?, false),
            Not(a) => f.not(t(a)?),
            And(a, b) => f.and([t(a)?, t(b)?]),
            Or(a, b) => f.or([t(a)?, t(b)?]),
            Implies(a, b) => f.implies(t(a)?, t(b)?),
            CondExp(a, b, c) => f.ite(t(a)?, t(b)?, t(c)?),
            EqCmp(a, b) | NeCmp(a, b) => {
                let equal = f.equals(t(a)?, t(b)?);
                // Source first builds Equals (including its simplifications), then
                // builtin-domain rewriting replaces any remaining Equals node.
                let equal = if self.builtin {
                    match equal.kind() {
                        TermKind::BuiltinEquals(a, b) | TermKind::CustomEquals(a, b) => {
                            f.builtin_equals(a.clone(), b.clone())
                        }
                        _ => equal,
                    }
                } else {
                    equal
                };
                if matches!(expression.kind(), NeCmp(..)) {
                    f.not(equal)
                } else {
                    equal
                }
            }
            Add(a, b) => f.plus(t(a)?, t(b)?),
            Sub(a, b) => f.minus(t(a)?, t(b)?),
            Mul(a, b) => f.times(t(a)?, t(b)?),
            Div(a, b) => f.div(t(a)?, t(b)?),
            Mod(a, b) => f.modulo(t(a)?, t(b)?),
            Minus(a) => f.minus(f.int_literal(0), t(a)?),
            LtCmp(a, b) | PermLtCmp(a, b) => f.less(t(a)?, t(b)?),
            LeCmp(a, b) | PermLeCmp(a, b) => f.at_most(t(a)?, t(b)?),
            GtCmp(a, b) | PermGtCmp(a, b) => f.greater(t(a)?, t(b)?),
            GeCmp(a, b) | PermGeCmp(a, b) => f.at_least(t(a)?, t(b)?),
            FullPerm => f.full_perm(),
            NoPerm => f.no_perm(),
            FractionalPerm(a, b) => f.fraction_perm(t(a)?, t(b)?),
            PermMinus(a) => f.perm_minus(f.no_perm(), t(a)?),
            PermAdd(a, b) => f.perm_plus(t(a)?, t(b)?),
            PermSub(a, b) => f.perm_minus(t(a)?, t(b)?),
            PermMul(a, b) => f.perm_times(t(a)?, t(b)?),
            IntPermMul(a, b) => f.int_perm_times(t(a)?, t(b)?),
            PermDiv(a, b) => f.perm_int_div(t(a)?, t(b)?),
            PermPermDiv(a, b) => f.perm_perm_div(t(a)?, t(b)?),
            SeqAppend(a, b) => f.seq_append(t(a)?, t(b)?),
            SeqContains(a, b) => f.seq_in(t(b)?, t(a)?),
            SeqDrop(a, b) => f.seq_drop(t(a)?, t(b)?),
            SeqIndex(a, b) => f.seq_at(t(a)?, t(b)?),
            SeqLength(a) => f.seq_length(t(a)?),
            SeqTake(a, b) => f.seq_take(t(a)?, t(b)?),
            EmptySeq(typ) => f.seq_nil(sort(typ)?),
            RangeSeq(a, b) => f.seq_ranged(t(a)?, t(b)?),
            SeqUpdate(a, b, c) => f.seq_update(t(a)?, t(b)?, t(c)?),
            ExplicitSeq(items) => {
                let (first, rest) = items
                    .split_first()
                    .ok_or(ExpressionTranslationError::InvalidCollection)?;
                let mut seq = f.seq_singleton(t(first)?);
                for item in rest {
                    seq = f.seq_append(seq, f.seq_singleton(t(item)?));
                }
                seq
            }
            EmptySet(typ) => f.empty_set(sort(typ)?),
            EmptyMultiset(typ) => f.empty_multiset(sort(typ)?),
            ExplicitSet(items) => {
                let (first, rest) = items
                    .split_first()
                    .ok_or(ExpressionTranslationError::InvalidCollection)?;
                let mut set = f.singleton_set(t(first)?);
                for item in rest {
                    set = f.set_add(set, t(item)?);
                }
                set
            }
            ExplicitMultiset(items) => {
                let (first, rest) = items
                    .split_first()
                    .ok_or(ExpressionTranslationError::InvalidCollection)?;
                let mut set = f.singleton_multiset(t(first)?);
                for item in rest {
                    set = f.multiset_add(set, t(item)?);
                }
                set
            }
            AnySetUnion(a, b)
            | AnySetIntersection(a, b)
            | AnySetSubset(a, b)
            | AnySetMinus(a, b)
            | AnySetContains(a, b) => {
                let typed = match expression.kind() {
                    AnySetSubset(..) => a,
                    AnySetContains(..) => b,
                    _ => expression,
                };
                let typ = typed.typ().map_err(ExpressionTranslationError::Type)?;
                let a = t(a)?;
                let b = t(b)?;
                match (expression.kind(), typ) {
                    (AnySetUnion(..), Type::Set(_)) => f.set_union(a, b),
                    (AnySetUnion(..), Type::Multiset(_)) => f.multiset_union(a, b),
                    (AnySetIntersection(..), Type::Set(_)) => f.set_intersection(a, b),
                    (AnySetIntersection(..), Type::Multiset(_)) => f.multiset_intersection(a, b),
                    (AnySetSubset(..), Type::Set(_)) => f.set_subset(a, b),
                    (AnySetSubset(..), Type::Multiset(_)) => f.multiset_subset(a, b),
                    (AnySetMinus(..), Type::Set(_)) => f.set_difference(a, b),
                    (AnySetMinus(..), Type::Multiset(_)) => f.multiset_difference(a, b),
                    (AnySetContains(..), Type::Set(_)) => f.set_in(a, b),
                    (AnySetContains(..), Type::Multiset(_)) => f.multiset_count(b, a),
                    _ => return Err(ExpressionTranslationError::InvalidCollection),
                }
            }
            AnySetCardinality(a) => match a.typ().map_err(ExpressionTranslationError::Type)? {
                Type::Set(_) => f.set_cardinality(t(a)?),
                Type::Multiset(_) => f.multiset_cardinality(t(a)?),
                _ => return Err(ExpressionTranslationError::InvalidCollection),
            },
            EmptyMap(k, v) => f.empty_map(sort(k)?, sort(v)?),
            Maplet(key, value) => {
                let key_term = t(key)?;
                let value_term = t(value)?;
                f.map_update(
                    f.empty_map(key_term.sort().clone(), value_term.sort().clone()),
                    key_term,
                    value_term,
                )
            }
            ExplicitMap(items) => {
                let pairs: Vec<_> = items
                    .iter()
                    .filter_map(|e| match e.kind() {
                        Maplet(k, v) => Some((k, v)),
                        _ => None,
                    })
                    .collect();
                let (key, value) = pairs
                    .first()
                    .ok_or(ExpressionTranslationError::InvalidCollection)?;
                let mut map = f.empty_map(
                    sort(&key.typ().map_err(ExpressionTranslationError::Type)?)?,
                    sort(&value.typ().map_err(ExpressionTranslationError::Type)?)?,
                );
                for (key, value) in pairs {
                    map = f.map_update(map, t(key)?, t(value)?);
                }
                map
            }
            MapContains(key, map) => f.set_in(t(key)?, f.map_domain(t(map)?)),
            MapUpdate(map, key, value) => f.map_update(t(map)?, t(key)?, t(value)?),
            MapCardinality(map) => f.map_cardinality(t(map)?),
            MapLookup(map, key) => f.map_lookup(t(map)?, t(key)?),
            MapDomain(map) => f.map_domain(t(map)?),
            MapRange(map) => f.map_range(t(map)?),
            Let(decl, value, body) => {
                let var = f.var(
                    Identifier::Simple(decl.name.clone()),
                    sort(&decl.typ)?,
                    false,
                );
                f.let_term([(var, t(value)?)], t(body)?)
            }
            Forall(vars, triggers, body) | Exists(vars, triggers, body) => {
                let mut converted_triggers = Vec::new();
                for trigger in triggers {
                    let mut terms = Vec::new();
                    for exp in &trigger.exps {
                        let term = t(exp)?;
                        let term = match term.kind() {
                            TermKind::App {
                                applicable: ApplicationTarget::Function(fun),
                                args,
                            } if fun.data().kind == ApplicableKind::HeapDepFun => f.app(
                                crate::rules::function_supporter::limited_version(f, fun),
                                args.clone(),
                            ),
                            _ => term.clone(),
                        };
                        terms.push(term);
                    }
                    converted_triggers.push(Trigger { terms });
                }
                let variables = vars
                    .iter()
                    .map(|v| Ok(f.var(Identifier::Simple(v.name.clone()), sort(&v.typ)?, false)))
                    .collect::<std::result::Result<Vec<_>, ExpressionTranslationError<E>>>()?;
                let info = &expression.metadata().info;
                let weight = match info.find(&|i| matches!(i, Info::WeightedQuantifier(_))) {
                    Some(Info::WeightedQuantifier(weight)) => (*weight >= 0).then_some(*weight),
                    _ => match info.find(&|i| matches!(i, Info::Annotation(_))) {
                        Some(Info::Annotation(values)) => {
                            values
                                .get("weight")
                                .and_then(|values| match values.as_slice() {
                                    [s] => s.parse::<i32>().ok().filter(|n| *n >= 0),
                                    _ => None,
                                })
                        }
                        _ => None,
                    },
                };
                f.quantification(
                    if matches!(expression.kind(), Forall(..)) {
                        Quantifier::Forall
                    } else {
                        Quantifier::Exists
                    },
                    variables,
                    t(body)?,
                    converted_triggers,
                    String::new(),
                    false,
                    weight,
                )
                .map_err(ExpressionTranslationError::Quantifier)?
            }
            DomainFuncApp(name, args, _) | BackendFuncApp(name, args) | FuncApp(name, args) => {
                let mut terms = if matches!(expression.kind(), FuncApp(..)) {
                    self.pure_function_snapshots.clone()
                } else {
                    vec![]
                };
                for arg in args {
                    terms.push(t(arg)?);
                }
                let output = sort(&expression.typ().map_err(ExpressionTranslationError::Type)?)?;
                let (kind, id) = match expression.kind() {
                    DomainFuncApp(..) => (
                        ApplicableKind::Fun,
                        if self.builtin {
                            name.clone()
                        } else {
                            format!(
                                "{}[{}]",
                                name,
                                (self.render_sort)(&output)
                                    .map_err(ExpressionTranslationError::Render)?
                            )
                        },
                    ),
                    BackendFuncApp(..) => (
                        ApplicableKind::SmtFun,
                        expression
                            .0
                            .extra
                            .interpretation
                            .clone()
                            .ok_or(ExpressionTranslationError::MissingInterpretation)?,
                    ),
                    _ => (ApplicableKind::HeapDepFun, name.clone()),
                };
                let applicable = f.applicable(ApplicableData {
                    kind,
                    id: Identifier::Simple(id),
                    arg_sorts: terms.iter().map(|t| t.sort().clone()).collect(),
                    result_sort: output,
                });
                f.app(applicable, terms)
            }
            _ => return Err(ExpressionTranslationError::UnsupportedExpression),
        };
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::TermOptions;
    use ferrum_silver::ast::ast::Metadata;
    use ferrum_silver::ast::expression::LocalVar;
    #[test]
    fn builtin_translation_substitutes_types_and_preserves_equals_simplification() {
        use ferrum_silver::ast::r#type::TypeVar;
        use std::sync::Arc;
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let tv = TypeVar::new("E");
        let substitution = [(tv.clone(), Type::Int)].into_iter().collect();
        let typ = Type::Seq(Arc::new(Type::Var(tv)));
        let local = |name: &str| {
            Exp::new(
                ExpKind::LocalVar(LocalVar::new(name.into(), typ.clone(), Metadata::default())),
                Metadata::default(),
            )
        };
        let mut translator =
            ExpressionTranslator::new(&factory, &converter, |s: &Sort| Ok::<_, ()>(s.to_string()));
        translator.builtin = true;
        translator.type_substitution = Some(&substitution);
        let x = local("x");
        let y = local("y");
        let same = Exp::new(ExpKind::EqCmp(x.clone(), x.clone()), Metadata::default());
        let distinct = Exp::new(ExpKind::EqCmp(x, y), Metadata::default());
        assert!(matches!(
            translator.translate(&same).unwrap().kind(),
            TermKind::True
        ));
        assert!(matches!(
            translator.translate(&distinct).unwrap().kind(),
            TermKind::BuiltinEquals(..)
        ));
    }
    struct ReplaceLocal;
    impl<R> ExpressionOverrides<R, ()> for ReplaceLocal
    where
        R: Fn(&Sort) -> Result<String, ()>,
    {
        fn translate_special(
            &mut self,
            translator: &ExpressionTranslator<'_, R>,
            expression: &Exp,
        ) -> Option<Result<Term, ExpressionTranslationError<()>>> {
            match expression.kind() {
                ExpKind::LocalVar(v) if v.name == "x" => {
                    Some(Ok(translator.factory.int_literal(7)))
                }
                _ => None,
            }
        }
    }
    #[test]
    fn recursive_overrides_reach_nested_pure_operators() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let translator =
            ExpressionTranslator::new(&factory, &converter, |_: &Sort| Ok::<_, ()>(String::new()));
        let x = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Int, Metadata::default())),
            Metadata::default(),
        );
        let expression = Exp::new(
            ExpKind::Add(x, Exp::new(ExpKind::IntLit(3.into()), Metadata::default())),
            Metadata::default(),
        );
        let result = translator
            .translate_with(&expression, &mut ReplaceLocal)
            .unwrap();
        assert_eq!(result, factory.int_literal(10));
    }
}
