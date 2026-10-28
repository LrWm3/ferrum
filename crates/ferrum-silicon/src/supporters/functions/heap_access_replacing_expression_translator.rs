//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/HeapAccessReplacingExpressionTranslator.scala
//!
//! Purpose:
//! Translate function contracts and bodies using snapshots recorded during symbolic execution.
//!
//! Planned Rust structure:
//! Port HeapAccessReplacingExpressionTranslator translate/body/precondition/postcondition, context
//! stack and getOrFail; extend expression_translator.
//!
//! Behavior to preserve:
//! Preconditions use exhale interpretation and ignore access predicates/wands; postconditions use
//! inhale interpretation. Resolve locations and calls by AST plus let/quantifier context,
//! normalize quantified variable suffixes and choose limited versus defined application by call
//! height and opaque/reveal annotations. Missing recordings warn once unless prior failure,
//! optionally mark failure and yield a fresh unresolved symbol; nested-context fallback applies
//! under quantifiers. Preserve encoding-specific function application and source behavior of
//! mutable flags. translatePrecondition sets ignoreAccessPredicates to true; the other public
//! translation methods do not reset it, an upstream behavior to reconcile with callers.
//!
//! Integration:
//! functions::{function_data,function_recorder,function_encoding},
//! supporters::expression_translator, rules::function_supporter, state::terms and reporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for AST keys, source context, diagnostic and symbol freshness.
//!
//! Open decisions:
//! Review mutable ignoreAccessPredicates/reset behavior and unresolved symbol dependence on
//! quantified variables with function axiom generation.
//!
//! Status: partial; recursive heap snapshot replacement, resolution fallback, contexts,
//! projections and function version selection implemented. Fresh-symbol and reporting services
//! and quantified term transforms retain explicit error boundaries.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.
use crate::state::identifiers::Identifier;
use crate::state::terms::{Applicable, Sort, Term, TermKind};
use crate::supporters::expression_translator::{
    ExpressionOverrides, ExpressionTranslationError, ExpressionTranslator,
};
use crate::supporters::functions::function_data::FunctionData;
use crate::supporters::functions::function_recorder::{ExpContext, SnapshotKey};
use ferrum_silver::ast::ast::Info;
use ferrum_silver::ast::expression::{Exp, ExpKind};
use ferrum_silver::ast::program::{Function, Program};
use std::collections::HashMap;

pub trait HeapExpressionServices {
    type Error;
    fn fresh_unresolved(&mut self, sort: &Sort, expression: &Exp) -> Result<Term, Self::Error>;
    fn warn_unresolved(&mut self, expression: &Exp, function: &Function)
    -> Result<(), Self::Error>;
    fn stop_on_unresolved(&self, expression: &Exp, function: &Function) -> bool;
    fn callee_height(&self, name: &str) -> Option<i32>;
    fn heap_function(
        &mut self,
        function: &Function,
        program: &Program,
    ) -> Result<Applicable, Self::Error>;
    fn translate_heap_function_application(
        &mut self,
        function: Applicable,
        snapshot: Term,
        args: Vec<Term>,
        callee: &Function,
        program: &Program,
    ) -> Result<Term, Self::Error>;
}
/// Stateful source translator; it must be reset at each entry point and is not shared
/// across concurrent translations. Resolution failure remains explicit in `failed`.
pub struct HeapAccessReplacingTranslator<'a, D, S: HeapExpressionServices> {
    pub program: &'a Program,
    pub data: &'a FunctionData<D>,
    pub services: &'a mut S,
    pub failed: bool,
    pub prior_verification_failures: bool,
    pub ignore_access_predicates: bool,
    pub context: Vec<ExpContext>,
    pub check_inner_contexts: bool,
}
impl<D: Clone, S: HeapExpressionServices> HeapAccessReplacingTranslator<'_, D, S> {
    fn resolve<R>(
        &mut self,
        translator: &ExpressionTranslator<'_, R>,
        expression: &Exp,
        sort: Sort,
        function_snapshot: bool,
    ) -> Result<Term, ExpressionTranslationError<S::Error>>
    where
        R: Fn(&Sort) -> Result<String, S::Error>,
    {
        let values = if function_snapshot {
            &self.data.recorder_handler.function_snapshots
        } else {
            &self.data.recorder_handler.location_snapshots
        };
        let exact = values
            .iter()
            .find(|(key, _)| key.expression == *expression && key.context == self.context);
        let inner = if self.check_inner_contexts {
            values.iter().find(|(key, _)| {
                key.expression == *expression && key.context.starts_with(&self.context)
            })
        } else {
            None
        };
        if let Some((_, term)) = exact.or(inner) {
            return Ok(translator.factory.sort_wrapper(term.clone(), sort));
        }
        if !self.failed && !self.prior_verification_failures {
            self.services
                .warn_unresolved(expression, &self.data.program_function)
                .map_err(ExpressionTranslationError::Service)?;
        }
        self.failed |= self
            .services
            .stop_on_unresolved(expression, &self.data.program_function);
        self.services
            .fresh_unresolved(&sort, expression)
            .map_err(ExpressionTranslationError::Service)
    }
    pub fn translate_body<R>(
        &mut self,
        translator: &ExpressionTranslator<'_, R>,
    ) -> Result<Option<Term>, ExpressionTranslationError<S::Error>>
    where
        R: Fn(&Sort) -> Result<String, S::Error>,
    {
        self.failed = false;
        self.context.clear();
        self.check_inner_contexts = false;
        let result = self
            .data
            .program_function
            .body
            .as_ref()
            .map(|body| translator.translate_with(body, self))
            .transpose()?;
        Ok(if self.failed { None } else { result })
    }
    pub fn translate_preconditions<R>(
        &mut self,
        translator: &ExpressionTranslator<'_, R>,
        expressions: &[Exp],
    ) -> Result<Vec<Term>, ExpressionTranslationError<S::Error>>
    where
        R: Fn(&Sort) -> Result<String, S::Error>,
    {
        self.failed = false;
        self.ignore_access_predicates = true;
        self.context.clear();
        self.check_inner_contexts = false;
        expressions
            .iter()
            .map(|e| {
                ferrum_silver::ast::utility::expressions::when_exhaling(e)
                    .map_err(ExpressionTranslationError::Projection)
            })
            .map(|e| e.and_then(|e| translator.translate_with(&e, self)))
            .collect()
    }
    pub fn translate_postconditions<R>(
        &mut self,
        translator: &ExpressionTranslator<'_, R>,
        expressions: &[Exp],
    ) -> Result<Vec<Term>, ExpressionTranslationError<S::Error>>
    where
        R: Fn(&Sort) -> Result<String, S::Error>,
    {
        self.failed = false;
        self.context.clear();
        self.check_inner_contexts = false;
        expressions
            .iter()
            .map(|e| {
                ferrum_silver::ast::utility::expressions::when_inhaling(e)
                    .map_err(ExpressionTranslationError::Projection)
            })
            .map(|e| e.and_then(|e| translator.translate_with(&e, self)))
            .collect()
    }
}
impl<D: Clone, S: HeapExpressionServices, R> ExpressionOverrides<R, S::Error>
    for HeapAccessReplacingTranslator<'_, D, S>
where
    R: Fn(&Sort) -> Result<String, S::Error>,
{
    fn translate_special(
        &mut self,
        translator: &ExpressionTranslator<'_, R>,
        expression: &Exp,
    ) -> Option<Result<Term, ExpressionTranslationError<S::Error>>> {
        let f = translator.factory;
        let result = match expression.kind() {
            ExpKind::FieldAccessPredicate(..)
            | ExpKind::PredicateAccessPredicate(..)
            | ExpKind::MagicWand(..)
                if self.ignore_access_predicates =>
            {
                Ok(f.boolean(true))
            }
            ExpKind::Forall(..) if self.ignore_access_predicates && !expression.is_pure() => {
                Ok(f.boolean(true))
            }
            ExpKind::Result(_) => Ok(self.data.formal_result.clone()),
            ExpKind::LocalVar(_) | ExpKind::LocalVarWithVersion(..) => {
                match self
                    .data
                    .formal_args
                    .iter()
                    .find(|(key, _)| key.expression() == expression)
                {
                    Some((_, term)) => Ok(term.clone()),
                    None => return None,
                }
            }
            ExpKind::Let(decl, value, body) => (|| {
                let local = Exp::new(ExpKind::LocalVar(decl.local_var()), decl.meta.clone());
                let variable = translator.translate_with(&local, self)?;
                let value = translator.translate_with(value, self)?;
                self.context.push(ExpContext::Let(expression.clone()));
                let translated = translator.translate_with(body, self);
                self.context.pop();
                Ok(f.let_term([(variable, value)], translated?))
            })(),
            ExpKind::Forall(..) | ExpKind::Exists(..) => (|| {
                self.context
                    .push(ExpContext::Quantifier(expression.clone()));
                let old = self.check_inner_contexts;
                self.check_inner_contexts = true;
                let translated = translator.translate_without_override(expression, self);
                self.context.pop();
                self.check_inner_contexts = old;
                let quantifier = translated?;
                let TermKind::Quantification { vars, .. } = quantifier.kind() else {
                    return Err(ExpressionTranslationError::UnsupportedExpression);
                };
                let names: Vec<_> = vars
                    .iter()
                    .filter_map(|v| match v.kind() {
                        TermKind::Var(v) => Some(v.id.name()),
                        _ => None,
                    })
                    .collect();
                let mut substitutions = HashMap::new();
                let vars = quantifier
                    .deep_collect(&mut |term| match term.kind() {
                        TermKind::Var(v) => match &v.id {
                            Identifier::Suffixed { prefix, .. }
                                if names.contains(&prefix.name()) =>
                            {
                                Some((
                                    term.clone(),
                                    f.var(Identifier::Simple(prefix.name()), v.sort.clone(), false),
                                ))
                            }
                            _ => None,
                        },
                        _ => None,
                    })
                    .map_err(ExpressionTranslationError::Traversal)?;
                for (from, to) in vars {
                    substitutions.insert(from, to);
                }
                f.replace(&quantifier, &substitutions)
                    .map_err(ExpressionTranslationError::Quantifier)
            })(),
            ExpKind::FieldAccess(_) | ExpKind::PredicateAccess(_) => (|| {
                let typ = expression.typ().map_err(ExpressionTranslationError::Type)?;
                let sort = translator
                    .converter
                    .to_sort(&typ)
                    .map_err(ExpressionTranslationError::Sort)?;
                self.resolve(translator, expression, sort, false)
            })(),
            ExpKind::Unfolding(_, body)
            | ExpKind::Applying(_, body)
            | ExpKind::Asserting(_, body) => translator.translate_with(body, self),
            ExpKind::FuncApp(name, args) => (|| {
                let callee = self
                    .program
                    .find_function_optionally(name)
                    .cloned()
                    .ok_or_else(|| ExpressionTranslationError::MissingFunction(name.clone()))?;
                let height = self
                    .services
                    .callee_height(name)
                    .ok_or_else(|| ExpressionTranslationError::MissingFunction(name.clone()))?;
                let defined = self
                    .services
                    .heap_function(&callee, self.program)
                    .map_err(ExpressionTranslationError::Service)?;
                let default = if self.data.height < height {
                    defined.clone()
                } else {
                    crate::rules::function_supporter::limited_version(f, &defined)
                };
                let opaque = matches!(callee.meta.info.find(&|i|matches!(i,Info::Annotation(_))),Some(Info::Annotation(a)) if a.contains_key("opaque"));
                let reveal = matches!(expression.metadata().info.find(&|i|matches!(i,Info::Annotation(_))),Some(Info::Annotation(a)) if a.contains_key("reveal"));
                let applicable = if opaque && !reveal {
                    crate::rules::function_supporter::limited_version(f, &defined)
                } else {
                    default
                };
                let mut values = Vec::new();
                for arg in args {
                    values.push(translator.translate_with(arg, self)?);
                }
                let snapshot = self.resolve(translator, expression, Sort::Snap, true)?;
                self.services
                    .translate_heap_function_application(
                        applicable,
                        snapshot,
                        values,
                        &callee,
                        self.program,
                    )
                    .map_err(ExpressionTranslationError::Service)
            })(),
            _ => return None,
        };
        Some(result)
    }
}
/// Retrieve an exact or inner-context recording using source order.
pub fn find_snapshot<'a>(
    values: &'a [(SnapshotKey, Term)],
    expression: &Exp,
    context: &[ExpContext],
    inner: bool,
) -> Option<&'a Term> {
    values
        .iter()
        .find(|(key, _)| key.expression == *expression && key.context == context)
        .or_else(|| {
            inner
                .then(|| {
                    values.iter().find(|(key, _)| {
                        key.expression == *expression && key.context.starts_with(context)
                    })
                })
                .flatten()
        })
        .map(|(_, term)| term)
}
