//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/QuantifiedPropertyInterpreter.scala
//!
//! Purpose:
//! Instantiate an instance property as a quantified condition over a quantified chunk.
//!
//! Planned Rust structure:
//! Port QuantifiedPropertyInterpreter Info, buildPathConditionForChunk, accessors, Check and
//! ForEach overrides.
//!
//! Behavior to preserve:
//! Substitute quantified chunk variables with supplied arguments, generate forall with supplied
//! triggers and qid prefix/property name. Guard by condition only when arguments or value were
//! accessed; reset argsUsed after each build. Check becomes ITE and ForEach is unsupported. Debug
//! value access is unimplemented upstream.
//!
//! Integration:
//! resources::property_interpreter, interfaces::state quantified chunks, state::terms and Silver
//! debug AST.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for quantifier triggers, explicit mutable context and debugging.
//!
//! Open decisions:
//! Resolve unsupported debug value access and argsUsed ownership with quantified chunk producers
//! and verifier.
//!
//! Status: partial; term construction and quantified chunk callbacks implemented.
//! Debug-expression construction remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::property::Property;
use super::property_expressions::{BooleanExpression, ChunkPlaceholder};
use super::property_interpreter::{PropertyContext, PropertyError, PropertyInterpreter};
use crate::interfaces::state::chunks::QuantifiedChunk;
use crate::state::terms::{Quantifier, Term, TermFactory, Trigger, UnsupportedTriggerTransform};
use std::collections::HashMap;

#[derive(Debug)]
pub enum QuantifiedPropertyError {
    ForEachUnsupported,
    Transform(UnsupportedTriggerTransform),
    ZeroDenominator,
    InvalidQuantifier,
    MissingDebugExpression,
    DebugSubstitution,
    DebugValueUnsupported,
}
struct Context<'a, Q> {
    chunk: &'a Q,
    factory: &'a TermFactory,
    args: &'a [Term],
    permission: &'a Term,
    args_used: bool,
}
impl<Q: QuantifiedChunk> PropertyContext for Context<'_, Q> {
    type Error = QuantifiedPropertyError;
    fn permission(&mut self, _: &ChunkPlaceholder) -> Result<Term, Self::Error> {
        Ok(self.permission.clone())
    }
    fn value(&mut self, _: &ChunkPlaceholder) -> Result<Term, Self::Error> {
        self.args_used = true;
        Ok(self.chunk.value_at(self.factory, self.args))
    }
    fn arguments(&mut self, _: &ChunkPlaceholder) -> Result<Vec<Term>, Self::Error> {
        self.args_used = true;
        Ok(self.args.to_vec())
    }
    fn check(&mut self, _: &Term) -> Result<Option<bool>, Self::Error> {
        Ok(None)
    }
    fn for_each(
        &mut self,
        _: &TermFactory,
        _: &[ChunkPlaceholder],
        _: &BooleanExpression,
    ) -> Result<Term, PropertyError<Self::Error>> {
        Err(PropertyError::Context(
            QuantifiedPropertyError::ForEachUnsupported,
        ))
    }
}
/// Produce the quantified term; debug-expression reconstruction remains a separate gap.
pub fn build_for_chunk<Q: QuantifiedChunk>(
    factory: &TermFactory,
    chunk: &Q,
    property: &Property,
    qvars: Vec<Term>,
    args: &[Term],
    permission: &Term,
    condition: &Term,
    triggers: Vec<Trigger>,
    qid_prefix: &str,
) -> Result<Term, QuantifiedPropertyError> {
    let context = Context {
        chunk,
        factory,
        args,
        permission,
        args_used: false,
    };
    let mut interpreter = PropertyInterpreter { factory, context };
    let body = interpreter
        .boolean(&property.expression)
        .map_err(|e| match e {
            PropertyError::Context(e) => e,
            PropertyError::ZeroDenominator => QuantifiedPropertyError::ZeroDenominator,
            PropertyError::InvalidQuantifier => QuantifiedPropertyError::InvalidQuantifier,
        })?;
    let substitutions: HashMap<_, _> = chunk
        .quantified_vars(factory)
        .into_iter()
        .zip(args.iter().cloned())
        .collect();
    let body = factory
        .replace(&body, &substitutions)
        .map_err(QuantifiedPropertyError::Transform)?;
    let condition = if interpreter.context.args_used {
        condition.clone()
    } else {
        factory.boolean(true)
    };
    factory
        .quantification(
            Quantifier::Forall,
            qvars,
            factory.implies(condition, body),
            triggers,
            format!("{qid_prefix}-{}", property.name),
            false,
            None,
        )
        .map_err(QuantifiedPropertyError::Transform)
}

struct DebugContext<'a> {
    args: &'a [Term],
    args_exp: &'a [ferrum_silver::ast::expression::Exp],
    permission: &'a Term,
    permission_exp: &'a ferrum_silver::ast::expression::Exp,
    args_used: bool,
}
impl super::debug_property_interpreter::DebugPropertyContext for &mut DebugContext<'_> {
    type Error = QuantifiedPropertyError;
    fn permission(
        &mut self,
        _: &ChunkPlaceholder,
    ) -> Result<super::debug_property_interpreter::Pair, Self::Error> {
        Ok((self.permission.clone(), self.permission_exp.clone()))
    }
    fn value(
        &mut self,
        _: &ChunkPlaceholder,
    ) -> Result<super::debug_property_interpreter::Pair, Self::Error> {
        Err(QuantifiedPropertyError::DebugValueUnsupported)
    }
    fn arguments(
        &mut self,
        _: &ChunkPlaceholder,
    ) -> Result<(Vec<Term>, Vec<ferrum_silver::ast::expression::Exp>), Self::Error> {
        self.args_used = true;
        Ok((self.args.to_vec(), self.args_exp.to_vec()))
    }
    fn check(&mut self, _: &Term) -> Result<Option<bool>, Self::Error> {
        Ok(None)
    }
    fn for_each(
        &mut self,
        _: &TermFactory,
        _: &[ChunkPlaceholder],
        _: &BooleanExpression,
    ) -> Result<super::debug_property_interpreter::Pair, PropertyError<Self::Error>> {
        Err(PropertyError::Context(
            QuantifiedPropertyError::ForEachUnsupported,
        ))
    }
}
/// Source quantified property construction, including the corresponding forall expression.
pub fn build_debug_for_chunk<Q: QuantifiedChunk>(
    factory: &TermFactory,
    chunk: &Q,
    property: &Property,
    qvars: Vec<Term>,
    qvars_exp: &[ferrum_silver::ast::program::LocalVarDecl],
    args: &[Term],
    args_exp: &[ferrum_silver::ast::expression::Exp],
    permission: &Term,
    permission_exp: &ferrum_silver::ast::expression::Exp,
    condition: &Term,
    condition_exp: &ferrum_silver::ast::expression::Exp,
    triggers: Vec<Trigger>,
    qid_prefix: &str,
) -> Result<(Term, ferrum_silver::ast::expression::Exp), QuantifiedPropertyError> {
    use ferrum_silver::ast::{
        ast::Metadata,
        expression::{Exp, ExpKind},
    };
    let mut context = DebugContext {
        args,
        args_exp,
        permission,
        permission_exp,
        args_used: false,
    };
    let (body, body_exp) = super::debug_property_interpreter::DebugPropertyInterpreter {
        factory,
        context: &mut context,
    }
    .boolean(&property.expression)
    .map_err(|e| match e {
        PropertyError::Context(e) => e,
        PropertyError::ZeroDenominator => QuantifiedPropertyError::ZeroDenominator,
        PropertyError::InvalidQuantifier => QuantifiedPropertyError::InvalidQuantifier,
    })?;
    let substitutions: HashMap<_, _> = chunk
        .quantified_vars(factory)
        .into_iter()
        .zip(args.iter().cloned())
        .collect();
    let body = factory
        .replace(&body, &substitutions)
        .map_err(QuantifiedPropertyError::Transform)?;
    let names = chunk
        .quantified_var_exps()
        .ok_or(QuantifiedPropertyError::MissingDebugExpression)?
        .into_iter()
        .map(|v| v.name.clone())
        .collect::<Vec<_>>();
    let body_exp = crate::utils::ast::replace_vars_in_exp(&body_exp, &names, args_exp)
        .map_err(|_| QuantifiedPropertyError::DebugSubstitution)?;
    let guard = if context.args_used {
        condition.clone()
    } else {
        factory.boolean(true)
    };
    let guard_exp = if context.args_used {
        condition_exp.clone()
    } else {
        Exp::new(ExpKind::TrueLit, condition_exp.metadata().clone())
    };
    let term = factory
        .quantification(
            Quantifier::Forall,
            qvars,
            factory.implies(guard, body),
            triggers,
            format!("{qid_prefix}-{}", property.name),
            false,
            None,
        )
        .map_err(QuantifiedPropertyError::Transform)?;
    let exp = Exp::new(
        ExpKind::Forall(
            qvars_exp.to_vec(),
            vec![],
            Exp::new(ExpKind::Implies(guard_exp, body_exp), Metadata::default()),
        ),
        Metadata::default(),
    );
    Ok((term, exp))
}
