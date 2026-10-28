//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/LetSupporter.scala
//!
//! Purpose:
//! Evaluate nested let expressions and return bound store to the caller.
//!
//! Planned Rust structure:
//! LetSupportRules and letSupporter.handle overloads recursively evaluate each binding with
//! evaluator; extend store and collect bindings before passing final body and Store to Q.
//!
//! Behavior to preserve:
//! Evaluate bindings left to right with each prior binding in scope; non-let input invokes Q with
//! an empty store. Evaluation failure prevents Q; restoration belongs to callers.
//!
//! Integration:
//! rules::evaluator, rules::consumer, rules::producer and state::store.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Typed expression and continuation interfaces.
//!
//! Status: implemented continuation-driven let binding; evaluator integration is pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::state::State;
use crate::state::store::{AbstractLocalVar, MapBackedStore, StoreValue};
use ferrum_silver::ast::expression::{Exp, ExpKind};
use std::sync::Arc;

/// Evaluators retain control of branching and may invoke the continuation for each path.
pub trait LetEvaluator<P, D, J, R> {
    type Error;
    fn evaluate(
        &mut self,
        state: State<P, D, J>,
        expression: &Exp,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            StoreValue,
        ) -> Result<R, Self::Error>,
    ) -> Result<R, Self::Error>;
}
/// Peel nested lets in evaluation order and carry their bindings into the continuation.
pub fn handle<P, D, J: Clone, R, E: LetEvaluator<P, D, J, R>>(
    evaluator: &mut E,
    state: State<P, D, J>,
    expression: &Exp,
    continuation: &mut dyn FnMut(
        State<P, D, J>,
        MapBackedStore,
        Exp,
        &mut E,
    ) -> Result<R, E::Error>,
) -> Result<R, E::Error> {
    fn recurse<P, D, J: Clone, R, E: LetEvaluator<P, D, J, R>>(
        evaluator: &mut E,
        state: State<P, D, J>,
        expression: &Exp,
        bindings: Vec<(AbstractLocalVar, StoreValue)>,
        continuation: &mut dyn FnMut(
            State<P, D, J>,
            MapBackedStore,
            Exp,
            &mut E,
        ) -> Result<R, E::Error>,
    ) -> Result<R, E::Error> {
        if let ExpKind::Let(variable, value, body) = expression.kind() {
            let local = variable.local_var();
            let key =
                AbstractLocalVar::new(Exp::new(ExpKind::LocalVar(local), variable.meta.clone()));
            evaluator.evaluate(state, value, &mut |evaluator, mut state, result| {
                let mut bindings = bindings.clone();
                bindings.push((key.clone(), result.clone()));
                state.g = Arc::new(state.g.with_binding(key.clone(), result));
                recurse(evaluator, state, body, bindings, continuation)
            })
        } else {
            continuation(
                state,
                MapBackedStore::from_bindings(bindings),
                expression.clone(),
                evaluator,
            )
        }
    }
    recurse(evaluator, state, expression, Vec::new(), continuation)
}
