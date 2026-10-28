//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/MethodSupporter.scala
//!
//! Purpose:
//! Verify methods by producing contracts and executing their CFGs.
//!
//! Planned Rust structure:
//! Port MethodVerificationUnit and DefaultMethodVerificationUnitProvider analyze/verify/lifecycle,
//! including annotations and debug logging.
//!
//! Behavior to preserve:
//! Set member prover options; warn for ignored non-loop label invariants; initialize fresh store,
//! empty heap and old heaps. Locally produce preconditions, saturate and save pre-state,
//! separately check postcondition wellformedness in empty heap and execute CFG then consume
//! postconditions. Preserve continuation ordering, failure attribution and prover-option reset.
//!
//! Integration:
//! rules::{producer,consumer,executor,execution_flow_controller}, state::{state,store},
//! decider::decider and Silver CFG/reporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for independent states, continuations and solver lifecycle.
//!
//! Open decisions:
//! Reconcile option cleanup on exceptional paths and debug-heap ownership with verifier and rules.
//!
//! Status: partial; method analysis and source verification control flow implemented.
//! Concrete solver, diagnostics, debug/logging and rule services remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::verification::VerificationResult;
use crate::state::heap::ListBackedHeap;
use crate::state::state::State;
use crate::state::terms::Term;
use ferrum_silver::ast::expression::Exp;
use ferrum_silver::ast::program::{LocalVarDecl, Method, Program};
use ferrum_silver::cfg::silver::silver_cfg::SilverCfg;
use std::sync::Arc;

/// Owned continuation at the end of a method CFG. It carries the source
/// method so postcondition checking can resume on the current verifier.
#[derive(Clone)]
pub struct MethodCfgContinuation {
    method: Method,
}

pub trait MethodVerificationServices<P, D, J, V>: Sized {
    type Error;
    fn warn_method_annotation(&mut self, warning: String) -> Result<(), Self::Error>;
    fn set_method_prover_options(
        &mut self,
        options: crate::package::Map<String, String>,
    ) -> Result<(), Self::Error>;
    fn reset_method_prover_options(&mut self) -> Result<(), Self::Error>;
    fn open_method_log(&mut self, method: &Method) -> Result<(), Self::Error>;
    fn open_post_wellformedness_scope(
        &mut self,
        _state: &State<P, D, J>,
        _posts: &[ferrum_silver::ast::expression::Exp],
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn close_post_wellformedness_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn close_method_log(&mut self) -> Result<(), Self::Error>;
    fn warn_ignored_loop_labels(
        &mut self,
        labels: &[ferrum_silver::ast::program::LabelDeclaration],
    ) -> Result<(), Self::Error>;
    fn fresh_method_local(
        &mut self,
        formal: &LocalVarDecl,
    ) -> Result<(Term, Option<Exp>), Self::Error>;
    fn empty_method_heap(
        &mut self,
        state: &State<P, D, J>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn prepare_method_debug(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn record_method_pre_state(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn prepare_method_post_state(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn output_method_cfg(&mut self, method: &Method, cfg: &SilverCfg) -> Result<(), Self::Error>;
    fn reset_method_error_count(&mut self);
    fn saturate_method_contract(&mut self) -> Result<(), Self::Error>;
    fn method_locally(
        &mut self,
        state: State<P, D, J>,
        action: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            MethodVerificationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, MethodVerificationError<Self::Error>>;
    fn produce_method_contract(
        &mut self,
        state: State<P, D, J>,
        assertions: &[Exp],
        method: &Method,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            MethodVerificationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, MethodVerificationError<Self::Error>>;
    fn execute_method_cfg(
        &mut self,
        state: State<P, D, J>,
        cfg: &SilverCfg,
        continuation: MethodCfgContinuation,
    ) -> Result<VerificationResult<V>, MethodVerificationError<Self::Error>>;
    fn consume_method_posts(
        &mut self,
        state: State<P, D, J>,
        posts: &[Exp],
        method: &Method,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<
            VerificationResult<V>,
            MethodVerificationError<Self::Error>,
        >,
    ) -> Result<VerificationResult<V>, MethodVerificationError<Self::Error>>;
}
#[derive(Debug)]
pub enum MethodVerificationError<E> {
    Annotation(crate::supporters::annotation_supporter::AnnotationError<E>),
    Cfg(ferrum_silver::cfg::silver::cfg_generator::GeneratorError),
    Traversal(ferrum_silver::ast::utility::nodes::TraversalError),
    Service(E),
}
/// Complete an executed CFG by restoring its method post-state and consuming
/// postconditions before returning the branch result.
pub fn complete_method_cfg<P, D, J, V, C: MethodVerificationServices<P, D, J, V>>(
    context: &mut C,
    state: State<P, D, J>,
    continuation: &MethodCfgContinuation,
) -> Result<VerificationResult<V>, MethodVerificationError<C::Error>> {
    let state = context
        .prepare_method_post_state(state)
        .map_err(MethodVerificationError::Service)?;
    context.consume_method_posts(
        state,
        &continuation.method.posts,
        &continuation.method,
        &mut |_, _| Ok(VerificationResult::success()),
    )
}

/// Verify a method by proving postcondition well-formedness and executing the body
/// in separate local scopes after precondition production and pre-state recording.
pub fn verify_method<P, D, J: Clone, V, C: MethodVerificationServices<P, D, J, V>>(
    context: &mut C,
    initial: State<P, D, J>,
    method: &Method,
) -> Result<Vec<VerificationResult<V>>, MethodVerificationError<C::Error>> {
    use crate::state::store::{AbstractLocalVar, MapBackedStore};
    use ferrum_silver::ast::expression::ExpKind;
    use ferrum_silver::ast::program::Declaration;
    let options = crate::supporters::annotation_supporter::prover_config_args(
        &method.name,
        &method.meta.info,
        |warning| context.warn_method_annotation(warning),
    )
    .map_err(MethodVerificationError::Annotation)?;
    context
        .set_method_prover_options(options)
        .map_err(MethodVerificationError::Service)?;
    context
        .open_method_log(method)
        .map_err(MethodVerificationError::Service)?;
    let body = method.body_or_assume_false();
    let cfg = Arc::new(
        ferrum_silver::cfg::silver::cfg_generator::statement_to_cfg(&body, true, true)
            .map_err(MethodVerificationError::Cfg)?,
    );
    context
        .warn_ignored_loop_labels(&ignored_loop_invariant_labels(&cfg))
        .map_err(MethodVerificationError::Service)?;
    let mut locals: Vec<LocalVarDecl> = method
        .formal_args
        .iter()
        .chain(&method.formal_returns)
        .cloned()
        .collect();
    locals.extend(
        method
            .scoped_declarations()
            .map_err(MethodVerificationError::Traversal)?
            .into_iter()
            .filter_map(|decl| match decl {
                Declaration::Local(local) => Some(local),
                _ => None,
            }),
    );
    let mut bindings = Vec::new();
    for local in locals {
        let value = context
            .fresh_method_local(&local)
            .map_err(MethodVerificationError::Service)?;
        bindings.push((
            AbstractLocalVar::new(Exp::new(
                ExpKind::LocalVar(local.local_var()),
                local.meta.clone(),
            )),
            value,
        ));
    }
    let mut state = initial;
    state.g = Arc::new(MapBackedStore::from_bindings(bindings));
    state.h = context
        .empty_method_heap(&state)
        .map_err(MethodVerificationError::Service)?;
    state.old_heaps = Default::default();
    state.debug_old_heaps = Default::default();
    state.method_cfg = Some(cfg.clone());
    let initial_method_state = state.clone();
    state = context
        .prepare_method_debug(state)
        .map_err(MethodVerificationError::Service)?;
    context
        .output_method_cfg(method, &cfg)
        .map_err(MethodVerificationError::Service)?;
    context.reset_method_error_count();
    let result = context.method_locally(state, &mut |context, state| {
        context.produce_method_contract(state, &method.pres, method, &mut |context, mut state| {
            context
                .saturate_method_contract()
                .map_err(MethodVerificationError::Service)?;
            state.old_heaps.insert("old".into(), state.h.clone());
            state = context
                .record_method_pre_state(state)
                .map_err(MethodVerificationError::Service)?;
            let check_state = state.clone();
            let wellformed = context.method_locally(check_state, &mut |context, mut state| {
                state.h = context
                    .empty_method_heap(&state)
                    .map_err(MethodVerificationError::Service)?;
                let scope = context
                    .open_post_wellformedness_scope(&initial_method_state, &method.posts)
                    .map_err(MethodVerificationError::Service)?;
                context.produce_method_contract(state, &method.posts, method, &mut |context, _| {
                    context
                        .close_post_wellformedness_scope(scope)
                        .map_err(MethodVerificationError::Service)?;
                    Ok(VerificationResult::success())
                })
            })?;
            if wellformed.is_fatal() {
                return Ok(wellformed);
            }
            let execution = context.method_locally(state, &mut |context, state| {
                context.execute_method_cfg(
                    state,
                    &cfg,
                    MethodCfgContinuation {
                        method: method.clone(),
                    },
                )
            })?;
            Ok(wellformed.and_then(|| execution))
        })
    })?;
    context
        .reset_method_prover_options()
        .map_err(MethodVerificationError::Service)?;
    context
        .close_method_log()
        .map_err(MethodVerificationError::Service)?;
    Ok(vec![result])
}
/// Unit analysis follows source program method order.
pub fn analyze_methods(program: &Program) -> Vec<Method> {
    program.methods.clone()
}

/// Source warns once for the first label in each non-loop statement block that
/// retained loop invariants; label declarations at actual loop heads are excluded.
pub fn ignored_loop_invariant_labels(
    cfg: &SilverCfg,
) -> Vec<ferrum_silver::ast::program::LabelDeclaration> {
    use ferrum_silver::ast::statement::StmtKind;
    use ferrum_silver::cfg::block::BlockKind;
    let mut labels = Vec::new();
    for block in cfg.graph().blocks() {
        if let BlockKind::Statement {
            statements,
            invariants: Some(_),
            ..
        } = block.kind()
        {
            if let Some(label) = statements.iter().find_map(|stmt| match stmt.kind() {
                StmtKind::Label(label) => Some(label.clone()),
                _ => None,
            }) {
                labels.push(label);
            }
        }
    }
    labels
}

#[cfg(test)]
mod owned_method_continuation_tests {
    #[test]
    fn method_cfg_continuation_is_send() {
        fn require_send<T: Send>() {}
        require_send::<super::MethodCfgContinuation>();
    }
}
