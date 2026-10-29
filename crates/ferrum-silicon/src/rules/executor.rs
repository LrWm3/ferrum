//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/Executor.scala
//!
//! Purpose:
//! Execute Silver CFGs and statements over symbolic state.
//!
//! Planned Rust structure:
//! ExecutionRules and executor implement CFG/block/statement exec, execs, follow/follows,
//! handleOutEdge, path IDs, ssaifyRhs and hack407 helpers. Dispatch sequence, labels, declarations,
//! local/field assignments, allocation, inhale/exhale/assert, method calls, fold/unfold,
//! package/apply, havoc/havocall and TryBlock.
//!
//! Behavior to preserve:
//! Follow edge conditions through brancher; optional all-join mode merges if-statement branches,
//! while loop incoming edges first havoc written locals, check invariant well-definedness in a
//! local scope, consume invariant, retain leftover heap in invariantContexts, replay recorded
//! assumptions, check guard framing and follow ordered internal then exit edges. Backedges consume
//! invariant and terminate; out edges merge leftover context. Preserve block/path reports and
//! nonfatal/fatal result combination. Allocation assumes nonnull and reference disjointness. Assert
//! false uses smoke check; assertions restore heap unless extended exhale transfers resources;
//! disableSubsumption uses isolated consume. Calls evaluate actuals, bind formals, consume
//! preconditions, fresh returns, produce postconditions and restore caller store/old heaps; during
//! packaging reconstruct old heap from consumed precondition snapshot. SSAify RHS terms other than
//! variables and literals with a fresh equality definition. Preserve special havoc and consolidation
//! calls, wand reserve movement, TryBlock fallback and rejection of unexpected CFG-level statements.
//!
//! Integration:
//! rules::evaluator, consumer, producer, brancher, joiner, execution_flow_controller,
//! predicate_supporter, magic_wand_supporter, havoc_supporter, heap_supporter and silver::cfg.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! CFG path reporting, branch state, snapshots and continuation/verifier ownership.
//!
//! Status: partial; statement and CFG execution use native verifier services. Owned CFG
//! terminals support internally gated branch jobs through loop bodies and exits. Owned
//! permission-rule callers and diagnostic coverage remain incomplete; opaque callbacks
//! retain synchronous execution.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::interfaces::verification::VerificationResult;
use crate::state::{
    heap::ListBackedHeap,
    state::State,
    store::{AbstractLocalVar, StoreValue},
};
use ferrum_silver::ast::{
    expression::{Exp, ExpKind, LocalVar},
    statement::{Stmt, StmtKind},
};
use std::sync::Arc;
type TermValue = crate::state::terms::Term;

#[derive(Debug)]
pub enum ExecutionError<E> {
    Context(E),
    MissingReserveHeap,
    FieldAssignmentDuringExtendedExhale,
    MissingDebugExpression,
    MissingMethod(String),
    MissingCallSnapshot,
    MissingReturnValue,
    UnexpectedCfgBlock,
    MissingInvariantContext,
    MissingCfg,
    InvalidCfgEdgePair,
    ReentrantContinuation,
    OwnedCfgSchedulerUnavailable,
    Cfg(ferrum_silver::cfg::silver::silver_cfg::SilverCfgError),
    Traversal(ferrum_silver::ast::utility::nodes::TraversalError),
    ExpressionType(ferrum_silver::ast::expression::ExpressionTypeError),
}
/// Owned traversal to the join point of a CFG branch. The alternate path ID
/// is allocated when the branch actually runs, as in the source continuation.
#[derive(Clone)]
pub struct CfgJoinBranch {
    edge: ferrum_silver::cfg::silver::silver_cfg::SilverEdge,
    join: ferrum_silver::cfg::silver::silver_cfg::SilverBlock,
    path_id: Option<i32>,
}

#[cfg(test)]
impl CfgJoinBranch {
    pub(crate) fn for_test(edge: SilverEdge, join: SilverBlock) -> Self {
        Self {
            edge,
            join,
            path_id: Some(0),
        }
    }
}

/// Debug information captured at statement entry, after selecting its execution heap.
#[derive(Clone)]
pub struct DebugStatementSnapshot {
    pub heap_label: String,
    pub path_conditions: Arc<crate::decider::path_conditions::LayeredPathConditionStack>,
}

/// Concrete verifier services preserve branching, failures, logging and solver state.
pub trait ExecutionContext<P, D, J, V>: Sized {
    type Error;
    fn open_statement(
        &mut self,
        state: &State<P, D, J>,
        statement: &Stmt,
    ) -> Result<(), Self::Error>;
    fn close_statement(&mut self) -> Result<(), Self::Error>;
    fn open_statement_scope(
        &mut self,
        state: &State<P, D, J>,
        statement: &Stmt,
    ) -> Result<Option<i32>, Self::Error> {
        self.open_statement(state, statement)?;
        Ok(None)
    }
    fn close_statement_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        self.close_statement()
    }
    fn execution_heap(
        &mut self,
        state: &State<P, D, J>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn move_to_reserve_heap(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn evaluation_heap(
        &mut self,
        state: &State<P, D, J>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn debug_statement_snapshot(
        &mut self,
        _state: &State<P, D, J>,
    ) -> Result<Option<DebugStatementSnapshot>, Self::Error> {
        Ok(None)
    }
    fn record_label(
        &mut self,
        state: State<P, D, J>,
        label: &str,
        snapshot: Option<&DebugStatementSnapshot>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn fresh_local(&mut self, variable: &LocalVar) -> Result<StoreValue, Self::Error>;
    fn evaluate_assignment(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        rhs: &Exp,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            StoreValue,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn factory(&self) -> &crate::state::terms::TermFactory;
    fn debugging(&self) -> bool;
    fn fresh_ssa(
        &mut self,
        name: &str,
        typ: &ferrum_silver::ast::r#type::Type,
        source: &Exp,
    ) -> Result<StoreValue, Self::Error>;
    fn assume_ssa_definition(
        &mut self,
        equation: &TermValue,
        name: &str,
        typ: &ferrum_silver::ast::r#type::Type,
        source: &Exp,
        rewritten: Option<&Exp>,
        new_variable: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn assign_field(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        receiver: TermValue,
        receiver_exp: Option<Exp>,
        snapshot: TermValue,
        rhs_exp: Option<Exp>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn produce(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        assertion: &Exp,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    /// Resume production with a transferable caller only when the caller explicitly owns it.
    fn produce_with_owned_tail(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        assertion: &Exp,
        _tail: Option<&CfgStatementTail>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>> {
        self.produce(state, statement, assertion, continuation)
    }
    fn statement_scope_transferable(&self, _scope: Option<i32>) -> bool {
        false
    }
    fn execute_owned_nested_sequence(
        &mut self,
        _state: State<P, D, J>,
        _statements: &[Stmt],
        _tail: &CfgStatementTail,
        _continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Option<Result<VerificationResult<V>, ExecutionError<Self::Error>>> {
        None
    }
    fn execute_owned_try_body(
        &mut self,
        _state: State<P, D, J>,
        _body: &Stmt,
        _tail: &CfgStatementTail,
        _success: std::sync::Arc<std::sync::atomic::AtomicBool>,
        _continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Option<Result<VerificationResult<V>, ExecutionError<Self::Error>>> {
        None
    }
    fn consume_with_owned_tail(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        assertion: &Exp,
        _completion: crate::rules::consumer::OwnedConsumptionCompletion,
        _tail: Option<&CfgStatementTail>,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>> {
        self.consume(state, statement, assertion, continuation)
    }
    fn consume(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        assertion: &Exp,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn saturate_after_inhale(&mut self) -> Result<(), Self::Error>;
    fn assume_new_nonnull(
        &mut self,
        term: &TermValue,
        original: &LocalVar,
        rewritten: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn fresh_field_snapshot(
        &mut self,
        field: &ferrum_silver::ast::program::Field,
        original: &LocalVar,
    ) -> Result<TermValue, Self::Error>;
    /// Produce a full-permission fresh field chunk, using the source null partial error.
    fn produce_new_field(
        &mut self,
        state: State<P, D, J>,
        field: &ferrum_silver::ast::program::Field,
        receiver: &TermValue,
        original: &LocalVar,
        rewritten: Option<&Exp>,
        snapshot: TermValue,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn assume_reference_disjointness(
        &mut self,
        terms: &[TermValue],
        expressions: Option<&[Exp]>,
    ) -> Result<(), Self::Error>;
    fn record_new_heap(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        snapshot: Option<&DebugStatementSnapshot>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn disable_subsumption(&self) -> bool;
    fn start_key_heap(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        snapshot: Option<&DebugStatementSnapshot>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn finish_key_heap(&mut self, state: State<P, D, J>) -> Result<State<P, D, J>, Self::Error>;
    fn check_empty_exhale_ext(&mut self, state: &State<P, D, J>) -> Result<(), Self::Error>;
    fn retry_smoke_assertion(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        original_heap: Arc<ListBackedHeap>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn disable_havoc_hack_407(&self) -> bool;
    fn open_method_call_scope(
        &mut self,
        _state: &State<P, D, J>,
        _statement: &Stmt,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn open_call_comment_scope(
        &mut self,
        _state: &State<P, D, J>,
        _comment: &str,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn close_call_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn evaluate_call_arguments(
        &mut self,
        state: State<P, D, J>,
        call: &Stmt,
        arguments: &[Exp],
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Vec<TermValue>,
            Option<Vec<Exp>>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    /// Services build the source call/precondition error transformations and logging scopes.
    fn consume_call_preconditions(
        &mut self,
        state: State<P, D, J>,
        caller_store: &Arc<crate::state::store::MapBackedStore>,
        call: &Stmt,
        method: &ferrum_silver::ast::program::Method,
        return_snapshot: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            Option<TermValue>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    /// Returns None when source's local re-production yielded no state, triggering its fallback heap.
    fn reconstruct_pre_heap(
        &mut self,
        state: &State<P, D, J>,
        call: &Stmt,
        method: &ferrum_silver::ast::program::Method,
        snapshot: &TermValue,
    ) -> Result<Option<Arc<ListBackedHeap>>, Self::Error>;
    fn produce_call_postconditions(
        &mut self,
        state: State<P, D, J>,
        call: &Stmt,
        method: &ferrum_silver::ast::program::Method,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    /// Heap writes, calls, assertions, fold/unfold, wands, havoc and CFG-only cases.
    fn execute_special(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
}
pub fn execute<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    statement: &Stmt,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: ExecutionContext<P, D, J, V>,
{
    execute_with_owned_tail(context, state, statement, None, continuation)
}

fn execute_with_owned_tail<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    statement: &Stmt,
    owned_tail: Option<&CfgStatementTail>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: ExecutionContext<P, D, J, V>,
{
    let scope = context
        .open_statement_scope(&state, statement)
        .map_err(ExecutionError::Context)?;
    state.h = context
        .execution_heap(&state)
        .map_err(ExecutionError::Context)?;
    let debug_snapshot = context
        .debug_statement_snapshot(&state)
        .map_err(ExecutionError::Context)?;
    let mut finish = |context: &mut C, state| {
        let state = context
            .move_to_reserve_heap(state)
            .map_err(ExecutionError::Context)?;
        context
            .close_statement_scope(scope)
            .map_err(ExecutionError::Context)?;
        continuation(context, state)
    };
    match statement.kind() {
        StmtKind::Seqn { statements, .. } => {
            if let Some(tail) = owned_tail
                .filter(|_| !state.exhale_ext && context.statement_scope_transferable(scope))
            {
                if let Some(result) = context.execute_owned_nested_sequence(
                    state.clone(),
                    statements,
                    tail,
                    &mut finish,
                ) {
                    return result;
                }
            }
            execute_all(context, state, statements, &mut finish)
        }
        StmtKind::Label(label) => {
            let name = &label.name;
            let heap = context
                .evaluation_heap(&state)
                .map_err(ExecutionError::Context)?;
            state.old_heaps.insert(name.clone(), heap);
            let state = context
                .record_label(state, name, debug_snapshot.as_ref())
                .map_err(ExecutionError::Context)?;
            finish(context, state)
        }
        StmtKind::LocalVarDeclStmt(decl) => {
            let var = decl.local_var();
            let value = context.fresh_local(&var).map_err(ExecutionError::Context)?;
            let key = AbstractLocalVar::new(Exp::new(ExpKind::LocalVar(var), decl.meta.clone()));
            state.g = Arc::new(state.g.with_binding(key, value));
            finish(context, state)
        }
        StmtKind::LocalVarAssign { lhs, rhs } => {
            let state = context
                .start_key_heap(state, statement, debug_snapshot.as_ref())
                .map_err(ExecutionError::Context)?;
            context.evaluate_assignment(state, statement, rhs, &mut |context, state, value| {
                let value = ssaify(context, &lhs.name, &lhs.typ, rhs, value)?;
                let mut state = context
                    .finish_key_heap(state)
                    .map_err(ExecutionError::Context)?;
                let key = AbstractLocalVar::new(Exp::new(
                    ExpKind::LocalVar(lhs.clone()),
                    lhs.meta.clone(),
                ));
                state.g = Arc::new(state.g.with_binding(key, value));
                finish(context, state)
            })
        }
        StmtKind::NewStmt { lhs, fields } => {
            let (receiver, rewritten) =
                context.fresh_local(lhs).map_err(ExecutionError::Context)?;
            if context.debugging() && rewritten.is_none() {
                return Err(ExecutionError::MissingDebugExpression);
            }
            context
                .assume_new_nonnull(&receiver, lhs, rewritten.as_ref())
                .map_err(ExecutionError::Context)?;
            let disjoint = crate::state::utils::compute_reference_disjointnesses(
                state.g.as_ref(),
                state.h.as_ref(),
                &receiver,
                context.factory(),
            );
            let disjoint_exps = if let Some(exp) = &rewritten {
                Some(
                    crate::state::utils::compute_reference_disjointnesses_exp(
                        state.g.as_ref(),
                        state.h.as_ref(),
                        exp,
                    )
                    .map_err(ExecutionError::ExpressionType)?,
                )
            } else {
                None
            };
            produce_new_fields(
                context,
                state,
                fields,
                lhs,
                &receiver,
                rewritten.as_ref(),
                &mut |context, mut state| {
                    let key = AbstractLocalVar::new(Exp::new(
                        ExpKind::LocalVar(lhs.clone()),
                        lhs.meta.clone(),
                    ));
                    state.g = Arc::new(
                        state
                            .g
                            .with_binding(key, (receiver.clone(), rewritten.clone())),
                    );
                    let state = context
                        .record_new_heap(state, statement, debug_snapshot.as_ref())
                        .map_err(ExecutionError::Context)?;
                    context
                        .assume_reference_disjointness(&disjoint, disjoint_exps.as_deref())
                        .map_err(ExecutionError::Context)?;
                    finish(context, state)
                },
            )
        }
        StmtKind::MethodCall {
            method_name,
            args,
            targets,
        } if method_name != "___silicon_hack510_consolidate_state"
            && (context.disable_havoc_hack_407()
                || !method_name.starts_with("___silicon_hack407_havoc_all_")) =>
        {
            let method = state
                .program
                .methods
                .iter()
                .find(|m| &m.name == method_name)
                .cloned()
                .ok_or_else(|| ExecutionError::MissingMethod(method_name.clone()))?;
            let call_scope = context
                .open_method_call_scope(&state, statement)
                .map_err(ExecutionError::Context)?;
            let parameters_scope = context
                .open_call_comment_scope(&state, "Parameters")
                .map_err(ExecutionError::Context)?;
            let original_exhale_ext = state.exhale_ext;
            let state = context
                .start_key_heap(state, statement, debug_snapshot.as_ref())
                .map_err(ExecutionError::Context)?;
            context.evaluate_call_arguments(state,statement,args,&mut |context,state,terms,debug_args| {
                context.close_call_scope(parameters_scope).map_err(ExecutionError::Context)?;
                let pre_scope = context.open_call_comment_scope(&state, "Precondition").map_err(ExecutionError::Context)?;
                let caller = state.clone();
                let values = terms.iter().enumerate().map(|(i,term)| {
                    let debug = if context.debugging() { Some(debug_args.as_ref().and_then(|es| es.get(i)).cloned().ok_or(ExecutionError::MissingDebugExpression)?) } else { None };
                    Ok((term.clone(),debug))
                }).collect::<Result<Vec<_>,ExecutionError<C::Error>>>()?;
                let bindings = method.formal_args.iter().zip(values).map(|(decl,value)| (AbstractLocalVar::new(Exp::new(ExpKind::LocalVar(decl.local_var()),decl.meta.clone())),value));
                let mut pre_state = state; pre_state.g = Arc::new(crate::state::store::MapBackedStore::from_bindings(bindings)); pre_state.record_visited = true;
                let mut needs_old = false;
                if original_exhale_ext {
                    for post in &method.posts {
                        if ferrum_silver::ast::utility::visitor::exists_defined(&ferrum_silver::ast::utility::nodes::Node::Exp(post.clone()),&ferrum_silver::ast::utility::nodes::subnodes,&mut |node| matches!(node, ferrum_silver::ast::utility::nodes::Node::Exp(exp) if matches!(exp.kind(),ExpKind::Old(..)))).map_err(ExecutionError::Traversal)? { needs_old = true; break; }
                    }
                }
                context.consume_call_preconditions(pre_state,&caller.g,statement,&method,needs_old,&mut |context,mut state,snapshot| {
                    context.close_call_scope(pre_scope).map_err(ExecutionError::Context)?;
                    let post_scope = context.open_call_comment_scope(&state, "Postcondition").map_err(ExecutionError::Context)?;
                    let mut returns = Vec::new();
                    for decl in &method.formal_returns {
                        let var = decl.local_var(); let value = context.fresh_local(&var).map_err(ExecutionError::Context)?;
                        returns.push((AbstractLocalVar::new(Exp::new(ExpKind::LocalVar(var),decl.meta.clone())),value));
                    }
                    let output_store = crate::state::store::MapBackedStore::from_bindings(returns);
                    let old_heap = if needs_old {
                        let snapshot = snapshot.as_ref().ok_or(ExecutionError::MissingCallSnapshot)?;
                        match context.reconstruct_pre_heap(&state,statement,&method,snapshot).map_err(ExecutionError::Context)? { Some(heap) => heap, None => context.evaluation_heap(&caller).map_err(ExecutionError::Context)? }
                    } else { context.evaluation_heap(&caller).map_err(ExecutionError::Context)? };
                    state.old_heaps.insert("old".into(),old_heap);
                    state.g = Arc::new(state.g.with_store(&output_store));
                    context.produce_call_postconditions(state,statement,&method,&mut |context,mut state| {
                        context.close_call_scope(post_scope).map_err(ExecutionError::Context)?;
                        context.saturate_after_inhale().map_err(ExecutionError::Context)?;
                        use crate::state::store::Store;
                        let mut outputs = Vec::new();
                        for (target,decl) in targets.iter().zip(&method.formal_returns) {
                            let source = AbstractLocalVar::new(Exp::new(ExpKind::LocalVar(decl.local_var()),decl.meta.clone()));
                            let value = state.g.values().iter().find(|(key,_)| key == &source).map(|(_,value)| value.clone()).ok_or(ExecutionError::MissingReturnValue)?;
                            let target = AbstractLocalVar::new(Exp::new(ExpKind::LocalVar(target.clone()),target.meta.clone())); outputs.push((target,value));
                        }
                        state.g = Arc::new(caller.g.with_store(&crate::state::store::MapBackedStore::from_bindings(outputs)));
                        state.old_heaps = caller.old_heaps.clone(); state.record_visited = caller.record_visited;
                        context.close_call_scope(call_scope).map_err(ExecutionError::Context)?;
                        let state = context.finish_key_heap(state).map_err(ExecutionError::Context)?;
                        finish(context,state)
                    })
                })
            })
        }
        StmtKind::FieldAssign { lhs, rhs } => {
            if state.exhale_ext {
                return Err(ExecutionError::FieldAssignmentDuringExtendedExhale);
            }
            context.evaluate_assignment(state, statement, &lhs.receiver, &mut |context,
                                                                               state,
                                                                               (
                receiver,
                receiver_exp,
            )| {
                let state = context
                    .start_key_heap(state, statement, debug_snapshot.as_ref())
                    .map_err(ExecutionError::Context)?;
                context.evaluate_assignment(state, statement, rhs, &mut |context, state, value| {
                    let rhs_exp = value.1.clone();
                    let (snapshot, _) =
                        ssaify(context, &lhs.field.name, &lhs.field.typ, rhs, value)?;
                    context.assign_field(
                        state,
                        statement,
                        receiver.clone(),
                        receiver_exp.clone(),
                        snapshot,
                        rhs_exp,
                        &mut |context, state| {
                            let state = context
                                .finish_key_heap(state)
                                .map_err(ExecutionError::Context)?;
                            finish(context, state)
                        },
                    )
                })
            })
        }
        StmtKind::Assert(assertion)
            if matches!(assertion.kind(), ExpKind::FalseLit) && !state.is_in_package =>
        {
            let original_heap = state.h.clone();
            state.h = context
                .evaluation_heap(&state)
                .map_err(ExecutionError::Context)?;
            context.retry_smoke_assertion(state, statement, original_heap)
        }
        StmtKind::Assert(assertion) if context.disable_subsumption() => {
            let original = state.clone();
            let result = context.consume(state, statement, assertion, &mut |_, _| {
                Ok(VerificationResult::success())
            })?;
            if !result.continue_verification() {
                return Ok(result);
            }
            let next = finish(context, original)?;
            Ok(result.combine(|| next, false))
        }
        StmtKind::Assert(assertion) => {
            let original_heap = state.h.clone();
            let original_reserve = state.reserve_heaps.clone();
            let exhale_ext = state.exhale_ext;
            if exhale_ext {
                context
                    .check_empty_exhale_ext(&state)
                    .map_err(ExecutionError::Context)?;
            }
            let state = context
                .start_key_heap(state, statement, debug_snapshot.as_ref())
                .map_err(ExecutionError::Context)?;
            let tail =
                owned_tail.filter(|_| context.statement_scope_transferable(scope) && !exhale_ext);
            let completion = crate::rules::consumer::OwnedConsumptionCompletion::Assert {
                heap: original_heap.clone(),
                reserve: original_reserve.clone(),
            };
            context.consume_with_owned_tail(
                state,
                statement,
                assertion,
                completion,
                tail,
                &mut |context, mut state| {
                    if exhale_ext {
                        state.h = state
                            .reserve_heaps
                            .first()
                            .cloned()
                            .ok_or(ExecutionError::MissingReserveHeap)?;
                    } else {
                        state.h = original_heap.clone();
                        state.reserve_heaps = original_reserve.clone();
                    }
                    let state = context
                        .finish_key_heap(state)
                        .map_err(ExecutionError::Context)?;
                    finish(context, state)
                },
            )
        }
        StmtKind::Inhale(assertion) if matches!(assertion.kind(), ExpKind::FalseLit) => {
            Ok(VerificationResult::success())
        }
        StmtKind::Inhale(assertion) => {
            let state = context
                .start_key_heap(state, statement, debug_snapshot.as_ref())
                .map_err(ExecutionError::Context)?;
            let tail = owned_tail.filter(|_| context.statement_scope_transferable(scope));
            context.produce_with_owned_tail(
                state,
                statement,
                assertion,
                tail,
                &mut |context, state| {
                    context
                        .saturate_after_inhale()
                        .map_err(ExecutionError::Context)?;
                    let state = context
                        .finish_key_heap(state)
                        .map_err(ExecutionError::Context)?;
                    finish(context, state)
                },
            )
        }
        StmtKind::Exhale(assertion) => {
            let state = context
                .start_key_heap(state, statement, debug_snapshot.as_ref())
                .map_err(ExecutionError::Context)?;
            let tail = owned_tail.filter(|_| context.statement_scope_transferable(scope));
            context.consume_with_owned_tail(
                state,
                statement,
                assertion,
                crate::rules::consumer::OwnedConsumptionCompletion::Exhale,
                tail,
                &mut |context, state| {
                    let state = context
                        .finish_key_heap(state)
                        .map_err(ExecutionError::Context)?;
                    finish(context, state)
                },
            )
        }
        StmtKind::Extension(extension)
            if extension
                .0
                .as_any()
                .is::<crate::extensions::try_block_stmt::TryBlock>() =>
        {
            let body = &extension
                .0
                .as_any()
                .downcast_ref::<crate::extensions::try_block_stmt::TryBlock>()
                .expect("checked extension type")
                .body;
            let original = state.clone();
            if let Some(tail) = owned_tail
                .filter(|_| !state.exhale_ext && context.statement_scope_transferable(scope))
            {
                let success = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
                let marker = success.clone();
                if let Some(result) = context.execute_owned_try_body(
                    state.clone(),
                    body,
                    tail,
                    marker.clone(),
                    &mut |context, state| {
                        marker.store(true, std::sync::atomic::Ordering::SeqCst);
                        finish(context, state)
                    },
                ) {
                    let result = result?;
                    return if success.load(std::sync::atomic::Ordering::SeqCst) {
                        Ok(result)
                    } else {
                        finish(context, original)
                    };
                }
            }
            let mut body_succeeded = false;
            let body_result = execute(context, state, body, &mut |context, state| {
                body_succeeded = true;
                finish(context, state)
            })?;
            if body_succeeded {
                Ok(body_result)
            } else {
                finish(context, original)
            }
        }
        _ => context.execute_special(state, statement, &mut finish),
    }
}
/// Owned position in a source statement sequence. Each continuation invocation
/// resumes from the same next index, even when a prior statement branches.
#[derive(Clone)]
pub struct StatementSequenceFrame {
    statements: Arc<[Stmt]>,
    next: usize,
}
impl StatementSequenceFrame {
    fn new(statements: &[Stmt]) -> Self {
        Self {
            statements: Arc::from(statements),
            next: 0,
        }
    }
}

pub fn execute_all<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    statements: &[Stmt],
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: ExecutionContext<P, D, J, V>,
{
    execute_statement_frame(
        context,
        state,
        StatementSequenceFrame::new(statements),
        continuation,
    )
}

fn execute_statement_frame<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    frame: StatementSequenceFrame,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: ExecutionContext<P, D, J, V>,
{
    if let Some(statement) = frame.statements.get(frame.next) {
        let next = StatementSequenceFrame {
            statements: frame.statements.clone(),
            next: frame.next + 1,
        };
        execute(context, state, statement, &mut |context, state| {
            execute_statement_frame(context, state, next.clone(), continuation)
        })
    } else {
        continuation(context, state)
    }
}

/// SSA variables replace every non-variable, non-literal RHS; the definition is assumed.
fn ssaify<C, P, D, J, V>(
    context: &mut C,
    name: &str,
    typ: &ferrum_silver::ast::r#type::Type,
    rhs: &Exp,
    value: StoreValue,
) -> Result<StoreValue, ExecutionError<C::Error>>
where
    C: ExecutionContext<P, D, J, V>,
{
    use crate::state::terms::TermKind;
    if matches!(
        value.0.kind(),
        TermKind::Var(_)
            | TermKind::Unit
            | TermKind::IntLiteral(_)
            | TermKind::Null
            | TermKind::ZeroMask
            | TermKind::PredZeroMask
            | TermKind::True
            | TermKind::False
            | TermKind::SeqNil(_)
            | TermKind::EmptySet(_)
            | TermKind::EmptyMultiset(_)
            | TermKind::EmptyMap(..)
    ) {
        return Ok(value);
    }
    let (variable, debug_var) = context
        .fresh_ssa(name, typ, rhs)
        .map_err(ExecutionError::Context)?;
    if context.debugging() && (debug_var.is_none() || value.1.is_none()) {
        return Err(ExecutionError::MissingDebugExpression);
    }
    let equation = context.factory().builtin_equals(variable.clone(), value.0);
    context
        .assume_ssa_definition(
            &equation,
            name,
            typ,
            rhs,
            value.1.as_ref(),
            debug_var.as_ref(),
        )
        .map_err(ExecutionError::Context)?;
    Ok((variable, debug_var))
}

fn produce_new_fields<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    fields: &[ferrum_silver::ast::program::Field],
    original: &LocalVar,
    receiver: &TermValue,
    rewritten: Option<&Exp>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: ExecutionContext<P, D, J, V>,
{
    let Some((field, rest)) = fields.split_first() else {
        return continuation(context, state);
    };
    let snapshot = context
        .fresh_field_snapshot(field, original)
        .map_err(ExecutionError::Context)?;
    context.produce_new_field(
        state,
        field,
        receiver,
        original,
        rewritten,
        snapshot,
        &mut |context, state| {
            produce_new_fields(
                context,
                state,
                rest,
                original,
                receiver,
                rewritten,
                continuation,
            )
        },
    )
}

static NEXT_PATH_ID: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(0);
fn next_path_id() -> i32 {
    NEXT_PATH_ID
        .fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        .wrapping_add(1)
}
type SilverBlock = ferrum_silver::cfg::silver::silver_cfg::SilverBlock;
type SilverEdge = ferrum_silver::cfg::silver::silver_cfg::SilverEdge;
/// Executable continuation reached when a transferred CFG path exits.
#[derive(Clone)]
pub enum CfgContinuationTerminal {
    Method(crate::supporters::method_supporter::MethodCfgContinuation),
    Standalone,
}

/// Owned branch action. The optional path ID is allocated only when the action runs.
#[derive(Clone)]
pub struct CfgContinuationAction {
    pub edge: ferrum_silver::cfg::silver::silver_cfg::SilverEdge,
    pub outer_join: Option<ferrum_silver::cfg::silver::silver_cfg::SilverBlock>,
    pub path_id: Option<i32>,
    pub terminal: CfgContinuationTerminal,
}

#[derive(Clone, Copy)]
pub enum LoopDebugHeapStart {
    InhaleInvariant,
    ExhaleInvariant,
    StateMerge,
}

/// CFG-specific verifier services. Loop checking and branch/join use the same
/// source continuations as the statement executor and must propagate failures.
pub trait CfgContext<P, D, J, V>: ExecutionContext<P, D, J, V> {
    fn resume_owned_cfg_terminal(
        &mut self,
        _state: State<P, D, J>,
        _terminal: &CfgContinuationTerminal,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>> {
        Err(ExecutionError::OwnedCfgSchedulerUnavailable)
    }
    fn block_reached(
        &mut self,
        state: State<P, D, J>,
        block: &SilverBlock,
        path_id: i32,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn block_finished(
        &mut self,
        block: &SilverBlock,
        path_id: i32,
        result: &VerificationResult<V>,
    ) -> Result<(), Self::Error>;
    fn outgoing_edges(
        &mut self,
        state: &State<P, D, J>,
        block: &SilverBlock,
    ) -> Result<Vec<SilverEdge>, Self::Error>;
    fn merge_invariant_context(
        &mut self,
        state: State<P, D, J>,
        saved: Arc<ListBackedHeap>,
    ) -> Result<State<P, D, J>, Self::Error>;
    fn evaluate_edge(
        &mut self,
        state: State<P, D, J>,
        condition: &Exp,
        is_loop_guard: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
            TermValue,
            Option<Exp>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn branch_edge(
        &mut self,
        state: State<P, D, J>,
        term: TermValue,
        condition: &Exp,
        rewritten: Option<&Exp>,
        yes: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
        no: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn all_cfg_joins(&self, state: &State<P, D, J>) -> bool;
    fn parallelize_cfg_branches(&self) -> bool;
    /// True only while an owner-local scheduler can accept complete owned CFG tails.
    fn supports_owned_cfg_branch(&self) -> bool {
        false
    }
    /// A continuation may bypass a conditional close only when it is a proven no-op.
    fn owned_cfg_conditional_close_is_noop(&self, _id: Option<i32>) -> bool {
        false
    }

    fn try_branch_owned_cfg(
        &mut self,
        _state: &State<P, D, J>,
        _condition: &TermValue,
        _original: &Exp,
        _rewritten: Option<&Exp>,
        _yes: CfgContinuationAction,
        _no: CfgContinuationAction,
    ) -> Option<Result<VerificationResult<V>, ExecutionError<Self::Error>>> {
        None
    }

    fn join_cfg_branches(
        &mut self,
        state: State<P, D, J>,
        condition: TermValue,
        original: &Exp,
        rewritten: Option<&Exp>,
        yes: CfgJoinBranch,
        no: CfgJoinBranch,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn begin_edges(&mut self, count: usize) -> Result<(), Self::Error>;
    fn next_edge(&mut self, index: usize) -> Result<(), Self::Error>;
    fn mark_edge_reachable(&mut self) -> Result<(), Self::Error>;
    fn end_edges(&mut self) -> Result<(), Self::Error>;
    fn begin_edges_scope(&mut self, count: usize) -> Result<Option<i32>, Self::Error> {
        self.begin_edges(count)?;
        Ok(None)
    }
    fn next_edge_scope(&mut self, _id: Option<i32>, index: usize) -> Result<(), Self::Error> {
        self.next_edge(index)
    }
    fn mark_edge_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        self.mark_edge_reachable()
    }
    fn end_edges_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        self.end_edges()
    }
    fn open_conditional_edge_scope(
        &mut self,
        _state: &State<P, D, J>,
        _expression: &Exp,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn close_conditional_edge_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn empty_heap(&mut self, state: &State<P, D, J>) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn locally_loop(
        &mut self,
        state: State<P, D, J>,
        block: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn loop_mark(&mut self) -> crate::decider::path_conditions::Mark;
    fn loop_path_after(
        &mut self,
        mark: crate::decider::path_conditions::Mark,
    ) -> Result<crate::decider::path_conditions::RecordedPathConditions, Self::Error>;
    fn loop_fresh_declarations(
        &self,
    ) -> (
        Vec<crate::state::terms::Declaration>,
        Vec<crate::state::terms::Declaration>,
    );
    fn replay_loop_path(
        &mut self,
        paths: &crate::decider::path_conditions::RecordedPathConditions,
        functions: &[crate::state::terms::Declaration],
        macros: &[crate::state::terms::Declaration],
    ) -> Result<(), Self::Error>;
    fn loop_produce_invariants(
        &mut self,
        state: State<P, D, J>,
        invariants: &[Exp],
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    /// preserved=true selects LoopInvariantNotPreserved; false selects NotEstablished.
    fn loop_consume_invariants(
        &mut self,
        state: State<P, D, J>,
        invariants: &[Exp],
        preserved: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            State<P, D, J>,
        )
            -> Result<VerificationResult<V>, ExecutionError<Self::Error>>,
    ) -> Result<VerificationResult<V>, ExecutionError<Self::Error>>;
    fn loop_start_debug_heap(
        &mut self,
        state: State<P, D, J>,
        _start: LoopDebugHeapStart,
    ) -> Result<State<P, D, J>, Self::Error> {
        Ok(state)
    }
    fn loop_finish_debug_heap(
        &mut self,
        state: State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error> {
        Ok(state)
    }
    fn loop_capture_debug_heap(
        &mut self,
        _state: &State<P, D, J>,
    ) -> Result<Option<(String, crate::state::state::HeapRecord)>, Self::Error> {
        Ok(None)
    }
    fn loop_merge_debug_heaps(
        &mut self,
        state: State<P, D, J>,
        _record: Option<&(String, crate::state::state::HeapRecord)>,
    ) -> Result<State<P, D, J>, Self::Error> {
        Ok(state)
    }
    fn loop_saturate(&mut self) -> Result<(), Self::Error>;
    fn loop_smoke(&mut self) -> Result<bool, Self::Error>;
    fn loop_comment(&mut self, text: &str) -> Result<(), Self::Error>;
}
pub fn execute_cfg<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    cfg: &ferrum_silver::cfg::silver::silver_cfg::SilverCfg,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    execute_block(
        context,
        state,
        cfg.graph().entry(),
        ferrum_silver::cfg::edge::Kind::Normal,
        None,
        next_path_id(),
        continuation,
    )
}
/// Run a CFG with an explicitly owned terminal; the closure is verifier-local.
pub(crate) fn execute_cfg_owned<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    cfg: &ferrum_silver::cfg::silver::silver_cfg::SilverCfg,
    terminal: &CfgContinuationTerminal,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    execute_block_inner(
        context,
        state,
        cfg.graph().entry(),
        ferrum_silver::cfg::edge::Kind::Normal,
        None,
        next_path_id(),
        Some(terminal),
        continuation,
    )
}

/// Owned successor context for a statement block. Edges are still obtained
/// after the statements finish, using the resulting symbolic state.
#[derive(Clone)]
pub struct CfgSuccessorFrame {
    block: SilverBlock,
    join_point: Option<SilverBlock>,
    path_id: i32,
}

#[derive(Clone)]
enum OwnedStatementSuccessor {
    Block(CfgSuccessorFrame),
    Loop(LoopHeadSuccessorFrame),
}
impl OwnedStatementSuccessor {
    fn join_point(&self) -> Option<&SilverBlock> {
        match self {
            Self::Block(frame) => frame.join_point.as_ref(),
            Self::Loop(frame) => frame.join_point.as_ref(),
        }
    }
}

#[derive(Clone)]
enum OwnedStatementFrame {
    Sequence(StatementSequenceFrame),
    FinishSequence,
    TrySuccess(std::sync::Arc<std::sync::atomic::AtomicBool>),
}

/// Complete caller tail for a statement inside an owned CFG block.
#[derive(Clone)]
pub struct CfgStatementTail {
    remaining: StatementSequenceFrame,
    enclosing: Vec<OwnedStatementFrame>,
    successor: OwnedStatementSuccessor,
    terminal: CfgContinuationTerminal,
}

fn execute_cfg_successor_frame<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    frame: &CfgSuccessorFrame,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    let edges = context
        .outgoing_edges(&state, &frame.block)
        .map_err(ExecutionError::Context)?;
    follow_edges(
        context,
        state,
        &edges,
        frame.join_point.as_ref(),
        frame.path_id,
        owned,
        continuation,
    )
}

fn execute_cfg_statements<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    sequence: StatementSequenceFrame,
    enclosing: &[OwnedStatementFrame],
    successor: &OwnedStatementSuccessor,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    if let Some(statement) = sequence.statements.get(sequence.next) {
        let next = StatementSequenceFrame {
            statements: sequence.statements.clone(),
            next: sequence.next + 1,
        };
        let tail = owned
            .filter(|_| {
                successor.join_point().is_none()
                    && context.supports_owned_cfg_branch()
                    && state.parallelize_branches
                    && !state.under_join
                    && !state.is_in_package
                    && !state.exhale_ext
            })
            .map(|terminal| CfgStatementTail {
                remaining: next.clone(),
                enclosing: enclosing.to_vec(),
                successor: successor.clone(),
                terminal: terminal.clone(),
            });
        execute_with_owned_tail(
            context,
            state,
            statement,
            tail.as_ref(),
            &mut |context, state| {
                execute_cfg_statements(
                    context,
                    state,
                    next.clone(),
                    enclosing,
                    successor,
                    owned,
                    continuation,
                )
            },
        )
    } else {
        continuation(context, state)
    }
}

fn resume_cfg_statement_frames<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    frames: &[OwnedStatementFrame],
    successor: &OwnedStatementSuccessor,
    terminal: &CfgContinuationTerminal,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    if let Some((first, rest)) = frames.split_first() {
        match first {
            OwnedStatementFrame::Sequence(sequence) => execute_cfg_statements(
                context,
                state,
                sequence.clone(),
                rest,
                successor,
                Some(terminal),
                &mut |context, state| {
                    resume_cfg_statement_frames(context, state, rest, successor, terminal)
                },
            ),
            OwnedStatementFrame::FinishSequence => {
                let state = context
                    .move_to_reserve_heap(state)
                    .map_err(ExecutionError::Context)?;
                context
                    .close_statement_scope(None)
                    .map_err(ExecutionError::Context)?;
                resume_cfg_statement_frames(context, state, rest, successor, terminal)
            }
            OwnedStatementFrame::TrySuccess(success) => {
                success.store(true, std::sync::atomic::Ordering::SeqCst);
                resume_cfg_statement_frames(context, state, rest, successor, terminal)
            }
        }
    } else {
        match successor {
            OwnedStatementSuccessor::Block(frame) => execute_cfg_successor_frame(
                context,
                state,
                frame,
                Some(terminal),
                &mut |context, state| context.resume_owned_cfg_terminal(state, terminal),
            ),
            OwnedStatementSuccessor::Loop(frame) => execute_loop_head_successors(
                context,
                state,
                frame,
                Some(terminal),
                &mut |context, state| context.resume_owned_cfg_terminal(state, terminal),
            ),
        }
    }
}

/// Resume a transferred CFG statement tail with verifier-local callbacks.
pub(crate) fn execute_cfg_statement_tail<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    tail: &CfgStatementTail,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    let mut frames = vec![OwnedStatementFrame::Sequence(tail.remaining.clone())];
    frames.extend_from_slice(&tail.enclosing);
    resume_cfg_statement_frames(context, state, &frames, &tail.successor, &tail.terminal)
}

pub(crate) fn execute_cfg_nested_sequence<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    statements: &[Stmt],
    tail: &CfgStatementTail,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    let mut enclosing = vec![
        OwnedStatementFrame::FinishSequence,
        OwnedStatementFrame::Sequence(tail.remaining.clone()),
    ];
    enclosing.extend_from_slice(&tail.enclosing);
    execute_cfg_statements(
        context,
        state,
        StatementSequenceFrame::new(statements),
        &enclosing,
        &tail.successor,
        Some(&tail.terminal),
        continuation,
    )
}

pub(crate) fn execute_cfg_try_body<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    body: &Stmt,
    tail: &CfgStatementTail,
    success: std::sync::Arc<std::sync::atomic::AtomicBool>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    let mut enclosing = vec![
        OwnedStatementFrame::TrySuccess(success),
        OwnedStatementFrame::FinishSequence,
        OwnedStatementFrame::Sequence(tail.remaining.clone()),
    ];
    enclosing.extend_from_slice(&tail.enclosing);
    let inner = CfgStatementTail {
        remaining: StatementSequenceFrame::new(&[]),
        enclosing,
        successor: tail.successor.clone(),
        terminal: tail.terminal.clone(),
    };
    execute_with_owned_tail(context, state, body, Some(&inner), continuation)
}

pub fn execute_block<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    block: &SilverBlock,
    incoming: ferrum_silver::cfg::edge::Kind,
    join_point: Option<&SilverBlock>,
    path_id: i32,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    execute_block_inner(
        context,
        state,
        block,
        incoming,
        join_point,
        path_id,
        None,
        continuation,
    )
}

fn execute_block_inner<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    block: &SilverBlock,
    incoming: ferrum_silver::cfg::edge::Kind,
    join_point: Option<&SilverBlock>,
    path_id: i32,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    use ferrum_silver::cfg::block::BlockKind;
    let state = context
        .block_reached(state, block, path_id)
        .map_err(ExecutionError::Context)?;
    let result = match block.kind() {
        BlockKind::Statement { statements, .. } => {
            let frame = CfgSuccessorFrame {
                block: block.clone(),
                join_point: join_point.cloned(),
                path_id,
            };
            let successor = OwnedStatementSuccessor::Block(frame.clone());
            execute_cfg_statements(
                context,
                state,
                StatementSequenceFrame::new(statements),
                &[],
                &successor,
                owned,
                &mut |context, state| {
                    execute_cfg_successor_frame(context, state, &frame, owned, continuation)
                },
            )?
        }
        BlockKind::LoopHead {
            invariants,
            statements,
            ..
        } => execute_loop_head(
            context,
            state,
            block,
            incoming,
            invariants,
            statements,
            join_point,
            path_id,
            owned,
            continuation,
        )?,
        BlockKind::Precondition(_) | BlockKind::Postcondition(_) => {
            return Err(ExecutionError::UnexpectedCfgBlock);
        }
    };
    context
        .block_finished(block, path_id, &result)
        .map_err(ExecutionError::Context)?;
    Ok(result)
}
/// Owned continuation after a joined pair of CFG edges.
#[derive(Clone)]
struct CfgPostJoinFrame {
    cfg: Arc<ferrum_silver::cfg::silver::silver_cfg::SilverCfg>,
    join: SilverBlock,
    outer_join: Option<SilverBlock>,
    path_id: i32,
}

fn execute_cfg_post_join<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    frame: &CfgPostJoinFrame,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    if frame
        .outer_join
        .as_ref()
        .is_some_and(|outer| outer == &frame.join)
    {
        return continuation(context, state);
    }
    let incoming = frame
        .cfg
        .graph()
        .in_edges(&frame.join)
        .first()
        .map(|edge| edge.kind())
        .ok_or(ExecutionError::InvalidCfgEdgePair)?;
    execute_block_inner(
        context,
        state,
        &frame.join,
        incoming,
        frame.outer_join.as_ref(),
        frame.path_id,
        owned,
        continuation,
    )
}

/// Owned ordered edges and enclosing join for the sequential edge fold.
struct CfgEdgeSequenceFrame {
    edges: Arc<[SilverEdge]>,
    join_point: Option<SilverBlock>,
    path_id: i32,
}

fn execute_cfg_edge_sequence<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    frame: &CfgEdgeSequenceFrame,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    let branch_scope = context
        .begin_edges_scope(frame.edges.len())
        .map_err(ExecutionError::Context)?;
    let mut result = VerificationResult::success();
    for (index, edge) in frame.edges.iter().enumerate() {
        if index != 0 {
            context
                .next_edge_scope(branch_scope, index)
                .map_err(ExecutionError::Context)?;
        }
        let branch_path_id = if index == 0 {
            frame.path_id
        } else {
            next_path_id()
        };
        context
            .mark_edge_scope(branch_scope)
            .map_err(ExecutionError::Context)?;
        if result.continue_verification() {
            let next = follow_edge(
                context,
                state.clone(),
                edge,
                frame.join_point.as_ref(),
                branch_path_id,
                owned,
                continuation,
            )?;
            result = result.combine(|| next, false);
        }
    }
    context
        .end_edges_scope(branch_scope)
        .map_err(ExecutionError::Context)?;
    Ok(result)
}

fn follow_edges<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    edges: &[SilverEdge],
    join_point: Option<&SilverBlock>,
    path_id: i32,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    if edges.is_empty() {
        return continuation(context, state);
    }
    if edges.len() == 1 {
        return follow_edge(
            context,
            state,
            &edges[0],
            join_point,
            path_id,
            owned,
            continuation,
        );
    }
    use ferrum_silver::cfg::{block::BlockKind, edge::Edge};
    if let [
        Edge::Conditional {
            condition: first,
            source: source1,
            ..
        },
        Edge::Conditional {
            condition: second,
            source: source2,
            ..
        },
    ] = edges
    {
        if context.all_cfg_joins(&state)
            && matches!(source1.kind(), BlockKind::Statement { .. })
            && matches!(source2.kind(), BlockKind::Statement { .. })
        {
            let cfg = state.method_cfg.clone().ok_or(ExecutionError::MissingCfg)?;
            let joins = cfg.join_points().map_err(ExecutionError::Cfg)?;
            if let Some(new_join) = joins.get(source1) {
                if source1 != source2
                    || !matches!((first.kind(),second.kind()), (_,ExpKind::Not(exp)) if first == exp)
                        && !matches!((first.kind(),second.kind()), (ExpKind::Not(exp),_) if exp == second)
                {
                    return Err(ExecutionError::InvalidCfgEdgePair);
                }
                let new_join = new_join.clone();
                let join_for_yes = new_join.clone();
                let join_for_no = new_join.clone();
                let post_join = CfgPostJoinFrame {
                    cfg,
                    join: new_join,
                    outer_join: join_point.cloned(),
                    path_id,
                };
                return context.evaluate_edge(
                    state,
                    first,
                    false,
                    &mut |context, state, term, rewritten| {
                        context.join_cfg_branches(
                            state,
                            term,
                            first,
                            rewritten.as_ref(),
                            CfgJoinBranch {
                                edge: edges[0].clone(),
                                join: join_for_yes.clone(),
                                path_id: Some(path_id),
                            },
                            CfgJoinBranch {
                                edge: edges[1].clone(),
                                join: join_for_no.clone(),
                                path_id: None,
                            },
                            &mut |context, state| {
                                execute_cfg_post_join(
                                    context,
                                    state,
                                    &post_join,
                                    owned,
                                    continuation,
                                )
                            },
                        )
                    },
                );
            }
        }
        let owned_profile =
            owned.is_some() && join_point.is_none() && context.supports_owned_cfg_branch();
        if (owned_profile || context.parallelize_cfg_branches())
            && matches!(second.kind(),ExpKind::Not(exp) if exp == first)
        {
            // Source opens this record without a matching close in the complementary-edge path.
            let _scope = context
                .open_conditional_edge_scope(&state, first)
                .map_err(ExecutionError::Context)?;
            return context.evaluate_edge(
                state,
                first,
                matches!(source1.kind(), BlockKind::LoopHead { .. }),
                &mut |context, state, term, rewritten| {
                    if owned_profile
                        && state.parallelize_branches
                        && !state.under_join
                        && !state.is_in_package
                        && !state.exhale_ext
                    {
                        let terminal = owned.expect("owned profile has terminal").clone();
                        let yes = CfgContinuationAction {
                            edge: edges[0].clone(),
                            outer_join: None,
                            path_id: Some(path_id),
                            terminal: terminal.clone(),
                        };
                        let no = CfgContinuationAction {
                            edge: edges[1].clone(),
                            outer_join: None,
                            path_id: None,
                            terminal,
                        };
                        return context
                            .try_branch_owned_cfg(&state, &term, first, rewritten.as_ref(), yes, no)
                            .ok_or(ExecutionError::OwnedCfgSchedulerUnavailable)?;
                    }
                    let continuation = std::cell::RefCell::new(&mut *continuation);
                    context.branch_edge(
                        state,
                        term,
                        first,
                        rewritten.as_ref(),
                        &mut |context, state| {
                            follow_edge(
                                context,
                                state,
                                &edges[0],
                                join_point,
                                path_id,
                                owned,
                                &mut |context, state| {
                                    (continuation
                                        .try_borrow_mut()
                                        .map_err(|_| ExecutionError::ReentrantContinuation)?)(
                                        context, state,
                                    )
                                },
                            )
                        },
                        &mut |context, state| {
                            follow_edge(
                                context,
                                state,
                                &edges[1],
                                join_point,
                                next_path_id(),
                                owned,
                                &mut |context, state| {
                                    (continuation
                                        .try_borrow_mut()
                                        .map_err(|_| ExecutionError::ReentrantContinuation)?)(
                                        context, state,
                                    )
                                },
                            )
                        },
                    )
                },
            );
        }
    }
    let frame = CfgEdgeSequenceFrame {
        edges: Arc::from(edges),
        join_point: join_point.cloned(),
        path_id,
    };
    execute_cfg_edge_sequence(context, state, &frame, owned, continuation)
}
/// Run an owned branch action on its verifier thread; all callbacks remain local.
pub(crate) fn execute_cfg_continuation<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    action: &CfgContinuationAction,
    terminal: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
        &CfgContinuationTerminal,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    follow_edge(
        context,
        state,
        &action.edge,
        action.outer_join.as_ref(),
        action.path_id.unwrap_or_else(next_path_id),
        Some(&action.terminal),
        &mut |context, state| terminal(context, state, &action.terminal),
    )
}

pub(crate) fn execute_cfg_join_branch<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    branch: &CfgJoinBranch,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    follow_edge(
        context,
        state,
        &branch.edge,
        Some(&branch.join),
        branch.path_id.unwrap_or_else(next_path_id),
        None,
        continuation,
    )
}

/// Owned destination and enclosing join for an edge continuation.
#[derive(Clone)]
struct CfgEdgeTargetFrame {
    target: SilverBlock,
    incoming: ferrum_silver::cfg::edge::Kind,
    join_point: Option<SilverBlock>,
    path_id: i32,
}

fn execute_cfg_edge_target<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    frame: &CfgEdgeTargetFrame,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    execute_block_inner(
        context,
        state,
        &frame.target,
        frame.incoming,
        frame.join_point.as_ref(),
        frame.path_id,
        owned,
        continuation,
    )
}

fn follow_edge<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    edge: &SilverEdge,
    join_point: Option<&SilverBlock>,
    path_id: i32,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    use ferrum_silver::cfg::edge::{Edge, Kind};
    let conditional_scope = if !join_point.is_some_and(|point| point == edge.target()) {
        match edge {
            Edge::Conditional { condition, .. } => context
                .open_conditional_edge_scope(&state, condition)
                .map_err(ExecutionError::Context)?,
            _ => None,
        }
    } else {
        None
    };
    if edge.kind() == Kind::Out {
        state = context
            .loop_start_debug_heap(state, LoopDebugHeapStart::StateMerge)
            .map_err(ExecutionError::Context)?;
        let saved = state
            .invariant_contexts
            .first()
            .cloned()
            .ok_or(ExecutionError::MissingInvariantContext)?;
        state = context
            .merge_invariant_context(state, saved)
            .map_err(ExecutionError::Context)?;
        state.invariant_contexts.remove(0);
        state = context
            .loop_finish_debug_heap(state)
            .map_err(ExecutionError::Context)?;
    }
    if join_point.is_some_and(|point| point == edge.target()) {
        return continuation(context, state);
    }
    let frame = CfgEdgeTargetFrame {
        target: edge.target().clone(),
        incoming: edge.kind(),
        join_point: join_point.cloned(),
        path_id,
    };
    match edge {
        Edge::Unconditional { .. } => {
            execute_cfg_edge_target(context, state, &frame, owned, continuation)
        }
        Edge::Conditional {
            condition, source, ..
        } => context.evaluate_edge(
            state,
            condition,
            matches!(
                source.kind(),
                ferrum_silver::cfg::block::BlockKind::LoopHead { .. }
            ),
            &mut |context, state, term, rewritten| {
                let parallel = state.parallelize_branches;
                let mut scoped = state;
                scoped.parallelize_branches = false;
                context.branch_edge(
                    scoped,
                    term,
                    condition,
                    rewritten.as_ref(),
                    &mut |context, mut state| {
                        state.parallelize_branches = parallel;
                        let target_owned =
                            if context.owned_cfg_conditional_close_is_noop(conditional_scope) {
                                owned
                            } else {
                                None
                            };
                        execute_cfg_edge_target(
                            context,
                            state,
                            &frame,
                            target_owned,
                            &mut |context, state| {
                                context
                                    .close_conditional_edge_scope(conditional_scope)
                                    .map_err(ExecutionError::Context)?;
                                continuation(context, state)
                            },
                        )
                    },
                    &mut |context, _| {
                        context
                            .close_conditional_edge_scope(conditional_scope)
                            .map_err(ExecutionError::Context)?;
                        Ok(VerificationResult::success())
                    },
                )
            },
        ),
    }
}

/// Continuation after loop-head statements: check conditions, then follow edges.
#[derive(Clone)]
struct LoopHeadSuccessorFrame {
    conditions: Arc<[Exp]>,
    edges: Arc<[SilverEdge]>,
    join_point: Option<SilverBlock>,
    path_id: i32,
}

fn execute_loop_head_successors<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    frame: &LoopHeadSuccessorFrame,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    context
        .loop_comment("Loop head block: Check well-definedness of edge conditions")
        .map_err(ExecutionError::Context)?;
    let mut checked = VerificationResult::success();
    for condition in frame.conditions.iter() {
        if !checked.continue_verification() {
            break;
        }
        let result = context.locally_loop(state.clone(), &mut |context, state| {
            context.evaluate_edge(state, condition, true, &mut |_, _, _, _| {
                Ok(VerificationResult::success())
            })
        })?;
        checked = checked.combine(|| result, false);
    }
    context
        .loop_comment("Loop head block: Follow loop-internal edges")
        .map_err(ExecutionError::Context)?;
    if !checked.continue_verification() {
        return Ok(checked);
    }
    let followed = follow_edges(
        context,
        state,
        &frame.edges,
        frame.join_point.as_ref(),
        frame.path_id,
        owned,
        continuation,
    )?;
    Ok(checked.combine(|| followed, false))
}

struct LoopPhase<P, D, J> {
    state: State<P, D, J>,
    paths: crate::decider::path_conditions::RecordedPathConditions,
    functions: Vec<crate::state::terms::Declaration>,
    macros: Vec<crate::state::terms::Declaration>,
}
struct LoopPhaseExecutionFrame<P, D, J> {
    phases: Vec<LoopPhase<P, D, J>>,
    statements: Arc<[Stmt]>,
    successors: LoopHeadSuccessorFrame,
}

fn execute_loop_phases<C, P, D, J: Clone, V>(
    context: &mut C,
    leftover: State<P, D, J>,
    frame: &LoopPhaseExecutionFrame<P, D, J>,
    debug_record: Option<&(String, crate::state::state::HeapRecord)>,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    let mut accumulated = VerificationResult::success();
    for phase in &frame.phases {
        if !accumulated.continue_verification() {
            break;
        }
        let mut phase_state = phase.state.clone();
        phase_state.invariant_contexts.insert(0, leftover.h.clone());
        phase_state = context
            .loop_merge_debug_heaps(phase_state, debug_record)
            .map_err(ExecutionError::Context)?;
        let result = context.locally_loop(phase_state, &mut |context, state| {
            context
                .replay_loop_path(&phase.paths, &phase.functions, &phase.macros)
                .map_err(ExecutionError::Context)?;
            context.loop_saturate().map_err(ExecutionError::Context)?;
            if context.loop_smoke().map_err(ExecutionError::Context)? {
                return Ok(VerificationResult::success());
            }
            let successor = OwnedStatementSuccessor::Loop(frame.successors.clone());
            execute_cfg_statements(
                context,
                state,
                StatementSequenceFrame::new(&frame.statements),
                &[],
                &successor,
                owned,
                &mut |context, state| {
                    execute_loop_head_successors(
                        context,
                        state,
                        &frame.successors,
                        owned,
                        continuation,
                    )
                },
            )
        })?;
        accumulated = accumulated.combine(|| result, false);
    }
    Ok(accumulated)
}

/// Execute the source two-phase loop rule: invariant framing in an empty heap,
/// establishment in the incoming state, then replay each framed phase before following edges.
fn execute_loop_head<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    block: &SilverBlock,
    incoming: ferrum_silver::cfg::edge::Kind,
    invariants: &[Exp],
    statements: &[Stmt],
    join_point: Option<&SilverBlock>,
    path_id: i32,
    owned: Option<&CfgContinuationTerminal>,
    continuation: &mut dyn FnMut(
        &mut C,
        State<P, D, J>,
    ) -> Result<VerificationResult<V>, ExecutionError<C::Error>>,
) -> Result<VerificationResult<V>, ExecutionError<C::Error>>
where
    C: CfgContext<P, D, J, V>,
{
    use ferrum_silver::cfg::edge::{Edge, Kind};
    if incoming != Kind::In {
        context
            .loop_comment("Loop head block: Re-establish invariant")
            .map_err(ExecutionError::Context)?;
        return context.loop_consume_invariants(state, invariants, true, &mut |_, _| {
            Ok(VerificationResult::success())
        });
    }
    let cfg = state.method_cfg.clone().ok_or(ExecutionError::MissingCfg)?;
    let written = cfg.written_vars(block).map_err(ExecutionError::Cfg)?;
    let mut body_state = state.clone();
    for variable in written {
        let value = context
            .fresh_local(&variable)
            .map_err(ExecutionError::Context)?;
        let key = AbstractLocalVar::new(Exp::new(
            ExpKind::LocalVar(variable.clone()),
            variable.meta.clone(),
        ));
        body_state.g = Arc::new(body_state.g.with_binding(key, value));
    }
    body_state.h = context
        .empty_heap(&state)
        .map_err(ExecutionError::Context)?;
    let edges: Vec<_> = cfg.graph().out_edges(block).into_iter().cloned().collect();
    let mut sorted: Vec<_> = edges
        .iter()
        .filter(|e| e.kind() != Kind::Out)
        .cloned()
        .collect();
    sorted.extend(edges.into_iter().filter(|e| e.kind() == Kind::Out));
    let mut conditions = Vec::<Exp>::new();
    for edge in &sorted {
        if let Edge::Conditional { condition, .. } = edge {
            if !conditions.contains(condition) {
                conditions.push(condition.clone());
            }
        }
    }
    let successors = LoopHeadSuccessorFrame {
        conditions: Arc::from(conditions),
        edges: Arc::from(sorted),
        join_point: join_point.cloned(),
        path_id,
    };
    let mut phases = Vec::<LoopPhase<P, D, J>>::new();
    let first = context.locally_loop(body_state, &mut |context, state| {
        context
            .loop_comment("Loop head block: Check well-definedness of invariant")
            .map_err(ExecutionError::Context)?;
        let mark = context.loop_mark();
        let state = context
            .loop_start_debug_heap(state, LoopDebugHeapStart::InhaleInvariant)
            .map_err(ExecutionError::Context)?;
        context.loop_produce_invariants(state, invariants, &mut |context, state| {
            let state = context
                .loop_finish_debug_heap(state)
                .map_err(ExecutionError::Context)?;
            let paths = context
                .loop_path_after(mark)
                .map_err(ExecutionError::Context)?;
            let (functions, macros) = context.loop_fresh_declarations();
            phases.push(LoopPhase {
                state,
                paths,
                functions,
                macros,
            });
            Ok(VerificationResult::success())
        })
    })?;
    if !first.continue_verification() {
        return Ok(first);
    }
    let frame = LoopPhaseExecutionFrame {
        phases,
        statements: Arc::from(statements),
        successors,
    };
    let second = context.locally_loop(state, &mut |context, state| {
        context
            .loop_comment("Loop head block: Establish invariant")
            .map_err(ExecutionError::Context)?;
        let state = context
            .loop_start_debug_heap(state, LoopDebugHeapStart::ExhaleInvariant)
            .map_err(ExecutionError::Context)?;
        context.loop_consume_invariants(state, invariants, false, &mut |context, leftover| {
            let leftover = context
                .loop_finish_debug_heap(leftover)
                .map_err(ExecutionError::Context)?;
            let debug_record = context
                .loop_capture_debug_heap(&leftover)
                .map_err(ExecutionError::Context)?;
            context
                .loop_comment(
                    "Loop head block: Execute statements of loop head block (in invariant state)",
                )
                .map_err(ExecutionError::Context)?;
            execute_loop_phases(
                context,
                leftover,
                &frame,
                debug_record.as_ref(),
                owned,
                continuation,
            )
        })
    })?;
    Ok(first.combine(|| second, false))
}

#[cfg(test)]
mod cfg_join_action_tests {
    #[test]
    fn cfg_join_action_is_send() {
        fn require_send<T: Send>() {}
        require_send::<super::CfgJoinBranch>();
    }
}
