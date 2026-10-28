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
//! Status: partial; CPS statement sequencing, locals, labels, inhale/exhale dispatch implemented.
//! Loop phases and CFG traversal use verifier services; wand rules remain.

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
    fn record_label(
        &mut self,
        state: State<P, D, J>,
        label: &str,
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
    ) -> Result<State<P, D, J>, Self::Error>;
    fn disable_subsumption(&self) -> bool;
    fn start_key_heap(
        &mut self,
        state: State<P, D, J>,
        statement: &Stmt,
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
    mut state: State<P, D, J>,
    statement: &Stmt,
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
        StmtKind::Seqn { statements, .. } => execute_all(context, state, statements, &mut finish),
        StmtKind::Label(label) => {
            let name = &label.name;
            let heap = context
                .evaluation_heap(&state)
                .map_err(ExecutionError::Context)?;
            state.old_heaps.insert(name.clone(), heap);
            let state = context
                .record_label(state, name)
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
                .start_key_heap(state, statement)
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
                        .record_new_heap(state, statement)
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
            let original_exhale_ext = state.exhale_ext;
            let state = context
                .start_key_heap(state, statement)
                .map_err(ExecutionError::Context)?;
            context.evaluate_call_arguments(state,statement,args,&mut |context,state,terms,debug_args| {
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
                    .start_key_heap(state, statement)
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
                .start_key_heap(state, statement)
                .map_err(ExecutionError::Context)?;
            context.consume(state, statement, assertion, &mut |context, mut state| {
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
            })
        }
        StmtKind::Inhale(assertion) if matches!(assertion.kind(), ExpKind::FalseLit) => {
            Ok(VerificationResult::success())
        }
        StmtKind::Inhale(assertion) => {
            let state = context
                .start_key_heap(state, statement)
                .map_err(ExecutionError::Context)?;
            context.produce(state, statement, assertion, &mut |context, state| {
                context
                    .saturate_after_inhale()
                    .map_err(ExecutionError::Context)?;
                let state = context
                    .finish_key_heap(state)
                    .map_err(ExecutionError::Context)?;
                finish(context, state)
            })
        }
        StmtKind::Exhale(assertion) => {
            let state = context
                .start_key_heap(state, statement)
                .map_err(ExecutionError::Context)?;
            context.consume(state, statement, assertion, &mut |context, state| {
                let state = context
                    .finish_key_heap(state)
                    .map_err(ExecutionError::Context)?;
                finish(context, state)
            })
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
/// CFG-specific verifier services. Loop checking and branch/join use the same
/// source continuations as the statement executor and must propagate failures.
pub trait CfgContext<P, D, J, V>: ExecutionContext<P, D, J, V> {
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
    fn loop_merge_debug_heaps(
        &mut self,
        state: State<P, D, J>,
        leftover: &State<P, D, J>,
    ) -> Result<State<P, D, J>, Self::Error>;
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
/// Owned successor context for a statement block. Edges are still obtained
/// after the statements finish, using the resulting symbolic state.
#[derive(Clone)]
pub struct CfgSuccessorFrame {
    block: SilverBlock,
    join_point: Option<SilverBlock>,
    path_id: i32,
}

fn execute_cfg_successor_frame<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    frame: &CfgSuccessorFrame,
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
        continuation,
    )
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
            execute_all(context, state, statements, &mut |context, state| {
                execute_cfg_successor_frame(context, state, &frame, continuation)
            })?
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
fn follow_edges<C, P, D, J: Clone, V>(
    context: &mut C,
    state: State<P, D, J>,
    edges: &[SilverEdge],
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
    if edges.is_empty() {
        return continuation(context, state);
    }
    if edges.len() == 1 {
        return follow_edge(context, state, &edges[0], join_point, path_id, continuation);
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
                                if join_point.is_some_and(|outer| outer == &new_join) {
                                    return continuation(context, state);
                                }
                                let incoming = cfg
                                    .graph()
                                    .in_edges(&new_join)
                                    .first()
                                    .map(|edge| edge.kind())
                                    .ok_or(ExecutionError::InvalidCfgEdgePair)?;
                                execute_block(
                                    context,
                                    state,
                                    &new_join,
                                    incoming,
                                    join_point,
                                    path_id,
                                    continuation,
                                )
                            },
                        )
                    },
                );
            }
        }
        if context.parallelize_cfg_branches()
            && matches!(second.kind(),ExpKind::Not(exp) if exp == first)
        {
            return context.evaluate_edge(
                state,
                first,
                matches!(source1.kind(), BlockKind::LoopHead { .. }),
                &mut |context, state, term, rewritten| {
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
    context
        .begin_edges(edges.len())
        .map_err(ExecutionError::Context)?;
    let mut result = VerificationResult::success();
    for (index, edge) in edges.iter().enumerate() {
        if index != 0 {
            context.next_edge(index).map_err(ExecutionError::Context)?;
        }
        let branch_path_id = if index == 0 { path_id } else { next_path_id() };
        context
            .mark_edge_reachable()
            .map_err(ExecutionError::Context)?;
        if result.continue_verification() {
            let next = follow_edge(
                context,
                state.clone(),
                edge,
                join_point,
                branch_path_id,
                continuation,
            )?;
            result = result.combine(|| next, false);
        }
    }
    context.end_edges().map_err(ExecutionError::Context)?;
    Ok(result)
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
        continuation,
    )
}

fn follow_edge<C, P, D, J: Clone, V>(
    context: &mut C,
    mut state: State<P, D, J>,
    edge: &SilverEdge,
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
    use ferrum_silver::cfg::edge::{Edge, Kind};
    if edge.kind() == Kind::Out {
        let saved = state
            .invariant_contexts
            .first()
            .cloned()
            .ok_or(ExecutionError::MissingInvariantContext)?;
        state = context
            .merge_invariant_context(state, saved)
            .map_err(ExecutionError::Context)?;
        state.invariant_contexts.remove(0);
    }
    if join_point.is_some_and(|point| point == edge.target()) {
        return continuation(context, state);
    }
    match edge {
        Edge::Unconditional { target, kind, .. } => execute_block(
            context,
            state,
            target,
            *kind,
            join_point,
            path_id,
            continuation,
        ),
        Edge::Conditional {
            condition,
            target,
            kind,
            source,
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
                        execute_block(
                            context,
                            state,
                            target,
                            *kind,
                            join_point,
                            path_id,
                            continuation,
                        )
                    },
                    &mut |_, _| Ok(VerificationResult::success()),
                )
            },
        ),
    }
}

struct LoopPhase<P, D, J> {
    state: State<P, D, J>,
    paths: crate::decider::path_conditions::RecordedPathConditions,
    functions: Vec<crate::state::terms::Declaration>,
    macros: Vec<crate::state::terms::Declaration>,
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
    let mut phases = Vec::<LoopPhase<P, D, J>>::new();
    let first = context.locally_loop(body_state, &mut |context, state| {
        context
            .loop_comment("Loop head block: Check well-definedness of invariant")
            .map_err(ExecutionError::Context)?;
        let mark = context.loop_mark();
        context.loop_produce_invariants(state, invariants, &mut |context, state| {
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
    let second = context.locally_loop(state, &mut |context, state| {
        context
            .loop_comment("Loop head block: Establish invariant")
            .map_err(ExecutionError::Context)?;
        context.loop_consume_invariants(state, invariants, false, &mut |context, leftover| {
            context
                .loop_comment(
                    "Loop head block: Execute statements of loop head block (in invariant state)",
                )
                .map_err(ExecutionError::Context)?;
            let mut accumulated = VerificationResult::success();
            for phase in &phases {
                if !accumulated.continue_verification() {
                    break;
                }
                let mut phase_state = phase.state.clone();
                phase_state.invariant_contexts.insert(0, leftover.h.clone());
                phase_state = context
                    .loop_merge_debug_heaps(phase_state, &leftover)
                    .map_err(ExecutionError::Context)?;
                let result = context.locally_loop(phase_state, &mut |context, state| {
                    context
                        .replay_loop_path(&phase.paths, &phase.functions, &phase.macros)
                        .map_err(ExecutionError::Context)?;
                    context.loop_saturate().map_err(ExecutionError::Context)?;
                    if context.loop_smoke().map_err(ExecutionError::Context)? {
                        return Ok(VerificationResult::success());
                    }
                    execute_all(context, state, statements, &mut |context, state| {
                        context
                            .loop_comment(
                                "Loop head block: Check well-definedness of edge conditions",
                            )
                            .map_err(ExecutionError::Context)?;
                        let mut checked = VerificationResult::success();
                        for condition in &conditions {
                            if !checked.continue_verification() {
                                break;
                            }
                            let result =
                                context.locally_loop(state.clone(), &mut |context, state| {
                                    context.evaluate_edge(
                                        state,
                                        condition,
                                        true,
                                        &mut |_, _, _, _| Ok(VerificationResult::success()),
                                    )
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
                            &sorted,
                            join_point,
                            path_id,
                            continuation,
                        )?;
                        Ok(checked.combine(|| followed, false))
                    })
                })?;
                accumulated = accumulated.combine(|| result, false);
            }
            Ok(accumulated)
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
