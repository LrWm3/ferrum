//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/PredicateVerificationUnit.scala
//!
//! Purpose:
//! Verify predicate bodies and collect trigger symbols and simplified-unfold data.
//!
//! Planned Rust structure:
//! Port PredicateData, PredicateContentsTree branch/leaf variants, PredicateVerificationUnit and
//! provider analyze/verify/makePredTree/preamble/lifecycle.
//!
//! Behavior to preserve:
//! Declare trigger per predicate. Verify body by producing with fresh snapshot and args; abstract
//! predicate succeeds. When simplified unfolds enabled, record branch conditions, heap and
//! assumptions and merge function recorders; create branch tree only on nonfatal result. Declare
//! recorded symbols after verification with macros last to avoid undeclared dependencies.
//!
//! Integration:
//! rules::{producer,execution_flow_controller}, supporters::functions::function_recorder,
//! state::{heap,terms} and decider::decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for branching, ordered assumptions, snapshots and symbol
//! declaration ordering.
//!
//! Open decisions:
//! Agree on branch tree identity, recorder ownership and failure/empty-branch behavior with
//! predicate rules and function recorder.
//!
//! Status: partial; shared predicate data, trigger symbols, contents trees and analysis implemented.
//! Body verification, branch trees and declaration replay implemented; concrete production,
//! path-condition and verifier services remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::state::heap::ListBackedHeap;
use crate::state::identifiers::Identifier;
use crate::state::symbol_converter::{DefaultSymbolConverter, SymbolConversionError};
use crate::state::terms::{Applicable, ApplicableData, ApplicableKind, Sort, Term, TermFactory};
use ferrum_silver::ast::expression::Exp;
use ferrum_silver::ast::program::{Predicate, Program};
use std::sync::{Arc, Mutex};

#[derive(Clone, Debug)]
pub enum PredicateContentsTree {
    Branch {
        condition: Term,
        condition_exp: (Exp, Option<Exp>),
        left: Box<Self>,
        right: Box<Self>,
    },
    Leaf {
        heap: Arc<ListBackedHeap>,
        assumptions: InsertionOrderedSet<Term>,
    },
}
#[derive(Clone, Debug, Default)]
pub struct PredicateContents {
    pub tree: Option<PredicateContentsTree>,
    pub params: Option<Vec<Term>>,
}
/// Data is shared by states; predicate verification installs contents and parameters
/// into the same shared cell, matching the source's mutable PredicateData instance.
#[derive(Debug)]
pub struct PredicateData {
    pub predicate: Predicate,
    pub argument_sorts: Vec<Sort>,
    pub trigger_function: Applicable,
    pub contents: Mutex<PredicateContents>,
    pub fresh_symbols: Mutex<InsertionOrderedSet<crate::state::terms::Declaration>>,
}
impl PredicateData {
    pub fn new(
        predicate: Predicate,
        converter: &DefaultSymbolConverter,
        factory: &TermFactory,
        trigger_sort: Sort,
    ) -> Result<Self, SymbolConversionError> {
        let argument_sorts = predicate
            .formal_args
            .iter()
            .map(|arg| converter.to_sort(&arg.typ))
            .collect::<Result<Vec<_>, _>>()?;
        let mut sorts = vec![trigger_sort];
        sorts.extend(argument_sorts.clone());
        let trigger_function = factory.applicable(ApplicableData {
            kind: ApplicableKind::Fun,
            id: Identifier::Simple(format!("{}%trigger", predicate.name)),
            arg_sorts: sorts,
            result_sort: Sort::Bool,
        });
        Ok(Self {
            predicate,
            argument_sorts,
            trigger_function,
            contents: Mutex::new(PredicateContents::default()),
            fresh_symbols: Mutex::new(InsertionOrderedSet::new()),
        })
    }
}
/// Analyze every predicate in program order; duplicate names follow the source map builder.
pub fn analyze_predicates(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    trigger_sort: Sort,
) -> Result<crate::state::package::OrderedMap<String, Arc<PredicateData>>, SymbolConversionError> {
    let mut result = crate::state::package::OrderedMap::new();
    for predicate in &program.predicates {
        let data = PredicateData::new(predicate.clone(), converter, factory, trigger_sort.clone())?;
        result.insert(predicate.name.clone(), Arc::new(data));
    }
    Ok(result)
}

#[derive(Clone, Debug)]
pub struct PredicateBranchResult {
    pub conditions: Vec<Term>,
    pub condition_exps: Vec<(Exp, Option<Exp>)>,
    pub heap: Arc<ListBackedHeap>,
    pub assumptions: InsertionOrderedSet<Term>,
}
#[derive(Debug)]
pub enum PredicateTreeError {
    EmptyBranches,
    InvalidConditionLengths,
    MultipleUnbranchedLeaves,
}
/// Reconstruct the source decision tree, omitting branch nodes when only one arm survived.
pub fn make_predicate_tree(
    branches: &[PredicateBranchResult],
) -> Result<PredicateContentsTree, PredicateTreeError> {
    let first = branches.first().ok_or(PredicateTreeError::EmptyBranches)?;
    if branches
        .iter()
        .any(|b| b.conditions.len() != b.condition_exps.len())
    {
        return Err(PredicateTreeError::InvalidConditionLengths);
    }
    if first.conditions.is_empty() {
        if branches.len() != 1 {
            return Err(PredicateTreeError::MultipleUnbranchedLeaves);
        }
        return Ok(PredicateContentsTree::Leaf {
            heap: first.heap.clone(),
            assumptions: first.assumptions.clone(),
        });
    }
    let condition = first.conditions[0].clone();
    let condition_exp = first.condition_exps[0].clone();
    let mut yes = Vec::new();
    let mut no = Vec::new();
    for branch in branches {
        if branch.conditions.is_empty() {
            return Err(PredicateTreeError::InvalidConditionLengths);
        }
        let mut tail = branch.clone();
        tail.conditions.remove(0);
        tail.condition_exps.remove(0);
        if branch.conditions[0] == condition {
            yes.push(tail);
        } else {
            no.push(tail);
        }
    }
    if no.is_empty() {
        return make_predicate_tree(&yes);
    }
    if yes.is_empty() {
        return make_predicate_tree(&no);
    }
    Ok(PredicateContentsTree::Branch {
        condition,
        condition_exp,
        left: Box::new(make_predicate_tree(&yes)?),
        right: Box::new(make_predicate_tree(&no)?),
    })
}

pub trait PredicateVerificationServices<P, D, J, V>: Sized {
    type Error;
    fn open_predicate_verification(&mut self, predicate: &Predicate) -> Result<(), Self::Error>;
    fn close_predicate_verification(&mut self) -> Result<(), Self::Error>;
    fn fresh_predicate_snapshot(&mut self) -> Result<Term, Self::Error>;
    fn fresh_predicate_argument(
        &mut self,
        formal: &ferrum_silver::ast::program::LocalVarDecl,
    ) -> Result<(Term, Option<Exp>), Self::Error>;
    fn empty_predicate_heap(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
    ) -> Result<Arc<ListBackedHeap>, Self::Error>;
    fn start_predicate_debug_heap(
        &mut self,
        state: crate::state::state::State<P, D, J>,
    ) -> Result<crate::state::state::State<P, D, J>, Self::Error>;
    fn simplified_unfolds_enabled(&self) -> bool;
    fn predicate_debugging(&self) -> bool;
    /// Locally produce the body. Invoke the callback for every reachable branch with
    /// source-ordered branch conditions and current path assumptions.
    fn produce_predicate_locally(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        body: &Exp,
        snapshot: &Term,
        predicate: &Predicate,
        branch: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
            PredicateBranchResult,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            PredicateVerificationError<Self::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        PredicateVerificationError<Self::Error>,
    >;
    fn store_predicate_recorder(
        &mut self,
        predicate: &Predicate,
        recorder: crate::supporters::functions::function_recorder::FunctionRecorder<D>,
    ) -> Result<(), Self::Error>;
}
#[derive(Debug)]
pub enum PredicateVerificationError<E> {
    Tree(PredicateTreeError),
    Recorder(crate::supporters::functions::function_data::RecorderHandlerError),
    Service(E),
}
/// Verify a predicate body in a local scope and retain the branch tree only after
/// nonfatal simplified-unfold verification; abstract predicates succeed upstream.
pub fn verify_predicate<P, D: Clone, J: Clone, V, C: PredicateVerificationServices<P, D, J, V>>(
    factory: &TermFactory,
    context: &mut C,
    initial: crate::state::state::State<P, D, J>,
    data: &PredicateData,
) -> Result<
    Vec<crate::interfaces::verification::VerificationResult<V>>,
    PredicateVerificationError<C::Error>,
> {
    use crate::state::store::{AbstractLocalVar, MapBackedStore};
    use crate::supporters::functions::function_recorder::{FunctionRecorder, RecorderOwner};
    use ferrum_silver::ast::expression::ExpKind;
    context
        .open_predicate_verification(&data.predicate)
        .map_err(PredicateVerificationError::Service)?;
    let snapshot = context
        .fresh_predicate_snapshot()
        .map_err(PredicateVerificationError::Service)?;
    let mut args = Vec::new();
    let mut bindings = Vec::new();
    for formal in &data.predicate.formal_args {
        let (term, exp) = context
            .fresh_predicate_argument(formal)
            .map_err(PredicateVerificationError::Service)?;
        let var = AbstractLocalVar::new(Exp::new(
            ExpKind::LocalVar(formal.local_var()),
            formal.meta.clone(),
        ));
        args.push(term.clone());
        bindings.push((var, (term, exp)));
    }
    let mut params = vec![snapshot.clone()];
    params.extend(args);
    let simplified = context.simplified_unfolds_enabled();
    let mut recorder = if simplified {
        FunctionRecorder::actual(RecorderOwner::Predicate {
            predicate: Arc::new(data.predicate.clone()),
            arguments: params.clone(),
        })
    } else {
        FunctionRecorder::Noop
    };
    let mut state = initial;
    state.g = Arc::new(MapBackedStore::from_bindings(bindings));
    state.h = context
        .empty_predicate_heap(&state)
        .map_err(PredicateVerificationError::Service)?;
    state.old_heaps = Default::default();
    state.function_recorder = recorder.clone();
    if context.predicate_debugging() {
        state = context
            .start_predicate_debug_heap(state)
            .map_err(PredicateVerificationError::Service)?;
    }
    let mut branches = Vec::new();
    let result = if let Some(body) = &data.predicate.body {
        context.produce_predicate_locally(
            state,
            body,
            &snapshot,
            &data.predicate,
            &mut |_, state, branch| {
                branches.push(branch);
                recorder = recorder.merge(&state.function_recorder);
                Ok(crate::interfaces::verification::VerificationResult::success())
            },
        )?
    } else {
        crate::interfaces::verification::VerificationResult::success()
    };
    let tree = if data.predicate.body.is_some() && !result.is_fatal() && simplified {
        Some(make_predicate_tree(&branches).map_err(PredicateVerificationError::Tree)?)
    } else {
        None
    };
    {
        let mut contents = data.contents.lock().expect("predicate contents poisoned");
        contents.tree = tree;
        contents.params = Some(params);
    }
    let mut handler =
        crate::supporters::functions::function_data::FunctionRecorderHandler::default();
    handler
        .add_recorders(factory, &[recorder.clone()], &[])
        .map_err(PredicateVerificationError::Recorder)?;
    {
        let mut symbols = data
            .fresh_symbols
            .lock()
            .expect("predicate symbols poisoned");
        for decl in handler.fresh_symbols_across_phases.iter() {
            *symbols = symbols.incl(decl.clone());
        }
    }
    context
        .store_predicate_recorder(&data.predicate, recorder)
        .map_err(PredicateVerificationError::Service)?;
    context
        .close_predicate_verification()
        .map_err(PredicateVerificationError::Service)?;
    Ok(vec![result])
}

/// Declare predicate trigger symbols in analyzed program order.
pub fn declare_predicate_triggers<E>(
    factory: &TermFactory,
    sink: &mut impl crate::interfaces::decider::prover::ProverLike<Error = E>,
    predicates: &crate::state::package::OrderedMap<String, Arc<PredicateData>>,
) -> Result<(), E> {
    sink.comment(&mut || "Declaring predicate trigger functions".into())?;
    for (_, data) in predicates.iter() {
        sink.declare(&factory.function_decl(data.trigger_function.clone()))?;
    }
    Ok(())
}
/// Replay collected symbols after verification, with all macros declared last.
pub fn declare_predicate_verification_symbols<E>(
    sink: &mut impl crate::interfaces::decider::prover::ProverLike<Error = E>,
    predicates: &crate::state::package::OrderedMap<String, Arc<PredicateData>>,
) -> Result<(), E> {
    use crate::state::terms::DeclarationKind;
    let mut ordinary = Vec::new();
    let mut macros = Vec::new();
    for (_, data) in predicates.iter() {
        let symbols = data
            .fresh_symbols
            .lock()
            .expect("predicate symbols poisoned");
        for decl in symbols.iter() {
            if matches!(decl.kind(), DeclarationKind::Macro { .. }) {
                macros.push(decl.clone());
            } else {
                ordinary.push(decl.clone());
            }
        }
    }
    sink.comment(&mut || {
        "Declaring symbols related to program functions (from verification)".into()
    })?;
    for decl in ordinary.iter().chain(&macros) {
        sink.declare(decl)?;
    }
    Ok(())
}
