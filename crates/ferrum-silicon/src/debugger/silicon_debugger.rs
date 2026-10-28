//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/SiliconDebugger.scala
//!
//! Purpose:
//! Inspect and replay a failed proof obligation interactively.
//!
//! Planned Rust structure:
//! Port ProofObligation and SiliconDebugger: failure selection, state/heap/branch/assumption
//! rendering, typechecker initialization, worker/prover replay, command loop and
//! solver/timeout/assumption helpers.
//!
//! Behavior to preserve:
//! Require debugging and available failure context; replay declarations, preamble and assumption
//! terms into fresh worker. Preserve commands for zoom, reset, remove/add free or proven
//! assumptions, prove, configure, change solver and timeout; typecheck input as Bool in captured
//! scope, evaluate before optional proof and assumption. Retain source versus internal display and
//! basic/quantified field/predicate/wand heap formatting.
//!
//! Integration:
//! debugger::{debug_exp,debug_parser,debug_typechecker}, decider prover/path conditions,
//! rules::evaluator, verifier worker and failure contexts.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for solver/process lifecycle, state isolation and diagnostics;
//! interactive IO remains an explicit native interface.
//!
//! Open decisions:
//! Reconcile replay worker cleanup, solver selection and debug metadata availability with verifier
//! and decider.
//!
//! Status: partial; proof-obligation state, command parsing, solver replay and assumption
//! operations exist. Interactive IO, detailed printing, failure-context extraction, parser scope
//! and concrete worker/evaluator services remain. Native services propagate typed errors.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright notice: the pinned upstream file does not carry an individual notice.

use super::debug_exp::{DebugAxiom, DebugExp, DebugExpPrintConfiguration};
use crate::{
    common::collections::immutable::insertion_ordered_set::InsertionOrderedSet,
    state::terms::{Term, TermFactory, UnsupportedTriggerTransform},
};
use ferrum_silver::ast::expression::Exp;
use std::{
    collections::HashSet,
    sync::{Arc, Mutex},
};

/// S, V and E retain the backend state, verifier handle and original error reason.
/// Print settings are shared across copies as in the source's mutable config object.
#[derive(Clone)]
pub struct ProofObligation<S, V, E> {
    pub state: S,
    pub verifier: V,
    pub prover_emits: Vec<String>,
    pub preamble_assumptions: Vec<DebugAxiom>,
    pub branch_conditions: Vec<Term>,
    pub branch_condition_exps: Vec<(Exp, Exp)>,
    pub assumptions: InsertionOrderedSet<DebugExp>,
    pub assertion: Term,
    pub assertion_exp: DebugExp,
    pub timeout: Option<i32>,
    pub print_config: Arc<Mutex<DebugExpPrintConfiguration>>,
    pub original_error_reason: E,
}
impl<S: Clone, V: Clone, E: Clone> ProofObligation<S, V, E> {
    pub fn remove_assumptions(&self, ids: &[i32]) -> Self {
        let mut result = self.clone();
        result.assumptions = self
            .assumptions
            .iter()
            .filter(|a| !ids.contains(&a.id()))
            .map(|a| a.remove_children_by_id(ids))
            .collect();
        result
    }
    pub fn find_assumption(&self, id: i32) -> Option<DebugExp> {
        self.assumptions
            .iter()
            .find_map(|a| a.find_by_id(id, &mut HashSet::new()))
    }
    /// Java parseUnsignedInt permits values through u32::MAX, returning the same
    /// bits as a signed int. Preserve that behavior and reject whitespace/minus.
    pub fn with_timeout_input(&self, input: &str) -> Option<Self> {
        let digits = input.strip_prefix('+').unwrap_or(input);
        if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let value = digits.parse::<u32>().ok()? as i32;
        let mut result = self.clone();
        result.timeout = if value == 0 { None } else { Some(value) };
        Some(result)
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DebugCommand {
    Quit,
    Zoom,
    Reset,
    RemoveAssumptions,
    Assume,
    AssertAssumption,
    Prove,
    Configure,
    Solver,
    Timeout,
    Invalid,
}
pub fn command(input: &str) -> DebugCommand {
    match input.to_lowercase().as_str() {
        "q" | "quit" => DebugCommand::Quit,
        "z" | "zoom" => DebugCommand::Zoom,
        "r" | "reset" => DebugCommand::Reset,
        "ra" | "remove" | "remove assumption" => DebugCommand::RemoveAssumptions,
        "af" | "assume" | "add free assumption" => DebugCommand::Assume,
        "ap" | "assert" | "add and prove assumption" => DebugCommand::AssertAssumption,
        "p" | "prove" => DebugCommand::Prove,
        "c" | "config" => DebugCommand::Configure,
        "s" | "solver" | "choose different SMT solver" => DebugCommand::Solver,
        "t" | "timeout" => DebugCommand::Timeout,
        _ => DebugCommand::Invalid,
    }
}
pub fn assumption_ids(input: &str) -> Vec<i32> {
    input
        .split(',')
        .filter_map(|s| s.trim().parse().ok())
        .collect()
}
pub fn boolean_setting(input: &str) -> Option<bool> {
    match input.to_lowercase().as_str() {
        "true" | "1" | "t" => Some(true),
        "false" | "0" | "f" => Some(false),
        _ => None,
    }
}
#[derive(Debug)]
pub enum DebuggerError<E> {
    Service(E),
    Transform(UnsupportedTriggerTransform),
    InvalidSolver,
}
pub struct EvaluatedAssumption<S, V> {
    pub state: S,
    pub verifier: V,
    pub term: Term,
    pub expression: Exp,
    pub introduced_assumptions: InsertionOrderedSet<DebugExp>,
}
/// Concrete services must use the captured failure scope and Bool type when
/// translating input, and retain the evaluator's before/after path-condition mark.
pub trait DebuggerServices<S, V> {
    type Error;
    fn solver_name(&self, verifier: &V) -> String;
    fn fresh_worker(&mut self, old: &V) -> Result<V, Self::Error>;
    fn start_worker(&mut self, verifier: &mut V) -> Result<(), Self::Error>;
    fn create_prover(
        &mut self,
        verifier: &mut V,
        solver: &str,
        args: Option<&str>,
    ) -> Result<(), Self::Error>;
    fn emit(&mut self, verifier: &mut V, commands: &[String]) -> Result<(), Self::Error>;
    fn assume_axioms(&mut self, verifier: &mut V, axiom: &DebugAxiom) -> Result<(), Self::Error>;
    fn debugger_assume(
        &mut self,
        verifier: &mut V,
        terms: &[Term],
        debug: Option<&DebugExp>,
    ) -> Result<(), Self::Error>;
    fn translate_boolean(&mut self, input: &str) -> Result<Exp, Self::Error>;
    fn evaluate_assumption(
        &mut self,
        state: &S,
        expression: &Exp,
        verifier: &V,
    ) -> Result<Option<EvaluatedAssumption<S, V>>, Self::Error>;
    fn assert_term(
        &mut self,
        verifier: &mut V,
        term: &Term,
        timeout: Option<i32>,
    ) -> Result<bool, Self::Error>;
    fn make_debug_expression(
        &mut self,
        original: &Exp,
        evaluated: &Exp,
    ) -> Result<DebugExp, Self::Error>;
}
#[derive(Default)]
pub struct SiliconDebugger {
    pub counter: i32,
    pub last_solver_options: Option<String>,
}
impl SiliconDebugger {
    /// Recreate solver state by emitting declarations, preamble axioms, then
    /// debugger assumptions in source order. Old verifier lifetime is caller-owned.
    pub fn initialize<S: Clone, V: Clone, E: Clone, C: DebuggerServices<S, V>>(
        &mut self,
        factory: &TermFactory,
        context: &mut C,
        obligation: &ProofObligation<S, V, E>,
        solver: &str,
        args: Option<&str>,
    ) -> Result<ProofObligation<S, V, E>, DebuggerError<C::Error>> {
        let mut verifier = context
            .fresh_worker(&obligation.verifier)
            .map_err(DebuggerError::Service)?;
        self.counter = self.counter.wrapping_add(1);
        context
            .start_worker(&mut verifier)
            .map_err(DebuggerError::Service)?;
        context
            .create_prover(&mut verifier, solver, args)
            .map_err(DebuggerError::Service)?;
        context
            .emit(&mut verifier, &obligation.prover_emits)
            .map_err(DebuggerError::Service)?;
        for axiom in &obligation.preamble_assumptions {
            context
                .assume_axioms(&mut verifier, axiom)
                .map_err(DebuggerError::Service)?;
        }
        for assumption in &obligation.assumptions {
            let terms = assumption
                .all_terms(factory, &mut HashSet::new())
                .map_err(DebuggerError::Transform)?;
            context
                .debugger_assume(&mut verifier, &terms, Some(assumption))
                .map_err(DebuggerError::Service)?;
        }
        let mut result = obligation.clone();
        result.verifier = verifier;
        Ok(result)
    }
    pub fn change_solver<S: Clone, V: Clone, E: Clone, C: DebuggerServices<S, V>>(
        &mut self,
        factory: &TermFactory,
        context: &mut C,
        obligation: &ProofObligation<S, V, E>,
        solver: &str,
        args: String,
    ) -> Result<ProofObligation<S, V, E>, DebuggerError<C::Error>> {
        if !matches!(solver, "Z3" | "cvc5") {
            return Err(DebuggerError::InvalidSolver);
        }
        self.last_solver_options = if args.is_empty() { None } else { Some(args) };
        let options = self.last_solver_options.clone();
        self.initialize(factory, context, obligation, solver, options.as_deref())
    }
    pub fn remove<S: Clone, V: Clone, E: Clone, C: DebuggerServices<S, V>>(
        &mut self,
        factory: &TermFactory,
        context: &mut C,
        obligation: &ProofObligation<S, V, E>,
        ids: &[i32],
    ) -> Result<ProofObligation<S, V, E>, DebuggerError<C::Error>> {
        let solver = context.solver_name(&obligation.verifier);
        let options = self.last_solver_options.clone();
        self.initialize(
            factory,
            context,
            &obligation.remove_assumptions(ids),
            &solver,
            options.as_deref(),
        )
    }
    /// `free` assumptions skip only the prove step. Failed evaluation or assertion
    /// returns the original obligation and does not fabricate a successful result.
    pub fn add_assumption<S: Clone, V: Clone, E: Clone, C: DebuggerServices<S, V>>(
        &mut self,
        context: &mut C,
        obligation: &ProofObligation<S, V, E>,
        input: &str,
        free: bool,
    ) -> Result<Option<ProofObligation<S, V, E>>, DebuggerError<C::Error>> {
        if input.is_empty() || input.eq_ignore_ascii_case("s") || input.eq_ignore_ascii_case("skip")
        {
            return Ok(None);
        }
        let original = context
            .translate_boolean(input)
            .map_err(DebuggerError::Service)?;
        let Some(mut evaluated) = context
            .evaluate_assumption(&obligation.state, &original, &obligation.verifier)
            .map_err(DebuggerError::Service)?
        else {
            return Ok(None);
        };
        if !free
            && !context
                .assert_term(&mut evaluated.verifier, &evaluated.term, None)
                .map_err(DebuggerError::Service)?
        {
            return Ok(None);
        }
        context
            .debugger_assume(
                &mut evaluated.verifier,
                std::slice::from_ref(&evaluated.term),
                None,
            )
            .map_err(DebuggerError::Service)?;
        let debug = context
            .make_debug_expression(&original, &evaluated.expression)
            .map_err(DebuggerError::Service)?
            .with_term(evaluated.term);
        let mut result = obligation.clone();
        result.state = evaluated.state;
        result.assumptions = obligation
            .assumptions
            .iter()
            .chain(evaluated.introduced_assumptions.iter())
            .cloned()
            .chain(std::iter::once(debug))
            .collect();
        // Source retains obl.v even when evaluation returns another verifier handle.
        Ok(Some(result))
    }
    pub fn prove<S, V, E, C: DebuggerServices<S, V>>(
        &mut self,
        context: &mut C,
        obligation: &mut ProofObligation<S, V, E>,
    ) -> Result<bool, DebuggerError<C::Error>> {
        context
            .assert_term(
                &mut obligation.verifier,
                &obligation.assertion,
                obligation.timeout,
            )
            .map_err(DebuggerError::Service)
    }
}
