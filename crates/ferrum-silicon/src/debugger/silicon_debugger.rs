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
pub enum AddAssumptionOutcome<S, V, E> {
    Skipped,
    EvaluationFailed,
    NotProven,
    Added(ProofObligation<S, V, E>),
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
    /// Render the service error for the interactive source-style retry message.
    fn error_message(&self, error: &Self::Error) -> String
    where
        Self::Error: std::fmt::Debug,
    {
        format!("{error:?}")
    }
    /// The evaluator should retain the source verification-result text on failure.
    fn evaluation_failure_message(&self) -> Option<String> {
        None
    }
    fn solver_name(&self, verifier: &V) -> String;
    fn fresh_worker(&mut self, old: &V) -> Result<V, Self::Error>;
    fn start_worker(&mut self, verifier: &mut V) -> Result<(), Self::Error>;
    fn create_prover(
        &mut self,
        verifier: &mut V,
        solver: &str,
        args: Option<&str>,
    ) -> Result<(), Self::Error>;
    /// Rebind a captured state to the freshly created replay worker.
    fn prepare_state(&mut self, state: &S, _verifier: &mut V) -> Result<S, Self::Error>
    where
        S: Clone,
    {
        Ok(state.clone())
    }
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
#[derive(Debug)]
pub enum InitializeError<E> {
    Debugger(DebuggerError<E>),
    Io(std::io::Error),
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
        match self.initialize_inner(factory, context, obligation, solver, args, || Ok(())) {
            Ok(value) => Ok(value),
            Err(InitializeError::Debugger(error)) => Err(error),
            Err(InitializeError::Io(_)) => unreachable!("no-op progress callback"),
        }
    }
    /// Emit the source progress message after the preamble and before assumptions.
    pub fn initialize_with_output<
        S: Clone,
        V: Clone,
        E: Clone,
        C: DebuggerServices<S, V>,
        W: std::io::Write,
    >(
        &mut self,
        factory: &TermFactory,
        context: &mut C,
        obligation: &ProofObligation<S, V, E>,
        solver: &str,
        args: Option<&str>,
        output: &mut W,
    ) -> Result<ProofObligation<S, V, E>, InitializeError<C::Error>> {
        self.initialize_inner(factory, context, obligation, solver, args, || {
            writeln!(output, "Initializing prover...")?;
            output.flush()
        })
    }
    fn initialize_inner<S: Clone, V: Clone, E: Clone, C: DebuggerServices<S, V>>(
        &mut self,
        factory: &TermFactory,
        context: &mut C,
        obligation: &ProofObligation<S, V, E>,
        solver: &str,
        args: Option<&str>,
        progress: impl FnOnce() -> std::io::Result<()>,
    ) -> Result<ProofObligation<S, V, E>, InitializeError<C::Error>> {
        let mut verifier = context
            .fresh_worker(&obligation.verifier)
            .map_err(|error| InitializeError::Debugger(DebuggerError::Service(error)))?;
        self.counter = self.counter.wrapping_add(1);
        context
            .start_worker(&mut verifier)
            .map_err(|error| InitializeError::Debugger(DebuggerError::Service(error)))?;
        context
            .create_prover(&mut verifier, solver, args)
            .map_err(|error| InitializeError::Debugger(DebuggerError::Service(error)))?;
        let state = context
            .prepare_state(&obligation.state, &mut verifier)
            .map_err(|error| InitializeError::Debugger(DebuggerError::Service(error)))?;
        context
            .emit(&mut verifier, &obligation.prover_emits)
            .map_err(|error| InitializeError::Debugger(DebuggerError::Service(error)))?;
        for axiom in &obligation.preamble_assumptions {
            context
                .assume_axioms(&mut verifier, axiom)
                .map_err(|error| InitializeError::Debugger(DebuggerError::Service(error)))?;
        }
        progress().map_err(InitializeError::Io)?;
        for assumption in &obligation.assumptions {
            let terms = assumption
                .all_terms(factory, &mut HashSet::new())
                .map_err(|error| InitializeError::Debugger(DebuggerError::Transform(error)))?;
            context
                .debugger_assume(&mut verifier, &terms, Some(assumption))
                .map_err(|error| InitializeError::Debugger(DebuggerError::Service(error)))?;
        }
        let mut result = obligation.clone();
        result.state = state;
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
        match self.add_assumption_outcome(context, obligation, input, free)? {
            AddAssumptionOutcome::Added(value) => Ok(Some(value)),
            _ => Ok(None),
        }
    }
    pub fn add_assumption_outcome<S: Clone, V: Clone, E: Clone, C: DebuggerServices<S, V>>(
        &mut self,
        context: &mut C,
        obligation: &ProofObligation<S, V, E>,
        input: &str,
        free: bool,
    ) -> Result<AddAssumptionOutcome<S, V, E>, DebuggerError<C::Error>> {
        if input.is_empty() || input.eq_ignore_ascii_case("s") || input.eq_ignore_ascii_case("skip")
        {
            return Ok(AddAssumptionOutcome::Skipped);
        }
        let original = context
            .translate_boolean(input)
            .map_err(DebuggerError::Service)?;
        let Some(mut evaluated) = context
            .evaluate_assumption(&obligation.state, &original, &obligation.verifier)
            .map_err(DebuggerError::Service)?
        else {
            return Ok(AddAssumptionOutcome::EvaluationFailed);
        };
        if !free
            && !context
                .assert_term(&mut evaluated.verifier, &evaluated.term, None)
                .map_err(DebuggerError::Service)?
        {
            return Ok(AddAssumptionOutcome::NotProven);
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
        Ok(AddAssumptionOutcome::Added(result))
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

/// Presentation supplied by the concrete debugger, including the source-compatible
/// rendering of the captured state and heap. Input and output are kept separate so
/// a session can also be driven from a terminal or a scripted client.
pub trait DebuggerPresentation<S, V, E> {
    type Error;
    fn error_message(&self, error: &Self::Error) -> String
    where
        Self::Error: std::fmt::Debug,
    {
        format!("{error:?}")
    }
    fn obligation(&mut self, obligation: &ProofObligation<S, V, E>) -> Result<String, Self::Error>;
    fn expression(
        &mut self,
        expression: &DebugExp,
        config: &DebugExpPrintConfiguration,
    ) -> Result<String, Self::Error>;
}

fn format_configuration(config: &DebugExpPrintConfiguration) -> String {
    let mut entries = config.per_id_levels.iter().collect::<Vec<_>>();
    entries.sort_by_key(|(id, _)| **id);
    let levels = entries
        .iter()
        .map(|(id, level)| format!("{id} -> {level}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        "  isPrintInternalEnabled = {}\n  nChildrenToShow        = {}\n  printHierarchyLevel    = {}\n  hierarchy per id       = HashMap({levels})\n  isPrintAxiomsEnabled   = {}\n  printInternalTermReps  = {}\n  printOldHeaps          = {}\n",
        config.print_internal,
        config.children_to_show,
        config.hierarchy_level,
        config.print_axioms,
        config.print_internal_terms,
        config.print_old_heaps
    )
}

#[derive(Debug)]
pub enum DebugSessionError<S, P> {
    Io(std::io::Error),
    Service(DebuggerError<S>),
    Presentation(P),
}

impl SiliconDebugger {
    /// Run the upstream obligation command protocol over explicit streams. EOF ends
    /// the session cleanly; the caller owns the worker and failure-selection loop.
    pub fn run_obligation<S: Clone, V: Clone, E: Clone, C, P, R, W>(
        &mut self,
        factory: &TermFactory,
        context: &mut C,
        presentation: &mut P,
        original: ProofObligation<S, V, E>,
        input: &mut R,
        output: &mut W,
    ) -> Result<(), DebugSessionError<C::Error, P::Error>>
    where
        C: DebuggerServices<S, V>,
        C::Error: std::fmt::Debug,
        P: DebuggerPresentation<S, V, E>,
        P::Error: std::fmt::Debug,
        R: std::io::BufRead,
        W: std::io::Write,
    {
        fn read<R: std::io::BufRead, W: std::io::Write>(
            input: &mut R,
            output: &mut W,
            prompt: &str,
        ) -> std::io::Result<Option<String>> {
            writeln!(output, "{prompt}")?;
            output.flush()?;
            let mut line = String::new();
            if input.read_line(&mut line)? == 0 {
                return Ok(None);
            }
            if line.ends_with('\n') {
                line.pop();
                if line.ends_with('\r') {
                    line.pop();
                }
            }
            Ok(Some(line))
        }
        macro_rules! read {
            ($prompt:expr) => {
                match read(input, output, $prompt).map_err(DebugSessionError::Io)? {
                    Some(line) => line,
                    None => return Ok(false),
                }
            };
        }
        macro_rules! initialize {
            ($obligation:expr, $solver:expr, $args:expr) => {
                self.initialize_with_output(factory, context, $obligation, $solver, $args, output)
                    .map_err(|error| match error {
                        InitializeError::Debugger(error) => DebugSessionError::Service(error),
                        InitializeError::Io(error) => DebugSessionError::Io(error),
                    })?
            };
        }
        macro_rules! show {
            ($obl:expr) => {
                writeln!(
                    output,
                    "Current obligation:\n{}",
                    presentation
                        .obligation($obl)
                        .map_err(DebugSessionError::Presentation)?
                )
                .map_err(DebugSessionError::Io)?
            };
        }
        let mut obl = original.clone();
        loop {
            let action = (|| -> Result<bool, DebugSessionError<C::Error, P::Error>> {
                let line = read!(
                    "\nEnter 'q' to quit, 'z' to zoom in on (i.e., show all children of) an assumption, 'r' to reset the proof obligation, 'ra' to remove assumptions, 'af' to add free assumptions, 'ap' prove additional assumptions, 'p' to execute proof, 'c' to change print configuration, 's' to change the SMT solver, 't' to change the timeout"
                );
                match command(&line) {
                    DebugCommand::Quit => return Ok(false),
                    DebugCommand::Invalid => {
                        writeln!(output, "Invalid input!").map_err(DebugSessionError::Io)?
                    }
                    DebugCommand::Zoom => {
                        let line = read!("Enter the assumption you want to zoom in on:");
                        match line.trim().parse::<i32>() {
                            Err(_) => {
                                writeln!(output, "Invalid input").map_err(DebugSessionError::Io)?
                            }
                            Ok(id) => match obl.find_assumption(id) {
                                None => writeln!(output, "Assumption not found")
                                    .map_err(DebugSessionError::Io)?,
                                Some(exp) => {
                                    let config = obl
                                        .print_config
                                        .lock()
                                        .unwrap_or_else(|e| e.into_inner())
                                        .clone();
                                    let mut rendered = String::new();
                                    for child in exp
                                        .children()
                                        .iter()
                                        .filter(|c| config.print_internal || !c.is_internal())
                                    {
                                        rendered.push_str(
                                            &presentation
                                                .expression(child, &config)
                                                .map_err(DebugSessionError::Presentation)?,
                                        );
                                    }
                                    if !rendered.is_empty() {
                                        writeln!(output, "{rendered}\n")
                                            .map_err(DebugSessionError::Io)?;
                                    }
                                }
                            },
                        }
                    }
                    DebugCommand::Reset => {
                        self.last_solver_options = None;
                        let solver = context.solver_name(&original.verifier);
                        obl = original.clone();
                        // Upstream starts a replacement worker but discards the returned obligation.
                        let _ = initialize!(&obl, &solver, None);
                        show!(&obl);
                    }
                    DebugCommand::RemoveAssumptions => {
                        let line = read!("Enter the assumptions you want to remove:");
                        let ids = assumption_ids(&line);
                        writeln!(
                            output,
                            "Removing assumptions with IDs {}",
                            ids.iter().map(i32::to_string).collect::<Vec<_>>().join(",")
                        )
                        .map_err(DebugSessionError::Io)?;
                        let solver = context.solver_name(&obl.verifier);
                        let options = self.last_solver_options.clone();
                        obl =
                            initialize!(&obl.remove_assumptions(&ids), &solver, options.as_deref());
                        show!(&obl);
                    }
                    DebugCommand::Assume | DebugCommand::AssertAssumption => {
                        let free = command(&line) == DebugCommand::Assume;
                        let line = read!("Enter the assumption you want to add or s(skip):");
                        match self
                            .add_assumption_outcome(context, &obl, &line, free)
                            .map_err(DebugSessionError::Service)?
                        {
                            AddAssumptionOutcome::Skipped => {}
                            AddAssumptionOutcome::EvaluationFailed => {
                                let suffix = context
                                    .evaluation_failure_message()
                                    .map(|s| format!(": {s}"))
                                    .unwrap_or_default();
                                writeln!(output, "Error while evaluating expression{suffix}")
                                    .map_err(DebugSessionError::Io)?;
                            }
                            AddAssumptionOutcome::NotProven => {
                                writeln!(output, "Fail! Could not prove assumption. Skipping")
                                    .map_err(DebugSessionError::Io)?
                            }
                            AddAssumptionOutcome::Added(next) => {
                                writeln!(output, "Assumption was added successfully!")
                                    .map_err(DebugSessionError::Io)?;
                                obl = next;
                            }
                        }
                        show!(&obl);
                    }
                    DebugCommand::Prove => {
                        let ok = self
                            .prove(context, &mut obl)
                            .map_err(DebugSessionError::Service)?;
                        writeln!(
                            output,
                            "{}",
                            if ok {
                                "PASS: Proving obligation was successful.\n"
                            } else {
                                "FAIL: Proving obligation failed.\n"
                            }
                        )
                        .map_err(DebugSessionError::Io)?;
                    }
                    DebugCommand::Solver => {
                        let solver = read!("Enter SMT solver to use. Options are Z3, cvc5:");
                        if !matches!(solver.as_str(), "Z3" | "cvc5") {
                            writeln!(output, "Invalid prover name.")
                                .map_err(DebugSessionError::Io)?;
                            return Ok(true);
                        }
                        let args = read!(
                            "Enter any additional command line options for the prover, separated by spaces:"
                        );
                        self.last_solver_options = if args.is_empty() { None } else { Some(args) };
                        let options = self.last_solver_options.clone();
                        obl = initialize!(&obl, &solver, options.as_deref());
                    }
                    DebugCommand::Timeout => {
                        let line = read!("Enter new timeout in ms, 0 for no timeout:");
                        if let Some(next) = obl.with_timeout_input(&line) {
                            obl = next;
                        } else {
                            writeln!(output, "Invalid timeout value.")
                                .map_err(DebugSessionError::Io)?;
                        }
                    }
                    DebugCommand::Configure => {
                        let mut config = obl.print_config.lock().unwrap_or_else(|e| e.into_inner());
                        writeln!(
                            output,
                            "Current configuration:\n{}",
                            format_configuration(&config)
                        )
                        .map_err(DebugSessionError::Io)?;
                        if let Some(v) = boolean_setting(&read!(
                            "Enter the new value for isPrintInternalEnabled:"
                        )) {
                            config.print_internal = v;
                        }
                        if let Ok(v) = read!("Enter the new value for nChildrenToShow:").parse() {
                            config.children_to_show = v;
                        }
                        config.set_hierarchy_level(&read!(
                            "Enter the new value for printHierarchyLevel:"
                        ));
                        if let Some(v) =
                            boolean_setting(&read!("Enter the new value for isPrintAxiomsEnabled:"))
                        {
                            config.print_axioms = v;
                        }
                        if let Some(v) = boolean_setting(&read!(
                            "Enter the new value for printInternalTermRepresentation:"
                        )) {
                            config.print_internal_terms = v;
                        }
                        if let Some(v) =
                            boolean_setting(&read!("Enter the new value for printOldHeaps:"))
                        {
                            config.print_old_heaps = v;
                        }
                        drop(config);
                        show!(&obl);
                    }
                }
                Ok(true)
            })();
            match action {
                Ok(true) => {}
                Ok(false) => return Ok(()),
                Err(DebugSessionError::Io(error)) => return Err(DebugSessionError::Io(error)),
                Err(error) => {
                    let message = match &error {
                        DebugSessionError::Service(DebuggerError::Service(error)) => {
                            context.error_message(error)
                        }
                        DebugSessionError::Service(DebuggerError::Transform(error)) => {
                            format!("{error:?}")
                        }
                        DebugSessionError::Service(DebuggerError::InvalidSolver) => {
                            "Invalid prover name".into()
                        }
                        DebugSessionError::Presentation(error) => presentation.error_message(error),
                        DebugSessionError::Io(_) => unreachable!(),
                    };
                    writeln!(output, "Unexpected error: {message}. \nTry again")
                        .map_err(DebugSessionError::Io)?;
                }
            }
        }
    }
}

#[cfg(test)]
mod session_tests {
    use super::*;
    use crate::state::terms::TermOptions;
    use std::io::Cursor;

    #[derive(Default)]
    struct Services {
        assertions: Vec<Option<i32>>,
        workers: usize,
        fail_next_assertion: bool,
        state_preparations: usize,
    }
    impl DebuggerServices<(), usize> for Services {
        type Error = ();
        fn error_message(&self, _: &()) -> String {
            "source-readable failure".into()
        }
        fn solver_name(&self, _: &usize) -> String {
            "Z3".into()
        }
        fn fresh_worker(&mut self, _: &usize) -> Result<usize, ()> {
            self.workers += 1;
            Ok(self.workers)
        }
        fn start_worker(&mut self, _: &mut usize) -> Result<(), ()> {
            Ok(())
        }
        fn create_prover(&mut self, _: &mut usize, _: &str, _: Option<&str>) -> Result<(), ()> {
            Ok(())
        }
        fn prepare_state(&mut self, _: &(), _: &mut usize) -> Result<(), ()> {
            self.state_preparations += 1;
            Ok(())
        }
        fn emit(&mut self, _: &mut usize, _: &[String]) -> Result<(), ()> {
            Ok(())
        }
        fn assume_axioms(&mut self, _: &mut usize, _: &DebugAxiom) -> Result<(), ()> {
            Ok(())
        }
        fn debugger_assume(
            &mut self,
            _: &mut usize,
            _: &[Term],
            _: Option<&DebugExp>,
        ) -> Result<(), ()> {
            Ok(())
        }
        fn evaluation_failure_message(&self) -> Option<String> {
            Some("verification failed".into())
        }
        fn translate_boolean(&mut self, input: &str) -> Result<Exp, ()> {
            use ferrum_silver::ast::expression::ExpKind;
            let kind = match input {
                "good" => ExpKind::TrueLit,
                "denied" => ExpKind::FalseLit,
                "no-eval" => ExpKind::NullLit,
                _ => return Err(()),
            };
            Ok(Exp::new(kind, Default::default()))
        }
        fn evaluate_assumption(
            &mut self,
            _: &(),
            expression: &Exp,
            _: &usize,
        ) -> Result<Option<EvaluatedAssumption<(), usize>>, ()> {
            use ferrum_silver::ast::expression::ExpKind;
            if matches!(expression.kind(), ExpKind::NullLit) {
                return Ok(None);
            }
            self.fail_next_assertion = matches!(expression.kind(), ExpKind::FalseLit);
            let factory = TermFactory::new(TermOptions {
                use_flyweight: false,
                use_old_axiomatization: false,
                mask_heap_mode: false,
            });
            Ok(Some(EvaluatedAssumption {
                state: (),
                verifier: 0,
                term: factory.boolean(true),
                expression: expression.clone(),
                introduced_assumptions: Default::default(),
            }))
        }
        fn assert_term(
            &mut self,
            _: &mut usize,
            _: &Term,
            timeout: Option<i32>,
        ) -> Result<bool, ()> {
            self.assertions.push(timeout);
            Ok(!std::mem::take(&mut self.fail_next_assertion))
        }
        fn make_debug_expression(&mut self, _: &Exp, _: &Exp) -> Result<DebugExp, ()> {
            Ok(DebugExp::group("assumption".into(), Default::default()))
        }
    }
    struct Presentation;
    impl DebuggerPresentation<(), usize, ()> for Presentation {
        type Error = ();
        fn obligation(&mut self, _: &ProofObligation<(), usize, ()>) -> Result<String, ()> {
            Ok("obligation".into())
        }
        fn expression(
            &mut self,
            _: &DebugExp,
            _: &DebugExpPrintConfiguration,
        ) -> Result<String, ()> {
            Ok("expression".into())
        }
    }
    #[test]
    fn scripted_session_changes_timeout_proves_and_resets() {
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let obligation = ProofObligation {
            state: (),
            verifier: 0,
            prover_emits: vec![],
            preamble_assumptions: vec![],
            branch_conditions: vec![],
            branch_condition_exps: vec![],
            assumptions: Default::default(),
            assertion: factory.boolean(false),
            assertion_exp: DebugExp::group("assertion".into(), Default::default()),
            timeout: None,
            print_config: Default::default(),
            original_error_reason: (),
        };
        let mut services = Services::default();
        let mut input = Cursor::new(
            b"af\nbad\naf\nno-eval\nap\ndenied\naf\ngood\nc\n\n\n\n\n\n\nt\n37\np\nr\np\nq\n"
                .as_slice(),
        );
        let mut output = Vec::new();
        SiliconDebugger::default()
            .run_obligation(
                &factory,
                &mut services,
                &mut Presentation,
                obligation,
                &mut input,
                &mut output,
            )
            .unwrap();
        assert_eq!(services.assertions, [None, Some(37), None]);
        assert_eq!(services.workers, 1);
        assert_eq!(services.state_preparations, 1);
        let output = String::from_utf8(output).unwrap();
        assert!(output.contains("Unexpected error: source-readable failure."));
        assert!(output.contains("Try again"));
        assert!(output.contains("Initializing prover..."));
        assert!(output.contains("Error while evaluating expression: verification failed"));
        assert!(output.contains("Fail! Could not prove assumption. Skipping"));
        assert!(output.contains("Assumption was added successfully!"));
        assert!(output.contains("isPrintInternalEnabled = false"));
        assert_eq!(
            output
                .matches("PASS: Proving obligation was successful.")
                .count(),
            2
        );
    }
}
