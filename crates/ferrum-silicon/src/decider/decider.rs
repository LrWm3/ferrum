//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/Decider.scala
//!
//! Purpose:
//! Coordinate solver, path conditions, fresh symbols and assertions for a verifier.
//!
//! Planned Rust structure:
//! Decider interface and DefaultDeciderProvider.decider implement prover selection/lifecycle,
//! option save/reset, scope and path stack, assumptions/definitions/debug recording,
//! checks/assertions, fresh variables/functions/macros/ARPs, aliases, model and statistics, and
//! branch worker declaration transfer.
//!
//! Behavior to preserve:
//! Unknown prover name warns and falls back to Z3 stdio; start probes version and warns outside
//! bounds. Push path stack then solver, pop solver then stack; setPcs replays layers into solver
//! scopes for parallel work. Filter already-known facts unless enforced, retain ordered definition
//! versus ordinary assumptions; checkSmoke means unsat, assert stores failing query and calls
//! continuation. Fresh declarations use ordered set except parallel branch mode, macros retain
//! order and deduplicate by name. Alias only eligible HasVarRepr terms in method verification
//! outside quantified and wand packaging contexts. Reset solver/path/declarations/options; model
//! generation asserts False.
//!
//! Integration:
//! interfaces::decider::prover, decider::path_conditions, verifier::base_verifier, state::terms and
//! rules::brancher.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Per-worker solver, mutable term alias, path stack and continuation ownership.
//!
//! Status: partial; per-worker options, scoped assumptions, proof checks and optional
//! symbolic logging are implemented. Runtime logger attachment and source-exact
//! floating-point statistics formatting remain to be connected.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::debugger::debug_exp::DebugExp;
use crate::decider::path_conditions::{LayeredPathConditionStack, Mark, PathError};
use crate::interfaces::decider::prover::{Prover, SatResult};
use crate::package::Map;
use crate::state::terms::{Term, TermFactory, TermKind};

/// Solver errors remain distinct from a failed proof or an invalid path operation.
#[derive(Debug)]
pub enum DeciderError<E> {
    Prover(E),
    Path(PathError),
    MissingDebugExpression,
    InvalidDeclaration,
    InvalidFreshVariable,
    MissingDebugVariableType,
    Logging(crate::logger::records::symbolic_record::RecordError),
}

/// Owner-local attachment for source symbolic events. The caller supplies the
/// Java-compatible double formatter used by logger statistics; there is no
/// implicit Rust-format substitution for source output.
#[derive(Clone)]
pub struct DeciderLogging {
    pub member: std::sync::Arc<crate::logger::symb_ex_logger::MemberSymbExLog>,
    pub factory: TermFactory,
    pub render_double: fn(f64) -> String,
}
impl DeciderLogging {
    fn enabled(&self) -> bool {
        self.member.when_enabled(|| ()).is_some()
    }
    fn open(
        &self,
        record: std::sync::Arc<dyn crate::logger::records::data::data_record::DataRecord>,
    ) -> Result<i32, crate::logger::records::symbolic_record::RecordError> {
        let renderer = crate::logger::state_reporting::NativeStateRecordRenderer {
            factory: &self.factory,
        };
        self.member.open_scope(record, &renderer)
    }
}

/// Per-worker decider. Options and solver ownership are explicit until verifier integration.
pub struct DefaultDecider<P: Prover> {
    pub prover: P,
    logging: Option<DeciderLogging>,
    pub pcs: LayeredPathConditionStack,
    pcs_identity: std::sync::Arc<()>,
    pub debug_mode: bool,
    pub assert_timeout: Option<i32>,
    pub check_timeout: Option<i32>,
    pub push_timeout: Option<i32>,
    /// Last failed assertion; the symbolic execution logger consumes this at integration.
    pub failed_query: Option<Term>,
    options: Map<String, String>,
    reset_options: Map<String, String>,
    pub fresh_functions:
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::state::terms::Declaration,
        >,
    pub fresh_macros: Vec<crate::state::terms::Declaration>,
    pub debug_variable_types:
        crate::package::Map<String, ferrum_silver::parser::parse_ast::PTypeHandle>,
}
impl<P: Prover> DefaultDecider<P> {
    pub fn new(
        prover: P,
        debug_mode: bool,
        assert_timeout: Option<i32>,
        check_timeout: Option<i32>,
        push_timeout: Option<i32>,
    ) -> Self {
        Self {
            prover,
            logging: None,
            pcs: LayeredPathConditionStack::new(debug_mode),
            pcs_identity: std::sync::Arc::new(()),
            debug_mode,
            assert_timeout,
            check_timeout,
            push_timeout,
            failed_query: None,
            options: Map::new(),
            reset_options: Map::new(),
            fresh_functions: Default::default(),
            fresh_macros: Vec::new(),
            debug_variable_types: Default::default(),
        }
    }
    /// Attach the current owner-thread member log, or disable symbolic logging.
    pub fn set_logging(&mut self, logging: Option<DeciderLogging>) {
        self.logging = logging;
    }
    fn assume_without_smoke_checks(
        &mut self,
        terms: &crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            Term,
        >,
        definition: bool,
        log_empty: bool,
    ) -> Result<(), DeciderError<P::Error>> {
        let logging = self
            .logging
            .clone()
            .filter(|log| log.enabled() && (log_empty || !terms.is_empty()));
        let scope = if let Some(log) = &logging {
            Some(
                log.open(std::sync::Arc::new(
                    crate::logger::records::data::decider_assume_record::DeciderAssumeRecord::new(
                        Some(terms.iter().cloned().collect()),
                    ),
                ))
                .map_err(DeciderError::Logging)?,
            )
        } else {
            None
        };
        for term in terms {
            if definition {
                self.pcs.add_definition(term)
            } else {
                self.pcs.add(term)
            }
            .map_err(DeciderError::Path)?;
        }
        for term in terms {
            self.prover.assume(term).map_err(DeciderError::Prover)?;
        }
        if let (Some(log), Some(scope)) = (logging, scope) {
            log.member
                .close_scope(scope)
                .map_err(DeciderError::Logging)?;
        }
        Ok(())
    }
    pub fn start(&mut self, user_args: Option<&str>) -> Result<(), DeciderError<P::Error>> {
        self.pcs = LayeredPathConditionStack::new(self.debug_mode);
        self.pcs_identity = std::sync::Arc::new(());
        self.fresh_functions = Default::default();
        self.fresh_macros.clear();
        self.prover.start(user_args).map_err(DeciderError::Prover)
    }
    pub fn reset(&mut self) -> Result<(), DeciderError<P::Error>> {
        self.prover.reset().map_err(DeciderError::Prover)?;
        self.pcs = LayeredPathConditionStack::new(self.debug_mode);
        self.pcs_identity = std::sync::Arc::new(());
        self.fresh_functions = Default::default();
        self.fresh_macros.clear();
        self.options.clear();
        Ok(())
    }
    pub fn stop(&mut self) -> Result<(), DeciderError<P::Error>> {
        self.prover.stop().map_err(DeciderError::Prover)
    }
    pub fn options(&self) -> &Map<String, String> {
        &self.options
    }
    pub fn set_options(
        &mut self,
        options: Map<String, String>,
    ) -> Result<(), DeciderError<P::Error>> {
        self.options.extend(options);
        for (key, value) in &self.options {
            let previous = self
                .prover
                .set_option(key, value)
                .map_err(DeciderError::Prover)?;
            self.reset_options.entry(key.clone()).or_insert(previous);
        }
        Ok(())
    }
    pub fn reset_options(&mut self) -> Result<(), DeciderError<P::Error>> {
        for (key, value) in &self.reset_options {
            self.prover
                .set_option(key, value)
                .map_err(DeciderError::Prover)?;
        }
        self.reset_options.clear();
        self.options.clear();
        Ok(())
    }
    pub fn push_scope(&mut self) -> Result<(), DeciderError<P::Error>> {
        self.pcs.push_scope();
        self.prover
            .push(1, self.push_timeout)
            .map_err(DeciderError::Prover)
    }
    pub fn pop_scope(&mut self) -> Result<(), DeciderError<P::Error>> {
        self.prover.pop(1).map_err(DeciderError::Prover)?;
        self.pcs.pop_scope().map_err(DeciderError::Path)
    }
    /// Replace this worker's path stack and replay each source layer into solver scopes.
    pub fn set_path_conditions(
        &mut self,
        other: LayeredPathConditionStack,
    ) -> Result<(), DeciderError<P::Error>> {
        self.pcs = other;
        self.pcs_identity = std::sync::Arc::new(());
        while self.prover.push_pop_scope_depth() > 1 {
            self.prover.pop(1).map_err(DeciderError::Prover)?;
        }
        for layer in self.pcs.replay_layers() {
            for assumption in &layer {
                self.prover
                    .assume(assumption)
                    .map_err(DeciderError::Prover)?;
            }
            self.prover
                .push(1, self.push_timeout)
                .map_err(DeciderError::Prover)?;
        }
        Ok(())
    }
    /// Identity changes when the path stack is replaced, not when its scopes mutate.
    pub fn path_condition_identity(&self) -> std::sync::Arc<()> {
        self.pcs_identity.clone()
    }
    pub fn mark(&mut self) -> Mark {
        self.pcs.mark()
    }
    pub fn known_true(&self, term: &Term) -> bool {
        matches!(term.kind(), TermKind::True)
            || self.pcs.contains(term)
            || matches!(term.kind(), TermKind::Quantification { body, .. } if matches!(body.kind(), TermKind::True))
    }
    /// Assumptions are filtered before recording; debug expressions are required in debug mode.
    pub fn assume(
        &mut self,
        assumptions: impl IntoIterator<Item = (Term, Option<DebugExp>)>,
        enforce: bool,
        definition: bool,
    ) -> Result<(), DeciderError<P::Error>> {
        let mut filtered = Vec::new();
        for (term, debug) in assumptions {
            if enforce || !self.known_true(&term) {
                if !filtered
                    .iter()
                    .any(|pair: &(Term, Option<DebugExp>)| pair.0 == term && pair.1 == debug)
                {
                    filtered.push((term, debug));
                }
            }
        }
        if self.debug_mode {
            for (term, debug) in &filtered {
                let debug = debug.as_ref().ok_or(DeciderError::MissingDebugExpression)?;
                self.pcs
                    .add_debug_exp(debug.with_term(term.clone()))
                    .map_err(DeciderError::Path)?;
            }
        }
        let terms: crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<Term> = filtered.into_iter().map(|(term, _)| term).collect();
        self.assume_without_smoke_checks(&terms, definition, false)
    }
    /// The bulk overload attaches one conjunction to its debug expression after filtering.
    pub fn assume_terms(
        &mut self,
        factory: &TermFactory,
        terms: impl IntoIterator<Item = Term>,
        debug: Option<&DebugExp>,
        enforce: bool,
        definition: bool,
    ) -> Result<(), DeciderError<P::Error>> {
        let filtered: Vec<Term> = terms
            .into_iter()
            .filter(|t| enforce || !self.known_true(t))
            .collect();
        if self.debug_mode && !filtered.is_empty() {
            let debug = debug.ok_or(DeciderError::MissingDebugExpression)?;
            self.pcs
                .add_debug_exp(debug.with_term(factory.and(filtered.clone())))
                .map_err(DeciderError::Path)?;
        }
        let terms: crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<Term> = filtered.into_iter().collect();
        self.assume_without_smoke_checks(&terms, definition, false)
    }
    /// The caller supplies the constructed debug expression when the final expression exists.
    pub fn set_branch_condition(
        &mut self,
        term: Term,
        expression: (
            ferrum_silver::ast::expression::Exp,
            Option<ferrum_silver::ast::expression::Exp>,
        ),
        debug: Option<DebugExp>,
    ) -> Result<(), DeciderError<P::Error>> {
        self.pcs
            .set_branch_condition(term.clone(), expression)
            .map_err(DeciderError::Path)?;
        self.assume([(term, debug)], false, false)
    }
    /// The source sequence overload records all terms without filtering, then debug records.
    pub fn assume_sequence(
        &mut self,
        terms: impl IntoIterator<Item = Term>,
        debug_expressions: Option<&[DebugExp]>,
    ) -> Result<(), DeciderError<P::Error>> {
        let terms: crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<Term> = terms.into_iter().collect();
        self.assume_without_smoke_checks(&terms, false, true)?;
        if self.debug_mode {
            for expression in debug_expressions.ok_or(DeciderError::MissingDebugExpression)? {
                self.pcs
                    .add_debug_exp(expression.clone())
                    .map_err(DeciderError::Path)?;
            }
        }
        Ok(())
    }
    pub fn start_debug_subexpression(&mut self) -> Result<(), DeciderError<P::Error>> {
        if self.debug_mode {
            self.pcs
                .start_debug_subexpression()
                .map_err(DeciderError::Path)?;
        }
        Ok(())
    }
    pub fn finish_debug_subexpression(
        &mut self,
        description: String,
    ) -> Result<(), DeciderError<P::Error>> {
        if self.debug_mode {
            self.pcs
                .finish_debug_subexpression(description)
                .map_err(DeciderError::Path)?;
        }
        Ok(())
    }
    /// Record a fresh function received from the prover. The prover owns its declaration.
    pub fn fresh(
        &mut self,
        factory: &TermFactory,
        id: &str,
        args: &[crate::state::terms::Sort],
        result: &crate::state::terms::Sort,
    ) -> Result<
        (
            crate::state::terms::ApplicationTarget,
            crate::state::terms::Declaration,
        ),
        DeciderError<P::Error>,
    > {
        let target = self
            .prover
            .fresh(id, args, result)
            .map_err(DeciderError::Prover)?;
        let declaration = factory.function_decl_target(target.clone());
        self.fresh_functions = self.fresh_functions.incl(declaration.clone());
        Ok((target, declaration))
    }
    /// Fresh variable creation keeps the source conversion from a nullary prover function.
    pub fn fresh_variable(
        &mut self,
        factory: &TermFactory,
        name: &str,
        sort: &crate::state::terms::Sort,
        is_arp: bool,
        debug_type: Option<ferrum_silver::parser::parse_ast::PTypeHandle>,
    ) -> Result<Term, DeciderError<P::Error>> {
        use crate::state::terms::{ApplicationTarget, TermKind};
        let target = self
            .prover
            .fresh(name, &[], sort)
            .map_err(DeciderError::Prover)?;
        let variable = match target {
            ApplicationTarget::Variable(term) if matches!(term.kind(), TermKind::Var(_)) => term,
            ApplicationTarget::Function(fun) if fun.data().arg_sorts.is_empty() => factory.var(
                fun.data().id.clone(),
                fun.data().result_sort.clone(),
                is_arp,
            ),
            _ => return Err(DeciderError::InvalidFreshVariable),
        };
        self.fresh_functions = self
            .fresh_functions
            .incl(factory.function_decl_target(ApplicationTarget::Variable(variable.clone())));
        if self.debug_mode {
            let typ = debug_type.ok_or(DeciderError::MissingDebugVariableType)?;
            if let TermKind::Var(var) = variable.kind() {
                self.debug_variable_types.insert(var.id.name(), typ);
            }
        }
        Ok(variable)
    }
    pub fn fresh_arp(
        &mut self,
        factory: &TermFactory,
        name: &str,
        debug_type: Option<ferrum_silver::parser::parse_ast::PTypeHandle>,
    ) -> Result<(Term, Term), DeciderError<P::Error>> {
        let variable = self.fresh_variable(
            factory,
            name,
            &crate::state::terms::Sort::Perm,
            true,
            debug_type,
        )?;
        let constraint = factory.is_read_perm_var(variable.clone());
        Ok((variable, constraint))
    }
    /// Define and record an actual SMT macro with a fresh source identifier.
    pub fn fresh_macro(
        &mut self,
        factory: &TermFactory,
        identifiers: &mut impl crate::state::identifiers::IdentifierFactory,
        name: &str,
        args: Vec<Term>,
        body: Term,
    ) -> Result<crate::state::terms::Declaration, DeciderError<P::Error>> {
        let declaration = factory.macro_decl(identifiers.fresh(name), args, body);
        self.prover
            .declare(&declaration)
            .map_err(DeciderError::Prover)?;
        self.fresh_macros.push(declaration.clone());
        Ok(declaration)
    }
    /// Add a zero-argument macro alias only where the source permits it.
    pub fn create_alias<PD, FD, J>(
        &mut self,
        factory: &TermFactory,
        identifiers: &mut impl crate::state::identifiers::IdentifierFactory,
        term: &Term,
        state: &crate::state::state::State<PD, FD, J>,
    ) -> Result<Term, DeciderError<P::Error>> {
        use crate::state::terms::{ApplicableData, ApplicableKind, TermKind};
        let eligible = matches!(
            term.kind(),
            TermKind::HeapUpdate(..)
                | TermKind::HeapToSnap(..)
                | TermKind::SnapToHeap(..)
                | TermKind::MaskAdd(..)
                | TermKind::MergeSingle(..)
                | TermKind::MergeHeaps(..)
        );
        if eligible
            && term.var_repr().is_none()
            && state.quantified_variables.is_empty()
            && state.packaging_wand_snapshots.is_empty()
            && state.current_member.as_ref().is_none_or(|member| {
                matches!(member, ferrum_silver::ast::program::Member::Method(_))
            })
        {
            let decl =
                self.fresh_macro(factory, identifiers, "tmpTerm", Vec::new(), term.clone())?;
            let macro_fn = factory.applicable(ApplicableData {
                kind: ApplicableKind::Macro,
                id: decl.id(),
                arg_sorts: vec![],
                result_sort: term.sort().clone(),
            });
            term.set_var_repr(Some(factory.app(macro_fn, Vec::new())));
        }
        Ok(term.clone())
    }
    /// Declarations imported from another branch are emitted once, preserving input order.
    pub fn declare_fresh_functions(
        &mut self,
        declarations: impl IntoIterator<Item = crate::state::terms::Declaration>,
    ) -> Result<(), DeciderError<P::Error>> {
        for declaration in declarations {
            if !matches!(
                declaration.kind(),
                crate::state::terms::DeclarationKind::Function(_)
            ) {
                return Err(DeciderError::InvalidDeclaration);
            }
            if !self.fresh_functions.contains(&declaration) {
                self.prover
                    .declare(&declaration)
                    .map_err(DeciderError::Prover)?;
                self.fresh_functions = self.fresh_functions.incl(declaration);
            }
        }
        Ok(())
    }
    /// Source macro transfer deduplicates by name rather than structural declaration equality.
    pub fn declare_fresh_macros(
        &mut self,
        declarations: impl IntoIterator<Item = crate::state::terms::Declaration>,
    ) -> Result<(), DeciderError<P::Error>> {
        for declaration in declarations {
            if !matches!(
                declaration.kind(),
                crate::state::terms::DeclarationKind::Macro { .. }
            ) {
                return Err(DeciderError::InvalidDeclaration);
            }
            if !self
                .fresh_macros
                .iter()
                .any(|old| old.id().name() == declaration.id().name())
            {
                self.prover
                    .declare(&declaration)
                    .map_err(DeciderError::Prover)?;
                self.fresh_macros.push(declaration);
            }
        }
        Ok(())
    }
    pub fn check_smoke(&mut self, is_assert: bool) -> Result<bool, DeciderError<P::Error>> {
        self.prover
            .check(if is_assert {
                self.assert_timeout
            } else {
                self.check_timeout
            })
            .map(|r| r == SatResult::Unsat)
            .map_err(DeciderError::Prover)
    }
    pub fn check(
        &mut self,
        term: &Term,
        timeout: Option<i32>,
    ) -> Result<bool, DeciderError<P::Error>> {
        let logging = self.logging.clone().filter(|log| log.enabled());
        let scope = if let Some(log) = &logging {
            Some(
                log.open(std::sync::Arc::new(
                    crate::logger::records::data::decider_assert_record::DeciderAssertRecord::new(
                        Some(term.clone()),
                        timeout,
                    ),
                ))
                .map_err(DeciderError::Logging)?,
            )
        } else {
            None
        };
        let result = if self.known_true(term) {
            true
        } else {
            self.prover_assert(term, timeout)?
        };
        if let (Some(log), Some(scope)) = (logging, scope) {
            log.member
                .close_scope(scope)
                .map_err(DeciderError::Logging)?;
        }
        Ok(result)
    }
    /// Source proverAssert scope, shared by deciderAssert and generateModel.
    fn prover_assert(
        &mut self,
        term: &Term,
        timeout: Option<i32>,
    ) -> Result<bool, DeciderError<P::Error>> {
        let logging = self.logging.clone().filter(|log| log.enabled());
        let Some(log) = logging else {
            return self
                .prover
                .assert_goal(term, timeout)
                .map_err(DeciderError::Prover);
        };
        let record = std::sync::Arc::new(
            crate::logger::records::data::prover_assert_record::ProverAssertRecord::new(
                Some(term.clone()),
                timeout,
            ),
        );
        let scope = log.open(record.clone()).map_err(DeciderError::Logging)?;
        let result = self
            .prover
            .assert_goal(term, timeout)
            .map_err(DeciderError::Prover)?;
        let statistics = self
            .prover
            .statistics()
            .map_err(DeciderError::Prover)?
            .into_iter()
            .collect();
        let statistics = log
            .member
            .delta_statistics(statistics, log.render_double)
            .map_err(DeciderError::Logging)?;
        *record.statistics.lock().map_err(|_| {
            DeciderError::Logging(crate::logger::records::symbolic_record::RecordError::Poisoned)
        })? = Some(statistics);
        log.member
            .close_scope(scope)
            .map_err(DeciderError::Logging)?;
        Ok(result)
    }
    pub fn assert_with<R>(
        &mut self,
        term: &Term,
        timeout: Option<i32>,
        continuation: impl FnOnce(bool) -> R,
    ) -> Result<R, DeciderError<P::Error>> {
        let success = self.check(term, timeout)?;
        self.failed_query = (!success).then(|| term.clone());
        if let Some(logging) = &self.logging {
            logging
                .member
                .set_smt_query(self.failed_query.clone())
                .map_err(DeciderError::Logging)?;
        }
        Ok(continuation(success))
    }
    pub fn has_model(&self) -> bool {
        self.prover.has_model()
    }
    pub fn is_model_valid(&self) -> bool {
        self.prover.is_model_valid()
    }
    pub fn get_model(
        &mut self,
    ) -> Result<ferrum_silver::verifier::verification_error::Model, DeciderError<P::Error>> {
        self.prover.get_model().map_err(DeciderError::Prover)
    }
    pub fn clear_model(&mut self) {
        self.prover.clear_last_assert();
    }
    pub fn statistics(&mut self) -> Result<Vec<(String, String)>, DeciderError<P::Error>> {
        self.prover.statistics().map_err(DeciderError::Prover)
    }
    pub fn generate_model(&mut self, factory: &TermFactory) -> Result<(), DeciderError<P::Error>> {
        self.prover_assert(&factory.boolean(false), self.assert_timeout)
            .map(|_| ())
    }
}
