//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/SymbolicExecutionRules.scala
//!
//! Purpose:
//! Construct verifier failures and diagnostics shared by symbolic execution.
//!
//! Planned Rust structure:
//! SymbolicExecutionRules provides debugOn and createFailure overloads for term, expression,
//! description and model request.
//!
//! Behavior to preserve:
//! Count/report unexpected failures only at final retry; unwrap counterexample transformer;
//! optionally generate model and only construct counterexample when valid. Select native, variable,
//! mapped, raw or resolved model, apply transformer, optionally include unknown reason and filtered
//! branch conditions. Debug context records state, declarations and assumptions; otherwise use
//! ordinary failure context. Failure continuation flag follows reportFurtherErrors.
//!
//! Integration:
//! interfaces::verification, reporting, verifier, decider and silver::verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Failure context lifetime and solver/model ownership.
//!
//! Status: partial; source failure reporting, model selection and context-attachment
//! ordering implemented. Concrete diagnostics, debugger and solver services remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::debugger::debug_exp::DebugExp;
use crate::interfaces::verification::VerificationResult;
use crate::state::state::State;
use crate::state::terms::Term;
use ferrum_silver::ast::expression::{Exp, ExpKind};

/// Model variants supported by the upstream failure builder.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CounterexampleKind {
    Native,
    Variables,
    Mapped,
    Raw,
    Resolved,
}
pub trait FailureServices<P, D, J> {
    type Error;
    type VerificationError;
    type Counterexample;
    type CounterexampleTransform;
    fn is_expected_failure(&self, error: &Self::VerificationError) -> bool;
    fn generate_block_messages(&self) -> bool;
    fn report_failed_block(
        &mut self,
        member: &str,
        block: &str,
        id: i32,
    ) -> Result<(), Self::Error>;
    fn increment_error_count(&mut self);
    fn unwrap_counterexample_transform(
        &mut self,
        error: Self::VerificationError,
    ) -> Result<
        (
            Self::VerificationError,
            Option<Self::CounterexampleTransform>,
        ),
        Self::Error,
    >;
    fn report_reason_unknown(&self) -> bool;
    fn counterexample_kind(&self) -> Option<CounterexampleKind>;
    fn has_model(&self) -> bool;
    fn generate_model(&mut self) -> Result<(), Self::Error>;
    fn is_model_valid(&self) -> bool;
    fn build_counterexample(
        &mut self,
        state: &State<P, D, J>,
        kind: CounterexampleKind,
    ) -> Result<Self::Counterexample, Self::Error>;
    fn transform_counterexample(
        &mut self,
        transform: Self::CounterexampleTransform,
        counterexample: Self::Counterexample,
    ) -> Result<Self::Counterexample, Self::Error>;
    fn reason_unknown(&mut self) -> Result<Option<String>, Self::Error>;
    fn report_branch_conditions(&self) -> bool;
    fn debugging(&self) -> bool;
    fn branch_condition_exps(&self) -> Vec<Exp>;
    /// Construct the ordinary or debug failure context with solver/path/declaration
    /// ownership, and attach it to the unwrapped error.
    fn attach_failure_context(
        &mut self,
        error: Self::VerificationError,
        state: &State<P, D, J>,
        branches: Vec<Exp>,
        counterexample: Option<Self::Counterexample>,
        reason: Option<Option<String>>,
        failed_assert: &Term,
        debug_assert: Option<&DebugExp>,
    ) -> Result<Self::VerificationError, Self::Error>;
    fn report_further_errors(&self) -> bool;
}
#[derive(Debug)]
pub enum FailureConstructionError<E> {
    MissingDebugAssertion,
    Service(E),
}
/// Construct a failure only after reporting/counting, optional model generation and
/// context attachment. Unknown or invalid models never become proof success.
pub fn create_failure<P, D, J, C: FailureServices<P, D, J>>(
    context: &mut C,
    state: &State<P, D, J>,
    error: C::VerificationError,
    failed_assert: &Term,
    debug_assert: Option<&DebugExp>,
    generate_new_model: bool,
) -> Result<VerificationResult<C::VerificationError>, FailureConstructionError<C::Error>> {
    if state.retry_level == 0 && !context.is_expected_failure(&error) {
        if context.generate_block_messages()
            && let (Some(member), Some((block, id))) = (&state.current_member, &state.current_block)
        {
            context
                .report_failed_block(member.name(), block, *id)
                .map_err(FailureConstructionError::Service)?;
        }
        context.increment_error_count();
    }
    let (error, transform) = context
        .unwrap_counterexample_transform(error)
        .map_err(FailureConstructionError::Service)?;
    let kind = context.counterexample_kind();
    if (context.report_reason_unknown() || kind.is_some())
        && (generate_new_model || !context.has_model())
    {
        context
            .generate_model()
            .map_err(FailureConstructionError::Service)?;
    }
    let counterexample = if let Some(kind) = kind
        && context.is_model_valid()
    {
        let example = context
            .build_counterexample(state, kind)
            .map_err(FailureConstructionError::Service)?;
        Some(match transform {
            Some(transform) => context
                .transform_counterexample(transform, example)
                .map_err(FailureConstructionError::Service)?,
            None => example,
        })
    } else {
        None
    };
    let reason = if context.report_reason_unknown() {
        Some(
            context
                .reason_unknown()
                .map_err(FailureConstructionError::Service)?,
        )
    } else {
        None
    };
    let branches = if context.report_branch_conditions() {
        context
            .branch_condition_exps()
            .into_iter()
            .filter(|exp| !matches!(exp.kind(), ExpKind::TrueLit))
            .collect()
    } else {
        Vec::new()
    };
    if context.debugging() && debug_assert.is_none() {
        return Err(FailureConstructionError::MissingDebugAssertion);
    }
    let error = context
        .attach_failure_context(
            error,
            state,
            branches,
            counterexample,
            reason,
            failed_assert,
            debug_assert,
        )
        .map_err(FailureConstructionError::Service)?;
    Ok(VerificationResult::failure(
        error,
        context.report_further_errors(),
    ))
}
