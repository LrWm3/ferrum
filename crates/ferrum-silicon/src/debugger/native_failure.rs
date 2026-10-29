//! Ferrum failure snapshot assembly described in PLAN.md.
//! Source: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/Verification.scala
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//! Immutable snapshots of native debugging failures.
//! Scala collection provenance is preserved wherever retained by native execution.
use crate::{
    config::JoinMode,
    debugger::{
        debug_exp::{DebugAxiom, DebugExp, DebugExpPrintConfiguration},
        silicon_debugger::ProofObligation,
    },
    state::{
        state::State,
        terms::{Declaration, Term},
    },
};
use ferrum_silver::{
    ast::expression::Exp,
    parser::parse_ast::PTypeHandle,
    verifier::verification_error::{Counterexample, ErrorReason, FailureContext},
};
use std::sync::{Arc, Mutex};

#[derive(Clone)]
pub struct NativeDebugVerifierSnapshot {
    pub worker_id: String,
    pub prover_name: String,
    pub macro_declarations: Vec<Declaration>,
    pub function_declarations: Vec<Declaration>,
    pub debug_variable_types: crate::package::Map<String, PTypeHandle>,
}

pub struct NativeDebugFailureRecord {
    pub verifier: NativeDebugVerifierSnapshot,
    pub prover_emits: Vec<String>,
    pub preamble_assumptions: Vec<DebugAxiom>,
    pub branch_conditions: Vec<Term>,
    pub branch_condition_exps: Vec<(Exp, Exp)>,
    pub assumptions:
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<DebugExp>,
    pub assertion: Term,
    pub assertion_exp: DebugExp,
    pub original_error_reason: ErrorReason,
    pub counterexample: Option<Arc<dyn Counterexample>>,
    pub reason_unknown: Option<Option<String>>,
}
pub type NativeDebugFunctionOwners<FD> = Vec<(
    String,
    Arc<Mutex<crate::supporters::functions::function_data::FunctionData<FD>>>,
)>;
pub type NativeDebugFailureFactory<PD, FD> = Arc<
    dyn Fn(
            State<PD, FD, JoinMode>,
            NativeDebugFailureRecord,
            &NativeDebugFunctionOwners<FD>,
        ) -> Result<Arc<dyn FailureContext>, String>
        + Send
        + Sync,
>;

pub struct NativeDebugFailureContext<PD, FD> {
    pub obligation:
        ProofObligation<State<PD, FD, JoinMode>, NativeDebugVerifierSnapshot, ErrorReason>,
    pub counterexample: Option<Arc<dyn Counterexample>>,
    pub reason_unknown: Option<Option<String>>,
    pub function_owners: NativeDebugFunctionOwners<FD>,
}
impl<PD, FD> NativeDebugFailureContext<PD, FD> {
    pub fn new(state: State<PD, FD, JoinMode>, record: NativeDebugFailureRecord) -> Self {
        Self {
            obligation: ProofObligation {
                state,
                verifier: record.verifier,
                prover_emits: record.prover_emits,
                preamble_assumptions: record.preamble_assumptions,
                branch_conditions: record.branch_conditions,
                branch_condition_exps: record.branch_condition_exps,
                assumptions: record.assumptions,
                assertion: record.assertion,
                assertion_exp: record.assertion_exp,
                timeout: None,
                print_config: Arc::new(Mutex::new(DebugExpPrintConfiguration::default())),
                original_error_reason: record.original_error_reason,
            },
            counterexample: record.counterexample,
            reason_unknown: record.reason_unknown,
            function_owners: Vec::new(),
        }
    }
}
impl
    NativeDebugFailureContext<
        crate::supporters::predicate_verification_unit::PredicateData,
        crate::verifier::native_context::NativeFunctionData,
    >
{
    /// Detach function phase data from the verifier and rebind every weak handle
    /// to the captured registry, including recorder owners.
    pub fn capture_native(
        mut state: State<
            crate::supporters::predicate_verification_unit::PredicateData,
            crate::verifier::native_context::NativeFunctionData,
            JoinMode,
        >,
        record: NativeDebugFailureRecord,
        source: &NativeDebugFunctionOwners<crate::verifier::native_context::NativeFunctionData>,
    ) -> Result<Self, String> {
        use crate::supporters::functions::function_recorder::{FunctionRecorder, RecorderOwner};
        use crate::verifier::native_context::NativeFunctionData;
        let mut predicates = crate::state::package::OrderedMap::new();
        for (name, data) in state.predicate_data.iter() {
            let contents = data
                .contents
                .lock()
                .map_err(|_| "poisoned predicate contents")?
                .clone();
            let symbols = data
                .fresh_symbols
                .lock()
                .map_err(|_| "poisoned predicate symbols")?
                .clone();
            predicates.insert(
                name.clone(),
                Arc::new(
                    crate::supporters::predicate_verification_unit::PredicateData {
                        predicate: data.predicate.clone(),
                        argument_sorts: data.argument_sorts.clone(),
                        trigger_function: data.trigger_function.clone(),
                        contents: Mutex::new(contents),
                        fresh_symbols: Mutex::new(symbols),
                    },
                ),
            );
        }
        state.predicate_data = predicates;
        let mut owners = Vec::with_capacity(source.len());
        for (name, data) in source {
            let copy = data
                .lock()
                .map_err(|_| "poisoned function data")?
                .phase_snapshot();
            owners.push((name.clone(), Arc::new(Mutex::new(copy))));
        }
        let rebind = |old: &Arc<NativeFunctionData>| -> Result<Arc<NativeFunctionData>, String> {
            let index = if let Some(index) = source
                .iter()
                .position(|(_, owner)| old.0.ptr_eq(&Arc::downgrade(owner)))
            {
                index
            } else {
                // An edited replay state may refer to the previous session's
                // detached registry. Match its still-live function by name.
                let owner = old
                    .0
                    .upgrade()
                    .ok_or_else(|| "debug function data owner expired".to_owned())?;
                let name = owner
                    .lock()
                    .map_err(|_| "poisoned replay function data")?
                    .program_function
                    .name
                    .clone();
                source
                    .iter()
                    .position(|(candidate, _)| candidate == &name)
                    .ok_or_else(|| format!("unknown debug function {name}"))?
            };
            Ok(Arc::new(NativeFunctionData(Arc::downgrade(
                &owners[index].1,
            ))))
        };
        let rebind_recorder =
            |recorder: &mut FunctionRecorder<NativeFunctionData>| -> Result<(), String> {
                if let FunctionRecorder::Actual(actual) = recorder {
                    if let RecorderOwner::Function { data, .. } = &mut actual.owner {
                        *data = rebind(data)?;
                    }
                }
                Ok(())
            };
        let mut handles = crate::state::package::OrderedMap::new();
        for (name, handle) in state.function_data.iter() {
            handles.insert(name.clone(), rebind(handle)?);
        }
        state.function_data = handles;
        rebind_recorder(&mut state.function_recorder)?;
        for (_, owner) in &owners {
            let mut data = owner
                .lock()
                .map_err(|_| "poisoned captured function data")?;
            rebind_recorder(&mut data.recorder_handler.recorder)?;
        }
        let mut result = Self::new(state, record);
        result.function_owners = owners;
        Ok(result)
    }
}
impl
    NativeDebugFailureContext<
        crate::supporters::predicate_verification_unit::PredicateData,
        crate::verifier::native_context::NativeFunctionData,
    >
{
    /// Give each debugger replay a detached registry and state; mutations cannot
    /// change the original failure or another replay session.
    pub fn prepare_runtime<S: crate::interfaces::decider::prover::Prover>(
        &self,
        context: &mut crate::verifier::native_context::NativeVerifierContext<
            S,
            crate::supporters::predicate_verification_unit::PredicateData,
            crate::verifier::native_context::NativeFunctionData,
        >,
    ) -> Result<crate::verifier::native_context::NativeState, String> {
        self.prepare_runtime_with_state(context, &self.obligation.state)
    }
    /// Preserve the caller's edited replay state while detaching all registries.
    pub fn prepare_runtime_with_state<S: crate::interfaces::decider::prover::Prover>(
        &self,
        context: &mut crate::verifier::native_context::NativeVerifierContext<
            S,
            crate::supporters::predicate_verification_unit::PredicateData,
            crate::verifier::native_context::NativeFunctionData,
        >,
        state: &crate::verifier::native_context::NativeState,
    ) -> Result<crate::verifier::native_context::NativeState, String> {
        let obligation = &self.obligation;
        let record = NativeDebugFailureRecord {
            verifier: obligation.verifier.clone(),
            prover_emits: obligation.prover_emits.clone(),
            preamble_assumptions: obligation.preamble_assumptions.clone(),
            branch_conditions: obligation.branch_conditions.clone(),
            branch_condition_exps: obligation.branch_condition_exps.clone(),
            assumptions: obligation.assumptions.clone(),
            assertion: obligation.assertion.clone(),
            assertion_exp: obligation.assertion_exp.clone(),
            original_error_reason: obligation.original_error_reason.clone(),
            counterexample: self.counterexample.clone(),
            reason_unknown: self.reason_unknown.clone(),
        };
        let fork = Self::capture_native(state.clone(), record, &self.function_owners)?;
        context.restore_debug_runtime(&fork)?;
        Ok(fork.obligation.state.clone())
    }
}
impl<PD, FD> std::fmt::Debug for NativeDebugFailureContext<PD, FD> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeDebugFailureContext")
            .finish_non_exhaustive()
    }
}
impl<PD: Send + Sync + 'static, FD: Send + Sync + 'static> FailureContext
    for NativeDebugFailureContext<PD, FD>
{
    fn counterexample(&self) -> Option<Arc<dyn Counterexample>> {
        self.counterexample.clone()
    }
    fn render(&self) -> String {
        String::new()
    }
}
