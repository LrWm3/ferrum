// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

//! Main verifier sequencing from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/DefaultMainVerifier.scala.
//! Status: source program-verification ordering and worker result collection implemented over
//! required services. Concrete contributor, initial-state, pool, reporter, preprocessing and
//! verifier context assembly remain pending; each operation is fallible and none defaults to success.

use ferrum_silver::ast::program::Program;
use ferrum_silver::cfg::silver::silver_cfg::SilverCfg;

/// Services implement the source operations, including per-member initial states, result
/// flattening, error scopes, timings and reporting. Queued tasks must retain the supplied program.
pub trait MainVerificationServices {
    type Error;
    type Result;
    type Analysis;
    type FunctionUnit;
    type PredicateUnit;
    type Task;
    fn preprocess(&mut self, program: &Program) -> Result<Program, Self::Error>;
    fn setup_predicate_snapshots(&mut self, program: &Program) -> Result<(), Self::Error>;
    fn begin_preamble(&mut self, input_file: Option<&str>) -> Result<(), Self::Error>;
    fn emit_static_preamble(&mut self) -> Result<(), Self::Error>;
    fn analyze_and_emit_contributions(
        &mut self,
        program: &Program,
    ) -> Result<Self::Analysis, Self::Error>;
    fn end_preamble_and_saturate(&mut self) -> Result<(), Self::Error>;
    fn function_units(&mut self) -> Result<Vec<Self::FunctionUnit>, Self::Error>;
    fn predicate_units(&mut self) -> Result<Vec<Self::PredicateUnit>, Self::Error>;
    fn verify_function(
        &mut self,
        unit: Self::FunctionUnit,
        program: &Program,
        analysis: &Self::Analysis,
    ) -> Result<Vec<Self::Result>, Self::Error>;
    fn verify_predicate(
        &mut self,
        unit: Self::PredicateUnit,
        program: &Program,
        analysis: &Self::Analysis,
    ) -> Result<Vec<Self::Result>, Self::Error>;
    fn stop_main_prover(&mut self) -> Result<(), Self::Error>;
    fn begin_worker_preamble(&mut self) -> Result<(), Self::Error>;
    fn declare_predicate_sorts(&mut self) -> Result<(), Self::Error>;
    fn declare_function_sorts(&mut self) -> Result<(), Self::Error>;
    fn declare_predicate_symbols(&mut self) -> Result<(), Self::Error>;
    fn declare_function_symbols(&mut self) -> Result<(), Self::Error>;
    fn emit_predicate_axioms(&mut self) -> Result<(), Self::Error>;
    fn emit_function_axioms(&mut self) -> Result<(), Self::Error>;
    fn end_worker_preamble(&mut self) -> Result<(), Self::Error>;
    fn excluded_method(&mut self, method: &ferrum_silver::ast::program::Method) -> bool;
    fn queue_method(
        &mut self,
        method: &ferrum_silver::ast::program::Method,
        program: &Program,
        analysis: &Self::Analysis,
    ) -> Result<Self::Task, Self::Error>;
    fn queue_cfg(
        &mut self,
        cfg: &SilverCfg,
        program: &Program,
        analysis: &Self::Analysis,
    ) -> Result<Self::Task, Self::Error>;
    fn await_task(&mut self, task: Self::Task) -> Result<Vec<Self::Result>, Self::Error>;
    fn report_termination_and_optional_trace(&mut self) -> Result<(), Self::Error>;
    fn run_optional_debugger(&mut self, results: &[Self::Result]) -> Result<(), Self::Error>;
}

pub fn verify<S: MainVerificationServices>(
    services: &mut S,
    original: &Program,
    cfgs: &[SilverCfg],
    input_file: Option<&str>,
) -> Result<Vec<S::Result>, S::Error> {
    let program = services.preprocess(original)?;
    services.setup_predicate_snapshots(&program)?;
    services.begin_preamble(input_file)?;
    services.emit_static_preamble()?;
    let analysis = services.analyze_and_emit_contributions(&program)?;
    services.end_preamble_and_saturate()?;
    let mut results = Vec::new();
    for unit in services.function_units()? {
        results.extend(services.verify_function(unit, &program, &analysis)?);
    }
    for unit in services.predicate_units()? {
        results.extend(services.verify_predicate(unit, &program, &analysis)?);
    }
    services.stop_main_prover()?;
    services.begin_worker_preamble()?;
    services.declare_predicate_sorts()?;
    services.declare_function_sorts()?;
    services.declare_predicate_symbols()?;
    services.declare_function_symbols()?;
    services.emit_predicate_axioms()?;
    services.emit_function_axioms()?;
    services.end_worker_preamble()?;
    let mut tasks = Vec::new();
    for method in &program.methods {
        if !services.excluded_method(method) {
            tasks.push(services.queue_method(method, &program, &analysis)?);
        }
    }
    for cfg in cfgs {
        tasks.push(services.queue_cfg(cfg, &program, &analysis)?);
    }
    for task in tasks {
        results.extend(services.await_task(task)?);
    }
    services.report_termination_and_optional_trace()?;
    services.run_optional_debugger(&results)?;
    Ok(results)
}
