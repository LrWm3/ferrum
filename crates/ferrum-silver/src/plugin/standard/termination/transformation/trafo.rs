//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/Trafo.scala
//!
//! Purpose:
//! Assemble and memoize function and method termination transformations.
//!
//! Planned Rust structure:
//! Port Trafo with program, reportError, respectFuncPermAmounts and getTransformedProgram.
//!
//! Behavior to preserve:
//! Generate function proof methods first, then transform original methods; append proof methods to
//! transformed methods, preserve program metadata and cache the result.
//!
//! Integration:
//! function_check, method_check and program_manager; termination_plugin invokes it.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for contexts, ownership and configuration.
//!
//! Open decisions:
//! Agree on cached program handle and error callback lifetime with termination_plugin.
//!
//! Status: partial; ordering, error propagation and caching implemented with injected real
//! function/method checks. Concrete checks and plugin wiring remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::program_manager::ProgramManager;
use crate::ast::program::{Function, Method, Program};

/// Collaborators perform actual termination proof generation and method rewriting.
/// Errors cannot be converted into unchanged methods or successful proof obligations.
pub trait TerminationChecks {
    type Error;
    fn generate_proof_methods(
        &mut self,
        manager: &mut ProgramManager,
        function: &Function,
        respect_function_permission_amounts: bool,
    ) -> Result<Vec<Method>, Self::Error>;
    fn transform_method(
        &mut self,
        manager: &mut ProgramManager,
        method: &Method,
    ) -> Result<Method, Self::Error>;
}
pub struct Trafo<C: TerminationChecks> {
    pub manager: ProgramManager,
    pub checks: C,
    pub respect_function_permission_amounts: bool,
    transformed_program: Option<Program>,
}
impl<C: TerminationChecks> Trafo<C> {
    pub fn new(
        manager: ProgramManager,
        checks: C,
        respect_function_permission_amounts: bool,
    ) -> Self {
        Self {
            manager,
            checks,
            respect_function_permission_amounts,
            transformed_program: None,
        }
    }
    pub fn get_transformed_program(&mut self) -> Result<Program, C::Error> {
        if let Some(program) = &self.transformed_program {
            return Ok(program.clone());
        }
        let original = self.manager.program.clone();
        let mut proof_methods = Vec::new();
        for function in &original.functions {
            proof_methods.extend(self.checks.generate_proof_methods(
                &mut self.manager,
                function,
                self.respect_function_permission_amounts,
            )?);
        }
        let mut methods = Vec::with_capacity(original.methods.len() + proof_methods.len());
        for method in &original.methods {
            methods.push(self.checks.transform_method(&mut self.manager, method)?);
        }
        methods.extend(proof_methods);
        let transformed = original.copy_with(|p| p.methods = methods);
        self.transformed_program = Some(transformed.clone());
        Ok(transformed)
    }
}
