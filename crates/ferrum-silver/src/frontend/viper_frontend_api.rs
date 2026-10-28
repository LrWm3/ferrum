//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/ViperFrontendAPI.scala
//!
//! Purpose:
//! Accept constructed Silver programs through a reusable frontend and plugin pipeline.
//!
//! Planned Rust structure:
//! Represent ViperFrontendAPI and MinimalViperFrontendAPI with initialize, verify, stop and
//! starting-state override.
//!
//! Behavior to preserve:
//! Initialize builds/configures verifier with ignoreFile and dummy filename, resets plugins;
//! verify and stop require initialization. Preserve upstream starting state and phase lists,
//! including Minimal’s verification-only path. The base API sets state to ConsistencyCheck
//! before running phases; DefaultFrontend.consistencyCheck only runs at Translation, so its
//! listed consistency phase is skipped in this call path. Verification still runs, including
//! plugin filtering. SiliconFrontendAPI supplies no override of this state or phase method.
//!
//! Integration:
//! frontend::sil_frontend, ast::program, plugin manager and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Reconcile repeated-call state/reset and the apparent skipped consistency check with
//! frontend::frontend, SiliconFrontendAPI and PLAN.md; record any deliberate correction.
//!
//! Status: partial; initialization, injected-program phase execution and stop are implemented.
//! Backend option extension and concrete plugin reset remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::frontend::{DefaultFrontend, DefaultState, FrontendError, FrontendPhases, Phase};
use super::sil_front_end_config::SilFrontendConfig;
use crate::ast::program::Program;
use crate::verifier::verification_result::VerificationResult;
use crate::verifier::verifier::Verifier;

pub const DUMMY_INPUT_FILENAME: &str =
    "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver";
pub const PHASES: &[Phase] = &[Phase::ConsistencyCheck, Phase::Verification];
pub const MINIMAL_PHASES: &[Phase] = &[Phase::Verification];

/// Frontends using this API inject an already constructed program. Plugin initialization
/// is supplied by the caller until the concrete Silver frontend is available.
pub struct ViperFrontendApi<F: FrontendPhases> {
    pub frontend: DefaultFrontend<F>,
    pub config: Option<SilFrontendConfig>,
    pub minimal: bool,
    initialized: bool,
}
impl<F: FrontendPhases> ViperFrontendApi<F> {
    pub fn new(frontend: DefaultFrontend<F>, minimal: bool) -> Self {
        Self {
            frontend,
            config: None,
            minimal,
            initialized: false,
        }
    }
    pub fn initialize(
        &mut self,
        mut verifier: Box<dyn Verifier>,
        args: &[String],
        reset_plugins: impl FnOnce(&SilFrontendConfig),
    ) -> Result<(), String> {
        let mut complete_args = args.to_vec();
        complete_args.push("--ignoreFile".into());
        complete_args.push(DUMMY_INPUT_FILENAME.into());
        verifier.parse_command_line(&complete_args);
        let config = SilFrontendConfig::parse_shared(verifier.name(), &complete_args);
        if let Some(error) = &config.error {
            return Err(error.clone());
        }
        if config.exit() {
            return Err("frontend configuration requested exit".into());
        }
        self.frontend.init(verifier);
        reset_plugins(&config);
        self.config = Some(config);
        self.initialized = true;
        Ok(())
    }
    pub fn verify(&mut self, program: Program) -> Result<VerificationResult, FrontendError> {
        if !self.initialized {
            return Err(FrontendError::NotInitialized);
        }
        // Upstream starts at ConsistencyCheck, so its consistency phase is a no-op
        // even in the non-minimal variant; verification is then run.
        self.frontend.state = DefaultState::ConsistencyCheck;
        self.frontend.program = Some(program);
        let phases = if self.minimal { MINIMAL_PHASES } else { PHASES };
        self.frontend
            .run_range(phases, phases[0], *phases.last().expect("API phases"))?;
        self.frontend.result()
    }
    pub fn stop(&mut self) -> Result<(), FrontendError> {
        if !self.initialized {
            return Err(FrontendError::NotInitialized);
        }
        if let Some(verifier) = self.frontend.verifier.as_mut() {
            verifier.stop();
        }
        Ok(())
    }
}
