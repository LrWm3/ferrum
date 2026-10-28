//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/Frontend.scala
//!
//! Purpose:
//! Define phase execution and the reusable default frontend state machine.
//!
//! Planned Rust structure:
//! Represent Frontend, Phase, DefaultPhases, SingleFileFrontend, DefaultFrontend, Succ/Fail and
//! DefaultStates; retain input, loader, verifier, phase results and errors.
//!
//! Behavior to preserve:
//! Run phases in declared order; range endpoints are inclusive and membership asserted. Reset
//! requires initialization and clears prior results/messages. Each phase runs only at its
//! expected state and without prior errors, but advances state after its own failure. Result
//! returns errors or requires verification. Single-file reset rejects other counts.
//!
//! Integration:
//! frontend::sil_frontend supplies phase bodies; ast::utility loader, reporter and verifier
//! supply interfaces.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on phase callbacks, loader errors and verifier ownership with sil_frontend and verifier.
//!
//! Status: partial; generic phase execution and state transitions are implemented.
//! Concrete Silver parsing, diagnostics, verifier and plugin integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::program::Program;
use crate::verifier::verification_result::{AbstractError, VerificationResult};
use crate::verifier::verifier::{Verifier, VerifierError};
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefaultState {
    Initial,
    Initialized,
    InputSet,
    Parsing,
    SemanticAnalysis,
    Translation,
    ConsistencyCheck,
    Verification,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    Parsing,
    SemanticAnalysis,
    Translation,
    ConsistencyCheck,
    Verification,
}
impl Phase {
    pub fn name(self) -> &'static str {
        match self {
            Self::Parsing => "Parsing",
            Self::SemanticAnalysis => "Semantic Analysis",
            Self::Translation => "Translation",
            Self::ConsistencyCheck => "Consistency Check",
            Self::Verification => "Verification",
        }
    }
}
pub const DEFAULT_PHASES: &[Phase] = &[
    Phase::Parsing,
    Phase::SemanticAnalysis,
    Phase::Translation,
    Phase::ConsistencyCheck,
    Phase::Verification,
];
#[derive(Debug)]
pub enum FrontendError {
    NotInitialized,
    MissingInput,
    MissingPhaseResult(&'static str),
    PhaseNotAvailable(Phase),
    WrongFileCount,
    Verifier(VerifierError),
}

/// Actual language-specific phase bodies. Failures retain all diagnostics in order.
pub trait FrontendPhases {
    type Parsed: Clone;
    type Analyzed: Clone;
    fn parse(&mut self, input: &str) -> Result<Self::Parsed, Vec<AbstractError>>;
    fn analyze(&mut self, input: Self::Parsed) -> Result<Self::Analyzed, Vec<AbstractError>>;
    fn translate(&mut self, input: Self::Analyzed) -> Result<Program, Vec<AbstractError>>;
    fn check_consistency(&mut self, input: Program) -> Result<Program, Vec<AbstractError>>;
    fn reset_messages(&mut self);
}
/// Phase state and retained results of the source DefaultFrontend.
pub struct DefaultFrontend<F: FrontendPhases> {
    pub phases: F,
    pub state: DefaultState,
    pub verifier: Option<Box<dyn Verifier>>,
    pub input: Option<String>,
    pub input_file: Option<PathBuf>,
    pub errors: Vec<AbstractError>,
    pub parsing_result: Option<F::Parsed>,
    pub semantic_result: Option<F::Analyzed>,
    pub verification_result: Option<VerificationResult>,
    pub program: Option<Program>,
}
impl<F: FrontendPhases> DefaultFrontend<F> {
    pub fn new(phases: F) -> Self {
        Self {
            phases,
            state: DefaultState::Initial,
            verifier: None,
            input: None,
            input_file: None,
            errors: Vec::new(),
            parsing_result: None,
            semantic_result: None,
            verification_result: None,
            program: None,
        }
    }
    pub fn init(&mut self, verifier: Box<dyn Verifier>) {
        self.state = DefaultState::Initialized;
        self.verifier = Some(verifier);
    }
    /// A failed load remains absent, as source reset uses `loadContent(...).toOption`.
    pub fn reset(
        &mut self,
        input: &Path,
        load: impl FnOnce(&Path) -> std::io::Result<String>,
    ) -> Result<(), FrontendError> {
        if self.state < DefaultState::Initialized {
            return Err(FrontendError::NotInitialized);
        }
        self.state = DefaultState::InputSet;
        self.input_file = Some(input.to_owned());
        self.input = load(input).ok();
        self.errors.clear();
        self.parsing_result = None;
        self.semantic_result = None;
        self.verification_result = None;
        self.program = None;
        self.phases.reset_messages();
        Ok(())
    }
    pub fn reset_files(
        &mut self,
        files: &[PathBuf],
        load: impl FnOnce(&Path) -> std::io::Result<String>,
    ) -> Result<(), FrontendError> {
        if let [file] = files {
            self.reset(file, load)
        } else {
            Err(FrontendError::WrongFileCount)
        }
    }
    pub fn run_phase(&mut self, phase: Phase) -> Result<(), FrontendError> {
        match phase {
            Phase::Parsing => {
                if self.state < DefaultState::InputSet {
                    return Err(FrontendError::NotInitialized);
                }
                if self.state == DefaultState::InputSet {
                    let input = self.input.as_deref().ok_or(FrontendError::MissingInput)?;
                    match self.phases.parse(input) {
                        Ok(value) => self.parsing_result = Some(value),
                        Err(errors) => self.errors.extend(errors),
                    }
                    self.state = DefaultState::Parsing;
                }
            }
            Phase::SemanticAnalysis
                if self.state == DefaultState::Parsing && self.errors.is_empty() =>
            {
                let input = self
                    .parsing_result
                    .clone()
                    .ok_or(FrontendError::MissingPhaseResult("parsing"))?;
                match self.phases.analyze(input) {
                    Ok(value) => self.semantic_result = Some(value),
                    Err(errors) => self.errors.extend(errors),
                }
                self.state = DefaultState::SemanticAnalysis;
            }
            Phase::Translation
                if self.state == DefaultState::SemanticAnalysis && self.errors.is_empty() =>
            {
                let input = self
                    .semantic_result
                    .clone()
                    .ok_or(FrontendError::MissingPhaseResult("semantic analysis"))?;
                match self.phases.translate(input) {
                    Ok(value) => self.program = Some(value),
                    Err(errors) => self.errors.extend(errors),
                }
                self.state = DefaultState::Translation;
            }
            Phase::ConsistencyCheck
                if self.state == DefaultState::Translation && self.errors.is_empty() =>
            {
                let program = self
                    .program
                    .clone()
                    .ok_or(FrontendError::MissingPhaseResult("translation"))?;
                match self.phases.check_consistency(program) {
                    Ok(value) => self.program = Some(value),
                    Err(errors) => self.errors.extend(errors),
                }
                self.state = DefaultState::ConsistencyCheck;
            }
            Phase::Verification
                if self.state == DefaultState::ConsistencyCheck && self.errors.is_empty() =>
            {
                let program = self
                    .program
                    .as_ref()
                    .ok_or(FrontendError::MissingPhaseResult("consistency"))?;
                let verifier = self
                    .verifier
                    .as_mut()
                    .ok_or(FrontendError::NotInitialized)?;
                self.verification_result =
                    Some(verifier.verify(program).map_err(FrontendError::Verifier)?);
                self.state = DefaultState::Verification;
            }
            _ => {}
        }
        Ok(())
    }
    pub fn run_range(
        &mut self,
        phases: &[Phase],
        from: Phase,
        to: Phase,
    ) -> Result<(), FrontendError> {
        let first = phases
            .iter()
            .position(|p| *p == from)
            .ok_or(FrontendError::PhaseNotAvailable(from))?;
        let last = phases
            .iter()
            .position(|p| *p == to)
            .ok_or(FrontendError::PhaseNotAvailable(to))?;
        if first <= last {
            for phase in &phases[first..=last] {
                self.run_phase(*phase)?;
            }
        }
        Ok(())
    }
    pub fn result(&self) -> Result<VerificationResult, FrontendError> {
        if !self.errors.is_empty() {
            return Ok(VerificationResult::Failure(self.errors.clone()));
        }
        if self.state < DefaultState::Verification {
            return Err(FrontendError::MissingPhaseResult("verification"));
        }
        self.verification_result
            .clone()
            .ok_or(FrontendError::MissingPhaseResult("verification"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::position::Position;
    use crate::verifier::verification_result::{ParseError, ParseReport};
    use crate::verifier::verifier::NoVerifier;
    struct FailingParser;
    impl FrontendPhases for FailingParser {
        type Parsed = ();
        type Analyzed = ();
        fn parse(&mut self, _: &str) -> Result<(), Vec<AbstractError>> {
            Err(vec![AbstractError::Parse(ParseReport::Error(
                ParseError::new("bad input", Position::NoPosition),
            ))])
        }
        fn analyze(&mut self, _: ()) -> Result<(), Vec<AbstractError>> {
            panic!("analysis must not run after parsing failure")
        }
        fn translate(&mut self, _: ()) -> Result<Program, Vec<AbstractError>> {
            panic!("translation must not run")
        }
        fn check_consistency(&mut self, _: Program) -> Result<Program, Vec<AbstractError>> {
            panic!("consistency must not run")
        }
        fn reset_messages(&mut self) {}
    }
    #[test]
    fn failed_parsing_advances_once_and_stops_later_phases() {
        let mut frontend = DefaultFrontend::new(FailingParser);
        frontend.init(Box::new(NoVerifier::default()));
        frontend
            .reset(Path::new("test.vpr"), |_| Ok("input".into()))
            .unwrap();
        frontend
            .run_range(DEFAULT_PHASES, Phase::Parsing, Phase::Verification)
            .unwrap();
        assert_eq!(frontend.state, DefaultState::Parsing);
        assert!(
            matches!(frontend.result().unwrap(), VerificationResult::Failure(errors) if errors.len() == 1)
        );
    }
}
