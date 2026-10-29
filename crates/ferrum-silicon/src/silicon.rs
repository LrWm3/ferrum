// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

//! Backend lifecycle and verification entry point from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Silicon.scala.
//! Status: lifecycle, backend consistency check, source selection and repeated-run reset
//! implemented over explicit backend services. CLI configuration, threaded timeout/cancellation,
//! result condensation and concrete frontend/runner assembly remain pending services.

use ferrum_silver::ast::{
    program::Program,
    utility::nodes::{Node, TraversalError},
};
use ferrum_silver::cfg::silver::silver_cfg::SilverCfg;
use ferrum_silver::verifier::verification_error::VerificationError;

pub const DUMMY_INPUT_FILENAME: &str =
    "dummy-file-to-prevent-cli-parser-from-complaining-about-missing-file-name.silver";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lifetime {
    Instantiated,
    Configured,
    Started,
    Running,
}
#[derive(Debug)]
pub enum SiliconError<E> {
    InvalidLifetime(Lifetime),
    Consistency(TraversalError),
    Backend(E),
}
#[derive(Debug)]
pub enum SiliconOutcome<R> {
    ConsistencyFailures(Vec<VerificationError>),
    BackendResult(R),
}

/// Implementations own real verifier lifecycle, timeout, error conversion and cleanup.
/// A timed-out or failed run must be represented in Result; it must not become success.
pub trait SiliconBackend {
    type Error;
    type Output;
    fn configure(&mut self, args: &[String]) -> Result<(), Self::Error>;
    fn start(&mut self) -> Result<(), Self::Error>;
    fn reset(&mut self) -> Result<(), Self::Error>;
    fn stop(&mut self) -> Result<(), Self::Error>;
    /// The source emits its start event before consistency checking.
    fn verification_started(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn input_file(&self) -> Option<&str>;
    fn ignore_file(&self) -> bool;
    fn set_recorded_source(&mut self, file: Option<&str>);
    fn render_node(&self, node: &Node) -> Result<String, TraversalError>;
    /// Must run the verifier, sort transformed failures, condense results, apply the configured
    /// timeout/exception rules and clean up its executor even when the run fails.
    fn run(
        &mut self,
        program: &Program,
        cfgs: &[SilverCfg],
        file: Option<&str>,
    ) -> Result<Self::Output, Self::Error>;
}
pub struct Silicon<B: SiliconBackend> {
    backend: B,
    lifetime: Lifetime,
}
impl<B: SiliconBackend> Silicon<B> {
    pub fn new(backend: B) -> Self {
        Self {
            backend,
            lifetime: Lifetime::Instantiated,
        }
    }
    pub fn lifetime(&self) -> Lifetime {
        self.lifetime
    }
    pub fn backend(&self) -> &B {
        &self.backend
    }
    pub fn backend_mut(&mut self) -> &mut B {
        &mut self.backend
    }
    pub fn configure(&mut self, args: &[String]) -> Result<(), SiliconError<B::Error>> {
        if self.lifetime != Lifetime::Instantiated {
            return Err(SiliconError::InvalidLifetime(self.lifetime));
        }
        self.lifetime = Lifetime::Configured;
        self.backend.configure(args).map_err(SiliconError::Backend)
    }
    pub fn start(&mut self) -> Result<(), SiliconError<B::Error>> {
        if self.lifetime != Lifetime::Configured {
            return Err(SiliconError::InvalidLifetime(self.lifetime));
        }
        self.lifetime = Lifetime::Started;
        self.backend.start().map_err(SiliconError::Backend)
    }
    pub fn stop(&mut self) -> Result<(), SiliconError<B::Error>> {
        self.backend.stop().map_err(SiliconError::Backend)
    }
    pub fn verify(
        &mut self,
        program: &Program,
        cfgs: &[SilverCfg],
    ) -> Result<SiliconOutcome<B::Output>, SiliconError<B::Error>> {
        match self.lifetime {
            Lifetime::Instantiated | Lifetime::Configured => {
                return Err(SiliconError::InvalidLifetime(self.lifetime));
            }
            Lifetime::Started => (),
            Lifetime::Running => self.backend.reset().map_err(SiliconError::Backend)?,
        }
        self.lifetime = Lifetime::Running;
        self.backend
            .verification_started()
            .map_err(SiliconError::Backend)?;
        let file = if self.backend.ignore_file() {
            None
        } else {
            self.backend
                .input_file()
                .filter(|f| *f != DUMMY_INPUT_FILENAME)
                .map(str::to_owned)
        };
        self.backend.set_recorded_source(file.as_deref());
        let errors =
            crate::utils::consistency::check(program, &|node| self.backend.render_node(node))
                .map_err(SiliconError::Consistency)?;
        if !errors.is_empty() {
            return Ok(SiliconOutcome::ConsistencyFailures(errors));
        }
        self.backend
            .run(program, cfgs, file.as_deref())
            .map(SiliconOutcome::BackendResult)
            .map_err(SiliconError::Backend)
    }
}
