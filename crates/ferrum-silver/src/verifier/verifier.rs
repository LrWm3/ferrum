//! Verifier lifecycle and dependency interfaces.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/Verifier.scala
//! Status: implemented interface and NoVerifier. Backends determine their own lifecycle policy.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2021 ETH Zurich.

use super::verification_result::VerificationResult;
use crate::ast::program::Program;
use crate::components::components::LifetimeComponent;
use crate::reporter::reporter::{NoopReporter, Reporter};
use std::any::Any;

/// A failure to execute the verifier itself, separate from verification failure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifierError {
    /// The source NoVerifier deliberately leaves verification unimplemented.
    NoVerifierCalled,
    Backend(String),
}

pub trait Dependency {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn location(&self) -> &str;
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct DefaultDependency {
    pub name: String,
    pub version: String,
    pub location: String,
}
impl Dependency for DefaultDependency {
    fn name(&self) -> &str {
        &self.name
    }
    fn version(&self) -> &str {
        &self.version
    }
    fn location(&self) -> &str {
        &self.location
    }
}

/// Argument and debug setup precede verification; implementations enforce their own protocol.
pub trait Verifier: LifetimeComponent {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn build_version(&self) -> &str;
    fn copyright(&self) -> &str;
    fn signature(&self) -> String {
        format!("{} {}", self.name(), self.version())
    }
    fn debug_info(&mut self, info: Vec<(String, Box<dyn Any + Send + Sync>)>);
    fn dependencies(&self) -> Vec<&dyn Dependency>;
    fn parse_command_line(&mut self, args: &[String]);
    fn verify(&mut self, program: &Program) -> Result<VerificationResult, VerifierError>;
    fn reporter(&self) -> &dyn Reporter;
    /// Fallible lifecycle seam for native backends; the source lifecycle interface is infallible.
    fn try_stop(&mut self) -> Result<(), VerifierError> {
        self.stop();
        Ok(())
    }
}

#[derive(Default)]
pub struct NoVerifier {
    reporter: NoopReporter,
}
impl LifetimeComponent for NoVerifier {
    fn start(&mut self) {}
    fn stop(&mut self) {}
}
impl Verifier for NoVerifier {
    fn name(&self) -> &str {
        "noverifier"
    }
    fn version(&self) -> &str {
        "0.0.0"
    }
    fn build_version(&self) -> &str {
        ""
    }
    fn copyright(&self) -> &str {
        ""
    }
    fn debug_info(&mut self, _: Vec<(String, Box<dyn Any + Send + Sync>)>) {}
    fn dependencies(&self) -> Vec<&dyn Dependency> {
        Vec::new()
    }
    fn parse_command_line(&mut self, _: &[String]) {}
    fn verify(&mut self, _: &Program) -> Result<VerificationResult, VerifierError> {
        Err(VerifierError::NoVerifierCalled)
    }
    fn reporter(&self) -> &dyn Reporter {
        &self.reporter
    }
}
