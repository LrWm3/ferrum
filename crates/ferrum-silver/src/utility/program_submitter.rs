//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/ProgramSubmitter.scala
//!
//! Purpose:
//! Optionally submit program and verification metrics to the upstream collection service.
//!
//! Planned Rust structure:
//! Port ProgramSubmitter, ManualProgramSubmitter, FEProgramSubmitter, FileProgramSubmitter and
//! ViperProgramSubmitter; retain setters, formatting and runtime calculation.
//!
//! Behavior to preserve:
//! Submit only when enabled and host nonempty; send program, frontend, args, verifier, success
//! and runtime; catch submission failure. Frontend args filter submission flag and .vpr
//! filenames; file reading failures yield empty text; only Success counts as success.
//!
//! Integration:
//! frontend::sil_frontend, ast::pretty::pretty_printer and verifier::verification_result.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Choose native HTTP/configuration and source ownership with frontend; preserve opt-in behavior.
//!
//! Status: partial; submission data, filtering, opt-in and manual/frontend metrics implemented.
//! Native HTTP transport, JSON encoding and AST pretty-printer integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use crate::ast::program::Program;
use crate::verifier::verification_result::VerificationResult;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

pub const API_HOST: &str = "http://viper-server.inf.ethz.ch:10000";
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Submission {
    pub program: String,
    pub frontend: String,
    pub args: Vec<String>,
    pub original_verifier: String,
    pub success: bool,
    pub runtime: i64,
}
/// Transport injection supplies the native HTTP/JSON implementation at integration time.
pub trait SubmissionTransport {
    type Error;
    fn post(&self, url: &str, submission: &Submission) -> Result<(), Self::Error>;
}
/// Construct and send only when enabled; submission errors retain the source's printed warning.
pub fn submit<T: SubmissionTransport>(
    allow: bool,
    payload: impl FnOnce() -> Submission,
    transport: &T,
) {
    if !API_HOST.is_empty() && allow {
        let submission = payload();
        if transport
            .post(&format!("{API_HOST}/submit-program"), &submission)
            .is_err()
        {
            println!("Program couldn't be submitted");
        }
    }
}
pub fn did_ver_succeed(result: Option<&VerificationResult>) -> bool {
    matches!(result, Some(VerificationResult::Success))
}
fn now_millis() -> i64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_millis() as i64,
        Err(error) => -(error.duration().as_millis() as i64),
    }
}
#[derive(Clone, Debug)]
pub struct ManualProgramSubmitter {
    pub allow_submission: bool,
    pub program: String,
    pub original_frontend: String,
    pub original_verifier: String,
    pub args: Vec<String>,
    pub succeeded: bool,
    start_time: i64,
}
impl ManualProgramSubmitter {
    pub fn new(
        allow_submission: bool,
        program: String,
        original_frontend: String,
        original_verifier: String,
        args: Vec<String>,
    ) -> Self {
        Self {
            allow_submission,
            program,
            original_frontend,
            original_verifier,
            args,
            succeeded: false,
            start_time: now_millis(),
        }
    }
    pub fn runtime(&self) -> i64 {
        now_millis().wrapping_sub(self.start_time)
    }
    pub fn set_program_ast(&mut self, program: &Program, pretty: impl FnOnce(&Program) -> String) {
        self.program = pretty(program);
    }
    pub fn submission(&self) -> Submission {
        Submission {
            program: self.program.clone(),
            frontend: self.original_frontend.clone(),
            args: self.args.clone(),
            original_verifier: self.original_verifier.clone(),
            success: self.succeeded,
            runtime: self.runtime(),
        }
    }
    pub fn submit<T: SubmissionTransport>(&self, transport: &T) {
        submit(self.allow_submission, || self.submission(), transport);
    }
}
/// Frontend-derived metrics; integration supplies current frontend values on each submission.
pub trait FrontendMetrics {
    fn allow_submission(&self) -> bool;
    fn verifier_name(&self) -> &str;
    fn verification_result(&self) -> Option<&VerificationResult>;
    fn runtime(&self) -> i64;
}
#[derive(Clone, Debug, Default)]
pub struct FrontendSubmissionArgs {
    pub args: Vec<String>,
    pub program_path: PathBuf,
}
impl FrontendSubmissionArgs {
    pub fn set_args(&mut self, args: &[String]) {
        self.program_path = args
            .iter()
            .find(|arg| arg.ends_with(".vpr"))
            .map(PathBuf::from)
            .unwrap_or_default();
        self.args = args
            .iter()
            .filter(|arg| *arg != "--submitForEvaluation" && !arg.ends_with(".vpr"))
            .cloned()
            .collect();
    }
    pub fn file_content(&self) -> String {
        std::fs::read_to_string(&self.program_path).unwrap_or_default()
    }
    pub fn submission(&self, frontend: &impl FrontendMetrics, program: String) -> Submission {
        let mut chars = frontend.verifier_name().chars();
        let verifier: String = chars
            .next()
            .map(|c| c.to_uppercase().chain(chars).collect())
            .unwrap_or_default();
        Submission {
            program,
            frontend: verifier.clone(),
            args: self.args.clone(),
            original_verifier: verifier,
            success: did_ver_succeed(frontend.verification_result()),
            runtime: frontend.runtime(),
        }
    }
}
