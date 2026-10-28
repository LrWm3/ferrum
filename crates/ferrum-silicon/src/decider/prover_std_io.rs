//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/ProverStdIO.scala
//!
//! Purpose:
//! Drive an SMT solver process over ordered line-oriented commands.
//!
//! Planned Rust structure:
//! ProverStdIO implements Prover lifecycle, scopes, emit/assume/declare/fresh, settings, assertion
//! modes, satisfiability checks, saturation, models/statistics/unknown reason, and protocol I/O
//! helpers; solver subclasses provide executable and timeouts.
//!
//! Behavior to preserve:
//! Start rejects repeated startup, validates executable and redirects stderr; reset stops and
//! restarts; stop flushes, forcibly destroys process before closing streams, waits up to ten
//! seconds, removes shutdown hook and clears recorded declarations/emits/preamble assumptions.
//! Preserve push/pop depth and response ordering, timeout caching in subclasses, lazy log comments
//! and debug recordings. Push-pop assertions refute negation, retrieve model and unknown reason
//! before pop; soft-constraint assertion uses fresh guard and retrieves model without reason query.
//! sat and unknown both fail assertion while check distinguishes sat/unsat/unknown. Skip/report
//! warning and quantifier-profile lines, reject unexpected success/EOF responses, and preserve
//! model-read error behavior.
//!
//! Integration:
//! decider::{z3_prover_std_io,cvc5_prover_std_io,term_to_smt_lib2_converter},
//! interfaces::decider::prover, state::identifiers and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Child-process cancellation, scope ownership, diagnostic and protocol error APIs.
//!
//! Status: native Unix solver lifecycle, protocol, scopes, assertions and models implemented; full Config/reporter wiring remains. Failure cleanup is explicit.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::common::config::package::Version;
use crate::decider::term_to_smt_lib2_converter::{ConversionError, TermToSmtLib2Converter};
use crate::interfaces::decider::prover::{Prover, ProverLike, SatResult, TextEmitter};
use crate::state::identifiers::{DefaultIdentifierFactory, IdentifierFactory};
use crate::state::terms::{
    ApplicableData, ApplicableKind, ApplicationTarget, Declaration, Sort, Term, TermFactory,
};
use ferrum_silver::utility::common::{PrintWriter, print_writer};
use ferrum_silver::verifier::verification_error::Model;
use std::collections::BTreeMap;
use std::io::{self, BufRead, BufReader, BufWriter, Write};
use std::path::PathBuf;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssertionMode {
    PushPop,
    SoftConstraints,
}
#[derive(Clone, Debug)]
pub struct ProverSettings {
    pub executable: PathBuf,
    pub user_args: Option<String>,
    pub log_file: Option<PathBuf>,
    pub timeout_ms: i32,
    pub time_bounds: bool,
    pub resources_per_millisecond: i32,
    pub assertion_mode: AssertionMode,
    pub debug: bool,
    pub counterexamples: bool,
    pub report_reason_unknown: bool,
    pub disable_nonlinear: bool,
}
impl ProverSettings {
    pub fn new(executable: PathBuf, resources_per_millisecond: i32) -> Self {
        Self {
            executable,
            user_args: None,
            log_file: None,
            timeout_ms: 0,
            time_bounds: false,
            resources_per_millisecond,
            assertion_mode: AssertionMode::PushPop,
            debug: false,
            counterexamples: false,
            report_reason_unknown: false,
            disable_nonlinear: false,
        }
    }
}
#[derive(Clone, Debug)]
pub struct SolverProfile {
    pub name: String,
    pub minimum_version: Version,
    pub maximum_version: Option<Version>,
    pub environment_variable: String,
    pub dependency_url: String,
    pub static_preamble: String,
    pub startup_args: Vec<String>,
    pub seed_options: Vec<String>,
    pub timeout_option: String,
    pub resource_option: String,
    pub supports_disable_nonlinear: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProverEvent {
    Configuration(String),
    Warning(String),
    QuantifierInstances {
        id: String,
        instances: i32,
        generation: i32,
        cost: i32,
    },
}
#[derive(Debug)]
pub enum ProverError {
    Io(io::Error),
    Conversion(ConversionError),
    Protocol { prover_id: String, message: String },
    Model(String),
    InvalidLifecycle(&'static str),
    UnsupportedPlatform,
}
impl std::fmt::Display for ProverError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Io(e) => e.fmt(f),
            Self::Conversion(e) => write!(f, "{e:?}"),
            Self::Protocol { prover_id, message } => write!(
                f,
                "Interaction with prover (instance {prover_id}) failed: {message}"
            ),
            Self::Model(message) => write!(f, "Invalid prover model: {message}"),
            Self::InvalidLifecycle(message) => f.write_str(message),
            Self::UnsupportedPlatform => {
                f.write_str("merged solver stdout/stderr requires the native Unix process adapter")
            }
        }
    }
}
impl std::error::Error for ProverError {}
impl From<io::Error> for ProverError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}
impl From<ConversionError> for ProverError {
    fn from(e: ConversionError) -> Self {
        Self::Conversion(e)
    }
}

/// A safe cross-thread handle to terminate the currently running stdio solver.
/// It never owns the solver's I/O streams and becomes inactive after stop; after
/// reset the same handle refers to the newly started child.
/// Coordinate cancellation with start/reset: a child that has not yet been installed
/// cannot be interrupted through this handle.
#[derive(Clone)]
pub struct StdioCancellationHandle(Arc<Mutex<Option<Child>>>);
impl StdioCancellationHandle {
    /// Terminate the child if currently running, returning whether it was interrupted.
    /// Cancellation invalidates the solver session; callers must not reuse it without reset.
    pub fn cancel(&self) -> io::Result<bool> {
        let mut child = self.0.lock().unwrap_or_else(|error| error.into_inner());
        match child.as_mut() {
            Some(child) => {
                if child.try_wait()?.is_some() {
                    return Ok(false);
                }
                if let Err(error) = child.kill() {
                    // The process can exit between try_wait and kill. Preserve a
                    // real kill failure unless a second wait confirms its exit.
                    if !matches!(child.try_wait(), Ok(Some(_))) {
                        return Err(error);
                    }
                    return Ok(false);
                }
                Ok(true)
            }
            None => Ok(false),
        }
    }
}
/// Owns one solver process. No streams or mutable solver scopes are shared between workers.
pub struct ProverStdIo {
    pub unique_id: String,
    pub settings: ProverSettings,
    pub profile: SolverProfile,
    pub converter: TermToSmtLib2Converter,
    factory: TermFactory,
    identifiers: DefaultIdentifierFactory,
    report: Box<dyn FnMut(ProverEvent) + Send>,
    child: Arc<Mutex<Option<Child>>>,
    input: Option<BufReader<std::fs::File>>,
    output: Option<BufWriter<ChildStdin>>,
    log: Option<PrintWriter>,
    scope_depth: usize,
    last_timeout: i32,
    last_model: Option<String>,
    last_reason_unknown: Option<String>,
    declarations: Vec<Declaration>,
    emits: Vec<String>,
    pub preamble_assumptions: Vec<(String, InsertionOrderedSet<Term>)>,
}
impl ProverStdIo {
    /// Obtain a handle which may interrupt a blocking solver read from another thread.
    pub fn cancellation_handle(&self) -> StdioCancellationHandle {
        StdioCancellationHandle(self.child.clone())
    }
    /// Share the source verifier's identifier stream with its prover.
    pub fn identifier_factory(&self) -> DefaultIdentifierFactory {
        self.identifiers.clone()
    }
    pub fn new(
        unique_id: String,
        settings: ProverSettings,
        profile: SolverProfile,
        factory: TermFactory,
        report: impl FnMut(ProverEvent) + Send + 'static,
    ) -> Self {
        Self {
            identifiers: DefaultIdentifierFactory::new(unique_id.clone()),
            converter: TermToSmtLib2Converter::new(factory.clone()),
            factory,
            unique_id,
            settings,
            profile,
            report: Box::new(report),
            child: Arc::new(Mutex::new(None)),
            input: None,
            output: None,
            log: None,
            scope_depth: 0,
            last_timeout: -1,
            last_model: None,
            last_reason_unknown: None,
            declarations: Vec::new(),
            emits: Vec::new(),
            preamble_assumptions: Vec::new(),
        }
    }
    fn protocol(&self, message: impl Into<String>) -> ProverError {
        ProverError::Protocol {
            prover_id: self.unique_id.clone(),
            message: message.into(),
        }
    }
    pub fn write_line(&mut self, line: &str) -> Result<(), ProverError> {
        if let Some(log) = &mut self.log {
            log.println(line)?;
        }
        let output = self
            .output
            .as_mut()
            .ok_or(ProverError::InvalidLifecycle("prover is not started"))?;
        writeln!(output, "{line}")?;
        output.flush()?;
        Ok(())
    }
    fn raw_line(&mut self) -> Result<String, ProverError> {
        let input = self
            .input
            .as_mut()
            .ok_or(ProverError::InvalidLifecycle("prover is not started"))?;
        let mut line = String::new();
        if input.read_line(&mut line)? == 0 {
            return Err(self.protocol("solver closed its output stream"));
        }
        if line.ends_with('\n') {
            line.pop();
        }
        if line.ends_with('\r') {
            line.pop();
        }
        Ok(line)
    }
    fn log_comment(&mut self, text: &str) -> Result<(), ProverError> {
        if let Some(log) = &mut self.log {
            log.println(&format!(
                "; {}",
                text.replace('\r', "").replace('\n', "\n; ")
            ))?;
        }
        Ok(())
    }
    pub fn read_line(&mut self) -> Result<String, ProverError> {
        loop {
            let line = self.raw_line()?;
            if !line.eq_ignore_ascii_case("success") {
                self.log_comment(&line)?;
            }
            if line.starts_with("WARNING") {
                (self.report)(ProverEvent::Warning(format!("Prover warning: {line}")));
                continue;
            }
            if let Some(body) = line.strip_prefix("[quantifier_instances]") {
                let parts: Vec<_> = body.split(':').map(str::trim).collect();
                if parts.len() != 4 {
                    (self.report)(ProverEvent::Warning(format!(
                        "Invalid quantifier instances line from prover: {line}"
                    )));
                } else {
                    let parse = |s: &str| {
                        s.parse::<i32>()
                            .map_err(|_| self.protocol(format!("invalid quantifier count: {s}")))
                    };
                    let event = ProverEvent::QuantifierInstances {
                        id: parts[0].into(),
                        instances: parse(parts[1])?,
                        generation: parse(parts[2])?,
                        cost: parse(parts[3])?,
                    };
                    (self.report)(event);
                }
                continue;
            }
            return Ok(line);
        }
    }
    pub fn read_success(&mut self) -> Result<(), ProverError> {
        let line = self.read_line()?;
        if line == "success" {
            Ok(())
        } else {
            Err(self.protocol(format!("expected success, received {line}")))
        }
    }
    fn read_sat(&mut self) -> Result<SatResult, ProverError> {
        match self.read_line()?.as_str() {
            "sat" => Ok(SatResult::Sat),
            "unsat" => Ok(SatResult::Unsat),
            "unknown" => Ok(SatResult::Unknown),
            other => {
                Err(self.protocol(format!("expected satisfiability result, received {other}")))
            }
        }
    }
    pub fn set_timeout(&mut self, timeout: Option<i32>) -> Result<(), ProverError> {
        let effective = timeout.unwrap_or(self.settings.timeout_ms);
        if effective != self.last_timeout {
            self.last_timeout = effective;
            let (option, value) = if self.settings.time_bounds {
                (&self.profile.timeout_option, effective)
            } else {
                (
                    &self.profile.resource_option,
                    effective.wrapping_mul(self.settings.resources_per_millisecond),
                )
            };
            self.write_line(&format!("(set-option :{option} {value})"))?;
            self.read_success()?;
        }
        Ok(())
    }
    pub fn assume_text(&mut self, term: &str) -> Result<(), ProverError> {
        self.write_line(&format!("(assert {term})"))?;
        self.read_success()
    }
    fn retrieve_model(&mut self) -> Result<(), ProverError> {
        if self.settings.counterexamples {
            self.write_line("(get-model)")?;
            let mut result = String::new();
            let mut first = true;
            loop {
                let line = self.raw_line()?;
                let done = line.trim().ends_with('"') || (first && !line.starts_with('"'));
                result.push('\n');
                result.push_str(&line);
                first = false;
                if done {
                    break;
                }
            }
            let mut result = result.trim().to_owned();
            if result.starts_with('"') {
                result = result.replace('"', "");
            }
            self.last_model = Some(result);
        }
        Ok(())
    }
    fn retrieve_reason(&mut self) -> Result<(), ProverError> {
        if self.settings.report_reason_unknown {
            self.write_line("(get-info :reason-unknown)")?;
            let line = self.read_line()?;
            let body = line
                .strip_prefix("(:reason-unknown \"")
                .and_then(|x| x.strip_suffix("\")"))
                .unwrap_or(&line);
            self.last_reason_unknown = Some(body.into());
        }
        Ok(())
    }
    pub fn assert_text(&mut self, goal: &str, timeout: Option<i32>) -> Result<bool, ProverError> {
        let started = Instant::now();
        let result = match self.settings.assertion_mode {
            AssertionMode::PushPop => {
                self.push(1, None)?;
                let result = (|| {
                    self.set_timeout(timeout)?;
                    self.assume_text(&format!("(not {goal})"))?;
                    self.write_line("(check-sat)")?;
                    let proved = self.read_sat()? == SatResult::Unsat;
                    if !proved {
                        self.retrieve_model()?;
                        self.retrieve_reason()?;
                    }
                    Ok(proved)
                })();
                // Restore the scope even on a failed query; preserve the original error.
                let pop = self.pop(1);
                match result {
                    Err(e) => Err(e),
                    Ok(v) => pop.map(|()| v),
                }
            }
            AssertionMode::SoftConstraints => {
                self.set_timeout(timeout)?;
                let guard = self.fresh("grd", &[], &Sort::Bool)?;
                let guard = match guard {
                    ApplicationTarget::Function(f) => self.factory.app(f, vec![]),
                    ApplicationTarget::Variable(v) => v,
                };
                let guard = self.converter.convert_term(&guard)?;
                self.assume_text(&format!("(=> {guard} (not {goal}))"))?;
                self.write_line(&format!("(check-sat {guard})"))?;
                let proved = self.read_sat()? == SatResult::Unsat;
                if !proved {
                    self.retrieve_model()?;
                }
                Ok(proved)
            }
        }?;
        self.log_comment(&format!("{}ms", started.elapsed().as_millis()))?;
        self.log_comment("(get-info :all-statistics)")?;
        Ok(result)
    }
}
impl TextEmitter for ProverStdIo {
    type Error = ProverError;
    fn emit(&mut self, content: &str) -> Result<(), Self::Error> {
        if self.settings.debug {
            self.emits.push(content.into());
        }
        self.write_line(content)?;
        self.read_success()
    }
    fn emit_settings(&mut self, contents: &[String]) -> Result<(), Self::Error> {
        self.emit_all(contents)?;
        if self.profile.supports_disable_nonlinear && self.settings.disable_nonlinear {
            self.log_comment("We disable non-linear integer arithmetic")?;
            self.write_line("(set-option :smt.arith.nl false)")?;
            self.read_success()?;
        }
        Ok(())
    }
}
impl ProverLike for ProverStdIo {
    fn assume_axioms(
        &mut self,
        terms: &InsertionOrderedSet<Term>,
        description: &str,
    ) -> Result<(), Self::Error> {
        if self.settings.debug {
            self.preamble_assumptions
                .push((description.into(), terms.clone()));
        }
        for term in terms.iter() {
            self.assume(term)?;
        }
        Ok(())
    }
    fn set_option(&mut self, name: &str, value: &str) -> Result<String, Self::Error> {
        self.write_line(&format!("(get-option :{name})"))?;
        let old = self.read_line()?;
        if old == "unsupported" {
            return Err(self.protocol(format!("unsupported option {name}")));
        }
        self.emit(&format!("(set-option :{name} {value})"))?;
        Ok(old)
    }
    fn assume(&mut self, term: &Term) -> Result<(), Self::Error> {
        let text = self.converter.convert_term(term)?;
        self.assume_text(&text)
    }
    fn declare(&mut self, declaration: &Declaration) -> Result<(), Self::Error> {
        let text = self.converter.convert_declaration(declaration)?;
        if self.settings.debug {
            self.declarations.push(declaration.clone());
        }
        self.emit(&text)
    }
    fn comment(&mut self, content: &mut dyn FnMut() -> String) -> Result<(), Self::Error> {
        if self.log.is_some() {
            self.log_comment(&content())?;
        }
        Ok(())
    }
    fn saturate(&mut self, timeout: i32, comment: &str) -> Result<(), Self::Error> {
        self.log_comment(&format!("State saturation: {comment}"))?;
        self.set_timeout(Some(timeout))?;
        self.write_line("(check-sat)")?;
        self.read_line()?;
        Ok(())
    }
}
impl Prover for ProverStdIo {
    type Version = Version;
    fn start(&mut self, user_args: Option<&str>) -> Result<(), Self::Error> {
        if self
            .child
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .is_some()
        {
            return Err(ProverError::InvalidLifecycle(
                "stop must be called between starts",
            ));
        }
        self.scope_depth = 0;
        self.last_timeout = -1;
        self.log = self
            .settings
            .log_file
            .as_ref()
            .map(|file| print_writer(file, true, false))
            .transpose()?;
        if !self.settings.executable.is_file() {
            return Err(self.protocol(format!(
                "prover path is not a file: {}",
                self.settings.executable.display()
            )));
        }
        (self.report)(ProverEvent::Configuration(format!(
            "Starting prover at location '{}'",
            self.settings.executable.display()
        )));
        let mut command = Command::new(&self.settings.executable);
        command
            .args(&self.profile.startup_args)
            .stdin(Stdio::piped());
        if let Some(args) = user_args {
            (self.report)(ProverEvent::Configuration(format!(
                "Additional command-line arguments are {args}"
            )));
            // Source splits literal spaces, keeps internal empty fields and trims each argument.
            command.args(args.split_terminator(' ').map(str::trim));
        }
        #[cfg(unix)]
        {
            use std::os::fd::OwnedFd;
            let (reader, writer) = std::os::unix::net::UnixStream::pair()?;
            let stderr: OwnedFd = writer.try_clone()?.into();
            let stdout: OwnedFd = writer.into();
            command
                .stdout(Stdio::from(stdout))
                .stderr(Stdio::from(stderr));
            let mut child = command.spawn()?;
            self.output = child.stdin.take().map(BufWriter::new);
            let reader: OwnedFd = reader.into();
            self.input = Some(BufReader::new(std::fs::File::from(reader)));
            *self.child.lock().unwrap_or_else(|error| error.into_inner()) = Some(child);
            Ok(())
        }
        #[cfg(not(unix))]
        {
            Err(ProverError::UnsupportedPlatform)
        }
    }
    fn reset(&mut self) -> Result<(), Self::Error> {
        self.stop()?;
        let args = self.settings.user_args.clone();
        self.start(args.as_deref())
    }
    fn stop(&mut self) -> Result<(), Self::Error> {
        let mut failure = None;
        if let Some(output) = &mut self.output {
            if let Err(e) = output.flush() {
                failure = Some(e);
            }
        }
        if let Some(log) = &mut self.log {
            if let Err(e) = log.flush() {
                if failure.is_none() {
                    failure = Some(e);
                }
            }
        }
        let child = self
            .child
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .take();
        if let Some(mut child) = child {
            if let Err(e) = child.kill() {
                if e.kind() != io::ErrorKind::InvalidInput && failure.is_none() {
                    failure = Some(e);
                }
            }
            let limit = Instant::now() + Duration::from_secs(10);
            loop {
                match child.try_wait() {
                    Ok(Some(_)) => break,
                    Ok(None) if Instant::now() < limit => {
                        std::thread::sleep(Duration::from_millis(10))
                    }
                    Ok(None) => {
                        if failure.is_none() {
                            failure = Some(io::Error::new(
                                io::ErrorKind::TimedOut,
                                "solver did not stop",
                            ));
                        }
                        break;
                    }
                    Err(e) => {
                        if failure.is_none() {
                            failure = Some(e);
                        }
                        break;
                    }
                }
            }
        }
        self.input = None;
        self.output = None;
        self.log = None;
        self.declarations.clear();
        self.emits.clear();
        self.preamble_assumptions.clear();
        failure.map_or(Ok(()), |e| Err(e.into()))
    }
    fn assert_goal(&mut self, goal: &Term, timeout: Option<i32>) -> Result<bool, Self::Error> {
        let text = self.converter.convert_term(goal)?;
        self.assert_text(&text, timeout)
    }
    fn check(&mut self, timeout: Option<i32>) -> Result<SatResult, Self::Error> {
        self.set_timeout(timeout)?;
        self.write_line("(check-sat)")?;
        self.read_sat()
    }
    fn fresh(
        &mut self,
        name: &str,
        arg_sorts: &[Sort],
        result_sort: &Sort,
    ) -> Result<ApplicationTarget, Self::Error> {
        let fun = self.factory.applicable(ApplicableData {
            kind: ApplicableKind::Fun,
            id: self.identifiers.fresh(name),
            arg_sorts: arg_sorts.to_vec(),
            result_sort: result_sort.clone(),
        });
        let decl = self.factory.function_decl(fun.clone());
        let text = self.converter.convert_declaration(&decl)?;
        self.emit(&text)?;
        Ok(ApplicationTarget::Function(fun))
    }
    fn statistics(&mut self) -> Result<Vec<(String, String)>, Self::Error> {
        self.write_line("(get-info :all-statistics)")?;
        let pattern = regex::Regex::new(r"\A\(?\s*:([A-za-z\-]+)\s+((?:[0-9]+\.)?[0-9]+)\)?\z")
            .expect("static statistic pattern");
        let mut stats = BTreeMap::new();
        loop {
            let line = self.raw_line()?;
            self.log_comment(&line)?;
            // Preserve upstream's conjunction (not a strengthened prefix rejection).
            if line.is_empty() && !line.starts_with("(:") {
                return Err(self.protocol("empty statistics line"));
            }
            if let Some(entry) = pattern.captures(&line) {
                stats.insert(entry[1].into(), entry[2].into());
            }
            if line.ends_with(')') {
                break;
            }
        }
        Ok(stats.into_iter().collect())
    }
    fn has_model(&self) -> bool {
        self.last_model.is_some()
    }
    fn is_model_valid(&self) -> bool {
        self.last_model
            .as_ref()
            .is_some_and(|x| !x.contains("model is not available"))
    }
    fn get_model(&mut self) -> Result<Model, Self::Error> {
        let text = self
            .last_model
            .as_deref()
            .ok_or_else(|| self.protocol("no last model"))?;
        Model::parse(text).map_err(|e| ProverError::Model(format!("{e:?}")))
    }
    fn get_reason_unknown(&mut self) -> Result<Option<String>, Self::Error> {
        Ok(self.last_reason_unknown.clone())
    }
    fn clear_last_assert(&mut self) {
        self.last_model = None;
        self.last_reason_unknown = None;
    }
    fn name(&self) -> &str {
        &self.profile.name
    }
    fn min_version(&self) -> Version {
        self.profile.minimum_version.clone()
    }
    fn max_version(&self) -> Option<Version> {
        self.profile.maximum_version.clone()
    }
    fn version(&mut self) -> Result<Version, Self::Error> {
        self.write_line("(get-info :version)")?;
        let line = self.raw_line()?;
        self.log_comment(&line)?;
        let pattern = regex::Regex::new(r#"\A\(?\s*:version\s+"(.*?)(?:\s*-.*?)?"\)?\z"#)
            .expect("static version pattern");
        let captures = pattern
            .captures(&line)
            .ok_or_else(|| self.protocol(format!("unexpected version: {line}")))?;
        Ok(Version::new(&captures[1]))
    }
    fn static_preamble(&self) -> &str {
        &self.profile.static_preamble
    }
    fn randomize_seeds_options(&self) -> &[String] {
        &self.profile.seed_options
    }
    fn push_pop_scope_depth(&self) -> usize {
        self.scope_depth
    }
    fn push(&mut self, n: usize, timeout: Option<i32>) -> Result<(), Self::Error> {
        self.set_timeout(timeout)?;
        self.scope_depth = self
            .scope_depth
            .checked_add(n)
            .ok_or_else(|| self.protocol("scope depth overflow"))?;
        let command = if n == 1 {
            "(push)".into()
        } else {
            format!("(push {n})")
        };
        self.write_line(&format!("{command} ; {}", self.scope_depth))?;
        self.read_success()
    }
    fn pop(&mut self, n: usize) -> Result<(), Self::Error> {
        let before = self.scope_depth;
        self.scope_depth = self
            .scope_depth
            .checked_sub(n)
            .ok_or_else(|| self.protocol("scope underflow"))?;
        let command = if n == 1 {
            "(pop)".into()
        } else {
            format!("(pop {n})")
        };
        self.write_line(&format!("{command} ; {before}"))?;
        self.read_success()
    }
    fn all_declarations(&self) -> Vec<Declaration> {
        self.declarations.clone()
    }
    fn all_emits(&self) -> Vec<String> {
        self.emits.clone()
    }
}
impl Drop for ProverStdIo {
    fn drop(&mut self) {
        let _ = self.stop();
    }
}

#[cfg(all(test, unix))]
mod cancellation_tests {
    use super::*;
    use crate::state::terms::TermOptions;
    use std::os::unix::fs::PermissionsExt;

    #[test]
    fn stdio_soft_assertion_reason_remains_absent() {
        use crate::interfaces::decider::prover::Prover;
        let Ok(path) = std::env::var("FERRUM_TEST_Z3") else {
            return;
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        for mode in [AssertionMode::PushPop, AssertionMode::SoftConstraints] {
            let mut settings = ProverSettings::new(path.clone().into(), 10000);
            settings.assertion_mode = mode;
            settings.report_reason_unknown = true;
            let mut prover = crate::decider::z3_prover_std_io::new(
                "reason".into(),
                settings,
                factory.clone(),
                |_| {},
            );
            prover.start(None).unwrap();
            prover
                .write_line("(set-option :print-success true)")
                .unwrap();
            prover.read_success().unwrap();
            assert_eq!(prover.get_reason_unknown().unwrap(), None);
            assert!(!prover.assert_goal(&factory.boolean(false), None).unwrap());
            let reason = prover.get_reason_unknown().unwrap();
            assert_eq!(reason.is_some(), mode == AssertionMode::PushPop);
            if mode == AssertionMode::SoftConstraints {
                prover.last_reason_unknown = Some("prior".into());
                assert!(!prover.assert_goal(&factory.boolean(false), None).unwrap());
                assert_eq!(
                    prover.get_reason_unknown().unwrap().as_deref(),
                    Some("prior")
                );
            }
            prover.clear_last_assert();
            assert_eq!(prover.get_reason_unknown().unwrap(), None);
            prover.stop().unwrap();
        }
    }

    #[test]
    fn cancellation_unblocks_a_solver_read_and_cleanup_reaps_child() {
        let script =
            std::env::temp_dir().join(format!("ferrum-blocked-solver-{}", std::process::id()));
        std::fs::write(&script, "#!/bin/sh\nexec /bin/sleep 60\n").unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o700)).unwrap();
        let path = script.clone();
        let (sender, receiver) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            let factory = TermFactory::new(TermOptions {
                use_flyweight: false,
                use_old_axiomatization: false,
                mask_heap_mode: false,
            });
            let mut prover = crate::decider::z3_prover_std_io::new(
                "blocked".into(),
                ProverSettings::new(path, 10000),
                factory,
                |_| {},
            );
            prover.start(None).unwrap();
            sender.send(prover.cancellation_handle()).unwrap();
            let read = prover.read_line();
            let stopped = prover.stop();
            (read, stopped)
        });
        let handle = receiver.recv().unwrap();
        assert!(handle.cancel().unwrap());
        let (read, stopped) = worker.join().unwrap();
        assert!(read.is_err());
        stopped.unwrap();
        assert!(!handle.cancel().unwrap());
        std::fs::remove_file(script).unwrap();
    }
}
