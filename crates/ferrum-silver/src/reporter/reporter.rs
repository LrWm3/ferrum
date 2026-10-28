//! Port plan: Dispatch structured messages to configured sinks.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/reporter/Reporter.scala
//!
//! Purpose:
//! Dispatch structured messages to configured sinks.
//!
//! Planned Rust structure:
//! Reporter, NoopReporter, ConfigurableReporter, PluginAwareReporter, CSVReporter, StdIOReporter
//! and PollingReporter.
//!
//! Behavior to preserve:
//! Plugin-aware report maps entity successes/failures through plugins before dispatch, but leaves
//! overall results alone. CSV appends and flushes per report, escaping multiline verifier state;
//! stdout has timeInfo and reportPartialResults branches, warning and exception handling. Polling
//! enqueue and pass-through happen under synchronization; dequeue on empty is an error.
//!
//! Integration:
//! reporter::{message,format}, frontend::sil_frontend, plugin manager and verifier results.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile sink lifetimes, synchronized queue and plugin callback ordering with frontend and
//! Silicon reporting.
//!
//! Status: partial; lifecycle, warnings, entity results, trigger and verifier-state rendering,
//! polling and source fallback for statistics, outlines, definitions and CSV traces are implemented.
//! Captured exception details render through an explicit origin payload; parse-program and
//! runtime-collection fallback strings still require retained provenance.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::message::Message;
use super::package::Entity;
use crate::verifier::verification_result::{DiagnosticError, VerificationResult};
use std::collections::VecDeque;
use std::io::{self, Write};
use std::sync::{Arc, Mutex, RwLock};

#[derive(Debug)]
pub enum ReportError {
    Io(io::Error),
    Diagnostic(DiagnosticError),
    EmptyQueue,
    Plugin(String),
    Print(crate::ast::pretty::pretty_printer::PrintError),
    Unsupported(&'static str),
}
impl From<io::Error> for ReportError {
    fn from(value: io::Error) -> Self {
        Self::Io(value)
    }
}
impl From<DiagnosticError> for ReportError {
    fn from(value: DiagnosticError) -> Self {
        Self::Diagnostic(value)
    }
}
impl From<crate::ast::pretty::pretty_printer::PrintError> for ReportError {
    fn from(value: crate::ast::pretty::pretty_printer::PrintError) -> Self {
        Self::Print(value)
    }
}

pub trait Reporter: Send + Sync {
    fn name(&self) -> &str;
    fn report(&self, message: Message) -> Result<(), ReportError>;
    /// Bind the manager only for reporters that transform entity results.
    fn bind_plugin_manager(
        &self,
        _manager: &crate::plugin::silver_plugin_manager::SilverPluginManager,
    ) -> Result<(), ReportError> {
        Ok(())
    }
    /// Called by a configured Silver frontend reset; most reporters ignore configuration.
    fn set_config(
        &self,
        _config: Option<&crate::frontend::sil_front_end_config::SilFrontendConfig>,
    ) -> Result<(), ReportError> {
        Ok(())
    }
}
#[derive(Default)]
pub struct NoopReporter;
impl Reporter for NoopReporter {
    fn name(&self) -> &str {
        "NoopReporter"
    }
    fn report(&self, _: Message) -> Result<(), ReportError> {
        Ok(())
    }
}
/// Plugin result mapping is invoked only for entity success and failure, never overall results.
pub trait EntityResultMapper: Send + Sync {
    fn map_entity_result(
        &self,
        entity: &Entity,
        result: VerificationResult,
    ) -> Result<VerificationResult, ReportError>;
}
impl<F> EntityResultMapper for F
where
    F: Fn(&Entity, VerificationResult) -> Result<VerificationResult, ReportError> + Send + Sync,
{
    fn map_entity_result(
        &self,
        entity: &Entity,
        result: VerificationResult,
    ) -> Result<VerificationResult, ReportError> {
        self(entity, result)
    }
}
type MapperSlot = RwLock<Option<Arc<dyn EntityResultMapper>>>;
fn bind_mapper(
    slot: &MapperSlot,
    manager: &crate::plugin::silver_plugin_manager::SilverPluginManager,
) -> Result<(), ReportError> {
    let mapper = manager.shared_entity_mapper()?;
    *slot.write().expect("poisoned reporter plugin lock") = Some(mapper);
    Ok(())
}
fn map_entity_message(mapper_lock: &MapperSlot, message: Message) -> Result<Message, ReportError> {
    let mapper = mapper_lock
        .read()
        .expect("poisoned reporter plugin lock")
        .clone();
    Ok(if let Some(mapper) = mapper {
        match message {
            Message::EntitySuccess {
                verifier,
                concerning,
                time,
                cached,
            } => {
                let result = mapper.map_entity_result(&concerning, VerificationResult::Success)?;
                Message::entity_result(verifier, concerning, time, result, cached)
            }
            Message::EntityFailure {
                verifier,
                concerning,
                time,
                errors,
                cached,
            } => {
                let result =
                    mapper.map_entity_result(&concerning, VerificationResult::Failure(errors))?;
                Message::entity_result(verifier, concerning, time, result, cached)
            }
            other => other,
        }
    } else {
        message
    })
}
pub struct PluginAwareReporter {
    pub name: String,
    pub target: Arc<dyn Reporter>,
    pub mapper: RwLock<Option<Arc<dyn EntityResultMapper>>>,
}
impl Reporter for PluginAwareReporter {
    fn bind_plugin_manager(
        &self,
        manager: &crate::plugin::silver_plugin_manager::SilverPluginManager,
    ) -> Result<(), ReportError> {
        bind_mapper(&self.mapper, manager)
    }
    fn name(&self) -> &str {
        &self.name
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        let message = map_entity_message(&self.mapper, message)?;
        self.target.report(message)
    }
}
/// Queue insertion and pass-through execute while holding the same lock, matching source ordering.
pub struct PollingReporter {
    pub name: String,
    pub pass_through: Arc<dyn Reporter>,
    messages: Mutex<VecDeque<Message>>,
    mapper: MapperSlot,
}
impl PollingReporter {
    pub fn new(pass_through: Arc<dyn Reporter>) -> Self {
        Self {
            name: "polling_reporter".into(),
            pass_through,
            messages: Mutex::new(VecDeque::new()),
            mapper: RwLock::new(None),
        }
    }
    pub fn has_new_message(&self) -> bool {
        !self
            .messages
            .lock()
            .expect("poisoned reporter queue")
            .is_empty()
    }
    pub fn get_new_message(&self) -> Result<Message, ReportError> {
        self.messages
            .lock()
            .expect("poisoned reporter queue")
            .pop_front()
            .ok_or(ReportError::EmptyQueue)
    }
}
impl Reporter for PollingReporter {
    fn bind_plugin_manager(
        &self,
        manager: &crate::plugin::silver_plugin_manager::SilverPluginManager,
    ) -> Result<(), ReportError> {
        bind_mapper(&self.mapper, manager)
    }
    fn name(&self) -> &str {
        &self.name
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        let message = map_entity_message(&self.mapper, message)?;
        let mut messages = self.messages.lock().expect("poisoned reporter queue");
        messages.push_back(message.clone());
        self.pass_through.report(message)
    }
}
fn render_state(state: &super::message::VerifierState) -> Result<String, ReportError> {
    Ok(state.try_render(&crate::ast::pretty::pretty_printer::expression_to_string)?)
}
fn render_entity(entity: &Entity) -> Result<String, ReportError> {
    let node = crate::ast::utility::nodes::Node::Member((**entity).clone());
    Ok(super::package::print_rendered_entity(
        &crate::ast::pretty::pretty_printer::pretty_node(&node)?,
    ))
}
fn render_entity_message(message: &Message) -> Result<String, ReportError> {
    Ok(match message {
        Message::EntitySuccess {
            verifier,
            concerning,
            time,
            cached,
        } => format!(
            "entity_success_message(verifier={verifier}, concerning={}, time={time}, cached={cached})",
            render_entity(concerning)?
        ),
        Message::EntityFailure {
            verifier,
            concerning,
            time,
            errors,
            cached,
        } => format!(
            "entity_failure_message(verifier={verifier}, concerning={}, time={time}, result={}, cached={cached})",
            render_entity(concerning)?,
            VerificationResult::Failure(errors.clone()).render()?
        ),
        Message::BranchFailure {
            verifier,
            concerning,
            errors,
            cached,
        } => format!(
            "branch_failure_message(verifier={verifier}, concerning={}, result={}, cached={cached})",
            render_entity(concerning)?,
            VerificationResult::Failure(errors.clone()).render()?
        ),
        _ => return Err(ReportError::Unsupported("expected entity result")),
    })
}
fn render_chosen_triggers(
    quantifier: &crate::ast::expression::Exp,
    triggers: &[crate::ast::expression::Trigger],
    old: &[crate::ast::expression::Trigger],
) -> Result<String, ReportError> {
    use crate::ast::expression::ExpKind;
    let kind = match quantifier.kind() {
        ExpKind::Forall(..) => "Forall",
        ExpKind::Exists(..) => "Exists",
        _ => {
            return Err(ReportError::Unsupported(
                "chosen triggers for non-quantifier",
            ));
        }
    };
    let render = |list: &[crate::ast::expression::Trigger]| -> Result<String, ReportError> {
        let groups = list
            .iter()
            .map(|trigger| {
                let expressions = trigger
                    .exps
                    .iter()
                    .map(crate::ast::pretty::pretty_printer::expression_to_string)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok::<_, ReportError>(format!("{{{}}}", expressions.join(", ")))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(format!("[{}]", groups.join(", ")))
    };
    Ok(format!(
        "quantifier_chosen_triggers_message(type={kind}, quantifier={}, triggers={}), oldTriggers={})",
        crate::ast::pretty::pretty_printer::expression_to_string(quantifier)?,
        render(triggers)?,
        render(old)?
    ))
}
fn render_fallback(message: &Message) -> Result<String, ReportError> {
    match message {
        Message::Statistics {
            methods,
            functions,
            predicates,
            domains,
            fields,
        } => Ok(format!(
            "statistics_report(nom={methods}, nofu={functions}, nop={predicates}, nod={domains}, nofi={fields})"
        )),
        Message::ProgramOutline { members } => {
            let members = members
                .iter()
                .map(render_entity)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(format!(
                "program_outline_report(members=List({}))",
                members.join(", ")
            ))
        }
        Message::ProgramDefinitions { definitions } => {
            use super::package::SymbolKind;
            let mut rendered = Vec::with_capacity(definitions.len());
            for definition in definitions {
                let kind = match &definition.typ {
                    SymbolKind::Domain => "ViperDomain".into(),
                    SymbolKind::Axiom => "ViperAxiom".into(),
                    SymbolKind::Function => "ViperFunction".into(),
                    SymbolKind::Predicate => "ViperPredicate".into(),
                    SymbolKind::Method => "ViperMethod".into(),
                    SymbolKind::UntypedLocalDefinition => "ViperUntypedLocalDefinition".into(),
                    kind => {
                        let (name, typ) = match kind {
                            SymbolKind::Field(t) => ("ViperField", t),
                            SymbolKind::Argument(t) => ("ViperArgument", t),
                            SymbolKind::ReturnParameter(t) => ("ViperReturnParameter", t),
                            SymbolKind::TypedLocalDefinition(t) => ("ViperTypedLocalDefinition", t),
                            _ => unreachable!(),
                        };
                        format!(
                            "{name}({})",
                            crate::ast::pretty::pretty_printer::show_type(typ)?
                        )
                    }
                };
                let scope = match &definition.scope {
                    Some(scope) => format!("Some({scope})"),
                    None => "None".into(),
                };
                rendered.push(format!(
                    "Definition({},{kind},{},{scope})",
                    definition.name, definition.location
                ));
            }
            // Source intentionally omits the final closing parenthesis.
            Ok(format!(
                "program_definitions_report(definitions=List({})",
                rendered.join(", ")
            ))
        }
        Message::ExecutionTrace {
            member_traces,
            axioms,
            function_post_axioms,
        } => {
            let render_list = |values: &[Arc<dyn super::message::TraceValue>]| {
                values
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            let members = member_traces
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(",");
            Ok(format!(
                "symbolic_execution_logger_report(\n  members=[{members}],\n  axioms=List({})\n  functionPostAxioms=List({})\n)",
                render_list(axioms),
                render_list(function_post_axioms)
            ))
        }
        _ => Err(ReportError::Unsupported("source message string rendering")),
    }
}

impl Message {
    /// Render the pinned source message form where the retained payload has enough provenance.
    pub fn render_source(&self) -> Result<String, ReportError> {
        let failure = |errors: &[crate::verifier::verification_result::AbstractError]| {
            VerificationResult::Failure(errors.to_vec())
                .render()
                .map_err(ReportError::from)
        };
        Ok(match self {
            Self::AstConstructionSuccess { time } => {
                format!("ast_construction_success(time={time})")
            }
            Self::AstConstructionFailure { time, errors } => format!(
                "ast_construction_failure(time={time}, result={})",
                failure(errors)?
            ),
            Self::OverallSuccess { verifier, time } => {
                format!("overall_success_message(verifier={verifier}, time={time})")
            }
            Self::OverallFailure {
                verifier,
                time,
                errors,
            } => format!(
                "overall_failure_message(verifier={verifier}, time={time}, result={})",
                failure(errors)?
            ),
            Self::EntitySuccess { .. }
            | Self::EntityFailure { .. }
            | Self::BranchFailure { .. } => render_entity_message(self)?,
            Self::Statistics { .. }
            | Self::ProgramOutline { .. }
            | Self::ProgramDefinitions { .. }
            | Self::ExecutionTrace { .. } => render_fallback(self)?,
            Self::Exception {
                details: Some(details),
                ..
            } => format!("exception_report(e={})", details.display),
            Self::Exception { details: None, .. } => {
                return Err(ReportError::Unsupported(
                    "exception source display not captured",
                ));
            }
            Self::InvalidArguments {
                tool_signature,
                errors,
            } => {
                let errors = errors
                    .iter()
                    .map(|error| error.render())
                    .collect::<Result<Vec<_>, _>>()?;
                format!(
                    "invalid_args_report(tool_signature={tool_signature}, errors=[{}])",
                    errors.join(",")
                )
            }
            Self::BackendSubProcess {
                tool_signature,
                process_exe,
                phase,
                pid,
            } => format!(
                "backend_sub_process_report(tool_signature={tool_signature}, process_exe={process_exe}, phase={}, pid={})",
                phase.name(),
                pid.map(|p| p.to_string())
                    .unwrap_or_else(|| "<not provided>".into())
            ),
            Self::Simple { kind, text } => format!("{}(text={text})", kind.name()),
            Self::QuantifierInstantiations {
                quantifier,
                instantiations,
                max_gen,
                max_cost,
            } => format!(
                "quantifier_instantiations_message(quantifier={quantifier}, instantiations={instantiations}, max_gen={max_gen}, max_cost={max_cost})"
            ),
            Self::QuantifierChosenTriggers {
                quantifier,
                triggers,
                old_triggers,
            } => render_chosen_triggers(quantifier, triggers, old_triggers)?,
            Self::VerificationTermination => "verification_termination_message".into(),
            Self::Benchmarking { category, payload } => {
                format!("Benchmarking message of type {category} with payload {payload}")
            }
            Self::BlockReached {
                method_name,
                label,
                path_id,
            } => format!(
                "block_reached_message(methodName={method_name}, label={label}, pathId={path_id})"
            ),
            Self::BlockFailure {
                method_name,
                label,
                path_id,
            } => format!(
                "block_failure_message(methodName={method_name}, label={label}, pathId={path_id})"
            ),
            Self::PathProcessed {
                method_name,
                path_id,
                result,
            } => format!(
                "path_processed_message(methodName={method_name}, pathId={path_id}, result={result})"
            ),
            Self::VerifierState {
                verifier,
                concerning,
                millis_since_progress,
                state,
            } => format!(
                "verifier_state_message(verifier={verifier}, concerning={}, millisSinceProgress={millis_since_progress}, state={})",
                concerning.name(),
                render_state(state)?
            ),
            Self::ExternalDependencies { dependencies } => {
                let deps = dependencies
                    .iter()
                    .map(|dependency| {
                        dependency
                            .render_source()
                            .ok_or(ReportError::Unsupported("dependency source rendering"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                format!("external_dependencies_report(deps=[{}])", deps.join(","))
            }
            Self::PProgram { .. }
            | Self::WarningsDuringParsing { .. }
            | Self::WarningsDuringTypechecking { .. }
            | Self::WarningsDuringVerification { .. } => {
                return Err(ReportError::Unsupported(
                    "source collection or product rendering lacks runtime provenance",
                ));
            }
        })
    }
}
/// Writes source CSV records in order and flushes each report.
pub struct CsvReporter<W: Write + Send> {
    pub name: String,
    mapper: MapperSlot,
    writer: Mutex<W>,
}
impl<W: Write + Send> CsvReporter<W> {
    pub fn new(writer: W) -> Self {
        Self {
            name: "csv_reporter".into(),
            mapper: RwLock::new(None),
            writer: Mutex::new(writer),
        }
    }
}
impl CsvReporter<std::fs::File> {
    pub fn open(path: impl AsRef<std::path::Path>) -> io::Result<Self> {
        Ok(Self::new(
            std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)?,
        ))
    }
}
impl<W: Write + Send> Reporter for CsvReporter<W> {
    fn bind_plugin_manager(
        &self,
        manager: &crate::plugin::silver_plugin_manager::SilverPluginManager,
    ) -> Result<(), ReportError> {
        bind_mapper(&self.mapper, manager)
    }
    fn name(&self) -> &str {
        &self.name
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        let message = map_entity_message(&self.mapper, message)?;
        let mut writer = self.writer.lock().expect("poisoned CSV reporter");
        match message {
            Message::AstConstructionFailure { time, .. } => {
                writeln!(writer, "AstConstructionFailureMessage,{time}")?
            }
            Message::AstConstructionSuccess { time } => {
                writeln!(writer, "AstConstructionSuccessMessage,{time}")?
            }
            Message::OverallFailure { time, .. } => {
                writeln!(writer, "OverallFailureMessage,{time}")?
            }
            Message::OverallSuccess { time, .. } => {
                writeln!(writer, "OverallSuccessMessage,{time}")?
            }
            Message::EntitySuccess {
                concerning,
                time,
                cached,
                ..
            } => writeln!(
                writer,
                "EntitySuccessMessage,{},{}, {}",
                concerning.name(),
                time,
                cached
            )?,
            Message::EntityFailure {
                concerning,
                time,
                cached,
                ..
            } => writeln!(
                writer,
                "EntityFailureMessage,{},{}, {}",
                concerning.name(),
                time,
                cached
            )?,
            Message::BranchFailure {
                concerning, cached, ..
            } => writeln!(
                writer,
                "BranchFailureMessage,{},{}",
                concerning.name(),
                cached
            )?,
            Message::Exception {
                details: Some(details),
                ..
            } => writeln!(writer, "ExceptionReport,{}", details.display)?,
            Message::Exception { details: None, .. } => {
                return Err(ReportError::Unsupported(
                    "exception source display not captured",
                ));
            }
            Message::ExternalDependencies { dependencies } => {
                for dep in dependencies {
                    writeln!(
                        writer,
                        "ExternalDependenciesReport,{} {} located at {}",
                        dep.name(),
                        dep.version(),
                        dep.location()
                    )?;
                }
            }
            Message::WarningsDuringTypechecking { warnings } => {
                for warning in warnings {
                    writeln!(
                        writer,
                        "WarningsDuringTypechecking,{}",
                        crate::verifier::verification_result::AbstractError::Frontend(warning)
                            .render()?
                    )?;
                }
            }
            Message::WarningsDuringVerification { warnings } => {
                for warning in warnings {
                    writeln!(
                        writer,
                        "WarningsDuringVerification,{}",
                        crate::verifier::verification_result::AbstractError::Frontend(warning)
                            .render()?
                    )?;
                }
            }
            Message::VerifierState {
                verifier,
                concerning,
                millis_since_progress,
                state,
            } => {
                let rendered = format!(
                    "verifier_state_message(verifier={verifier}, concerning={}, millisSinceProgress={millis_since_progress}, state={})",
                    concerning.name(), render_state(&state)?
                ).replace('\n', "\\n");
                writeln!(writer, "{rendered}")?;
            }
            Message::QuantifierInstantiations {
                quantifier,
                instantiations,
                max_gen,
                max_cost,
            } => writeln!(
                writer,
                "quantifier_instantiations_message(quantifier={quantifier}, instantiations={instantiations}, max_gen={max_gen}, max_cost={max_cost})"
            )?,
            Message::QuantifierChosenTriggers {
                quantifier,
                triggers,
                old_triggers,
            } => {
                writeln!(
                    writer,
                    "{}",
                    render_chosen_triggers(&quantifier, &triggers, &old_triggers)?
                )?;
            }
            Message::VerificationTermination => {
                writeln!(writer, "verification_termination_message")?
            }
            Message::BlockReached {
                method_name,
                label,
                path_id,
            } => writeln!(
                writer,
                "block_reached_message(methodName={method_name}, label={label}, pathId={path_id})"
            )?,
            Message::BlockFailure {
                method_name,
                label,
                path_id,
            } => writeln!(
                writer,
                "block_failure_message(methodName={method_name}, label={label}, pathId={path_id})"
            )?,
            Message::PathProcessed {
                method_name,
                path_id,
                result,
            } => writeln!(
                writer,
                "path_processed_message(methodName={method_name}, pathId={path_id}, result={result})"
            )?,
            Message::WarningsDuringParsing { warnings } => {
                for warning in warnings {
                    writeln!(writer, "WarningsDuringParsing,{warning}")?;
                }
            }
            Message::InvalidArguments { errors, .. } => {
                for error in errors {
                    writeln!(writer, "WarningsDuringParsing,{}", error.render()?)?;
                }
            }
            Message::Simple {
                kind: super::message::SimpleMessageKind::AnnotationWarning,
                text,
            } => writeln!(writer, "AnnotationWarning,{text}")?,
            Message::Simple { .. }
            | Message::BackendSubProcess { .. }
            | Message::Benchmarking { .. } => {}
            message @ (Message::Statistics { .. }
            | Message::ProgramOutline { .. }
            | Message::ProgramDefinitions { .. }
            | Message::ExecutionTrace { .. }) => {
                writeln!(
                    io::stdout().lock(),
                    "Cannot properly print message of unsupported type: {}",
                    render_fallback(&message)?
                )?;
            }
            _ => {
                return Err(ReportError::Unsupported(
                    "CSV formatting for this message is not yet implemented",
                ));
            }
        }
        writer.flush()?;
        Ok(())
    }
}

/// Console lifecycle, diagnostics and optional partial entity reporting.
pub struct StdIoReporter<W: Write + Send> {
    pub name: String,
    pub time_info: bool,
    pub report_partial_results: bool,
    // 0: standalone field, 1: configured false, 2: configured true.
    configured_partial_results: std::sync::atomic::AtomicU8,
    mapper: MapperSlot,
    writer: Mutex<W>,
    counter: std::sync::atomic::AtomicI32,
}
impl<W: Write + Send> StdIoReporter<W> {
    pub fn new(writer: W, time_info: bool) -> Self {
        Self {
            name: "stdout_reporter".into(),
            time_info,
            report_partial_results: false,
            configured_partial_results: std::sync::atomic::AtomicU8::new(0),
            mapper: RwLock::new(None),
            writer: Mutex::new(writer),
            counter: std::sync::atomic::AtomicI32::new(0),
        }
    }
    pub fn counter(&self) -> i32 {
        self.counter.load(std::sync::atomic::Ordering::Relaxed)
    }
    fn time(&self, millis: i64) -> Result<String, ReportError> {
        super::format::package::format_millis_readably(millis)
            .map_err(|_| ReportError::Unsupported("timestamp outside chrono range"))
    }
}
impl<W: Write + Send> Reporter for StdIoReporter<W> {
    fn bind_plugin_manager(
        &self,
        manager: &crate::plugin::silver_plugin_manager::SilverPluginManager,
    ) -> Result<(), ReportError> {
        bind_mapper(&self.mapper, manager)
    }
    fn set_config(
        &self,
        config: Option<&crate::frontend::sil_front_end_config::SilFrontendConfig>,
    ) -> Result<(), ReportError> {
        let value = config.map_or(
            0,
            |config| if config.report_partial_results { 2 } else { 1 },
        );
        self.configured_partial_results
            .store(value, std::sync::atomic::Ordering::Relaxed);
        Ok(())
    }
    fn name(&self) -> &str {
        &self.name
    }
    fn report(&self, message: Message) -> Result<(), ReportError> {
        use super::message::SimpleMessageKind;
        let message = map_entity_message(&self.mapper, message)?;
        let mut writer = self.writer.lock().expect("poisoned stdout reporter");
        match message {
            Message::AstConstructionSuccess { time } => {
                if self.time_info {
                    writeln!(
                        writer,
                        "the file represents a consistent Viper program; constructed AST in {}.",
                        self.time(time)?
                    )?;
                } else {
                    writeln!(writer, "the file represents a consistent Viper program.")?;
                }
            }
            Message::AstConstructionFailure { time, errors } => {
                let n = errors.len();
                let suffix = if n == 1 { "" } else { "s" };
                if self.time_info {
                    writeln!(
                        writer,
                        "AST construction resulted in {n} error{suffix} in {}:",
                        self.time(time)?
                    )?;
                } else {
                    writeln!(writer, "AST construction resulted in {n} error{suffix}:")?;
                }
                let width = n.to_string().len();
                for (i, error) in errors.iter().enumerate() {
                    writeln!(writer, "  [{i:>width$}] {}", error.readable_message()?)?;
                }
            }
            Message::OverallSuccess { verifier, time } => {
                if self.time_info {
                    writeln!(
                        writer,
                        "{verifier} finished verification successfully in {}.",
                        self.time(time)?
                    )?;
                } else {
                    writeln!(writer, "{verifier} finished verification successfully.")?;
                }
            }
            Message::OverallFailure {
                verifier,
                time,
                errors,
            } => {
                let n = errors.len();
                let suffix = if n == 1 { "" } else { "s" };
                if self.time_info {
                    writeln!(
                        writer,
                        "{verifier} found {n} error{suffix} in {}:",
                        self.time(time)?
                    )?;
                } else {
                    writeln!(writer, "{verifier} found {n} error{suffix}:")?;
                }
                let width = n.to_string().len();
                for (i, error) in errors.iter().enumerate() {
                    writeln!(writer, "  [{i:>width$}] {}", error.readable_message()?)?;
                }
            }
            Message::VerifierState {
                verifier,
                concerning,
                millis_since_progress,
                state,
            } => {
                let rendered = render_state(&state)?;
                if self.time_info {
                    writeln!(
                        writer,
                        "{verifier} has been working on {} without visible progress for {}. Current state:",
                        concerning.name(),
                        self.time(millis_since_progress)?
                    )?;
                } else {
                    writeln!(
                        writer,
                        "{verifier} has been working on {} without visible progress. Current state:",
                        concerning.name()
                    )?;
                }
                for line in rendered.lines() {
                    writeln!(writer, "  {line}")?;
                }
            }
            Message::Exception {
                details: Some(details),
                ..
            } => {
                if details.stack_trace.is_empty() {
                    return Err(ReportError::Unsupported("exception source stack is empty"));
                }
                writeln!(
                    writer,
                    "Verification aborted exceptionally: {}",
                    details.display
                )?;
                write!(writer, "{}", details.stack_trace)?;
                if !details.stack_trace.ends_with('\n') {
                    writeln!(writer)?;
                }
                if let Some(cause) = details.cause {
                    writeln!(writer, "  Cause: {cause}")?;
                }
            }
            Message::Exception { details: None, .. } => {
                return Err(ReportError::Unsupported(
                    "exception source stack not captured",
                ));
            }
            Message::ExternalDependencies { dependencies } => {
                writeln!(writer, "The following dependencies are used:")?;
                for dep in dependencies {
                    writeln!(
                        writer,
                        "  {} {}, located at {}.",
                        dep.name(),
                        dep.version(),
                        dep.location()
                    )?;
                }
            }
            Message::WarningsDuringTypechecking { warnings }
            | Message::WarningsDuringVerification { warnings } => {
                for warning in warnings {
                    writeln!(
                        writer,
                        "{}",
                        crate::verifier::verification_result::AbstractError::Frontend(warning)
                            .render()?
                    )?;
                }
            }
            Message::ExecutionTrace {
                member_traces,
                axioms,
                function_post_axioms,
            } => {
                writeln!(writer, "Execution trace for the last run:")?;
                writeln!(writer, "  Members:")?;
                for value in member_traces {
                    writeln!(writer, "    {value}")?;
                }
                writeln!(writer, "  Axioms:")?;
                for value in axioms {
                    writeln!(writer, "    {value}")?;
                }
                writeln!(writer, "  FunctionPostAxioms:")?;
                for value in function_post_axioms {
                    writeln!(writer, "    {value}")?;
                }
            }
            Message::WarningsDuringParsing { warnings } => {
                for warning in warnings {
                    writeln!(writer, "{warning}")?;
                }
            }
            Message::InvalidArguments { errors, .. } => {
                for error in errors {
                    writeln!(writer, "  {}", error.readable_message()?)?;
                }
                writeln!(writer, "Run with just --help for usage and options")?;
            }
            Message::Simple {
                kind: SimpleMessageKind::AnnotationWarning,
                text,
            } => writeln!(writer, "Annotation warning: {text}")?,
            Message::Simple {
                kind: SimpleMessageKind::Copyright,
                text,
            } => writeln!(writer, "{text}")?,
            Message::Simple {
                kind: SimpleMessageKind::MissingDependency,
                text,
            } => writeln!(writer, "encountered missing dependency: {text}")?,
            message @ (Message::EntitySuccess { .. }
            | Message::EntityFailure { .. }
            | Message::BranchFailure { .. })
                if match self
                    .configured_partial_results
                    .load(std::sync::atomic::Ordering::Relaxed)
                {
                    1 => false,
                    2 => true,
                    _ => self.report_partial_results,
                } =>
            {
                writeln!(writer, "{}", render_entity_message(&message)?)?;
            }
            Message::EntitySuccess { .. }
            | Message::EntityFailure { .. }
            | Message::BranchFailure { .. }
            | Message::Simple { .. }
            | Message::BackendSubProcess { .. }
            | Message::QuantifierInstantiations { .. }
            | Message::QuantifierChosenTriggers { .. }
            | Message::BlockReached { .. }
            | Message::BlockFailure { .. }
            | Message::PathProcessed { .. }
            | Message::VerificationTermination
            | Message::Benchmarking { .. } => {}
            message @ (Message::Statistics { .. }
            | Message::ProgramOutline { .. }
            | Message::ProgramDefinitions { .. }) => {
                writeln!(
                    writer,
                    "Cannot properly print message of unsupported type: {}",
                    render_fallback(&message)?
                )?;
            }
            _ => {
                return Err(ReportError::Unsupported(
                    "stdout formatting for this message is not yet implemented",
                ));
            }
        }
        writer.flush()?;
        self.counter
            .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::message::SimpleMessageKind;
    use super::*;
    fn method() -> Entity {
        use crate::ast::{
            ast::Metadata,
            program::{Member, Method, MethodData},
        };
        Arc::new(Member::Method(Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: Metadata::default(),
        })))
    }
    #[test]
    fn captured_exception_reports_original_stack_and_optional_cause() {
        use super::super::message::CapturedExceptionDetails;
        let error = Arc::new(io::Error::other("native failure"));
        let details = |cause| CapturedExceptionDetails {
            display: "native failure".into(),
            stack_trace: "native failure\n  origin frame".into(),
            cause,
        };
        let reporter = StdIoReporter::new(Vec::new(), false);
        reporter
            .report(Message::captured_exception(
                error.clone(),
                details(Some("underlying".into())),
            ))
            .unwrap();
        reporter
            .report(Message::captured_exception(error.clone(), details(None)))
            .unwrap();
        assert!(matches!(
            reporter.report(Message::exception(error.clone())),
            Err(ReportError::Unsupported(_))
        ));
        let out = String::from_utf8(reporter.writer.lock().unwrap().clone()).unwrap();
        assert_eq!(
            out,
            "Verification aborted exceptionally: native failure\nnative failure\n  origin frame\n  Cause: underlying\nVerification aborted exceptionally: native failure\nnative failure\n  origin frame\n"
        );
        assert_eq!(reporter.counter(), 2);
        let csv = CsvReporter::new(Vec::new());
        csv.report(Message::captured_exception(error.clone(), details(None)))
            .unwrap();
        assert_eq!(
            String::from_utf8(csv.writer.lock().unwrap().clone()).unwrap(),
            "ExceptionReport,native failure\n"
        );
        assert!(matches!(
            csv.report(Message::exception(error)),
            Err(ReportError::Unsupported(_))
        ));
    }
    #[test]
    fn source_fallback_renders_statistics_and_outline() {
        let reporter = StdIoReporter::new(Vec::new(), false);
        reporter
            .report(Message::Statistics {
                methods: 1,
                functions: 2,
                predicates: 3,
                domains: 4,
                fields: 5,
            })
            .unwrap();
        reporter
            .report(Message::ProgramOutline {
                members: vec![method()],
            })
            .unwrap();
        reporter
            .report(Message::ProgramDefinitions {
                definitions: vec![super::super::package::Definition {
                    name: "x".into(),
                    typ: super::super::package::SymbolKind::Field(crate::ast::r#type::Type::Int),
                    location: crate::ast::position::Position::NoPosition,
                    scope: None,
                }],
            })
            .unwrap();
        let out = String::from_utf8(reporter.writer.lock().unwrap().clone()).unwrap();
        assert!(out.starts_with("Cannot properly print message of unsupported type: statistics_report(nom=1, nofu=2, nop=3, nod=4, nofi=5)\n"));
        assert!(out.contains("program_outline_report(members=List(method m()"));
        assert!(out.contains("program_definitions_report(definitions=List(Definition(x,ViperField(Int),<no position>,None))\n"));
    }
    #[test]
    fn source_message_rendering_retains_protocol_names_and_missing_pid() {
        assert_eq!(
            Message::OverallSuccess {
                verifier: "Silicon".into(),
                time: 17
            }
            .render_source()
            .unwrap(),
            "overall_success_message(verifier=Silicon, time=17)"
        );
        assert_eq!(
            Message::BackendSubProcess {
                tool_signature: "sig".into(),
                process_exe: "z3".into(),
                phase: super::super::message::BackendSubProcessStage::OnExit,
                pid: None
            }
            .render_source()
            .unwrap(),
            "backend_sub_process_report(tool_signature=sig, process_exe=z3, phase=on_exit, pid=<not provided>)"
        );
        assert_eq!(
            Message::VerificationTermination.render_source().unwrap(),
            "verification_termination_message"
        );
        let dependency = crate::verifier::verifier::DefaultDependency {
            name: "z3".into(),
            version: "4.16".into(),
            location: "/bin/z3".into(),
        };
        assert_eq!(
            Message::ExternalDependencies {
                dependencies: vec![Arc::new(dependency)]
            }
            .render_source()
            .unwrap(),
            "external_dependencies_report(deps=[DefaultDependency(z3,4.16,/bin/z3)])"
        );
    }
    #[test]
    fn stdout_flush_failure_is_reported_before_counter_increment() {
        struct FailFlush;
        impl Write for FailFlush {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                Ok(bytes.len())
            }
            fn flush(&mut self) -> io::Result<()> {
                Err(io::Error::other("flush failed"))
            }
        }
        let reporter = StdIoReporter::new(FailFlush, false);
        assert!(matches!(
            reporter.report(Message::AstConstructionSuccess { time: 0 }),
            Err(ReportError::Io(_))
        ));
        assert_eq!(reporter.counter(), 0);
    }
    #[test]
    fn polling_maps_before_queue_lock_on_reentrant_report() {
        use crate::plugin::{
            silver_plugin::SilverPlugin, silver_plugin_manager::SilverPluginManager,
        };
        struct Reentrant(
            std::sync::Weak<PollingReporter>,
            Arc<std::sync::atomic::AtomicBool>,
        );
        impl SilverPlugin for Reentrant {
            fn shared_entity_mapper(&self) -> Option<Arc<dyn EntityResultMapper>> {
                let reporter = self.0.clone();
                let entered = self.1.clone();
                Some(Arc::new(move |_: &Entity, result| {
                    if !entered.swap(true, std::sync::atomic::Ordering::SeqCst) {
                        reporter.upgrade().unwrap().report(Message::EntitySuccess {
                            verifier: "Silicon".into(),
                            concerning: method(),
                            time: 0,
                            cached: false,
                        })?;
                    }
                    Ok(result)
                }))
            }
        }
        let reporter = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
        let manager = SilverPluginManager::new(vec![Box::new(Reentrant(
            Arc::downgrade(&reporter),
            Arc::new(std::sync::atomic::AtomicBool::new(false)),
        ))]);
        reporter.bind_plugin_manager(&manager).unwrap();
        reporter
            .report(Message::EntitySuccess {
                verifier: "Silicon".into(),
                concerning: method(),
                time: 0,
                cached: false,
            })
            .unwrap();
        assert!(reporter.get_new_message().is_ok());
        assert!(reporter.get_new_message().is_ok());
    }
    #[test]
    fn concrete_reporters_map_entities_before_writing_or_queueing() {
        use crate::plugin::{
            silver_plugin::SilverPlugin, silver_plugin_manager::SilverPluginManager,
        };
        struct Flip;
        impl SilverPlugin for Flip {
            fn shared_entity_mapper(&self) -> Option<Arc<dyn EntityResultMapper>> {
                Some(Arc::new(|_: &Entity, _: VerificationResult| {
                    Ok(VerificationResult::Failure(vec![]))
                }))
            }
        }
        let manager = SilverPluginManager::new(vec![Box::new(Flip)]);
        let message = || Message::EntitySuccess {
            verifier: "Silicon".into(),
            concerning: method(),
            time: 0,
            cached: false,
        };
        let polling = PollingReporter::new(Arc::new(NoopReporter));
        polling.bind_plugin_manager(&manager).unwrap();
        polling.report(message()).unwrap();
        assert!(matches!(
            polling.get_new_message().unwrap(),
            Message::EntityFailure { .. }
        ));
        let csv = CsvReporter::new(Vec::new());
        csv.bind_plugin_manager(&manager).unwrap();
        csv.report(message()).unwrap();
        let csv_text = String::from_utf8(csv.writer.lock().unwrap().clone()).unwrap();
        assert!(csv_text.starts_with("EntityFailureMessage,"));
        let mut stdout = StdIoReporter::new(Vec::new(), false);
        stdout.report_partial_results = true;
        stdout.bind_plugin_manager(&manager).unwrap();
        stdout.report(message()).unwrap();
        let output = String::from_utf8(stdout.writer.lock().unwrap().clone()).unwrap();
        assert!(output.contains("entity_failure_message"));
    }
    #[test]
    fn shared_mapping_allows_reentrant_entity_report() {
        use crate::plugin::{
            silver_plugin::SilverPlugin, silver_plugin_manager::SilverPluginManager,
        };
        struct Reentrant(
            std::sync::Weak<PluginAwareReporter>,
            Arc<std::sync::atomic::AtomicBool>,
        );
        impl SilverPlugin for Reentrant {
            fn shared_entity_mapper(&self) -> Option<Arc<dyn EntityResultMapper>> {
                let reporter = self.0.clone();
                let entered = self.1.clone();
                Some(Arc::new(move |_: &Entity, result| {
                    if !entered.swap(true, std::sync::atomic::Ordering::SeqCst) {
                        reporter.upgrade().unwrap().report(Message::EntitySuccess {
                            verifier: "Silicon".into(),
                            concerning: method(),
                            time: 0,
                            cached: false,
                        })?;
                    }
                    Ok(result)
                }))
            }
        }
        let target = Arc::new(PollingReporter::new(Arc::new(NoopReporter)));
        let reporter = Arc::new(PluginAwareReporter {
            name: "shared".into(),
            target: target.clone(),
            mapper: RwLock::new(None),
        });
        let manager = SilverPluginManager::new(vec![Box::new(Reentrant(
            Arc::downgrade(&reporter),
            Arc::new(std::sync::atomic::AtomicBool::new(false)),
        ))]);
        reporter.bind_plugin_manager(&manager).unwrap();
        reporter
            .report(Message::EntitySuccess {
                verifier: "Silicon".into(),
                concerning: method(),
                time: 0,
                cached: false,
            })
            .unwrap();
        assert!(matches!(
            target.get_new_message().unwrap(),
            Message::EntitySuccess { .. }
        ));
        assert!(matches!(
            target.get_new_message().unwrap(),
            Message::EntitySuccess { .. }
        ));
    }
    #[test]
    fn builtin_shared_mapper_matches_manager_success_mapping() {
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::parse_shared(
            "test",
            &["--ignoreFile".into(), "test.vpr".into()],
        );
        let mut manager = crate::frontend::sil_frontend::standard_plugin_manager(&config).unwrap();
        let entity = method();
        let view = manager.shared_entity_mapper().unwrap();
        let direct = manager
            .map_entity_verification_result(&entity, VerificationResult::Success)
            .unwrap();
        let shared = view
            .map_entity_result(&entity, VerificationResult::Success)
            .unwrap();
        assert!(matches!(direct, VerificationResult::Success));
        assert!(matches!(shared, VerificationResult::Success));
    }
    #[test]
    fn shared_mapper_supports_concurrent_reports_and_rejects_unavailable_plugins() {
        use crate::plugin::{
            silver_plugin::SilverPlugin, silver_plugin_manager::SilverPluginManager,
        };
        struct Unavailable;
        impl SilverPlugin for Unavailable {}
        let unsupported = SilverPluginManager::new(vec![Box::new(Unavailable)]);
        let plain = NoopReporter;
        plain.bind_plugin_manager(&unsupported).unwrap();
        let reporter = Arc::new(PluginAwareReporter {
            name: "shared".into(),
            target: Arc::new(NoopReporter),
            mapper: RwLock::new(None),
        });
        assert!(matches!(
            reporter.bind_plugin_manager(&unsupported),
            Err(ReportError::Unsupported(_))
        ));
        struct Concurrent(Arc<std::sync::Barrier>);
        impl SilverPlugin for Concurrent {
            fn shared_entity_mapper(&self) -> Option<Arc<dyn EntityResultMapper>> {
                let barrier = self.0.clone();
                Some(Arc::new(move |_: &Entity, result| {
                    barrier.wait();
                    Ok(result)
                }))
            }
        }
        let manager = SilverPluginManager::new(vec![Box::new(Concurrent(Arc::new(
            std::sync::Barrier::new(2),
        )))]);
        reporter.bind_plugin_manager(&manager).unwrap();
        let threads: Vec<_> = (0..2)
            .map(|_| {
                let reporter = reporter.clone();
                std::thread::spawn(move || {
                    reporter.report(Message::EntitySuccess {
                        verifier: "Silicon".into(),
                        concerning: method(),
                        time: 0,
                        cached: false,
                    })
                })
            })
            .collect();
        for thread in threads {
            thread.join().unwrap().unwrap();
        }
    }
    #[test]
    fn configured_partial_results_override_and_restore_standalone_field() {
        let mut reporter = StdIoReporter::new(Vec::new(), false);
        reporter.report_partial_results = true;
        let message = || Message::EntitySuccess {
            verifier: "Silicon".into(),
            concerning: method(),
            time: 0,
            cached: false,
        };
        let config = crate::frontend::sil_front_end_config::SilFrontendConfig::parse_shared(
            "test",
            &["--ignoreFile".into(), "test.vpr".into()],
        );
        reporter.set_config(Some(&config)).unwrap();
        reporter.report(message()).unwrap();
        assert!(reporter.writer.lock().unwrap().is_empty());
        let mut config = config;
        config.report_partial_results = true;
        reporter.set_config(Some(&config)).unwrap();
        reporter.report(message()).unwrap();
        assert!(!reporter.writer.lock().unwrap().is_empty());
        reporter.writer.lock().unwrap().clear();
        reporter.set_config(None).unwrap();
        reporter.report(message()).unwrap();
        assert!(!reporter.writer.lock().unwrap().is_empty());
    }
    #[test]
    fn partial_entity_and_branch_results_use_source_message_forms() {
        use crate::verifier::verification_result::{
            AbstractError, FrontendError, FrontendErrorKind,
        };
        let mut reporter = StdIoReporter::new(Vec::new(), false);
        reporter.report_partial_results = true;
        reporter
            .report(Message::EntitySuccess {
                verifier: "Silicon".into(),
                concerning: method(),
                time: 12,
                cached: true,
            })
            .unwrap();
        let error = AbstractError::Frontend(FrontendError::new(
            FrontendErrorKind::TypecheckerError("oops".into()),
            crate::ast::position::Position::NoPosition,
        ));
        reporter
            .report(Message::BranchFailure {
                verifier: "Silicon".into(),
                concerning: method(),
                errors: vec![error],
                cached: false,
            })
            .unwrap();
        let out = String::from_utf8(reporter.writer.lock().unwrap().clone()).unwrap();
        assert!(out.starts_with("entity_success_message(verifier=Silicon, concerning=method m()"));
        assert!(out.contains("time=12, cached=true)\n"));
        assert!(out.contains("branch_failure_message(verifier=Silicon, concerning=method m()"));
        assert!(out.contains("Verification failed with 1 errors:"));
        assert_eq!(reporter.counter(), 2);
    }
    #[test]
    fn chosen_triggers_and_expression_branch_render_through_source_printer() {
        use crate::ast::{
            ast::Metadata,
            expression::{Exp, ExpKind, Trigger},
        };
        let meta = Metadata::default();
        let truth = Exp::new(ExpKind::TrueLit, meta.clone());
        let quantifier = Exp::new(ExpKind::Forall(vec![], vec![], truth.clone()), meta);
        let trigger = Trigger::new(vec![truth.clone()], Default::default());
        let csv = CsvReporter::new(Vec::new());
        csv.report(Message::QuantifierChosenTriggers {
            quantifier,
            triggers: vec![trigger],
            old_triggers: vec![],
        })
        .unwrap();
        let out = String::from_utf8(csv.writer.lock().unwrap().clone()).unwrap();
        assert!(out.starts_with("quantifier_chosen_triggers_message(type=Forall, quantifier="));
        assert!(out.ends_with("triggers=[{true}]), oldTriggers=[])\n"));
        let state = super::super::message::VerifierState {
            frames: vec![super::super::message::VerifierStateFrame {
                branch_condition: Some(super::super::message::BranchCondition::Condition(truth)),
                steps: vec![],
            }],
        };
        assert_eq!(render_state(&state).unwrap(), "branch true:");
        csv.report(Message::VerifierState {
            verifier: "backend\nworker".into(),
            concerning: method(),
            millis_since_progress: 3,
            state,
        })
        .unwrap();
        let out = String::from_utf8(csv.writer.lock().unwrap().clone()).unwrap();
        assert!(out.contains("verifier=backend\\nworker"));
        assert_eq!(out.lines().count(), 2);
    }
    #[test]
    fn polling_preserves_order_and_reports_empty_queue() {
        let reporter = PollingReporter::new(Arc::new(NoopReporter));
        for text in ["first", "second"] {
            reporter
                .report(Message::Simple {
                    kind: SimpleMessageKind::Simple,
                    text: text.into(),
                })
                .unwrap();
        }
        for expected in ["first", "second"] {
            let Message::Simple { text, .. } = reporter.get_new_message().unwrap() else {
                panic!("simple event")
            };
            assert_eq!(text, expected);
        }
        assert!(matches!(
            reporter.get_new_message(),
            Err(ReportError::EmptyQueue)
        ));
    }
}
