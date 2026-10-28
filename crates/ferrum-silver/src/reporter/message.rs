//! Port plan: Define structured frontend, verification and progress messages.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/reporter/Message.scala
//!
//! Purpose:
//! Define structured frontend, verification and progress messages.
//!
//! Planned Rust structure:
//! Message and AST/verification result families, factories for overall/entity/cached results;
//! statistics, outline, definitions, parsed program, execution trace, exception, arguments,
//! subprocess stages, dependencies, warnings, simple, quantifier, termination, benchmarking,
//! block/path and verifier-state messages. VerifierState frames/steps and BranchCondition variants
//! render progress.
//!
//! Behavior to preserve:
//! Result factories dispatch Success/Failure; cached entity results use zero time. Preserve each
//! message name, fields and source rendering, subprocess stages and per-entity cached status.
//! State renders outermost frame first, branch indentation and optional line:column positions;
//! alternatives are displayed one-based.
//!
//! Integration:
//! reporter::{package,reporter}, verifier::{verification_result,verifier}, parser and Silicon
//! reporting.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile message ownership, extension/state payloads and serialized/rendered compatibility
//! with plugin manager and Silicon.
//!
//! Status: partial; structured result, source, dependency, warning and verifier-state events are
//! implemented. Source message forms and captured exception details have fallible renderers;
//! origin wiring and runtime collection/product provenance remain incomplete.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::package::{Definition, Entity, Time};
use crate::ast::expression::{Exp, Trigger};
use crate::ast::position::Position;
use crate::parser::parse_ast::PProgramHandle;
use crate::verifier::verification_result::{
    AbstractError, FrontendError, ParseReport, VerificationResult,
};
use std::fmt::Debug;
use std::sync::Arc;

/// A dependency can be rendered and inspected without losing its concrete implementation.
pub trait ReportDependency: Debug + Send + Sync {
    fn name(&self) -> &str;
    fn version(&self) -> &str;
    fn location(&self) -> &str;
    /// Source object's own toString; custom dependency implementations may supply it.
    fn render_source(&self) -> Option<String> {
        None
    }
}
impl ReportDependency for crate::verifier::verifier::DefaultDependency {
    fn name(&self) -> &str {
        &self.name
    }
    fn version(&self) -> &str {
        &self.version
    }
    fn location(&self) -> &str {
        &self.location
    }
    fn render_source(&self) -> Option<String> {
        Some(format!(
            "DefaultDependency({},{},{})",
            self.name, self.version, self.location
        ))
    }
}
pub trait TraceValue: std::fmt::Display + Debug + Send + Sync {}
impl<T: std::fmt::Display + Debug + Send + Sync> TraceValue for T {}

/// Exception text and stack captured at the origin, before reporting changes the call stack.
#[derive(Clone, Debug)]
pub struct CapturedExceptionDetails {
    pub display: String,
    /// Complete, pre-rendered native stack output, including its first line.
    pub stack_trace: String,
    pub cause: Option<String>,
}

/// Typed events sent to a reporter. Event families depending on backend dependency and
/// diagnostic representations will be added as those interfaces are connected.
#[derive(Clone, Debug)]
pub enum Message {
    AstConstructionSuccess {
        time: Time,
    },
    AstConstructionFailure {
        time: Time,
        errors: Vec<AbstractError>,
    },
    OverallSuccess {
        verifier: String,
        time: Time,
    },
    OverallFailure {
        verifier: String,
        time: Time,
        errors: Vec<AbstractError>,
    },
    EntitySuccess {
        verifier: String,
        concerning: Entity,
        time: Time,
        cached: bool,
    },
    EntityFailure {
        verifier: String,
        concerning: Entity,
        time: Time,
        errors: Vec<AbstractError>,
        cached: bool,
    },
    BranchFailure {
        verifier: String,
        concerning: Entity,
        errors: Vec<AbstractError>,
        cached: bool,
    },
    Statistics {
        methods: i32,
        functions: i32,
        predicates: i32,
        domains: i32,
        fields: i32,
    },
    ProgramOutline {
        members: Vec<Entity>,
    },
    ProgramDefinitions {
        definitions: Vec<Definition>,
    },
    PProgram {
        semantic_analysis_success: bool,
        program: PProgramHandle,
    },
    ExecutionTrace {
        member_traces: Vec<Arc<dyn TraceValue>>,
        axioms: Vec<Arc<dyn TraceValue>>,
        function_post_axioms: Vec<Arc<dyn TraceValue>>,
    },
    Exception {
        error: Arc<dyn std::error::Error + Send + Sync>,
        details: Option<CapturedExceptionDetails>,
    },
    ExternalDependencies {
        dependencies: Vec<Arc<dyn ReportDependency>>,
    },
    WarningsDuringTypechecking {
        warnings: Vec<FrontendError>,
    },
    WarningsDuringVerification {
        warnings: Vec<FrontendError>,
    },
    InvalidArguments {
        tool_signature: String,
        errors: Vec<AbstractError>,
    },
    BackendSubProcess {
        tool_signature: String,
        process_exe: String,
        phase: BackendSubProcessStage,
        pid: Option<i64>,
    },
    WarningsDuringParsing {
        warnings: Vec<ParseReport>,
    },
    Simple {
        kind: SimpleMessageKind,
        text: String,
    },
    QuantifierInstantiations {
        quantifier: String,
        instantiations: i32,
        max_gen: i32,
        max_cost: i32,
    },
    QuantifierChosenTriggers {
        quantifier: Exp,
        triggers: Vec<Trigger>,
        old_triggers: Vec<Trigger>,
    },
    VerificationTermination,
    Benchmarking {
        category: String,
        payload: String,
    },
    BlockReached {
        method_name: String,
        label: String,
        path_id: i32,
    },
    BlockFailure {
        method_name: String,
        label: String,
        path_id: i32,
    },
    PathProcessed {
        method_name: String,
        path_id: i32,
        result: String,
    },
    VerifierState {
        verifier: String,
        concerning: Entity,
        millis_since_progress: Time,
        state: VerifierState,
    },
}
impl Message {
    /// An error without captured origin details; source exception rendering fails explicitly.
    pub fn exception(error: Arc<dyn std::error::Error + Send + Sync>) -> Self {
        Self::Exception {
            error,
            details: None,
        }
    }
    pub fn captured_exception(
        error: Arc<dyn std::error::Error + Send + Sync>,
        details: CapturedExceptionDetails,
    ) -> Self {
        Self::Exception {
            error,
            details: Some(details),
        }
    }
    pub fn overall_result(
        verifier: impl Into<String>,
        time: Time,
        result: VerificationResult,
    ) -> Self {
        let verifier = verifier.into();
        match result {
            VerificationResult::Success => Self::OverallSuccess { verifier, time },
            VerificationResult::Failure(errors) => Self::OverallFailure {
                verifier,
                time,
                errors,
            },
        }
    }
    pub fn entity_result(
        verifier: impl Into<String>,
        concerning: Entity,
        time: Time,
        result: VerificationResult,
        cached: bool,
    ) -> Self {
        let verifier = verifier.into();
        match result {
            VerificationResult::Success => Self::EntitySuccess {
                verifier,
                concerning,
                time,
                cached,
            },
            VerificationResult::Failure(errors) => Self::EntityFailure {
                verifier,
                concerning,
                time,
                errors,
                cached,
            },
        }
    }
    pub fn cached_entity_result(
        verifier: impl Into<String>,
        concerning: Entity,
        result: VerificationResult,
    ) -> Self {
        Self::entity_result(verifier, concerning, 0, result, true)
    }
    pub fn name(&self) -> &'static str {
        match self {
            Self::AstConstructionSuccess { .. } | Self::AstConstructionFailure { .. } => {
                "ast_construction_result"
            }
            Self::OverallSuccess { .. }
            | Self::OverallFailure { .. }
            | Self::EntitySuccess { .. }
            | Self::EntityFailure { .. }
            | Self::BranchFailure { .. } => "verification_result",
            Self::Statistics { .. } => "statistics",
            Self::ProgramOutline { .. } => "program_outline",
            Self::ProgramDefinitions { .. } => "program_definitions",
            Self::PProgram { .. } => "pprogram",
            Self::ExecutionTrace { .. } => "symbolic_execution_logger_report",
            Self::Exception { .. } => "exception_report",
            Self::ExternalDependencies { .. } => "external_dependencies_report",
            Self::WarningsDuringTypechecking { .. } => "warnings_during_typechecking",
            Self::WarningsDuringVerification { .. } => "warnings_during_verification",
            Self::InvalidArguments { .. } => "invalid_args_report",
            Self::BackendSubProcess { .. } => "backend_sub_process_report",
            Self::WarningsDuringParsing { .. } => "warnings_during_parsing",
            Self::Simple { kind, .. } => kind.name(),
            Self::QuantifierInstantiations { .. } => "quantifier_instantiations_message",
            Self::QuantifierChosenTriggers { .. } => "quantifier_chosen_triggers_message",
            Self::VerificationTermination => "verification_termination_message",
            Self::Benchmarking { .. } => "benchmarking_message",
            Self::BlockReached { .. } => "block_reached_message",
            Self::BlockFailure { .. } => "block_failure_message",
            Self::PathProcessed { .. } => "path_processed_message",
            Self::VerifierState { .. } => "verifier_state_message",
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BackendSubProcessStage {
    BeforeInputSent,
    AfterInputSent,
    OnOutput,
    OnError,
    BeforeTermination,
    OnExit,
    AfterTermination,
}
impl BackendSubProcessStage {
    pub fn name(self) -> &'static str {
        match self {
            Self::BeforeInputSent => "before_input_sent",
            Self::AfterInputSent => "after_input_sent",
            Self::OnOutput => "on_output",
            Self::OnError => "on_error",
            Self::BeforeTermination => "before_termination",
            Self::OnExit => "on_exit",
            Self::AfterTermination => "after_termination",
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SimpleMessageKind {
    Simple,
    ConfigurationConfirmation,
    ConfigurationWarning,
    AnnotationWarning,
    InternalWarning,
    Copyright,
    MissingDependency,
    Pong,
}
impl SimpleMessageKind {
    pub fn name(self) -> &'static str {
        match self {
            Self::Simple => "simple_message",
            Self::ConfigurationConfirmation => "configuration_confirmation",
            Self::ConfigurationWarning => "configuration_warning",
            Self::AnnotationWarning => "annotation_warning",
            Self::InternalWarning => "internal_warning_message",
            Self::Copyright => "copyright_report",
            Self::MissingDependency => "missing_dependency_report",
            Self::Pong => "dbg__pong",
        }
    }
}

/// A retained AST node for a verifier step. The method exposes source position without
/// discarding the concrete node; clients may downcast through their own typed wrappers.
pub trait ReportNode: Debug + Send + Sync {
    fn position(&self) -> Position;
    fn as_any(&self) -> &dyn std::any::Any;
}
impl ReportNode for Exp {
    fn position(&self) -> Position {
        self.0.meta.position.clone()
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}
impl ReportNode for crate::ast::statement::Stmt {
    fn position(&self) -> Position {
        self.0.meta.position.clone()
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
}
#[derive(Clone, Debug)]
pub struct VerifierStep {
    pub kind: String,
    pub node: Option<Arc<dyn ReportNode>>,
    pub description: String,
}
impl VerifierStep {
    pub fn render(&self) -> String {
        with_position(
            format!("{} {}", self.kind, self.description),
            self.node.as_ref().map(|n| n.position()),
        )
    }
}
#[derive(Clone, Debug)]
pub enum BranchCondition {
    Condition(Exp),
    OpaqueCondition(String),
    Alternative { index: i32, count: i32 },
}
impl BranchCondition {
    /// The caller supplies the source AST printer for expression conditions.
    pub fn render(&self, print_exp: &impl Fn(&Exp) -> String) -> String {
        match self {
            Self::Condition(exp) => {
                with_position(print_exp(exp), Some(exp.0.meta.position.clone()))
            }
            Self::OpaqueCondition(description) => description.clone(),
            Self::Alternative { index, count } => {
                format!("alternative {} of {count}", index.wrapping_add(1))
            }
        }
    }
}
#[derive(Clone, Debug)]
pub struct VerifierStateFrame {
    pub branch_condition: Option<BranchCondition>,
    pub steps: Vec<VerifierStep>,
}
#[derive(Clone, Debug, Default)]
pub struct VerifierState {
    pub frames: Vec<VerifierStateFrame>,
}
impl VerifierState {
    pub fn try_render<E>(
        &self,
        print_exp: &impl Fn(&Exp) -> Result<String, E>,
    ) -> Result<String, E> {
        let mut lines = Vec::new();
        for (depth, frame) in self.frames.iter().enumerate() {
            if let Some(branch) = &frame.branch_condition {
                let text = match branch {
                    BranchCondition::Condition(exp) => {
                        with_position(print_exp(exp)?, Some(exp.0.meta.position.clone()))
                    }
                    BranchCondition::OpaqueCondition(text) => text.clone(),
                    BranchCondition::Alternative { index, count } => {
                        format!("alternative {} of {count}", index.wrapping_add(1))
                    }
                };
                lines.push(format!(
                    "{}branch {text}:",
                    "  ".repeat(depth.saturating_sub(1))
                ));
            }
            for step in &frame.steps {
                lines.push(format!("{}{}", "  ".repeat(depth), step.render()));
            }
        }
        Ok(lines.join("\n"))
    }
    pub fn render(&self, print_exp: &impl Fn(&Exp) -> String) -> String {
        let mut lines = Vec::new();
        for (depth, frame) in self.frames.iter().enumerate() {
            if let Some(branch) = &frame.branch_condition {
                lines.push(format!(
                    "{}branch {}:",
                    "  ".repeat(depth.saturating_sub(1)),
                    branch.render(print_exp)
                ));
            }
            for step in &frame.steps {
                lines.push(format!("{}{}", "  ".repeat(depth), step.render()));
            }
        }
        lines.join("\n")
    }
}
fn with_position(text: String, position: Option<Position>) -> String {
    match position.and_then(|p| p.line_column().cloned()) {
        Some(pos) => format!("{text} ({}:{})", pos.line(), pos.column()),
        None => text,
    }
}
