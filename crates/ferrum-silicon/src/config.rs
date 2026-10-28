//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/Config.scala
//!
//! Purpose:
//! Define Silicon command-line configuration, validation and solver policy.
//!
//! Planned Rust structure:
//! Config extends Silver frontend config; port SMT option/assertion/exhale/saturation converters,
//! all option groups and derived values, validation and final verify. Companion defines
//! ConfigValue, Sink, AssertionMode, ExhaleMode, JoinMode, ProverStateSaturationTimeout and
//! StateConsolidationMode.
//!
//! Behavior to preserve:
//! Preserve defaults and distinction between supplied and default values: Z3 stdio default, QP
//! more-complete default, ordinary greedy default, zero global timeout and error count zero meaning
//! unlimited. Solver timeout derives from config arguments before -t option; flyweight iff Z3-API.
//! Saturation scales five weights with minimum 10ms and disables zero weights/base. Z3 path
//! considers option, environment then PATH; cvc5 option/environment/default. Preserve mode and
//! resource/cache/trigger/branch/debug/axiomatization switches and validation of incompatible
//! mask-heap, parallel/debug, counterexample and solver choices. Prover log $infile is explicitly
//! unimplemented. Preserve parent frontend option behavior and exact error distinctions.
//!
//! Integration:
//! ferrum_silver::frontend::sil_front_end_config, decider solver implementations, verifier and rules.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Native CLI parsing, validation and execution-wide config ownership.
//!
//! Status: source options, defaults, converters, validation and solver settings implemented.
//! Scallop help/abbreviation compatibility and execution-wide policy wiring remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.
/// Source exhale algorithms, including the on-demand fallback.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExhaleMode {
    Greedy,
    MoreComplete,
    MoreCompleteOnDemand,
}
/// IDs match the source Enumeration's declaration order.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(i32)]
pub enum JoinMode {
    Off = 0,
    Impure = 1,
    All = 2,
}
impl TryFrom<i32> for JoinMode {
    type Error = i32;
    fn try_from(value: i32) -> Result<Self, i32> {
        match value {
            0 => Ok(Self::Off),
            1 => Ok(Self::Impure),
            2 => Ok(Self::All),
            _ => Err(value),
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(i32)]
pub enum StateConsolidationMode {
    Minimal = 0,
    Default = 1,
    Retrying = 2,
    MinimalRetrying = 3,
    MoreCompleteExhale = 4,
    LastRetry = 5,
    RetryingFailOnly = 6,
    LastRetryFailOnly = 7,
}
impl TryFrom<i32> for StateConsolidationMode {
    type Error = i32;
    fn try_from(value: i32) -> Result<Self, i32> {
        match value {
            0 => Ok(Self::Minimal),
            1 => Ok(Self::Default),
            2 => Ok(Self::Retrying),
            3 => Ok(Self::MinimalRetrying),
            4 => Ok(Self::MoreCompleteExhale),
            5 => Ok(Self::LastRetry),
            6 => Ok(Self::RetryingFailOnly),
            7 => Ok(Self::LastRetryFailOnly),
            _ => Err(value),
        }
    }
}

pub use crate::decider::prover_std_io::AssertionMode;
pub use crate::interfaces::decider::prover::ProverStateSaturationTimeout;
use ferrum_silver::frontend::sil_front_end_config::SilFrontendConfig;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

/// Keep user-supplied values distinct from defaults, as Scallop does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConfigValue<T> {
    Default(T),
    User(T),
}
impl<T> ConfigValue<T> {
    pub fn value(&self) -> &T {
        match self {
            Self::Default(v) | Self::User(v) => v,
        }
    }
    pub fn or_else(self, f: impl FnOnce(T) -> T) -> T {
        match self {
            Self::Default(v) => f(v),
            Self::User(v) => v,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Sink {
    Stdio,
    File,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigError(pub String);
impl std::fmt::Display for ConfigError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for ConfigError {}

#[derive(Clone, Debug)]
pub struct Config {
    pub frontend: SilFrontendConfig,
    pub disable_subsumption: bool,
    pub report_reason_unknown: bool,
    pub disable_short_circuiting_evaluations: bool,
    pub enable_simplified_unfolds: bool,
    pub disable_nl: bool,
    pub prover_enable_time_bounds: bool,
    pub prover_randomize_seeds: bool,
    pub enable_temp_directory: bool,
    pub disable_value_map_caching: bool,
    pub disable_isc_triggers: bool,
    pub disable_chunk_order_heuristics: bool,
    pub enable_predicate_triggers_on_inhale: bool,
    pub disable_caches: bool,
    pub disable_function_unfold_trigger: bool,
    pub enable_more_complete_exhale: bool,
    pub mask_heap_mode: bool,
    pub simplify_on_consume: bool,
    pub unsafe_wildcard_optimization: bool,
    pub parallelize_branches: bool,
    pub generate_block_messages: bool,
    pub print_translated_program: bool,
    pub print_method_cf_gs: bool,
    pub disable_catching_exceptions: bool,
    pub enable_branchcondition_reporting: bool,
    pub use_old_axiomatization: bool,
    pub disable_havoc_hack407: bool,
    pub conditionalize_permissions: bool,
    pub alternative_function_verification_order: bool,
    pub enable_debugging: bool,
    pub recursive_predicate_unfoldings: i32,
    pub timeout: i32,
    pub check_timeout: i32,
    pub prover_saturation_timeout: i32,
    pub push_timeout: i32,
    pub z3_resources_per_millisecond: i32,
    pub cvc5_resources_per_millisecond: i32,
    pub qp_split_timeout: i32,
    pub number_of_errors_to_report: i32,
    pub number_of_parallel_verifiers: i32,
    pub assert_timeout: Option<i32>,
    pub report_state_after: Option<i32>,
    pub include_methods: String,
    pub exclude_methods: String,
    pub temp_directory: String,
    pub prover: String,
    pub log_level: Option<String>,
    pub z3_exe: Option<String>,
    pub cvc5_exe: Option<String>,
    pub prover_args: Option<String>,
    pub log_config: Option<String>,
    pub set_axiomatization_file: Option<String>,
    pub multiset_axiomatization_file: Option<String>,
    pub sequence_axiomatization_file: Option<String>,
    pub map_axiomatization_file: Option<String>,
    pub logger: BTreeMap<String, String>,
    pub prover_config_args: BTreeMap<String, String>,
    pub raw_prover_log_file: ConfigValue<String>,
    pub saturation_weights: SaturationWeights,
    pub assertion_mode: AssertionMode,
    pub more_joins: JoinMode,
    pub exhale_mode_option: Option<ExhaleMode>,
    pub exhale_mode_option_qp: Option<ExhaleMode>,
    pub state_consolidation_mode: StateConsolidationMode,
    supplied: BTreeSet<String>,
}
impl Default for Config {
    fn default() -> Self {
        Self {
            frontend: SilFrontendConfig::new("Ferrum"),
            disable_subsumption: false,
            report_reason_unknown: false,
            disable_short_circuiting_evaluations: false,
            enable_simplified_unfolds: false,
            disable_nl: false,
            prover_enable_time_bounds: false,
            prover_randomize_seeds: false,
            enable_temp_directory: false,
            disable_value_map_caching: false,
            disable_isc_triggers: false,
            disable_chunk_order_heuristics: false,
            enable_predicate_triggers_on_inhale: false,
            disable_caches: false,
            disable_function_unfold_trigger: false,
            enable_more_complete_exhale: false,
            mask_heap_mode: false,
            simplify_on_consume: false,
            unsafe_wildcard_optimization: false,
            parallelize_branches: false,
            generate_block_messages: false,
            print_translated_program: false,
            print_method_cf_gs: false,
            disable_catching_exceptions: false,
            enable_branchcondition_reporting: false,
            use_old_axiomatization: false,
            disable_havoc_hack407: false,
            conditionalize_permissions: false,
            alternative_function_verification_order: false,
            enable_debugging: false,
            recursive_predicate_unfoldings: 1,
            timeout: 0,
            check_timeout: 10,
            prover_saturation_timeout: 100,
            push_timeout: 0,
            z3_resources_per_millisecond: 10000,
            cvc5_resources_per_millisecond: 50,
            qp_split_timeout: 500,
            number_of_errors_to_report: 1,
            number_of_parallel_verifiers: std::thread::available_parallelism()
                .map_or(1, |n| n.get() as i32),
            assert_timeout: None,
            report_state_after: None,
            include_methods: ".*".into(),
            exclude_methods: String::new(),
            temp_directory: "./tmp".into(),
            prover: "Z3".into(),
            log_level: None,
            z3_exe: None,
            cvc5_exe: None,
            prover_args: None,
            log_config: None,
            set_axiomatization_file: None,
            multiset_axiomatization_file: None,
            sequence_axiomatization_file: None,
            map_axiomatization_file: None,
            logger: BTreeMap::new(),
            prover_config_args: BTreeMap::new(),
            raw_prover_log_file: ConfigValue::Default("logfile".into()),
            saturation_weights: SaturationWeights::default(),
            assertion_mode: AssertionMode::PushPop,
            more_joins: JoinMode::Off,
            exhale_mode_option: None,
            exhale_mode_option_qp: None,
            state_consolidation_mode: StateConsolidationMode::Default,
            supplied: BTreeSet::new(),
        }
    }
}
impl Config {
    /// Parse backend options and pass the shared options to the Silver frontend.
    pub fn parse(args: &[String]) -> Result<Self, ConfigError> {
        let mut config = Self::default();
        let mut shared = Vec::new();
        let mut i = 0;
        while i < args.len() {
            let arg = &args[i];
            i += 1;
            if arg == "--" {
                shared.extend_from_slice(&args[i - 1..]);
                break;
            }
            if arg.starts_with("-L") {
                let properties = if arg == "-L" {
                    let value = args
                        .get(i)
                        .ok_or_else(|| ConfigError("Missing value for option -L".into()))?;
                    i += 1;
                    value.as_str()
                } else {
                    &arg[2..]
                };
                for property in properties.split(',') {
                    let (key, value) = property.split_once('=').ok_or_else(|| {
                        ConfigError(format!("Invalid logger property {property}"))
                    })?;
                    config.logger.insert(key.into(), value.into());
                }
                continue;
            }
            let Some(option) = arg.strip_prefix("--") else {
                shared.push(arg.clone());
                continue;
            };
            let (name, inline) = option
                .split_once('=')
                .map_or((option, None), |(n, v)| (n, Some(v)));
            let mut value = || -> Result<String, ConfigError> {
                if let Some(v) = inline {
                    return Ok(v.into());
                }
                let v = args
                    .get(i)
                    .ok_or_else(|| ConfigError(format!("Missing value for option --{name}")))?
                    .clone();
                i += 1;
                Ok(v)
            };
            match name {
                "disableSubsumption" => config.disable_subsumption = parse_flag(inline, name)?,
                "reportReasonUnknown" => config.report_reason_unknown = parse_flag(inline, name)?,
                "disableShortCircuitingEvaluations" => {
                    config.disable_short_circuiting_evaluations = parse_flag(inline, name)?
                }
                "enableSimplifiedUnfolds" => {
                    config.enable_simplified_unfolds = parse_flag(inline, name)?
                }
                "disableNL" => config.disable_nl = parse_flag(inline, name)?,
                "proverEnableTimeBounds" => {
                    config.prover_enable_time_bounds = parse_flag(inline, name)?
                }
                "proverRandomizeSeeds" => config.prover_randomize_seeds = parse_flag(inline, name)?,
                "enableTempDirectory" => config.enable_temp_directory = parse_flag(inline, name)?,
                "disableValueMapCaching" => {
                    config.disable_value_map_caching = parse_flag(inline, name)?
                }
                "disableISCTriggers" => config.disable_isc_triggers = parse_flag(inline, name)?,
                "disableChunkOrderHeuristics" => {
                    config.disable_chunk_order_heuristics = parse_flag(inline, name)?
                }
                "enablePredicateTriggersOnInhale" => {
                    config.enable_predicate_triggers_on_inhale = parse_flag(inline, name)?
                }
                "disableCaches" => config.disable_caches = parse_flag(inline, name)?,
                "disableFunctionUnfoldTrigger" => {
                    config.disable_function_unfold_trigger = parse_flag(inline, name)?
                }
                "enableMoreCompleteExhale" => {
                    config.enable_more_complete_exhale = parse_flag(inline, name)?
                }
                "maskHeapMode" => config.mask_heap_mode = parse_flag(inline, name)?,
                "simplifyOnConsume" => config.simplify_on_consume = parse_flag(inline, name)?,
                "unsafeWildcardOptimization" => {
                    config.unsafe_wildcard_optimization = parse_flag(inline, name)?
                }
                "parallelizeBranches" => config.parallelize_branches = parse_flag(inline, name)?,
                "generateBlockMessages" => {
                    config.generate_block_messages = parse_flag(inline, name)?
                }
                "printTranslatedProgram" => {
                    config.print_translated_program = parse_flag(inline, name)?
                }
                "printMethodCFGs" => config.print_method_cf_gs = parse_flag(inline, name)?,
                "disableCatchingExceptions" => {
                    config.disable_catching_exceptions = parse_flag(inline, name)?
                }
                "enableBranchconditionReporting" => {
                    config.enable_branchcondition_reporting = parse_flag(inline, name)?
                }
                "useOldAxiomatization" => config.use_old_axiomatization = parse_flag(inline, name)?,
                "disableHavocHack407" => config.disable_havoc_hack407 = parse_flag(inline, name)?,
                "conditionalizePermissions" => {
                    config.conditionalize_permissions = parse_flag(inline, name)?
                }
                "alternativeFunctionVerificationOrder" => {
                    config.alternative_function_verification_order = parse_flag(inline, name)?
                }
                "enableDebugging" => config.enable_debugging = parse_flag(inline, name)?,
                "recursivePredicateUnfoldings" => {
                    config.recursive_predicate_unfoldings = parse_int(&value()?, name)?
                }
                "timeout" => config.timeout = parse_int(&value()?, name)?,
                "checkTimeout" => config.check_timeout = parse_int(&value()?, name)?,
                "proverSaturationTimeout" => {
                    config.prover_saturation_timeout = parse_int(&value()?, name)?
                }
                "pushTimeout" => config.push_timeout = parse_int(&value()?, name)?,
                "z3ResourcesPerMillisecond" => {
                    config.z3_resources_per_millisecond = parse_int(&value()?, name)?
                }
                "cvc5ResourcesPerMillisecond" => {
                    config.cvc5_resources_per_millisecond = parse_int(&value()?, name)?
                }
                "qpSplitTimeout" => config.qp_split_timeout = parse_int(&value()?, name)?,
                "numberOfErrorsToReport" => {
                    config.number_of_errors_to_report = parse_int(&value()?, name)?
                }
                "numberOfParallelVerifiers" => {
                    config.number_of_parallel_verifiers = parse_int(&value()?, name)?
                }
                "assertTimeout" => config.assert_timeout = Some(parse_int(&value()?, name)?),
                "reportStateAfter" => config.report_state_after = Some(parse_int(&value()?, name)?),
                "includeMethods" => {
                    config.include_methods =
                        crate::common::config::package::wildcard_to_regex(&value()?)
                }
                "excludeMethods" => config.exclude_methods = value()?,
                "tempDirectory" => config.temp_directory = value()?,
                "prover" => config.prover = value()?,
                "logLevel" => config.log_level = Some(value()?.to_uppercase()),
                "z3Exe" => config.z3_exe = Some(value()?),
                "cvc5Exe" => config.cvc5_exe = Some(value()?),
                "proverArgs" => config.prover_args = Some(value()?),
                "logConfig" => config.log_config = Some(value()?),
                "setAxiomatizationFile" => config.set_axiomatization_file = Some(value()?),
                "multisetAxiomatizationFile" => {
                    config.multiset_axiomatization_file = Some(value()?)
                }
                "sequenceAxiomatizationFile" => {
                    config.sequence_axiomatization_file = Some(value()?)
                }
                "mapAxiomatizationFile" => config.map_axiomatization_file = Some(value()?),
                "proverConfigArgs" => config.prover_config_args = parse_smt_options(&value()?)?,
                "proverLogFile" => config.raw_prover_log_file = ConfigValue::User(value()?),
                "proverSaturationTimeoutWeights" => config.saturation_weights = value()?.parse()?,
                "assertionMode" => {
                    config.assertion_mode = match value()?.to_lowercase().as_str() {
                        "pp" => AssertionMode::PushPop,
                        "sc" => AssertionMode::SoftConstraints,
                        _ => return Err(ConfigError("unexpected arguments".into())),
                    }
                }
                "moreJoins" => {
                    config.more_joins = JoinMode::try_from(parse_int(&value()?, name)?)
                        .map_err(|v| ConfigError(format!("Invalid join mode {v}")))?
                }
                "stateConsolidationMode" => {
                    config.state_consolidation_mode =
                        StateConsolidationMode::try_from(parse_int(&value()?, name)?).map_err(
                            |v| ConfigError(format!("Invalid state consolidation mode {v}")),
                        )?
                }
                "exhaleMode" => config.exhale_mode_option = Some(parse_exhale(&value()?)?),
                "exhaleModeQP" => config.exhale_mode_option_qp = Some(parse_exhale(&value()?)?),
                _ => {
                    if let Some(v) = inline {
                        shared.extend([format!("--{name}"), v.into()]);
                    } else {
                        shared.push(arg.clone());
                    }
                    // Consume shared option values here so a value beginning with --
                    // cannot accidentally be interpreted as a backend option.
                    if inline.is_none() && matches!(name, "select" | "plugin" | "counterexample") {
                        shared.push(value()?);
                    }
                    continue;
                }
            }
            config.supplied.insert(name.into());
        }
        config.frontend = SilFrontendConfig::parse_shared("Ferrum", &shared);
        if let Some(error) = &config.frontend.error {
            return Err(ConfigError(error.clone()));
        }
        if !config.frontend.print_help && !config.frontend.print_version {
            config.validate()?;
        }
        Ok(config)
    }
}

fn parse_flag(value: Option<&str>, name: &str) -> Result<bool, ConfigError> {
    match value {
        None | Some("true") => Ok(true),
        Some("false") => Ok(false),
        _ => Err(ConfigError(format!("Invalid boolean for --{name}"))),
    }
}
fn parse_int(value: &str, name: &str) -> Result<i32, ConfigError> {
    value
        .parse()
        .map_err(|_| ConfigError(format!("Invalid integer for --{name}: {value}")))
}
fn parse_exhale(value: &str) -> Result<ExhaleMode, ConfigError> {
    match value {
        "0" => Ok(ExhaleMode::Greedy),
        "1" => Ok(ExhaleMode::MoreComplete),
        "2" => Ok(ExhaleMode::MoreCompleteOnDemand),
        _ => Err(ConfigError("unexpected arguments".into())),
    }
}
pub fn parse_smt_options(value: &str) -> Result<BTreeMap<String, String>, ConfigError> {
    let mut options = BTreeMap::new();
    for pair in value.split(' ').map(str::trim).filter(|p| !p.is_empty()) {
        // Java/Scala split removes trailing empty components.
        let fields = pair.split('=').collect::<Vec<_>>();
        let end = fields
            .iter()
            .rposition(|s| !s.is_empty())
            .map_or(0, |i| i + 1);
        if end != 2 {
            return Err(ConfigError(format!(
                "unexpected arguments '{}'",
                fields[..end].join(", ")
            )));
        }
        options.insert(fields[0].into(), fields[1].into());
    }
    Ok(options)
}
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SaturationWeights {
    pub after_preamble: f32,
    pub after_contract: f32,
    pub after_unfold: f32,
    pub after_inhale: f32,
    pub before_repetition: f32,
}
impl Default for SaturationWeights {
    fn default() -> Self {
        Self {
            after_preamble: 1.0,
            after_contract: 0.5,
            after_unfold: 0.4,
            after_inhale: 0.0,
            before_repetition: 0.0,
        }
    }
}
impl std::str::FromStr for SaturationWeights {
    type Err = ConfigError;
    fn from_str(value: &str) -> Result<Self, ConfigError> {
        let value = value.trim();
        let inner = value
            .strip_prefix('[')
            .and_then(|s| s.strip_suffix(']'))
            .ok_or_else(|| ConfigError("weights must be provided inside square brackets".into()))?;
        // The source deliberately drops unparseable and negative entries before
        // checking the resulting length; it does not reject the original list.
        let values: Vec<f32> = inner
            .split(',')
            .filter_map(|s| s.trim().parse::<f32>().ok())
            .filter(|v| *v >= 0.0)
            .collect();
        let [
            after_preamble,
            after_contract,
            after_unfold,
            after_inhale,
            before_repetition,
        ] = values.as_slice()
        else {
            return Err(ConfigError("expected 5 non-negative floats".into()));
        };
        Ok(Self {
            after_preamble: *after_preamble,
            after_contract: *after_contract,
            after_unfold: *after_unfold,
            after_inhale: *after_inhale,
            before_repetition: *before_repetition,
        })
    }
}
impl SaturationWeights {
    pub fn timeouts(&self, base: i32) -> [Option<ProverStateSaturationTimeout>; 5] {
        [
            (self.after_preamble, "after preamble"),
            (self.after_contract, "after contract"),
            (self.after_unfold, "after unfold"),
            (self.after_inhale, "after inhale"),
            (self.before_repetition, "before repetition"),
        ]
        .map(|(weight, comment)| {
            if weight == 0.0 || base == 0 {
                None
            } else {
                Some(ProverStateSaturationTimeout {
                    timeout_ms: (weight * base as f32).max(10.0) as i32,
                    comment: comment.into(),
                })
            }
        })
    }
}
impl Config {
    pub fn is_supplied(&self, name: &str) -> bool {
        self.supplied.contains(name)
    }
    pub fn output_prover_log(&self) -> bool {
        self.is_supplied("enableTempDirectory") || self.is_supplied("proverLogFile")
    }
    pub fn exhale_mode(&self) -> ExhaleMode {
        self.exhale_mode_option
            .unwrap_or(if self.enable_more_complete_exhale {
                ExhaleMode::MoreComplete
            } else {
                ExhaleMode::Greedy
            })
    }
    pub fn exhale_mode_qp(&self) -> ExhaleMode {
        self.exhale_mode_option_qp
            .unwrap_or(ExhaleMode::MoreComplete)
    }
    pub fn use_flyweight(&self) -> bool {
        self.prover == "Z3-API"
    }
    pub fn map_cache<T>(&self, value: Option<T>) -> Option<T> {
        if self.disable_caches { None } else { value }
    }
    pub fn prover_timeout(&self) -> Result<i32, ConfigError> {
        for (key, value) in &self.prover_config_args {
            if key.eq_ignore_ascii_case("timeout") && value.chars().all(|c| c.is_ascii_digit()) {
                return parse_int(value, "proverConfigArgs timeout");
            }
        }
        if let Some(args) = &self.prover_args {
            let pattern = regex::Regex::new(r"-t:(\d+)").expect("constant regex");
            if let Some(captures) = pattern.captures(args) {
                return parse_int(&captures[1], "proverArgs timeout");
            }
        }
        Ok(0)
    }
    pub fn prover_log_file(&self, suffix: &str) -> Result<PathBuf, ConfigError> {
        match &self.raw_prover_log_file {
            ConfigValue::User(file) if file.eq_ignore_ascii_case("$infile") => Err(ConfigError(
                "Implementation missing: prover log $infile".into(),
            )),
            ConfigValue::User(file) => Ok(PathBuf::from(format!("{file}-{suffix}.smt2"))),
            ConfigValue::Default(_) => {
                Ok(PathBuf::from(&self.temp_directory).join(format!("logfile-{suffix}.smt2")))
            }
        }
    }
    pub fn z3_executable(&self) -> PathBuf {
        if let Some(path) = &self.z3_exe {
            return path.into();
        }
        if let Some(path) = std::env::var_os("Z3_EXE") {
            return path.into();
        }
        let name = if cfg!(windows) { "z3.exe" } else { "z3" };
        if let Some(paths) = std::env::var_os("PATH") {
            if let Some(path) = std::env::split_paths(&paths)
                .map(|p| p.join(name))
                .find(|p| p.exists())
            {
                return path;
            }
        }
        name.into()
    }
    pub fn cvc5_executable(&self) -> PathBuf {
        self.cvc5_exe
            .as_ref()
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("CVC5_EXE").map(PathBuf::from))
            .unwrap_or_else(|| {
                if cfg!(windows) {
                    "cvc5.exe".into()
                } else {
                    "cvc5".into()
                }
            })
    }
    pub fn prover_settings(
        &self,
        suffix: &str,
    ) -> Result<crate::decider::prover_std_io::ProverSettings, ConfigError> {
        let (executable, resources) = match self.prover.as_str() {
            "Z3" => (self.z3_executable(), self.z3_resources_per_millisecond),
            "cvc5" => (self.cvc5_executable(), self.cvc5_resources_per_millisecond),
            "Z3-API" => {
                return Err(ConfigError(
                    "Z3-API requires the native API binding, not stdio settings".into(),
                ));
            }
            other => return Err(ConfigError(format!("Unknown prover '{other}'"))),
        };
        Ok(crate::decider::prover_std_io::ProverSettings {
            executable,
            resources_per_millisecond: resources,
            user_args: self.prover_args.clone(),
            log_file: if self.output_prover_log() {
                Some(self.prover_log_file(suffix)?)
            } else {
                None
            },
            timeout_ms: self.prover_timeout()?,
            time_bounds: self.prover_enable_time_bounds,
            assertion_mode: self.assertion_mode,
            debug: self.enable_debugging,
            counterexamples: self.frontend.counterexample.is_some(),
            report_reason_unknown: self.report_reason_unknown,
            disable_nonlinear: self.disable_nl,
        })
    }
    pub fn validate(&self) -> Result<(), ConfigError> {
        let fail = |message: String| Err(ConfigError(message));
        let incompatible = |a: &str, b: &str| {
            fail(format!(
                "Option {a} is not supported in combination with {b}"
            ))
        };
        if !matches!(self.prover.as_str(), "Z3" | "cvc5" | "Z3-API") {
            return fail(format!(
                "Unknown prover '{}' provided. Expected one of Z3, cvc5, Z3-API.",
                self.prover
            ));
        }
        if self.timeout < 0 {
            return fail(format!(
                "Timeout must be non-negative, but {} was provided",
                self.timeout
            ));
        }
        if self.frontend.ide_mode_advanced && self.parallelize_branches {
            return incompatible("ideModeAdvanced", "parallelizeBranches");
        }
        if let Some(n) = self.report_state_after {
            if n <= 0 {
                return fail(format!(
                    "Option reportStateAfter must be positive, but {n} was provided"
                ));
            }
            if self.parallelize_branches {
                return incompatible("reportStateAfter", "parallelizeBranches");
            }
        }
        if self.disable_nl && self.prover == "cvc5" {
            return fail("Option disableNL is only supported with Z3".into());
        }
        if self.frontend.counterexample.is_some()
            && ((!self.enable_more_complete_exhale && self.exhale_mode_option.is_none())
                || self.exhale_mode_option == Some(ExhaleMode::Greedy))
        {
            return fail(
                "Option counterexample requires setting exhaleMode to 1 (more complete exhale)"
                    .into(),
            );
        }
        if self.enable_more_complete_exhale
            && self
                .exhale_mode_option
                .is_some_and(|m| m != ExhaleMode::MoreComplete)
        {
            return fail(
                "Contradictory values given for options enableMoreCompleteExhale and exhaleMode"
                    .into(),
            );
        }
        if self.simplify_on_consume && !self.mask_heap_mode {
            return fail(
                "Option simplifyOnConsume is only supported in combination with maskHeapMode"
                    .into(),
            );
        }
        if self.mask_heap_mode {
            for (enabled, name) in [
                (self.frontend.counterexample.is_some(), "counterexample"),
                (self.exhale_mode_option.is_some(), "exhaleMode"),
                (self.exhale_mode_option_qp.is_some(), "exhaleModeQP"),
                (self.enable_more_complete_exhale, "enableMoreCompleteExhale"),
                (self.enable_debugging, "enableDebugging"),
            ] {
                if enabled {
                    return incompatible(name, "maskHeapMode");
                }
            }
            if self.enable_predicate_triggers_on_inhale {
                return fail("Option enablePredicateTriggersOnInhale has no effect in combination with maskHeapMode".into());
            }
            if self.state_consolidation_mode != StateConsolidationMode::Default {
                return incompatible("stateConsolidationMode", "maskHeapMode");
            }
        }
        if self.number_of_parallel_verifiers <= 0 {
            return fail(format!(
                "Number of parallel verifiers must be positive, but {} was provided",
                self.number_of_parallel_verifiers
            ));
        }
        // The pinned source intentionally does not validate mapAxiomatizationFile here.
        for (name, path) in [
            ("logConfig", &self.log_config),
            ("setAxiomatizationFile", &self.set_axiomatization_file),
            (
                "multisetAxiomatizationFile",
                &self.multiset_axiomatization_file,
            ),
            (
                "sequenceAxiomatizationFile",
                &self.sequence_axiomatization_file,
            ),
        ] {
            if let Some(path) = path {
                SilFrontendConfig::validate_file_opt(name, path).map_err(ConfigError)?;
            }
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    fn parse(options: &[&str]) -> Result<Config, ConfigError> {
        Config::parse(
            &options
                .iter()
                .chain(["--ignoreFile", "input.vpr"].iter())
                .map(|s| (*s).to_owned())
                .collect::<Vec<_>>(),
        )
    }
    #[test]
    fn preserves_timeout_precedence_and_supplied_defaults() {
        let config = parse(&[
            "--proverArgs",
            "-t:55",
            "--proverConfigArgs",
            "timeout=19",
            "--enableTempDirectory=false",
        ])
        .unwrap();
        assert_eq!(config.prover_timeout().unwrap(), 19);
        assert!(config.output_prover_log());
        assert!(!config.enable_temp_directory);
        assert_eq!(
            config.prover_settings("0").unwrap().log_file,
            Some(PathBuf::from("./tmp/logfile-0.smt2"))
        );
        assert_eq!(config.exhale_mode(), ExhaleMode::Greedy);
        assert_eq!(config.exhale_mode_qp(), ExhaleMode::MoreComplete);
        assert_eq!(config.number_of_errors_to_report, 1);
    }
    #[test]
    fn validates_counterexample_and_mask_combinations() {
        assert!(parse(&["--counterexample", "native"]).is_err());
        assert!(parse(&["--counterexample", "native", "--exhaleMode", "2"]).is_ok());
        assert!(parse(&["--enableMoreCompleteExhale", "--exhaleMode", "2"]).is_err());
        assert!(parse(&["--maskHeapMode", "--exhaleMode", "0"]).is_err());
        assert!(parse(&["--maskHeapMode", "--simplifyOnConsume"]).is_ok());
    }
    #[test]
    fn saturation_preserves_filtering_and_minimum() {
        let weights: SaturationWeights = "[invalid, -1, 1, 0.001, 0.4, 0, 0]".parse().unwrap();
        let times = weights.timeouts(100);
        assert_eq!(times[0].as_ref().unwrap().timeout_ms, 100);
        assert_eq!(times[1].as_ref().unwrap().timeout_ms, 10);
        assert!(times[3].is_none());
        assert!(weights.timeouts(0).iter().all(Option::is_none));
        assert!("[1,2,3,4]".parse::<SaturationWeights>().is_err());
    }
}
