//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/frontend/SilFrontEndConfig.scala
//!
//! Purpose:
//! Define shared command-line options, validation and counterexample selection.
//!
//! Planned Rust structure:
//! Model SilFrontendConfig and CounterexampleModel variants Native, Variables, Mapped, Resolved
//! and Raw; expose parser, file validation and error handling.
//!
//! Behavior to preserve:
//! Preserve defaults and visibility for parseOnly, dependencies, no-timing, select, ignoreFile,
//! caching, IDE, smoke, plugins, termination/ADT, permission options, submission and partial
//! results. Validate readable file unless ignored; help/version exit and parse errors remain
//! distinct; unsupported model is rejected.
//!
//! Integration:
//! frontend::sil_frontend configures verifier and plugin manager; reporter consumes errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Choose CLI parser and extendable backend configuration with verifier and sil_frontend.
//!
//! Status: partial; shared options and validation are implemented. Backend option extension
//! and full Scallop-compatible help, parsing and diagnostics remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use std::path::Path;
use std::str::FromStr;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CounterexampleModel {
    Native,
    Variables,
    Mapped,
    Raw,
    Resolved,
}
impl FromStr for CounterexampleModel {
    type Err = String;
    fn from_str(input: &str) -> Result<Self, Self::Err> {
        match input {
            "native" => Ok(Self::Native),
            "variables" => Ok(Self::Variables),
            "mapped" => Ok(Self::Mapped),
            "raw" => Ok(Self::Raw),
            "resolved" => Ok(Self::Resolved),
            _ => Err(format!(
                "Unsupported counterexample model provided. Expected 'resolved', 'raw', 'native', 'variables' or 'mapped' but got {input}"
            )),
        }
    }
}
#[derive(Clone, Debug, Default)]
pub struct SilFrontendConfig {
    pub project_name: String,
    pub error: Option<String>,
    pub parse_only: bool,
    pub file: Option<String>,
    pub dependencies: bool,
    pub no_timing: bool,
    pub select: Option<String>,
    pub ignore_file: bool,
    pub disable_caching: bool,
    pub ide_mode_advanced: bool,
    pub enable_smoke_detection: bool,
    pub disable_default_plugins: bool,
    pub plugin: Option<String>,
    pub counterexample: Option<CounterexampleModel>,
    pub disable_termination_plugin: bool,
    pub disable_adt_plugin: bool,
    pub assume_injectivity_on_inhale: bool,
    pub respect_function_pre_perm_amounts: bool,
    pub submit_for_evaluation: bool,
    pub report_partial_results: bool,
    pub print_help: bool,
    pub print_version: bool,
    exit_requested: bool,
}
impl SilFrontendConfig {
    pub fn new(project_name: impl Into<String>) -> Self {
        Self {
            project_name: project_name.into(),
            ..Self::default()
        }
    }
    pub fn exit(&self) -> bool {
        self.print_help || self.parse_only || self.exit_requested
    }
    pub fn usage(&self) -> String {
        format!("Usage: {} [options] <file>\n\nOptions:", self.project_name)
    }
    /// Preserve the file validation order and source diagnostic text.
    pub fn validate_file_opt(option_name: &str, filepath: &str) -> Result<(), String> {
        if !Path::new(filepath).is_file() {
            return Err(format!(
                "Cannot find file '{filepath}' from '{option_name}' argument"
            ));
        }
        if std::fs::File::open(filepath).is_err() {
            return Err(format!(
                "Cannot read from file '{filepath}' from '{option_name}' argument'"
            ));
        }
        Ok(())
    }
    pub fn validate_file(&self) -> Result<(), String> {
        if self.file.is_none() {
            return Err("Missing required argument 'file'".into());
        }
        if self.ignore_file {
            return Ok(());
        }
        match &self.file {
            Some(file) => Self::validate_file_opt("file", file),
            None => Err("Missing required argument 'file'".into()),
        }
    }
    /// Parse the shared options. Backend-specific option registration and Scallop's
    /// complete help and abbreviation behavior remain to be integrated.
    pub fn parse_shared(project_name: impl Into<String>, args: &[String]) -> Self {
        let mut config = Self::new(project_name);
        let mut index = 0;
        let mut positional = false;
        while index < args.len() {
            let arg = &args[index];
            if !positional && arg == "--" {
                positional = true;
                index += 1;
                continue;
            }
            if !positional && (arg == "--help" || arg == "-h") {
                config.print_help = true;
                config.exit_requested = true;
                return config;
            }
            if !positional && arg == "--version" {
                config.print_version = true;
                config.exit_requested = true;
                return config;
            }
            if !positional && arg.starts_with("--") {
                let option = &arg[2..];
                match option {
                    "parseOnly" => config.parse_only = true,
                    "dependencies" => config.dependencies = true,
                    "no-timing" => config.no_timing = true,
                    "ignoreFile" => config.ignore_file = true,
                    "disableCaching" => config.disable_caching = true,
                    "ideModeAdvanced" => config.ide_mode_advanced = true,
                    "enableSmokeDetection" => config.enable_smoke_detection = true,
                    "disableDefaultPlugins" => config.disable_default_plugins = true,
                    "disableTerminationPlugin" => config.disable_termination_plugin = true,
                    "disableAdtPlugin" => config.disable_adt_plugin = true,
                    "assumeInjectivityOnInhale" => config.assume_injectivity_on_inhale = true,
                    "respectFunctionPrePermAmounts" => {
                        config.respect_function_pre_perm_amounts = true
                    }
                    "submitForEvaluation" => config.submit_for_evaluation = true,
                    "reportPartialResults" => config.report_partial_results = true,
                    "select" | "plugin" | "counterexample" => {
                        index += 1;
                        if index == args.len() {
                            config.fail(format!("Missing value for option --{option}"));
                            return config;
                        }
                        let value = args[index].clone();
                        match option {
                            "select" => config.select = Some(value),
                            "plugin" => config.plugin = Some(value),
                            _ => match value.parse() {
                                Ok(model) => config.counterexample = Some(model),
                                Err(error) => {
                                    config.fail(error);
                                    return config;
                                }
                            },
                        }
                    }
                    _ => {
                        config.fail(format!("Unknown option --{option}"));
                        return config;
                    }
                }
            } else if config.file.replace(arg.clone()).is_some() {
                config.fail("Too many file arguments".into());
                return config;
            }
            index += 1;
        }
        if let Err(error) = config.validate_file() {
            config.fail(error);
        }
        config
    }
    fn fail(&mut self, error: String) {
        self.error = Some(error);
        self.exit_requested = true;
    }
}
