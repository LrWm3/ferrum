//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/Z3ProverStdIO.scala
//!
//! Purpose:
//! Specialize shared SMT-LIB transport for Z3.
//!
//! Planned Rust structure:
//! Z3ProverStdIO companion supplies version, dependency, executable, preamble, startup and seed
//! options; implementation resolves path, emits settings and timeout.
//!
//! Behavior to preserve:
//! Minimum 4.5.0, startup -smt2 -in; cache timeout changes, select rlimit scaled by resources/ms or
//! timeout, and read success. When configured disableNL, emit smt.arith.nl false after settings.
//!
//! Integration:
//! decider::prover_std_io, interfaces::decider::prover, config and common::config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Timeout arithmetic and process lifecycle.
//!
//! Status: native solver profile, settings and process constructor implemented; command-line Config wiring remains.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.

use super::prover_std_io::{ProverEvent, ProverSettings, ProverStdIo, SolverProfile};
use crate::common::config::package::Version;
use crate::state::terms::TermFactory;
use std::path::PathBuf;
pub fn profile() -> SolverProfile {
    SolverProfile {
        name: "Z3".into(),
        minimum_version: Version::new("4.5.0"),
        maximum_version: None,
        environment_variable: "Z3_EXE".into(),
        dependency_url: "https://github.com/Z3Prover/z3".into(),
        static_preamble: "/z3config.smt2".into(),
        startup_args: vec!["-smt2".into(), "-in".into()],
        seed_options: vec![
            "sat.random_seed".into(),
            "nlsat.seed".into(),
            "fp.spacer.random_seed".into(),
            "smt.random_seed".into(),
            "sls.random_seed".into(),
        ],
        timeout_option: "timeout".into(),
        resource_option: "rlimit".into(),
        supports_disable_nonlinear: true,
    }
}
pub fn settings(executable: PathBuf) -> ProverSettings {
    ProverSettings::new(executable, 10000)
}
pub fn new(
    unique_id: String,
    settings: ProverSettings,
    factory: TermFactory,
    report: impl FnMut(ProverEvent) + Send + 'static,
) -> ProverStdIo {
    ProverStdIo::new(unique_id, settings, profile(), factory, report)
}
