//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/CVC5ProverStdIO.scala
//!
//! Purpose:
//! Specialize the shared SMT-LIB process transport for cvc5.
//!
//! Planned Rust structure:
//! Cvc5ProverStdIO companion supplies name, version bounds, executable environment, dependency,
//! preamble, arguments and random seeds; implementation selects path, settings and timeout.
//!
//! Behavior to preserve:
//! Minimum version 1.0.0, startup --lang=smt2.6; update timeout only when changed, choosing
//! reproducible resource limit multiplied by configured resources/ms or tlimit-per, then consume
//! success response. emitSettings delegates to emit.
//!
//! Integration:
//! decider::prover_std_io, interfaces::decider::prover, config and common::config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Timeout arithmetic and process ownership.
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
        name: "cvc5".into(),
        minimum_version: Version::new("1.0.0"),
        maximum_version: None,
        environment_variable: "CVC5_EXE".into(),
        dependency_url: "https://github.com/cvc5/cvc5".into(),
        static_preamble: "/cvc5config.smt2".into(),
        startup_args: vec!["--lang=smt2.6".into()],
        seed_options: vec!["seed".into(), "sat-random-seed".into()],
        timeout_option: "tlimit-per".into(),
        resource_option: "reproducible-resource-limit".into(),
        supports_disable_nonlinear: false,
    }
}
pub fn settings(executable: PathBuf) -> ProverSettings {
    ProverSettings::new(executable, 50)
}
pub fn new(
    unique_id: String,
    settings: ProverSettings,
    factory: TermFactory,
    report: impl FnMut(ProverEvent) + Send + 'static,
) -> ProverStdIo {
    ProverStdIo::new(unique_id, settings, profile(), factory, report)
}
