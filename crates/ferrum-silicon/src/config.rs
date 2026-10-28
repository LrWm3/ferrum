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
//! Status: partial; source mode enums implemented. CLI options and validation remain pending.

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
