//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/AnnotationSupporter.scala
//!
//! Purpose:
//! Interpret per-member verifier annotations.
//!
//! Planned Rust structure:
//! Port annotation constants and getProverConfigArgs, getExhaleMode/QP, getJoinMode and
//! getStateConsolidationMode.
//!
//! Behavior to preserve:
//! Parse option=value at first equals; warn and ignore malformed entries. Preserve named and
//! numeric mode aliases, empty moreJoins as all, and warnings on invalid values.
//!
//! Integration:
//! config modes, Silver ast annotation info and reporter; method/function verification callers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for configuration and diagnostics.
//!
//! Open decisions:
//! Agree on numeric enum parsing and map duplicate semantics with config and reporter.
//!
//! Status: partial; source annotation parsing and warnings implemented.
//! Uses the shared Config mode enums; concrete frontend lifecycle integration is pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2025 ETH Zurich.
use crate::config::{ExhaleMode, JoinMode, StateConsolidationMode};
use crate::package::Map;
use ferrum_silver::ast::ast::Info;

pub const PROVER_CONFIG: &str = "proverConfigArgs";
pub const EXHALE_MODE: &str = "exhaleMode";
pub const EXHALE_MODE_QP: &str = "exhaleModeQP";
pub const JOIN_MODE: &str = "moreJoins";
pub const CONSOLIDATION_MODE: &str = "stateConsolidationMode";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AnnotationError<E> {
    Reporter(E),
    InvalidJoinId(i32),
}
fn values<'a>(info: &'a Info, key: &str) -> Option<&'a Vec<String>> {
    match info.find(&|x| matches!(x, Info::Annotation(_)))? {
        Info::Annotation(values) => values.get(key),
        _ => unreachable!(),
    }
}
fn seq_text(v: &[String]) -> String {
    format!("List({})", v.join(", "))
}
pub fn prover_config_args<E>(
    member: &str,
    info: &Info,
    mut warn: impl FnMut(String) -> Result<(), E>,
) -> Result<Map<String, String>, AnnotationError<E>> {
    let mut result = Map::new();
    if let Some(options) = values(info, PROVER_CONFIG) {
        for option in options {
            if let Some((name, value)) = option.split_once('=') {
                result.insert(name.into(), value.into());
            } else {
                warn(format!("Invalid {PROVER_CONFIG} annotation {option} on member {member}. Required format for each option is optionName=value.")).map_err(AnnotationError::Reporter)?;
            }
        }
    }
    Ok(result)
}
pub fn exhale_mode<E>(
    member: &str,
    info: &Info,
    quantified: bool,
    mut warn: impl FnMut(String) -> Result<(), E>,
) -> Result<Option<ExhaleMode>, AnnotationError<E>> {
    let key = if quantified {
        EXHALE_MODE_QP
    } else {
        EXHALE_MODE
    };
    let Some(v) = values(info, key) else {
        return Ok(None);
    };
    let mode = match v.as_slice() {
        [s] if s == "0" || s == "greedy" => Some(ExhaleMode::Greedy),
        [s] if s == "1" || s == "mce" || s == "moreCompleteExhale" => {
            Some(ExhaleMode::MoreComplete)
        }
        [s] if s == "2" || s == "mceOnDemand" => Some(ExhaleMode::MoreCompleteOnDemand),
        _ => None,
    };
    if mode.is_none() {
        warn(format!(
            "Member {member} has invalid {key} annotation value {}. Annotation will be ignored.",
            seq_text(v)
        ))
        .map_err(AnnotationError::Reporter)?;
    }
    Ok(mode)
}
/// IDs correspond to Config.JoinMode enumeration: off=0, impure=1, all=2.
pub fn join_mode<E>(
    member: &str,
    info: &Info,
    mut warn: impl FnMut(String) -> Result<(), E>,
) -> Result<Option<JoinMode>, AnnotationError<E>> {
    let Some(v) = values(info, JOIN_MODE) else {
        return Ok(None);
    };
    let text = match v.as_slice() {
        [] => return Ok(Some(JoinMode::All)),
        [s] if s == "all" => return Ok(Some(JoinMode::All)),
        [s] if s == "off" => return Ok(Some(JoinMode::Off)),
        [s] if s == "impure" => return Ok(Some(JoinMode::Impure)),
        [s] => s.clone(),
        _ => seq_text(v),
    };
    if v.len() == 1 {
        if let Ok(id) = text.parse::<i32>() {
            return JoinMode::try_from(id)
                .map(Some)
                .map_err(AnnotationError::InvalidJoinId);
        }
    }
    warn(format!("Member {member} has invalid {JOIN_MODE} annotation value {text}. Annotation will be ignored.")).map_err(AnnotationError::Reporter)?;
    Ok(None)
}
/// IDs correspond to Config.StateConsolidationMode enumeration, in declaration order.
pub fn consolidation_mode<E>(
    member: &str,
    info: &Info,
    mut warn: impl FnMut(String) -> Result<(), E>,
) -> Result<Option<StateConsolidationMode>, AnnotationError<E>> {
    let Some(v) = values(info, CONSOLIDATION_MODE) else {
        return Ok(None);
    };
    let names = [
        "minimal",
        "default",
        "retrying",
        "minimalRetrying",
        "moreCompleteExhale",
        "lastRetry",
        "retryingFailOnly",
        "lastRetryFailOnly",
    ];
    let id = if let [value] = v.as_slice() {
        names
            .iter()
            .position(|name| value == name)
            .map(|n| n as i32)
            .or_else(|| value.parse::<i32>().ok().filter(|id| (0..=7).contains(id)))
    } else {
        None
    };
    if id.is_none() {
        warn(format!("Member {member} has invalid {CONSOLIDATION_MODE} annotation value. Annotation will be ignored.")).map_err(AnnotationError::Reporter)?;
    }
    Ok(id.map(|id| StateConsolidationMode::try_from(id).expect("validated id")))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn invalid_numeric_join_propagates_but_consolidation_warns() {
        let info = Info::Annotation(
            [
                (JOIN_MODE.into(), vec!["42".into()]),
                (CONSOLIDATION_MODE.into(), vec!["42".into()]),
            ]
            .into_iter()
            .collect(),
        );
        let mut warnings = Vec::new();
        let join = join_mode(&"m", &info, |w| {
            warnings.push(w);
            Ok::<_, ()>(())
        });
        assert_eq!(join, Err(AnnotationError::InvalidJoinId(42)));
        assert!(warnings.is_empty());
        let mode = consolidation_mode("m", &info, |w| {
            warnings.push(w);
            Ok::<_, ()>(())
        })
        .unwrap();
        assert_eq!(mode, None);
        assert_eq!(warnings.len(), 1);
    }
}
