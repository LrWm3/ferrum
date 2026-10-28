//! Port plan: Represent proof errors, reasons and legacy solver models.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/verifier/VerificationError.scala
//!
//! Purpose:
//! Represent proof errors, reasons and legacy solver models.
//!
//! Planned Rust structure:
//! ModelEntry/ValueEntry variants, MapEntry, Model, Counterexample and transformer; ErrorMessage,
//! VerificationError, FailureContext, PartialVerificationError, AbstractVerificationError/Reason,
//! DummyNode/Reason, errors and reasons families.
//!
//! Behavior to preserve:
//! Keep distinct error IDs and reason IDs, offending node and reason, cached flag and failure
//! contexts. Include
//! assignment/call/contracts/assert/inhale/exhale/loop/fold/wand/havoc/termination/internal errors
//! and permission, null, arithmetic, bounds, injectivity, timeout and unsupported reasons.
//! Transform error node first then reason and retain contexts; special node positions and
//! counterexample wrappers matter. Model resolution accepts ordered :var constraints, rejects
//! malformed forms, and model parse failures throw.
//!
//! Integration:
//! ast::{ast,expression,statement,program},
//! verifier::{model_parser,verification_result,counterexample}, reporter and Silicon rules.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, lifecycle, error handling and provisional
//! ownership; retain observable source behavior.
//!
//! Open decisions:
//! Reconcile error-node and callback ownership, extensibility, transformed counterexamples and
//! result boundary with AST metadata, plugins and Silicon.
//!
//! Status: partial. Model entries, constraint resolution and counterexample
//! contracts are implemented; concrete verification errors and reasons remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

/// Solver model values as represented in VerificationError.scala.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ValueEntry {
    Unspecified,
    Constant(String),
    Application {
        name: String,
        arguments: Vec<ValueEntry>,
    },
}
impl fmt::Display for ValueEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unspecified => f.write_str("#unspecified"),
            Self::Constant(v) => f.write_str(v),
            Self::Application { name, arguments } => write!(
                f,
                "({} {})",
                name,
                arguments
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MapEntry {
    pub options: HashMap<Vec<ValueEntry>, ValueEntry>,
    pub default: ValueEntry,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ModelEntry {
    Value(ValueEntry),
    Map(MapEntry),
}
impl fmt::Display for ModelEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Value(v) => v.fmt(f),
            Self::Map(m) => m.fmt(f),
        }
    }
}
impl fmt::Display for MapEntry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.options.is_empty() {
            write!(f, "{{\n    {}\n}}", self.default)
        } else {
            let options = self
                .options
                .iter()
                .map(|(args, value)| {
                    format!(
                        "    {} -> {}",
                        args.iter()
                            .map(ToString::to_string)
                            .collect::<Vec<_>>()
                            .join(" "),
                        value
                    )
                })
                .collect::<Vec<_>>()
                .join("\n");
            write!(f, "{{\n{}\n    else -> {}\n}}", options, self.default)
        }
    }
}
impl MapEntry {
    fn single(entry: &ValueEntry) -> Option<(String, ValueEntry)> {
        match entry {
            ValueEntry::Application { name, arguments } if name == "=" && arguments.len() == 2 => {
                match &arguments[0] {
                    ValueEntry::Application {
                        name,
                        arguments: vars,
                    } if name == ":var" && vars.len() == 1 => match &vars[0] {
                        ValueEntry::Constant(i) => Some((i.clone(), arguments[1].clone())),
                        _ => None,
                    },
                    _ => None,
                }
            }
            _ => None,
        }
    }
    pub fn parse_arg_constraint_conjunction(entry: &ValueEntry) -> Option<Vec<ValueEntry>> {
        match entry {
            ValueEntry::Application { name, arguments } if name == "and" => {
                let entries = arguments
                    .iter()
                    .map(Self::single)
                    .collect::<Option<Vec<_>>>()?;
                if entries
                    .iter()
                    .enumerate()
                    .all(|(i, (index, _))| *index == i.to_string())
                {
                    Some(entries.into_iter().map(|(_, v)| v).collect())
                } else {
                    None
                }
            }
            _ => match Self::single(entry) {
                Some((index, value)) if index == "0" => Some(vec![value]),
                _ => None,
            },
        }
    }
    pub fn parse_arg_constraint_disjunction(entry: &ValueEntry) -> Option<Vec<Vec<ValueEntry>>> {
        match entry {
            ValueEntry::Application { name, arguments } if name == "or" => arguments
                .iter()
                .map(Self::parse_arg_constraint_conjunction)
                .collect(),
            _ => Self::parse_arg_constraint_conjunction(entry).map(|v| vec![v]),
        }
    }
    pub fn resolve_function_definition(&self) -> Self {
        if self.options.is_empty() && matches!(self.default, ValueEntry::Application { .. }) {
            if let Some(args) = Self::parse_arg_constraint_disjunction(&self.default) {
                return Self {
                    options: args
                        .into_iter()
                        .map(|a| (a, ValueEntry::Constant("true".into())))
                        .collect(),
                    default: ValueEntry::Constant("false".into()),
                };
            }
        }
        self.clone()
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Model {
    pub entries: HashMap<String, ModelEntry>,
}
impl fmt::Display for Model {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            self.entries
                .iter()
                .map(|(k, v)| format!("{k} -> {v}"))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}
pub trait Counterexample: fmt::Debug + Send + Sync {
    fn model(&self) -> &Model;
}
#[derive(Clone, Debug)]
pub struct SimpleCounterexample {
    pub model: Model,
}
impl Counterexample for SimpleCounterexample {
    fn model(&self) -> &Model {
        &self.model
    }
}
pub type CounterexampleTransformer =
    Arc<dyn Fn(Arc<dyn Counterexample>) -> Arc<dyn Counterexample> + Send + Sync>;
