//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/logger/renderer/SimpleTreeRenderer.scala
//!
//! Purpose:
//! Render symbolic records as an indented textual branch tree.
//!
//! Planned Rust structure:
//! Port SimpleTreeRenderer render, renderMember, recursive toSimpleTree and indentation helpers.
//!
//! Behavior to preserve:
//! Open/close events change indentation with branch minimum; render data and joins, branch labels
//! use condition/negation for at most two branches or numbered branches otherwise, and unreachable
//! branches print only the unreachable marker. Preserve member and branch order.
//!
//! Integration:
//! logger::symb_ex_logger, logger::records::{data,scoping,structural} and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered record traversal.
//!
//! Open decisions:
//! Agree on renderer snapshots and branch IDs with logger.
//!
//! Status: source indentation, scope and branch tree rendering implemented with injected exact text renderers.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::renderer::Renderer;
use crate::logger::records::{
    scoping::{close_scope_record::CloseScopeRecord, open_scope_record::OpenScopeRecord},
    structural::branching_record::BranchingRecord,
    symbolic_record::{RecordError, RecordRef, RecordRenderer},
};
use crate::state::terms::TermFactory;
pub struct SimpleTreeRenderer<'a> {
    pub text: &'a dyn RecordRenderer,
    pub factory: &'a TermFactory,
}
impl SimpleTreeRenderer<'_> {
    fn tree(
        &self,
        records: &[RecordRef],
        minimum: usize,
        level: usize,
    ) -> Result<String, RecordError> {
        let mut text = String::new();
        let mut level = level;
        for record in records {
            if record.as_any().is::<OpenScopeRecord>() {
                level += 1;
            } else if record.as_any().is::<CloseScopeRecord>() {
                level = minimum.max(level.saturating_sub(1));
            } else if let Some(branching) = record.as_any().downcast_ref::<BranchingRecord>() {
                let branches = branching.branch_infos()?;
                for (index, branch) in branches.iter().enumerate() {
                    let label = if branches.len() <= 2 {
                        branching
                            .condition
                            .as_ref()
                            .map(|condition| {
                                self.text.term(&if index == 0 {
                                    condition.clone()
                                } else {
                                    self.factory.not(condition.clone())
                                })
                            })
                            .transpose()?
                    } else {
                        None
                    };
                    text.push_str(&format!(
                        "{}Branch {}:\n",
                        "  ".repeat(level),
                        label.unwrap_or_else(|| (index + 1).to_string())
                    ));
                    text.push_str(&format!(
                        "{}comment: {}\n",
                        "  ".repeat(level + 1),
                        if branch.is_reachable {
                            "Reachable"
                        } else {
                            "Unreachable"
                        }
                    ));
                    if branch.is_reachable {
                        text.push_str(&self.tree(&branch.records, level + 1, level + 1)?);
                    }
                }
            } else if record.is_joining() {
                text.push_str(&format!("{}Join\n", "  ".repeat(level)));
            } else if record.as_data_record().is_some() {
                text.push_str(&format!(
                    "{}{}\n",
                    "  ".repeat(level),
                    record.render(self.text)?
                ));
            } else {
                return Err(RecordError::Unsupported("unknown symbolic record"));
            }
        }
        Ok(text)
    }
}
impl Renderer<[RecordRef]> for SimpleTreeRenderer<'_> {
    type Output = String;
    type Error = RecordError;
    fn render_member(&self, member: &[RecordRef]) -> Result<String, RecordError> {
        self.tree(member, 0, 0)
    }
    fn render(&self, members: &[&[RecordRef]]) -> Result<String, RecordError> {
        let mut result = String::new();
        for member in members {
            result.push_str(&self.render_member(member)?);
            result.push('\n');
        }
        Ok(result)
    }
}
