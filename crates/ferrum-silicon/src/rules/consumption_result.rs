//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/ConsumptionResult.scala
//!
//! Purpose:
//! Represent whether permission consumption has completed.
//!
//! Planned Rust structure:
//! ConsumptionResult, Complete and Incomplete carry completion and missing permission term/debug
//! expression; factory checks nonpositivity directly or universally quantified.
//!
//! Behavior to preserve:
//! Use decider.check with supplied timeout; complete short-circuits || while incomplete evaluates
//! and returns the alternative. A failed check yields Incomplete, not an assertion failure.
//!
//! Integration:
//! rules::chunk_supporter, rules::quantified_chunk_support, state::terms and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Permission-result and solver timeout ownership.
//!
//! Status: implemented using an injected fallible solver check.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::state::terms::{Quantifier, Term, TermFactory};
use ferrum_silver::ast::expression::Exp;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsumptionResult {
    Complete,
    Incomplete {
        perms_needed: Term,
        perms_needed_exp: Option<Exp>,
    },
}
impl ConsumptionResult {
    pub fn is_complete(&self) -> bool {
        matches!(self, Self::Complete)
    }
    /// The alternative is lazy: it is evaluated only when this result is incomplete.
    pub fn or_else(self, alternative: impl FnOnce() -> Self) -> Self {
        if self.is_complete() {
            self
        } else {
            alternative()
        }
    }
    /// A failed solver operation is propagated separately from an incomplete consumption.
    pub fn check<E>(
        factory: &TermFactory,
        term: Term,
        exp: Option<Exp>,
        variables: &[Term],
        timeout: i32,
        mut check: impl FnMut(&Term, i32) -> Result<bool, E>,
    ) -> Result<Self, E> {
        let body = factory.is_nonpositive_perm(term.clone());
        let query = if variables.is_empty() {
            body
        } else {
            factory.quantification_without_triggers(
                Quantifier::Forall,
                variables.to_vec(),
                body,
                TermFactory::forall_default_name(),
                false,
                None,
            )
        };
        Ok(if check(&query, timeout)? {
            Self::Complete
        } else {
            Self::Incomplete {
                perms_needed: term,
                perms_needed_exp: exp,
            }
        })
    }
}
