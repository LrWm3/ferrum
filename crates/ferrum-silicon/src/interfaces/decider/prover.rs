//! Solver and preamble interfaces.
//!
//! Port of [`Prover.scala`](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/decider/Prover.scala).
//! Status: operation contracts implemented; concrete solver lifecycle and model/version
//! representations are supplied by solver implementations.
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

/// The emission operations needed by preamble readers.
pub trait TextEmitter {
    type Error;

    fn emit(&mut self, content: &str) -> Result<(), Self::Error>;

    fn emit_all(&mut self, contents: &[String]) -> Result<(), Self::Error> {
        for content in contents {
            self.emit(content)?;
        }
        Ok(())
    }

    fn emit_settings(&mut self, contents: &[String]) -> Result<(), Self::Error>;
}

use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::state::terms::{ApplicationTarget, Declaration, Sort, Term};

/// Solver satisfiability outcome; unknown is not a successful proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SatResult {
    Sat,
    Unsat,
    Unknown,
}

/// Source timeouts are signed integer milliseconds; `None`, zero and positive
/// values must remain distinct until interpreted by the selected solver.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProverStateSaturationTimeout {
    pub timeout_ms: i32,
    pub comment: String,
}

/// Full source ProverLike operations, available without solver lifecycle.
pub trait ProverLike: TextEmitter {
    fn assume_axioms(
        &mut self,
        terms: &InsertionOrderedSet<Term>,
        description: &str,
    ) -> Result<(), Self::Error>;
    fn set_option(&mut self, name: &str, value: &str) -> Result<String, Self::Error>;
    fn assume(&mut self, term: &Term) -> Result<(), Self::Error>;
    fn declare(&mut self, declaration: &Declaration) -> Result<(), Self::Error>;
    fn comment(&mut self, content: &mut dyn FnMut() -> String) -> Result<(), Self::Error>;
    fn saturate(&mut self, timeout_ms: i32, comment: &str) -> Result<(), Self::Error>;
    fn saturate_configured(
        &mut self,
        data: Option<&ProverStateSaturationTimeout>,
    ) -> Result<(), Self::Error> {
        if let Some(data) = data {
            self.saturate(data.timeout_ms, &data.comment)?;
        }
        Ok(())
    }
}

/// Stateful solver operations. Concrete implementations own the process/API
/// context; transport failures and solver unknown are separate outcomes.
pub trait Prover: ProverLike {
    type Version;

    fn start(&mut self, user_args: Option<&str>) -> Result<(), Self::Error>;
    fn reset(&mut self) -> Result<(), Self::Error>;
    fn stop(&mut self) -> Result<(), Self::Error>;
    fn assert_goal(&mut self, goal: &Term, timeout_ms: Option<i32>) -> Result<bool, Self::Error>;
    fn check(&mut self, timeout_ms: Option<i32>) -> Result<SatResult, Self::Error>;
    fn fresh(
        &mut self,
        id: &str,
        arg_sorts: &[Sort],
        result_sort: &Sort,
    ) -> Result<ApplicationTarget, Self::Error>;
    fn statistics(&mut self) -> Result<Vec<(String, String)>, Self::Error>;
    fn has_model(&self) -> bool;
    fn is_model_valid(&self) -> bool;
    fn get_model(
        &mut self,
    ) -> Result<ferrum_silver::verifier::verification_error::Model, Self::Error>;
    fn get_reason_unknown(&mut self) -> Result<String, Self::Error>;
    fn clear_last_assert(&mut self);
    fn name(&self) -> &str;
    fn min_version(&self) -> Self::Version;
    fn max_version(&self) -> Option<Self::Version>;
    fn version(&mut self) -> Result<Self::Version, Self::Error>;
    fn static_preamble(&self) -> &str;
    fn randomize_seeds_options(&self) -> &[String];
    fn push_pop_scope_depth(&self) -> usize;
    fn push(&mut self, n: usize, timeout_ms: Option<i32>) -> Result<(), Self::Error>;
    fn pop(&mut self, n: usize) -> Result<(), Self::Error>;
    fn all_declarations(&self) -> Vec<Declaration>;
    fn all_emits(&self) -> Vec<String>;
}
