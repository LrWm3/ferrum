//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/VerificationUnit.scala
//!
//! Purpose:
//! Expose a stateful unit verifier.
//!
//! Planned Rust structure:
//! VerificationUnit provides units and verify(State, unit) returning a sequence of
//! VerificationResult.
//!
//! Behavior to preserve:
//! Preserve result multiplicity and component lifecycle.
//!
//! Integration:
//! interfaces::preamble, supporters and state::state.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Unit and state ownership with verification orchestration.
//!
//! Status: implemented generic lifecycle and verification contract.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::verification::VerificationResult;
/// A stateful unit exposes the source's ordered units and returns all results for each one.
pub trait VerificationUnit {
    type Unit;
    type State;
    type Diagnostic;
    type Error;
    fn start(&mut self) -> Result<(), Self::Error>;
    fn reset(&mut self) -> Result<(), Self::Error>;
    fn stop(&mut self) -> Result<(), Self::Error>;
    fn units(&self) -> &[Self::Unit];
    fn verify(
        &mut self,
        state: Self::State,
        unit: &Self::Unit,
    ) -> Result<Vec<VerificationResult<Self::Diagnostic>>, Self::Error>;
}
