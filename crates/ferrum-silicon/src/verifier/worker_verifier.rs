//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/WorkerVerifier.scala
//!
//! Purpose:
//! Host worker-local method and CFG verification components.
//!
//! Planned Rust structure:
//! WorkerVerifier extends BaseVerifier, keeps main verifier/reporter/debug mode, provides method
//! and CFG supporters and delegates pool and member log creation to main.
//!
//! Behavior to preserve:
//! Start, reset and stop base components before worker subcomponents, preserving lifecycle order;
//! open member scope on main root logger with worker path conditions.
//!
//! Integration:
//! verifier::base_verifier, verifier::verification_pool_manager, supporters::method_supporter and
//! cfg_supporter.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Main/worker lifetime, logging and solver ownership.
//!
//! Status: partial; worker ownership and lifecycle ordering implemented. Method/CFG
//! units, pool and symbolic-execution logger remain to be connected.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::decider::decider::DeciderError;
use crate::interfaces::decider::prover::Prover;
use crate::verifier::base_verifier::BaseVerifier;
use ferrum_silver::components::components::StatefulComponent;

/// A worker owns its base verifier and member/CFG verification units. Pool and
/// symbolic-execution logger are supplied by the main verifier when integrated.
pub struct WorkerVerifier<P: Prover, M: StatefulComponent, C: StatefulComponent> {
    pub base: BaseVerifier<P>,
    pub method_supporter: M,
    pub cfg_supporter: C,
    pub debug_mode: bool,
}
impl<P: Prover, M: StatefulComponent, C: StatefulComponent> WorkerVerifier<P, M, C> {
    pub fn start(&mut self, user_args: Option<&str>) -> Result<(), DeciderError<P::Error>> {
        self.base.start(user_args)?;
        self.method_supporter.start();
        self.cfg_supporter.start();
        Ok(())
    }
    pub fn reset(&mut self) -> Result<(), DeciderError<P::Error>> {
        self.base.reset()?;
        self.method_supporter.reset();
        self.cfg_supporter.reset();
        Ok(())
    }
    pub fn stop(&mut self) -> Result<(), DeciderError<P::Error>> {
        self.base.stop()?;
        self.method_supporter.stop();
        self.cfg_supporter.stop();
        Ok(())
    }
}

impl<P: Prover, M: StatefulComponent, C: StatefulComponent>
    crate::verifier::verification_pool_manager::ManagedWorker for WorkerVerifier<P, M, C>
{
    type Error = DeciderError<P::Error>;
    fn start_worker(&mut self) -> Result<(), Self::Error> {
        self.start(None)
    }
    fn reset_worker(&mut self) -> Result<(), Self::Error> {
        self.reset()
    }
    fn stop_worker(&mut self) -> Result<(), Self::Error> {
        self.stop()
    }
}
