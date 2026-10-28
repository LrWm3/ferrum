//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/BaseVerifier.scala
//!
//! Purpose:
//! Assemble worker-local verifier services and select heap/state strategies.
//!
//! Planned Rust structure:
//! BaseVerifier owns counters, decider, term and symbol converters, identifier factory,
//! trigger/axiom and quantifier supporters, formatter, snapshot supporter and optional member log;
//! choose heap and consolidation implementations from config/member annotations.
//!
//! Behavior to preserve:
//! Unique id must be globally unique and valid for files and solver symbols. Mask heap overrides
//! consolidation and selects mask snapshot/heap supporters. Per-member consolidation annotation
//! overrides configured mode otherwise; preserve every mode. Lifecycle starts/resets/stops decider,
//! converter and identifiers in order; reset clears error count and counters.
//!
//! Integration:
//! verifier::verifier, decider, rules::{state_consolidator,heap_supporter}, supporters and logger.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, identity, branch state, continuations, solver
//! context and native lifecycle.
//!
//! Open decisions:
//! Worker-owned mutable services, logging and strategy lifetimes.
//!
//! Status: partial; worker-local decider, converters, keyed counters, strategy selection
//! and lifecycle implemented. Concrete rule services, member logging and configuration remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::config::StateConsolidationMode;
use crate::decider::decider::{DeciderError, DefaultDecider};
use crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter;
use crate::interfaces::decider::prover::Prover;
use crate::state::identifiers::DefaultIdentifierFactory;
use crate::state::symbol_converter::DefaultSymbolConverter;
use crate::state::terms::TermFactory;
use crate::state::triggers::TriggerGenerator;
use std::any::Any;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeapEncoding {
    Default,
    Mask,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConsolidatorChoice {
    Default,
    Minimal,
    Retrying,
    MinimalRetrying,
    MoreCompleteExhale,
    LastRetry,
    RetryingFailOnly,
    LastRetryFailOnly,
    Mask,
}
/// Worker-owned concrete solver and core translators; rule services and member logging
/// are connected separately as their source implementations become available.
pub struct BaseVerifier<P: Prover> {
    pub unique_id: String,
    pub decider: DefaultDecider<P>,
    pub term_converter: TermToSmtLib2Converter,
    pub symbol_converter: DefaultSymbolConverter,
    pub identifiers: DefaultIdentifierFactory,
    pub trigger_generator: TriggerGenerator,
    pub heap_encoding: HeapEncoding,
    pub errors_reported: AtomicUsize,
    configured_consolidation: StateConsolidationMode,
    counters: Vec<(Arc<dyn Any + Send + Sync>, i32)>,
}
impl<P: Prover> BaseVerifier<P> {
    pub fn new(
        unique_id: String,
        decider: DefaultDecider<P>,
        factory: TermFactory,
        mask_heap: bool,
        configured_consolidation: StateConsolidationMode,
    ) -> Self {
        let identifiers = DefaultIdentifierFactory::new(unique_id.clone());
        Self::new_with_identifiers(
            unique_id,
            decider,
            factory,
            mask_heap,
            configured_consolidation,
            identifiers,
        )
    }
    /// Use the very same fresh identifier stream as the owned prover.
    pub fn new_with_identifiers(
        unique_id: String,
        decider: DefaultDecider<P>,
        factory: TermFactory,
        mask_heap: bool,
        configured_consolidation: StateConsolidationMode,
        identifiers: DefaultIdentifierFactory,
    ) -> Self {
        Self {
            identifiers,
            unique_id,
            decider,
            term_converter: TermToSmtLib2Converter::new(factory.clone()),
            symbol_converter: DefaultSymbolConverter::new(factory, mask_heap),
            trigger_generator: TriggerGenerator::default(),
            heap_encoding: if mask_heap {
                HeapEncoding::Mask
            } else {
                HeapEncoding::Default
            },
            errors_reported: AtomicUsize::new(0),
            configured_consolidation,
            counters: Vec::new(),
        }
    }
    /// Scala map keys use equality; Rust keys of the same concrete type use `Eq`.
    pub fn next_counter<T: Any + Eq + Send + Sync>(&mut self, key: &Arc<T>) -> i32 {
        if let Some((_, next)) = self.counters.iter_mut().find(|(candidate, _)| {
            candidate
                .downcast_ref::<T>()
                .is_some_and(|old| old == key.as_ref())
        }) {
            let value = *next;
            *next = next.wrapping_add(1);
            value
        } else {
            self.counters.push((key.clone(), 1));
            0
        }
    }
    /// Zero means no limit; otherwise stop reporting once the configured count is reached.
    pub fn report_further_errors(&self, limit: usize) -> bool {
        limit == 0 || limit > self.errors_reported.load(Ordering::SeqCst)
    }
    /// Member annotations override the configured mode; mask heap always wins.
    pub fn consolidator(
        &self,
        member_override: Option<StateConsolidationMode>,
    ) -> ConsolidatorChoice {
        if self.heap_encoding == HeapEncoding::Mask {
            return ConsolidatorChoice::Mask;
        }
        match member_override.unwrap_or(self.configured_consolidation) {
            StateConsolidationMode::Minimal => ConsolidatorChoice::Minimal,
            StateConsolidationMode::Default => ConsolidatorChoice::Default,
            StateConsolidationMode::Retrying => ConsolidatorChoice::Retrying,
            StateConsolidationMode::MinimalRetrying => ConsolidatorChoice::MinimalRetrying,
            StateConsolidationMode::MoreCompleteExhale => ConsolidatorChoice::MoreCompleteExhale,
            StateConsolidationMode::LastRetry => ConsolidatorChoice::LastRetry,
            StateConsolidationMode::RetryingFailOnly => ConsolidatorChoice::RetryingFailOnly,
            StateConsolidationMode::LastRetryFailOnly => ConsolidatorChoice::LastRetryFailOnly,
        }
    }
    pub fn start(&mut self, user_args: Option<&str>) -> Result<(), DeciderError<P::Error>> {
        self.decider.start(user_args)?;
        self.term_converter.start();
        self.identifiers.start();
        Ok(())
    }
    pub fn reset(&mut self) -> Result<(), DeciderError<P::Error>> {
        self.decider.reset()?;
        self.term_converter.reset();
        self.identifiers.reset();
        self.errors_reported.store(0, Ordering::SeqCst);
        self.counters.clear();
        Ok(())
    }
    pub fn stop(&mut self) -> Result<(), DeciderError<P::Error>> {
        self.decider.stop()?;
        self.term_converter.stop();
        self.identifiers.stop();
        Ok(())
    }
}
