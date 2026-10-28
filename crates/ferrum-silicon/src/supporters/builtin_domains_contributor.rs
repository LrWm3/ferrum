//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/BuiltinDomainsContributor.scala
//!
//! Purpose:
//! Load, instantiate and emit builtin collection domain axioms.
//!
//! Planned Rust structure:
//! Port BuiltinDomainsContributor and BuiltinDomainAwareSymbolConverter with analyze, source
//! transformations, sort/function/axiom collection, lifecycle and shared source-program cache.
//!
//! Behavior to preserve:
//! Skip source loading when no ground instances. Select user file or default resource;
//! parse/resolve/translate and cache by URL plus file modification time. Instantiate source
//! functions/axioms, retain insertion-ordered deduplication, skip interpreted functions, translate
//! builtin equality and prefix quantifier names, then declare sorts/symbols and assume axioms.
//!
//! Integration:
//! supporters::domains and default collection contributors, interfaces::preamble,
//! state::symbol_converter, Silver parser and prover.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered collections and native resource/cache ownership;
//! preserve .vpr resources.
//!
//! Open decisions:
//! Resolve cache synchronization, source loading and failure propagation with verifier and
//! frontend.
//!
//! Status: partial; ordered collection, reset and solver emission implemented.
//! Source loading/cache, instantiation, translation and analysis remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::interfaces::decider::prover::ProverLike;
use crate::state::terms::{Applicable, Sort, Term, TermFactory};

/// Ordered results of actual domain analysis. Parsing and translation must fill these explicitly.
#[derive(Default)]
pub struct BuiltinDomainsContributor {
    pub sorts: InsertionOrderedSet<Sort>,
    pub functions: InsertionOrderedSet<Applicable>,
    pub axioms: InsertionOrderedSet<Term>,
}
impl BuiltinDomainsContributor {
    pub fn reset(&mut self) {
        self.sorts = InsertionOrderedSet::new();
        self.functions = InsertionOrderedSet::new();
        self.axioms = InsertionOrderedSet::new();
    }
    pub fn declare_sorts<P: ProverLike>(
        &self,
        factory: &TermFactory,
        sink: &mut P,
    ) -> Result<(), P::Error> {
        for sort in &self.sorts {
            sink.declare(&factory.sort_decl(sort.clone()))?;
        }
        Ok(())
    }
    pub fn declare_symbols<P: ProverLike>(
        &self,
        factory: &TermFactory,
        sink: &mut P,
    ) -> Result<(), P::Error> {
        for function in &self.functions {
            sink.declare(&factory.function_decl(function.clone()))?;
        }
        Ok(())
    }
    pub fn emit_axioms<P: ProverLike>(&self, sink: &mut P) -> Result<(), P::Error> {
        sink.assume_axioms(&self.axioms, "Axioms from builtin domains contributor")
    }
}
