//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/Domains.scala
//!
//! Purpose:
//! Instantiate user-defined domains and translate their axioms into prover preamble terms.
//!
//! Planned Rust structure:
//! Port DomainsContributor, DefaultDomainsContributor and
//! DomainsTranslator/DefaultDomainsTranslator, including sort, function, axiom and uniqueness
//! collections.
//!
//! Behavior to preserve:
//! Instantiate concrete ground domain types; deduplicate by translated sort/symbol, skip
//! interpreted functions and group unique nullary symbols by result sort for Distinct. Conjoin
//! function precondition transformation with each axiom; assign named quantifier IDs when missing
//! and restore builtin translation mode. Declare sorts then symbols and assume axioms/uniqueness.
//!
//! Integration:
//! supporters::expression_translator, state::{symbol_converter,function_precondition_transformer},
//! interfaces::preamble and prover.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered preamble emission, term identity and explicit
//! translator context.
//!
//! Open decisions:
//! Agree on translator mode lifetime and stable collection order with builtin contributor and
//! decider.
//!
//! Status: partial; collection of translated members, uniqueness and solver emission implemented.
//! Ground type analysis, Silver domain instantiation and translation remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::interfaces::decider::prover::ProverLike;
use crate::package::Map;
use crate::state::function_precondition_transformer::{PreconditionTransformError, transform};
use crate::state::terms::{Applicable, ApplicableKind, Sort, Term, TermFactory};

#[derive(Default)]
pub struct DefaultDomainsContributor {
    pub sorts: InsertionOrderedSet<Sort>,
    pub functions: InsertionOrderedSet<Applicable>,
    pub axioms: InsertionOrderedSet<Term>,
    unique: Map<Sort, InsertionOrderedSet<Applicable>>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DomainCollectionError {
    ExpectedDomainFunction,
    UniqueFunctionHasArguments,
}
impl DefaultDomainsContributor {
    pub fn reset(&mut self) {
        *self = Self::default();
    }
    /// Add a translated uninterpreted domain function; interpreted functions are skipped upstream.
    pub fn collect_function(
        &mut self,
        function: Applicable,
        unique: bool,
    ) -> Result<(), DomainCollectionError> {
        if function.data().kind != ApplicableKind::DomainFun {
            return Err(DomainCollectionError::ExpectedDomainFunction);
        }
        if unique && !function.data().arg_sorts.is_empty() {
            return Err(DomainCollectionError::UniqueFunctionHasArguments);
        }
        self.functions = self.functions.incl(function.clone());
        if unique {
            let symbols = self
                .unique
                .entry(function.data().result_sort.clone())
                .or_default();
            *symbols = symbols.incl(function);
        }
        Ok(())
    }
    pub fn collect_axiom<E>(
        &mut self,
        factory: &TermFactory,
        axiom: Term,
        precondition: &mut impl FnMut(&Applicable) -> Result<Applicable, E>,
    ) -> Result<(), PreconditionTransformError<E>> {
        let well_defined = transform(factory, &axiom, precondition)?;
        self.axioms = self.axioms.incl(factory.and([well_defined, axiom]));
        Ok(())
    }
    pub fn uniqueness_assumptions(&self, factory: &TermFactory) -> InsertionOrderedSet<Term> {
        self.unique
            .values()
            .map(|functions| factory.distinct(functions.iter().cloned()))
            .collect()
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
        for fun in &self.functions {
            sink.declare(&factory.function_decl(fun.clone()))?;
        }
        Ok(())
    }
    pub fn emit_axioms<P: ProverLike>(&self, sink: &mut P) -> Result<(), P::Error> {
        sink.assume_axioms(&self.axioms, "Domain axioms")
    }
    pub fn emit_uniqueness<P: ProverLike>(
        &self,
        factory: &TermFactory,
        sink: &mut P,
    ) -> Result<(), P::Error> {
        sink.assume_axioms(&self.uniqueness_assumptions(factory), "Uniqueness axioms")
    }
}
