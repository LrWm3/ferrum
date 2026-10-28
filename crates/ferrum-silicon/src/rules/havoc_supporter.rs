//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/HavocSupporter.scala
//!
//! Purpose:
//! Execute single and quantified resource havoc.
//!
//! Planned Rust structure:
//! havocSupporter defines HavocHelperData, HavocOneData, HavocallData, execHavoc, execHavocall,
//! resourceName and getCodomainQVars.
//!
//! Behavior to preserve:
//! Single havoc defaults absent condition to true, evaluates condition then resource arguments and
//! replaces heap via heapSupporter. Havocall evaluates quantified condition and arguments, assumes
//! function-precondition transform, checks injectivity and fails with QuasihavocallNotInjective if
//! false; on success constructs and assumes inverse axioms and replaces heap. A missing quantified
//! result continues unchanged.
//!
//! Integration:
//! rules::evaluator, rules::quantified_chunk_support, rules::heap_supporter,
//! state::function_precondition_transformer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Quantified evaluation result and solver ownership.
//!
//! Status: partial; havoc condition data and substitution implemented. Statement execution remains.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::rules::quantified_chunk_support::InverseFunctions;
use crate::state::terms::{Term, TermFactory, UnsupportedTriggerTransform};
use std::collections::HashMap;

/// Data for replacing a single resource or an injective quantified family.
#[derive(Clone, Debug)]
pub enum HavocHelperData {
    One(Vec<Term>),
    All {
        inverse_functions: InverseFunctions,
        codomain_vars: Vec<Term>,
        images_of_codomain: Vec<Term>,
    },
}

/// Source replacement condition, with simultaneous inverse/codomain substitutions.
pub fn replacement_condition(
    factory: &TermFactory,
    lhs: &Term,
    chunk_args: &[Term],
    info: &HavocHelperData,
) -> Result<Term, UnsupportedTriggerTransform> {
    match info {
        HavocHelperData::One(args) => Ok(factory.and(
            std::iter::once(lhs.clone()).chain(
                chunk_args
                    .iter()
                    .zip(args)
                    .map(|(a, b)| factory.equals(a.clone(), b.clone())),
            ),
        )),
        HavocHelperData::All {
            inverse_functions,
            codomain_vars,
            images_of_codomain,
        } => {
            let inverse: HashMap<_, _> = inverse_functions
                .qvars_to_inverses_of(factory, chunk_args)
                .into_iter()
                .collect();
            let codomain: HashMap<_, _> = codomain_vars
                .iter()
                .cloned()
                .zip(chunk_args.iter().cloned())
                .collect();
            let condition = factory.replace(lhs, &inverse)?;
            let images = images_of_codomain
                .iter()
                .map(|image| factory.replace(image, &codomain))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(factory.and(std::iter::once(condition).chain(images)))
        }
    }
}
