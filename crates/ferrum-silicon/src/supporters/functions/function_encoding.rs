//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/FunctionEncoding.scala
//!
//! Purpose:
//! Define interchangeable heap-dependent function axiom and state-argument encodings.
//!
//! Planned Rust structure:
//! Port FunctionEncoding hooks and DefaultFunctionEncoding stateArgs, predicate trigger state,
//! definitional axiom and function application.
//!
//! Behavior to preserve:
//! Default passes one snapshot argument; definitions trigger directly on function application and
//! additionally on paired stateless/predicate triggers. Auxiliary symbols, axioms and
//! well-definedness declarations default empty; preserve hook ordering and substitutions.
//!
//! Integration:
//! supporters::functions::{function_data,function_verification_unit,heap_access_replacing_expression_translator}
//! and mask_heap_function_encoding; state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for snapshots, triggers and explicit verifier contexts.
//!
//! Open decisions:
//! Agree on trait ownership and state-argument/axiom interfaces with mask heap and function
//! verification.
//!
//! Status: partial; default snapshot arguments, definitional triggers and function applications
//! implemented. Predicate snapshot resolution and alternative encoding remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.
use crate::state::terms::{
    Applicable, Quantifier, Term, TermFactory, Trigger, UnsupportedTriggerTransform,
};

/// The default source encoding has exactly one snapshot state argument.
pub struct DefaultFunctionEncoding;
impl DefaultFunctionEncoding {
    pub fn state_args(factory: &TermFactory) -> Vec<Term> {
        vec![factory.predef_snapshot_var()]
    }
    /// The function application is always a trigger; each predicate trigger
    /// additionally forms a joint trigger with the stateless trigger function.
    pub fn definitional_axiom(
        factory: &TermFactory,
        arguments: Vec<Term>,
        body: Term,
        function_application: Term,
        trigger_application: Term,
        predicate_triggers: &[Term],
    ) -> Result<Term, UnsupportedTriggerTransform> {
        let mut triggers = vec![Trigger {
            terms: vec![function_application],
        }];
        triggers.extend(predicate_triggers.iter().map(|predicate| Trigger {
            terms: vec![trigger_application.clone(), predicate.clone()],
        }));
        factory.quantification(
            Quantifier::Forall,
            arguments,
            body,
            triggers,
            TermFactory::forall_default_name(),
            false,
            None,
        )
    }
    pub fn translate_function_application(
        factory: &TermFactory,
        function: Applicable,
        snapshot: Term,
        args: &[Term],
    ) -> Term {
        let args = std::iter::once(snapshot)
            .chain(args.iter().cloned())
            .collect();
        factory.app(function, args)
    }
}
