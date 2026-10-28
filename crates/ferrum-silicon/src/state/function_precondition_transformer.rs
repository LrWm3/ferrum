//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/FunctionPreconditionTransformer.scala
//!
//! Purpose:
//! Construct well-definedness conditions for heap-dependent function applications.
//!
//! Planned Rust structure:
//! FunctionPreconditionTransformer.transform dispatches literals, short-circuit boolean
//! operators, conditionals, lets, quantifiers, applications and generic subterms.
//!
//! Behavior to preserve:
//! Guard right-hand transformations of And, Or and Implies; transform let bindings and
//! body; quantified well-definedness is universally quantified even for existential input,
//! retaining triggers and metadata; heap-dependent applications add preconditionVersion
//! after argument transforms.
//!
//! Integration:
//! state::terms, rules::function_supporter and ferrum_silver::ast.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Term traversal and function supporter interface.
//!
//! Status: implemented with an injected heap-function precondition symbol resolver.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::{
    Applicable, ApplicableKind, ApplicationTarget, Quantifier, Term, TermFactory, TermKind,
    UnsupportedSubterms, UnsupportedTriggerTransform,
};

#[derive(Debug)]
pub enum PreconditionTransformError<E> {
    Traversal(UnsupportedSubterms),
    Trigger(UnsupportedTriggerTransform),
    Precondition(E),
}
/// Translate term well-definedness; the caller resolves actual heap-function precondition symbols.
pub fn transform<E>(
    factory: &TermFactory,
    term: &Term,
    precondition: &mut impl FnMut(&Applicable) -> Result<Applicable, E>,
) -> Result<Term, PreconditionTransformError<E>> {
    use TermKind::*;
    let recurse = |t: &Term, pre: &mut _| transform(factory, t, pre);
    Ok(match term.kind() {
        Unit | IntLiteral(..) | Null | ZeroMask | PredZeroMask | True | False | SeqNil(..)
        | EmptySet(..) | EmptyMultiset(..) | EmptyMap(..) => factory.boolean(true),
        And(terms) if !terms.is_empty() => {
            let head = &terms[0];
            let rest = factory.and(terms[1..].iter().cloned());
            factory.and([
                recurse(head, precondition)?,
                factory.implies(head.clone(), recurse(&rest, precondition)?),
            ])
        }
        Or(terms) if !terms.is_empty() => {
            let head = &terms[0];
            let rest = factory.or(terms[1..].iter().cloned());
            factory.and([
                recurse(head, precondition)?,
                factory.implies(factory.not(head.clone()), recurse(&rest, precondition)?),
            ])
        }
        Implies(a, b) => factory.and([
            recurse(a, precondition)?,
            factory.implies(a.clone(), recurse(b, precondition)?),
        ]),
        Ite(c, a, b) => factory.and([
            recurse(c, precondition)?,
            factory.ite(
                c.clone(),
                recurse(a, precondition)?,
                recurse(b, precondition)?,
            ),
        ]),
        Let(bindings, body) => {
            let mut well_defined = Vec::new();
            for (_, value) in bindings.iter() {
                well_defined.push(recurse(value, precondition)?);
            }
            let body = recurse(body, precondition)?;
            factory.and([
                factory.and(well_defined),
                factory.let_term(bindings.iter().cloned(), body),
            ])
        }
        Quantification {
            vars,
            body,
            triggers,
            name,
            is_global,
            weight,
            ..
        } => {
            let body = recurse(body, precondition)?;
            if matches!(body.kind(), True) {
                body
            } else {
                factory
                    .quantification(
                        Quantifier::Forall,
                        vars.clone(),
                        body,
                        triggers.clone(),
                        name.clone(),
                        *is_global,
                        *weight,
                    )
                    .map_err(PreconditionTransformError::Trigger)?
            }
        }
        App {
            applicable: ApplicationTarget::Function(function),
            args,
        } if function.data().kind == ApplicableKind::HeapDepFun => {
            let mut result = Vec::new();
            for arg in args {
                result.push(recurse(arg, precondition)?);
            }
            result.push(factory.app(
                precondition(function).map_err(PreconditionTransformError::Precondition)?,
                args.clone(),
            ));
            factory.and(result)
        }
        _ => {
            let mut result = Vec::new();
            for child in term
                .subterms()
                .map_err(PreconditionTransformError::Traversal)?
            {
                result.push(recurse(&child, precondition)?);
            }
            factory.and(result)
        }
    })
}
