//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Utils.scala
//!
//! Purpose:
//! Provide term traversal/reconstruction and reference disjointness helpers.
//!
//! Planned Rust structure:
//! computeReferenceDisjointnesses and expression variant inspect store and supported
//! chunks; subterms enumerates term families; transform applies pre, recursive
//! reconstruction and post.
//!
//! Behavior to preserve:
//! Exclude the reference itself; quantified fields contribute only singleton receivers;
//! expression variant uses optional debug expressions. Distinct is treated as leaf;
//! equality reconstruction asserts unchanged sort. Recursive predicate is evaluated on
//! original term, not pre-rewritten term.
//!
//! Integration:
//! state::terms, state::chunks, state::state and ferrum_silver::ast.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Exhaustive reconstruction and preserving upstream omissions with terms.
//!
//! Status: subterms and specialized replacement/reconstruction bodies are implemented
//! in state::terms; this module exposes the source entry point. General pre/post
//! transform remains pending; reference-disjointness helpers are implemented over
//! the explicit store and heap inputs.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::terms::{Term, UnsupportedSubterms};

pub fn subterms(term: &Term) -> Result<Vec<Term>, UnsupportedSubterms> {
    term.subterms()
}

use super::chunks::Chunk;
use super::heap::Heap;
use super::store::Store;
use super::terms::{Sort, TermFactory};
use ferrum_silver::ast::expression::{Exp, ExpKind, ExpressionTypeError};
use ferrum_silver::ast::r#type::Type;
use std::collections::HashSet;

/// Source `computeReferenceDisjointnesses`, parameterized by its actual store/heap inputs.
pub fn compute_reference_disjointnesses(
    store: &impl Store,
    heap: &impl Heap,
    reference: &Term,
    factory: &TermFactory,
) -> Vec<Term> {
    let mut refs = HashSet::new();
    let mut sets = HashSet::new();
    let mut seqs = HashSet::new();
    let mut collect = |term: &Term| match term.sort() {
        Sort::Ref if term != reference => {
            refs.insert(term.clone());
        }
        Sort::Set(element) if **element == Sort::Ref => {
            sets.insert(term.clone());
        }
        Sort::Seq(element) if **element == Sort::Ref => {
            seqs.insert(term.clone());
        }
        _ => {}
    };
    for (_, (term, _)) in store.values() {
        collect(term);
    }
    for chunk in heap.values() {
        match chunk {
            Chunk::Basic(b) => {
                for arg in &b.args {
                    collect(arg);
                }
                collect(&b.snap);
            }
            Chunk::QuantifiedField(q) => {
                if let Some(receiver) = &q.singleton_rcvr {
                    collect(receiver);
                    use crate::interfaces::state::chunks::QuantifiedChunk;
                    collect(&q.value_at(factory, std::slice::from_ref(receiver)));
                }
            }
            _ => {}
        }
    }
    let mut result = Vec::new();
    for r in refs {
        result.push(factory.not(factory.equals(reference.clone(), r)));
    }
    for set in sets {
        result.push(factory.not(factory.set_in(reference.clone(), set)));
    }
    for seq in seqs {
        result.push(factory.not(factory.seq_in(seq, reference.clone())));
    }
    result
}

/// Debug-expression counterpart. Missing stored/debug expressions fail as in
/// upstream's `.get`; a malformed Silver expression returns its typing error.
pub fn compute_reference_disjointnesses_exp(
    store: &impl Store,
    heap: &impl Heap,
    reference: &Exp,
) -> Result<Vec<Exp>, ExpressionTypeError> {
    let mut refs = Vec::new();
    let mut sets = Vec::new();
    let mut seqs = Vec::new();
    let mut collect = |exp: &Exp| -> Result<(), ExpressionTypeError> {
        let into = match exp.typ()? {
            Type::Ref if exp != reference => Some(&mut refs),
            Type::Set(element) if *element == Type::Ref => Some(&mut sets),
            Type::Seq(element) if *element == Type::Ref => Some(&mut seqs),
            _ => None,
        };
        if let Some(into) = into {
            if !into.contains(exp) {
                into.push(exp.clone());
            }
        }
        Ok(())
    };
    for (_, (_, exp)) in store.values() {
        collect(exp.as_ref().expect("missing store debug expression"))?;
    }
    for chunk in heap.values() {
        match chunk {
            Chunk::Basic(b) => {
                for exp in b
                    .args_exp
                    .as_ref()
                    .expect("missing chunk argument expressions")
                {
                    collect(exp)?;
                }
            }
            Chunk::QuantifiedField(q) => {
                if let Some(exp) = &q.singleton_rcvr_exp {
                    collect(exp)?;
                }
            }
            _ => {}
        }
    }
    let mut result = Vec::new();
    for r in refs {
        result.push(Exp::new(
            ExpKind::NeCmp(reference.clone(), r),
            Default::default(),
        ));
    }
    for set in sets {
        let contains = Exp::new(
            ExpKind::AnySetContains(reference.clone(), set),
            Default::default(),
        );
        result.push(Exp::new(ExpKind::Not(contains), Default::default()));
    }
    for seq in seqs {
        let contains = Exp::new(
            ExpKind::SeqContains(reference.clone(), seq),
            Default::default(),
        );
        result.push(Exp::new(ExpKind::Not(contains), Default::default()));
    }
    Ok(result)
}
