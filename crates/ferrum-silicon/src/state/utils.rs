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
//! transform and reference-disjointness helpers remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::terms::{Term, UnsupportedSubterms};

pub fn subterms(term: &Term) -> Result<Vec<Term>, UnsupportedSubterms> {
    term.subterms()
}
