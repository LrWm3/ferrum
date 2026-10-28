//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/common/src/main/scala/package.scala
//!
//! Purpose:
//! Define the common merge contract.
//!
//! Planned Rust structure:
//! Mergeable exposes merge(other) returning the same logical type.
//!
//! Behavior to preserve:
//! Merge semantics belong to each implementation, not a generic overwrite.
//!
//! Integration:
//! state::state and its mergeable recorders.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Trait shape and ownership with state merging.
//!
//! Status: implemented; integration and broad differential checks remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

/// Source merge contract; the receiver and other branch remain independently owned.
pub trait Mergeable: Sized {
    fn merge(&self, other: &Self) -> Self;
}
