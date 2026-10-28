//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/components/Components.scala
//!
//! Purpose:
//! LifetimeComponent and StatefulComponent express component lifecycle contracts.
//!
//! Planned Rust structure:
//! Model start/stop and reset interfaces, with implementations retaining their own state.
//!
//! Behavior to preserve:
//! The documented sequence is initialized → started → stopped; stateful components may reset
//! repeatedly while started. Implementations may be more permissive.
//!
//! Integration:
//! Verifier implementations in verifier and ferrum-silicon use these contracts.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Agree on lifecycle error and mutable ownership interfaces with verifier implementations.
//!
//! Status: implemented; not yet wired or validated.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

/// A component with an explicit start/stop lifecycle.
pub trait LifetimeComponent {
    fn start(&mut self);
    fn stop(&mut self);
}

/// A component that can be reset between uses while started.
pub trait StatefulComponent: LifetimeComponent {
    fn reset(&mut self);
}
