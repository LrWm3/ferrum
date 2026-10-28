//! Solver interface, initially limited to preamble emission.
//!
//! Port of [`Prover.scala`](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/decider/Prover.scala).
//! Status: partial; assertion, solver lifecycle, declarations, scopes and model interfaces remain
//! to be implemented with the decider and term representation.
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

/// The emission operations needed by preamble readers.
pub trait ProverLike {
    type Error;

    fn emit(&mut self, content: &str) -> Result<(), Self::Error>;

    fn emit_all(&mut self, contents: &[String]) -> Result<(), Self::Error> {
        for content in contents {
            self.emit(content)?;
        }
        Ok(())
    }

    fn emit_settings(&mut self, contents: &[String]) -> Result<(), Self::Error>;
}
