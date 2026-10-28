//! Preamble resource and reader interfaces.
//!
//! Port of [`Preamble.scala`](https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/interfaces/Preamble.scala).
//! Status: partial; contributor and verification-stage interfaces remain pending.
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::interfaces::decider::prover::TextEmitter;
use std::io;

/// Resolves an upstream resource name such as `/preamble.smt2`.
pub trait ResourceProvider {
    fn read_resource(&self, name: &str) -> io::Result<String>;
}

#[derive(Debug)]
pub enum PreambleError<E> {
    Resource(io::Error),
    Sink(E),
}

impl<E: std::fmt::Display> std::fmt::Display for PreambleError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Resource(error) => write!(f, "cannot read preamble resource: {error}"),
            Self::Sink(error) => write!(f, "cannot emit preamble: {error}"),
        }
    }
}
impl<E: std::error::Error + 'static> std::error::Error for PreambleError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Resource(error) => Some(error),
            Self::Sink(error) => Some(error),
        }
    }
}

/// The string preamble operations used by Silicon's SMT-LIB reader.
pub trait PreambleReader {
    fn read_preamble(&self, resource: &str) -> io::Result<Vec<String>>;
    fn read_parametric_preamble(
        &self,
        resource: &str,
        substitutions: &[(String, String)],
    ) -> io::Result<Vec<String>>;

    fn emit_preamble<S: TextEmitter>(
        &self,
        commands: &[String],
        sink: &mut S,
        is_options: bool,
    ) -> Result<(), S::Error> {
        if is_options {
            sink.emit_settings(commands)
        } else {
            sink.emit_all(commands)
        }
    }
    fn emit_resource<S: TextEmitter>(
        &self,
        resource: &str,
        sink: &mut S,
        is_options: bool,
    ) -> Result<(), PreambleError<S::Error>> {
        let commands = self
            .read_preamble(resource)
            .map_err(PreambleError::Resource)?;
        self.emit_preamble(&commands, sink, is_options)
            .map_err(PreambleError::Sink)
    }
    fn emit_parametric_preamble<S: TextEmitter>(
        &self,
        resource: &str,
        substitutions: &[(String, String)],
        sink: &mut S,
    ) -> Result<(), PreambleError<S::Error>> {
        let commands = self
            .read_parametric_preamble(resource, substitutions)
            .map_err(PreambleError::Resource)?;
        sink.emit_all(&commands).map_err(PreambleError::Sink)
    }
}
