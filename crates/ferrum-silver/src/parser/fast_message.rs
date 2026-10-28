//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/FastMessage.scala
//!
//! Purpose:
//! Store and order parser and typechecker diagnostics.
//!
//! Planned Rust structure:
//! Represent FastMessage and FastMessaging constructors, conditional message creation and
//! sortmessages.
//!
//! Behavior to preserve:
//! Require compatible source/file positions; conditional messages use node errorPosition. Sort by
//! line then column and remove duplicates, preserving error/warning flag.
//!
//! Integration:
//! parser::parse_ast and resolver; frontend::sil_frontend maps messages to verifier diagnostics.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Reconcile position and diagnostic types with ast::position and verifier.
//!
//! Status: implemented; broader parser integration and differential validation remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::position::{FilePosition, LineColumn, Position, SourcePosition};
use std::collections::HashSet;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FastMessage {
    pub label: String,
    pub pos: SourcePosition,
    pub error: bool,
}

impl FastMessage {
    pub fn new(label: impl Into<String>, pos: SourcePosition, error: bool) -> Self {
        Self {
            label: label.into(),
            pos,
            error,
        }
    }
    pub fn from_file_position(label: impl Into<String>, pos: &FilePosition, error: bool) -> Self {
        Self::new(
            label,
            SourcePosition::new(pos.file.clone(), pos.line, pos.column),
            error,
        )
    }
    pub fn from_position(
        label: impl Into<String>,
        pos: &Position,
        error: bool,
    ) -> Result<Self, UnexpectedPosition> {
        match pos {
            Position::LineColumn(LineColumn::Source(source)) => {
                Ok(Self::new(label, (**source).clone(), error))
            }
            _ => Err(UnexpectedPosition(pos.clone())),
        }
    }
    pub fn line(&self) -> i32 {
        self.pos.start.line()
    }
    pub fn column(&self) -> i32 {
        self.pos.start.column()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnexpectedPosition(pub Position);

pub type Messages = Vec<FastMessage>;
pub fn no_messages() -> Messages {
    Vec::new()
}
pub fn a_message(message: FastMessage) -> Messages {
    vec![message]
}

/// An absent condition must not inspect or validate the node's position.
pub fn message(
    position: impl FnOnce() -> Position,
    label: impl Into<String>,
    condition: bool,
    error: bool,
) -> Result<Messages, UnexpectedPosition> {
    if condition {
        Ok(a_message(FastMessage::from_position(
            label,
            &position(),
            error,
        )?))
    } else {
        Ok(no_messages())
    }
}

pub fn message_for_node(
    node: &super::parse_ast::PNodeHandle,
    label: impl Into<String>,
    condition: bool,
    error: bool,
) -> Result<Messages, UnexpectedPosition> {
    message(
        || node.read().expect("poisoned parse node").error_position(),
        label,
        condition,
        error,
    )
}

pub fn sortmessages(mut messages: Messages) -> Messages {
    messages.sort_by_key(|message| (message.line(), message.column()));
    let mut seen = HashSet::new();
    messages.retain(|message| seen.insert(message.clone()));
    messages
}
