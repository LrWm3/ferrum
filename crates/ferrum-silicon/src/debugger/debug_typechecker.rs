//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/DebugTypechecker.scala
//!
//! Purpose:
//! Resolve debugger versioned variables against captured types.
//!
//! Planned Rust structure:
//! Port DebugResolver and DebugTypeChecker checkInternal and acceptAndCheckTypedEntityWithVersion.
//!
//! Behavior to preserve:
//! Look up full versioned name in debugVariableTypes, set type or append positioned diagnostic;
//! delegate other expressions to ordinary TypeChecker.
//!
//! Integration:
//! debugger::{debug_parser,silicon_debugger}, ferrum_silver::parser::{resolver,fast_message}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for type and error ownership.
//!
//! Open decisions:
//! Agree on captured version naming and scope with debugger and parser.
//!
//! Status: partial; source debug tokens, typed nodes and translation/check callbacks exist.
//! General parser/resolver override registration and debugger-session integration remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright notice: the pinned upstream file does not carry an individual notice.

use super::debug_parser::versioned_name;
use ferrum_silver::{
    ast::position::Position,
    parser::parse_ast::{PExpHandle, PExpressionKind, PNodeKind, PTypeHandle},
};
use std::collections::HashMap;
#[derive(Clone, Debug)]
pub struct DebugTypeMessage {
    pub expression: PExpHandle,
    pub message: String,
    pub position: Position,
}
#[derive(Default)]
pub struct DebugTypeChecker {
    pub debug_variable_types: HashMap<String, PTypeHandle>,
    pub messages: Vec<DebugTypeMessage>,
}
impl DebugTypeChecker {
    pub fn check_internal<E>(
        &mut self,
        expression: &PExpHandle,
        fallback: &mut impl FnMut(&PExpHandle) -> Result<(), E>,
    ) -> Result<(), E> {
        let is_versioned = matches!(&expression.node().read().expect("poisoned parse node").kind, PNodeKind::Expression(e) if matches!(&e.kind, PExpressionKind::VersionedIdnUse { .. }));
        if is_versioned {
            let name = versioned_name(expression).expect("matched versioned expression");
            self.accept_versioned(std::slice::from_ref(expression), || {
                format!("Could not resolve the type of {name}")
            });
            Ok(())
        } else {
            fallback(expression)
        }
    }
    pub fn accept_versioned(&mut self, expressions: &[PExpHandle], message: impl Fn() -> String) {
        for expression in expressions {
            let name = versioned_name(expression).expect("versioned identifier required");
            if let Some(typ) = self.debug_variable_types.get(&name) {
                if let PNodeKind::Expression(e) =
                    &mut expression.node().write().expect("poisoned parse node").kind
                {
                    e.typ = typ.clone();
                }
            } else {
                self.messages.push(DebugTypeMessage {
                    expression: expression.clone(),
                    message: message(),
                    position: expression
                        .node()
                        .read()
                        .expect("poisoned parse node")
                        .error_position(),
                });
            }
        }
    }
}
