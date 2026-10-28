//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/PermissionSupporter.scala
//!
//! Purpose:
//! Check permission signs with verification errors and continuations.
//!
//! Planned Rust structure:
//! permissionSupporter.assertNotNegative and assertPositive take state, permission, error and
//! verifier, then invoke Q after a successful check.
//!
//! Behavior to preserve:
//! A constrainable ARP variable bypasses the sign assertion; otherwise assert nonnegative or
//! positive and attach NegativePermission or NonPositivePermission on failure. Debug expression
//! uses source position and metadata.
//!
//! Integration:
//! rules::symbolic_execution_rules, rules::evaluator, state::terms, decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Continuation and verifier context ownership.
//!
//! Status: partial; assertion decisions and failure continuation implemented.
//! Debug assertion construction and integration with concrete verifier errors remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2021 ETH Zurich.
use crate::state::terms::{Term, TermFactory, TermKind};
use ferrum_silver::ast::expression::Exp;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PermissionFailure {
    Negative,
    NonPositive,
}
/// The caller provides decider assertion and constructs its typed Silver failure, preserving
/// the original permission expression and the newly formed assertion for debug reporting.
pub fn assert_permission<E, R>(
    factory: &TermFactory,
    permission: &Term,
    original: &Exp,
    rewritten: Option<&Exp>,
    constrainable_arps: impl IntoIterator<Item = Term>,
    positive: bool,
    mut check: impl FnMut(&Term) -> Result<bool, E>,
    success: impl FnOnce() -> R,
    failure: impl FnOnce(PermissionFailure, &Exp, &Term, Option<&Exp>) -> R,
) -> Result<R, E> {
    if matches!(permission.kind(), TermKind::Var(_))
        && constrainable_arps.into_iter().any(|var| var == *permission)
    {
        return Ok(success());
    }
    let assertion = if positive {
        factory.is_positive_perm(permission.clone())
    } else {
        factory.is_nonnegative_perm(permission.clone())
    };
    if check(&assertion)? {
        Ok(success())
    } else {
        Ok(failure(
            if positive {
                PermissionFailure::NonPositive
            } else {
                PermissionFailure::Negative
            },
            original,
            &assertion,
            rewritten,
        ))
    }
}
