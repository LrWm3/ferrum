//! Port plan: Check local and context-dependent Silver AST consistency.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Consistency.scala
//!
//! Purpose:
//! Check local and context-dependent Silver AST consistency.
//!
//! Planned Rust structure:
//! Consistency diagnostics accumulator and legacy function-precondition flag;
//! identifier/assignability/purity and contract helpers, wildcard, trigger, forperm, backend
//! type, recursion and wand context checks; Context and InsideWandStatus.
//!
//! Behavior to preserve:
//! Preserve diagnostics order and positions, parser keyword restrictions and assignability
//! subtype rules. Legacy flag controls wildcard restrictions in function preconditions.
//! Validate trigger coverage, forperm direct resource arguments, wand proof scripts and
//! old[lhs] location, backend interpretation consistency, and recursion via function
//! preconditions. Existing extension-expression exception in noPermissions and mutable message
//! accumulator remain explicit.
//!
//! Integration:
//! ast::{ast,expression,statement,program,type},
//! ast::utility::{expressions,functions,viper_strategy}, parser keywords and verifier errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile per-run message/config ownership and extension rules with frontend and plugin
//! callers, preserving source diagnostics.
//!
//! Status: partially implemented; identifier validation and reserved names only.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::collections::HashSet;

/// The parser's basic keyword set, excluding plugin extensions.
pub fn reserved_names() -> HashSet<String> {
    [
        "Bool",
        "Int",
        "Map",
        "Multiset",
        "Rational",
        "Ref",
        "Seq",
        "Set",
        "acc",
        "apply",
        "applying",
        "assert",
        "asserting",
        "assume",
        "axiom",
        "define",
        "domain",
        "else",
        "elseif",
        "ensures",
        "epsilon",
        "exhale",
        "exists",
        "false",
        "field",
        "fold",
        "forall",
        "forperm",
        "function",
        "goto",
        "if",
        "import",
        "in",
        "inhale",
        "interpretation",
        "intersection",
        "invariant",
        "label",
        "let",
        "lhs",
        "method",
        "new",
        "none",
        "null",
        "old",
        "package",
        "perm",
        "predicate",
        "quasihavoc",
        "quasihavocall",
        "range",
        "requires",
        "result",
        "returns",
        "setminus",
        "subset",
        "true",
        "unfold",
        "unfolding",
        "union",
        "unique",
        "var",
        "while",
        "wildcard",
        "write",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

pub fn valid_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '$' || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '$' | '_' | '\'' | '@'))
}
