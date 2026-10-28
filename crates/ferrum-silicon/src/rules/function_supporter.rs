//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/FunctionSupporter.scala
//!
//! Purpose:
//! Build derived symbols for function encodings.
//!
//! Planned Rust structure:
//! functionSupporter creates limitedVersion, statelessVersion, preconditionVersion, frameVersion
//! and preconditionFrameVersion.
//!
//! Behavior to preserve:
//! Suffixes use %; stateless drops state arguments and returns Bool, precondition retains
//! heap-dependent arguments and returns Bool. Frame replaces n heap arguments with Snap and
//! preserves result, precondition frame returns Bool.
//!
//! Integration:
//! state::identifiers, state::terms, supporters::functions and
//! state::function_precondition_transformer.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Function symbol factory and identity with terms.
//!
//! Status: implemented all source function version constructors.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::state::terms::{Applicable, ApplicableData, ApplicableKind, Sort, TermFactory};
fn version(
    factory: &TermFactory,
    function: &Applicable,
    suffix: &str,
    kind: ApplicableKind,
    args: Vec<Sort>,
    result: Sort,
) -> Applicable {
    assert_eq!(
        function.data().kind,
        ApplicableKind::HeapDepFun,
        "expected heap-dependent function"
    );
    factory.applicable(ApplicableData {
        kind,
        id: function.data().id.with_separator_suffix("%", suffix),
        arg_sorts: args,
        result_sort: result,
    })
}
pub fn limited_version(factory: &TermFactory, function: &Applicable) -> Applicable {
    version(
        factory,
        function,
        "limited",
        ApplicableKind::HeapDepFun,
        function.data().arg_sorts.clone(),
        function.data().result_sort.clone(),
    )
}
pub fn precondition_version(factory: &TermFactory, function: &Applicable) -> Applicable {
    version(
        factory,
        function,
        "precondition",
        ApplicableKind::HeapDepFun,
        function.data().arg_sorts.clone(),
        Sort::Bool,
    )
}
pub fn stateless_version(
    factory: &TermFactory,
    function: &Applicable,
    state_args: i32,
) -> Applicable {
    version(
        factory,
        function,
        "stateless",
        ApplicableKind::Fun,
        function
            .data()
            .arg_sorts
            .iter()
            .skip(state_args.max(0) as usize)
            .cloned()
            .collect(),
        Sort::Bool,
    )
}
pub fn frame_version(factory: &TermFactory, function: &Applicable, heaps: i32) -> Applicable {
    let mut args = vec![Sort::Snap];
    args.extend(
        function
            .data()
            .arg_sorts
            .iter()
            .skip(heaps.max(0) as usize)
            .cloned(),
    );
    version(
        factory,
        function,
        "frame",
        ApplicableKind::Fun,
        args,
        function.data().result_sort.clone(),
    )
}
pub fn precondition_frame_version(
    factory: &TermFactory,
    function: &Applicable,
    heaps: i32,
) -> Applicable {
    let mut args = vec![Sort::Snap];
    args.extend(
        function
            .data()
            .arg_sorts
            .iter()
            .skip(heaps.max(0) as usize)
            .cloned(),
    );
    version(
        factory,
        function,
        "precondition%frame",
        ApplicableKind::Fun,
        args,
        Sort::Bool,
    )
}
