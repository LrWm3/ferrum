//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/FunctionData.scala
//!
//! Purpose:
//! Accumulate function verification recordings and construct phase-specific axioms.
//!
//! Planned Rust structure:
//! Port FunctionRecorderHandler and FunctionData: formal/state/result variables,
//! function/limited/stateless/precondition symbols, phase transitions, nested definitions,
//! predicate triggers, post/definition/precondition-propagation axioms.
//!
//! Behavior to preserve:
//! Merge recorders and retain insertion-ordered fresh declarations across phases; filter nested
//! definitions with unknown free variables. Limited and trigger axioms precede post axiom; phase 1
//! post axiom binds result to limited application, phase 2 definition guards body equality by
//! precondition and suppresses predicate triggers for opaque functions. Derive predicate triggers
//! from outer recursive unfoldings whose arguments have no free variables outside the formals;
//! arguments may be expressions. Preserve propagation axioms and encoding adaptations.
//!
//! Integration:
//! functions::{function_recorder,function_encoding,heap_access_replacing_expression_translator,function_verification_unit},
//! supporters::predicate_verification_unit, rules quantified definitions and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for term identity, ordering, source contexts and phase ownership.
//!
//! Open decisions:
//! Resolve free-variable filtering, recorder lifecycle and snapshot/heap encoding contracts with
//! function verification and rules.
//!
//! Status: partial; shared function-recorder aggregation and ordered symbol collection
//! implemented. Function-specific analysis and verification phases remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::state::terms::{ApplicationTarget, Declaration, Term, TermFactory, TermKind};
use crate::supporters::functions::function_recorder::{FunctionRecorder, SnapshotKey};

#[derive(Debug)]
pub enum RecorderHandlerError {
    InvalidSnapshotMap,
    InvalidPermissionMap,
}
/// Source FunctionRecorderHandler's accumulated cross-phase symbol declarations.
/// Individual recordings are replaced on each phase, while declarations accumulate.
pub struct FunctionRecorderHandler<D> {
    pub recorder: FunctionRecorder<D>,
    pub location_snapshots: Vec<(SnapshotKey, Term)>,
    pub function_snapshots: Vec<(SnapshotKey, Term)>,
    pub fresh_symbols_across_phases: InsertionOrderedSet<Declaration>,
}
impl<D> Default for FunctionRecorderHandler<D> {
    fn default() -> Self {
        Self {
            recorder: FunctionRecorder::Noop,
            location_snapshots: vec![],
            function_snapshots: vec![],
            fresh_symbols_across_phases: InsertionOrderedSet::new(),
        }
    }
}
impl<D: Clone> FunctionRecorderHandler<D> {
    pub fn add_recorders(
        &mut self,
        factory: &TermFactory,
        recorders: &[FunctionRecorder<D>],
        additional: &[Declaration],
    ) -> Result<(), RecorderHandlerError> {
        let recorder = if let Some((first, rest)) = recorders.split_first() {
            rest.iter().fold(first.clone(), |acc, next| acc.merge(next))
        } else {
            FunctionRecorder::Noop
        };
        let mut symbols = self.fresh_symbols_across_phases.clone();
        if let FunctionRecorder::Actual(actual) = &recorder {
            for symbol in &actual.fresh_path_symbols {
                symbols = symbols.incl(factory.function_decl_target(symbol.clone()));
            }
            for (var, _) in &actual.fresh_constrained_vars {
                symbols = symbols
                    .incl(factory.function_decl_target(ApplicationTarget::Variable(var.clone())));
            }
            for symbol in &actual.fresh_snapshots {
                symbols = symbols.incl(factory.function_decl_target(symbol.clone()));
            }
            for inverse in &actual.fresh_field_invs {
                for function in inverse.inverses().chain(inverse.images()) {
                    symbols = symbols.incl(factory.function_decl_target(function.clone()));
                }
            }
            for decl in &actual.fresh_macros {
                symbols = symbols.incl(decl.clone());
            }
            let declaration = |term: &Term| match term.kind() {
                TermKind::Var(_) => {
                    Some(factory.function_decl_target(ApplicationTarget::Variable(term.clone())))
                }
                TermKind::App {
                    applicable: ApplicationTarget::Function(fun),
                    ..
                } => Some(factory.function_decl(fun.clone())),
                _ => None,
            };
            for map in &actual.fresh_fvfs_and_domains {
                symbols = symbols.incl(
                    declaration(&map.snapshot_map)
                        .ok_or(RecorderHandlerError::InvalidSnapshotMap)?,
                );
            }
            for map in &actual.fresh_perm_maps {
                symbols = symbols.incl(
                    declaration(&map.permission_map)
                        .ok_or(RecorderHandlerError::InvalidPermissionMap)?,
                );
            }
        }
        for declaration in additional {
            symbols = symbols.incl(declaration.clone());
        }
        self.location_snapshots = recorder.location_snapshots(factory);
        self.function_snapshots = recorder.function_snapshots(factory);
        self.recorder = recorder;
        self.fresh_symbols_across_phases = symbols;
        Ok(())
    }
}
