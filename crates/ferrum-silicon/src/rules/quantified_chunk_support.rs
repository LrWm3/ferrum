//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/QuantifiedChunkSupport.scala
//!
//! Purpose:
//! Implement quantified permissions, snapshot/permission summaries and chunk matching.
//!
//! Planned Rust structure:
//! InverseFunctions carries condition, invertibles, additional arguments, inverse/image functions
//! and paired axioms; SnapshotMapDefinition and PermMapDefinition carry emitted definitions.
//! QuantifiedChunkSupport and quantifiedChunkSupporter implement singleton/general chunk
//! construction, heap partition, snapshot/permission map creation and caching,
//! quantified/single-location produce and consume, assertReadPermission/removePermissions, inverse
//! and injectivity axioms, alias matching, snapshot-map combination and chunk-order heuristics.
//!
//! Behavior to preserve:
//! Construct field, predicate and wand chunks with proper sorts, singleton args, inverse
//! substitutions and tags; splitHeap rejects matching nonquantified chunks. Summary definitions
//! condition value equality on positive permission, use snapshot-tuple codomains for
//! predicates/wands, preserve optional domains and configured triggers. Snapshot-map cache keys
//! use resource and ordered chunks; a hit also requires compatible stored domain condition
//! (equal, or cached True with no requested condition). Bypass snapshot cache in extended exhale
//! and re-emit value definitions on hits, plus domain definitions when requested. Permission-map
//! cache uses resource/chunks and likewise re-emits its value definitions.
//! Production scales permissions, selects explicit or inferred inverse triggers, checks nonnegative
//! and optionally injectivity, assumes inverse and resource properties then merges chunk; retain
//! function recorder and trigger summaries. Consumption checks nonnegative and injectivity, handles
//! wand reserve transfer, and otherwise removes from threaded partial heap. Greedy modes retry
//! after consolidation; complete mode avoids extra retry. Single-location paths distinguish missing
//! wand from insufficient permission and return wand snapshot-function lookup without Snap
//! conversion. Removal respects read-only mode, configurable ordering, greedy subset checks versus
//! complete matching, exact versus constrainable permissions, short intermediate checks and
//! mandatory final check; track untouched chunks for summaries and optional permission macros.
//! Inverse creation asserts arity/sorts and generates image functions for every quantified variable
//! despite older prose suggesting exceptions; axioms preserve trigger choices and global scope.
//! Greedy matching prioritizes original condition/tag then subset proof; complete matching proves
//! locations and conditions. Fresh snapshot maps when neither permission is provably positive avoid
//! unsound reuse.
//!
//! Integration:
//! rules::heap_supporter, mask_heap_supporter, consumer, producer, havoc_supporter,
//! magic_wand_supporter, state_consolidator, state::snapshot_map_cache, resources and
//! state::triggers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Inverse/trigger identity, caches, snapshot map and continuation/solver ownership with all heap
//! encodings.
//!
//! Status: InverseFunctions, SnapshotMapDefinition and PermMapDefinition data
//! contracts implemented; quantified execution rules remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::state::terms::{
    ApplicableKind, ApplicationTarget, Term, TermFactory, TermKind, UnsupportedTriggerTransform,
};
use ferrum_silver::ast::expression::Exp;
use ferrum_silver::ast::program::LocalVarDecl;
use std::collections::HashMap;

fn apply_function(factory: &TermFactory, function: &ApplicationTarget, args: Vec<Term>) -> Term {
    match function {
        ApplicationTarget::Function(f) => factory.app(f.clone(), args),
        ApplicationTarget::Variable(v) => factory.app_var(v.clone(), args),
    }
}

/// Ordered source map with map equality, independent of insertion order.
#[derive(Clone, Debug, Default)]
pub struct VariableFunctions(Vec<(Term, ApplicationTarget)>);
impl VariableFunctions {
    pub fn new(entries: impl IntoIterator<Item = (Term, ApplicationTarget)>) -> Self {
        let mut out: Vec<(Term, ApplicationTarget)> = Vec::new();
        for (var, function) in entries {
            assert!(
                matches!(var.kind(), TermKind::Var(_)),
                "expected quantified variable"
            );
            match &function {
                ApplicationTarget::Function(f) => {
                    assert_ne!(f.data().kind, ApplicableKind::Macro, "expected a function")
                }
                ApplicationTarget::Variable(v) => assert!(
                    matches!(v.kind(), TermKind::Var(_)),
                    "expected variable function"
                ),
            }
            if let Some((old_key, old)) = out.iter_mut().find(|(key, _)| key == &var) {
                *old_key = var;
                *old = function;
            } else {
                out.push((var, function));
            }
        }
        Self(out)
    }
    pub fn iter(&self) -> impl Iterator<Item = &(Term, ApplicationTarget)> {
        self.0.iter()
    }
}
impl PartialEq for VariableFunctions {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .all(|(k, v)| other.0.iter().any(|(k2, v2)| k == k2 && v == v2))
    }
}
impl Eq for VariableFunctions {}

/// Data contract retained across quantified-chunk merges; rules are not implemented here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InverseFunctions {
    pub(crate) condition: Term,
    pub(crate) invertibles: Vec<Term>,
    pub(crate) invertible_exps: Option<Vec<Exp>>,
    pub(crate) additional_arguments: Vec<Term>,
    pub(crate) axiom_inverses_of_invertibles: Term,
    pub(crate) axiom_invertibles_of_inverses: Term,
    pub(crate) qvar_exps: Option<Vec<LocalVarDecl>>,
    pub(crate) qvars_to_inverses: VariableFunctions,
    pub(crate) qvars_to_images: VariableFunctions,
}
impl InverseFunctions {
    pub fn validate(&self) {
        assert!(matches!(
            self.axiom_inverses_of_invertibles.kind(),
            TermKind::Quantification { .. }
        ));
        assert!(matches!(
            self.axiom_invertibles_of_inverses.kind(),
            TermKind::Quantification { .. }
        ));
    }
    pub fn inverses(&self) -> impl Iterator<Item = &ApplicationTarget> {
        self.qvars_to_inverses.iter().map(|(_, f)| f)
    }
    pub fn images(&self) -> impl Iterator<Item = &ApplicationTarget> {
        self.qvars_to_images.iter().map(|(_, f)| f)
    }
    pub fn definitional_axioms(&self) -> [&Term; 2] {
        [
            &self.axiom_inverses_of_invertibles,
            &self.axiom_invertibles_of_inverses,
        ]
    }
    pub fn inverses_of(&self, factory: &TermFactory, arguments: &[Term]) -> Vec<Term> {
        self.inverses()
            .map(|fun| {
                apply_function(
                    factory,
                    fun,
                    self.additional_arguments
                        .iter()
                        .chain(arguments)
                        .cloned()
                        .collect(),
                )
            })
            .collect()
    }
    pub fn qvars_to_inverses_of(
        &self,
        factory: &TermFactory,
        arguments: &[Term],
    ) -> Vec<(Term, Term)> {
        self.qvars_to_inverses
            .iter()
            .map(|(var, fun)| {
                (
                    var.clone(),
                    apply_function(
                        factory,
                        fun,
                        self.additional_arguments
                            .iter()
                            .chain(arguments)
                            .cloned()
                            .collect(),
                    ),
                )
            })
            .collect()
    }
    pub fn substitute(
        &self,
        factory: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, UnsupportedTriggerTransform> {
        let mut result = self.clone();
        result.condition = factory.replace(&self.condition, replacements)?;
        result.invertibles = self
            .invertibles
            .iter()
            .map(|x| factory.replace(x, replacements))
            .collect::<Result<_, _>>()?;
        result.additional_arguments = self
            .additional_arguments
            .iter()
            .map(|x| factory.replace(x, replacements))
            .collect::<Result<_, _>>()?;
        result.axiom_inverses_of_invertibles =
            factory.replace(&self.axiom_inverses_of_invertibles, replacements)?;
        result.axiom_invertibles_of_inverses =
            factory.replace(&self.axiom_invertibles_of_inverses, replacements)?;
        result.validate();
        Ok(result)
    }
}

impl InverseFunctions {
    pub fn new(
        condition: Term,
        invertibles: Vec<Term>,
        invertible_exps: Option<Vec<Exp>>,
        additional_arguments: Vec<Term>,
        axiom_inverses_of_invertibles: Term,
        axiom_invertibles_of_inverses: Term,
        qvar_exps: Option<Vec<LocalVarDecl>>,
        qvars_to_inverses: VariableFunctions,
        qvars_to_images: VariableFunctions,
    ) -> Self {
        let result = Self {
            condition,
            invertibles,
            invertible_exps,
            additional_arguments,
            axiom_inverses_of_invertibles,
            axiom_invertibles_of_inverses,
            qvar_exps,
            qvars_to_inverses,
            qvars_to_images,
        };
        result.validate();
        result
    }
    pub fn condition_ref(&self) -> &Term {
        &self.condition
    }
    pub fn invertibles_ref(&self) -> &Vec<Term> {
        &self.invertibles
    }
    pub fn invertible_exps_ref(&self) -> &Option<Vec<Exp>> {
        &self.invertible_exps
    }
    pub fn additional_arguments_ref(&self) -> &Vec<Term> {
        &self.additional_arguments
    }
    pub fn axiom_inverses_of_invertibles_ref(&self) -> &Term {
        &self.axiom_inverses_of_invertibles
    }
    pub fn axiom_invertibles_of_inverses_ref(&self) -> &Term {
        &self.axiom_invertibles_of_inverses
    }
    pub fn qvar_exps_ref(&self) -> &Option<Vec<LocalVarDecl>> {
        &self.qvar_exps
    }
    pub fn qvars_to_inverses_ref(&self) -> &VariableFunctions {
        &self.qvars_to_inverses
    }
    pub fn qvars_to_images_ref(&self) -> &VariableFunctions {
        &self.qvars_to_images
    }
}

/// Source AST resource for snapshot/permission definitions. Wand equality here is
/// structural AST equality, not the structure-index equality of a chunk identifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SnapshotResource {
    Field(std::sync::Arc<ferrum_silver::ast::program::Field>),
    Predicate(std::sync::Arc<ferrum_silver::ast::program::Predicate>),
    Wand(Exp),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotMapDefinition {
    pub resource: SnapshotResource,
    pub snapshot_map: Term,
    pub value_definitions: Vec<Term>,
    pub domain_definitions: Vec<Term>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PermMapDefinition {
    pub resource: SnapshotResource,
    pub permission_map: Term,
    pub value_definitions: Vec<Term>,
}
