//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/Chunks.scala
//!
//! Purpose:
//! Implement heap chunks for ordinary, quantified, wand and mask-heap resources.
//!
//! Planned Rust structure:
//! ChunkIdentifier/BasicChunkIdentifier and MagicWandIdentifier; BasicChunk,
//! QuantifiedBasicChunk, QuantifiedFieldChunk, QuantifiedPredicateChunk,
//! QuantifiedMagicWandChunk, MagicWandChunk and BasicMaskHeapChunk. Implement condition,
//! permission arithmetic, snapshot replacement, lookup and substitution for each.
//!
//! Behavior to preserve:
//! Check permission/snapshot sorts and field lookup arity; quantified field/predicate
//! permission is conditional and their scaling uses computed permission. Preserve optional
//! expression assumptions, tags, hints, inverse functions and singleton arguments. Wand
//! identifier equality uses structure index hash only; wand snapshot replacement requires
//! MagicWandSnapshot and no expression. Substitution follows each class fields, not all
//! metadata.
//!
//! Merging quantified chunks may retain inverse functions from multiple source
//! assertions because their definitions and matching triggers remain needed.
//! Quantified wand snapshots use predicate snapshot functions with wand-snapshot
//! codomain; the field's synthetic receiver is ?r and debug declarations are
//! created only in debugging mode.
//!
//! Integration:
//! interfaces::state::chunks, state::terms, resources, rules::quantified_chunk_support
//! (InverseFunctions) and ferrum_silver::ast.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, ownership, ordering, identity,
//! continuations, snapshots and solver context; preserve source behavior.
//!
//! Open decisions:
//! Chunk representation and expression pairing with heap and state remain open.
//!
//! Status: identifiers, concrete chunk data, updates and substitutions are implemented;
//! source chunk display and verifier rule integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use ferrum_silver::ast::expression::{Exp, ExpKind};
use ferrum_silver::ast::program::Program;
use ferrum_silver::ast::utility::expressions::MagicWandError;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct BasicChunkIdentifier(pub String);
impl fmt::Display for BasicChunkIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Equality is deliberately only the program's wand-structure index, as upstream.
/// The retained expression is used for source positions, not equality.
#[derive(Clone, Debug)]
pub struct MagicWandIdentifier {
    pub ghost_free_wand: Exp,
    pub structure_index: i32,
}
impl MagicWandIdentifier {
    /// Compute the program-local structure index, retaining -1 if the structure is absent.
    pub fn new(ghost_free_wand: Exp, program: &Program) -> Result<Self, MagicWandError> {
        let structure = ghost_free_wand.magic_wand_structure(program, false)?;
        let structures = program.magic_wand_structures()?;
        let index = structures
            .iter()
            .position(|candidate| candidate == &structure)
            .map_or(-1, |i| {
                i32::try_from(i).expect("too many magic wand structures")
            });
        Ok(Self::from_structure_index(ghost_free_wand, index))
    }
    /// Use the structure index computed from the Silver program (including -1 when absent).
    pub fn from_structure_index(ghost_free_wand: Exp, structure_index: i32) -> Self {
        assert!(
            matches!(ghost_free_wand.kind(), ExpKind::MagicWand(..)),
            "expected a magic wand expression"
        );
        Self {
            ghost_free_wand,
            structure_index,
        }
    }
}
impl PartialEq for MagicWandIdentifier {
    fn eq(&self, other: &Self) -> bool {
        self.structure_index == other.structure_index
    }
}
impl Eq for MagicWandIdentifier {}
impl Hash for MagicWandIdentifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.structure_index.hash(state);
    }
}
impl fmt::Display for MagicWandIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "wand@{}", self.structure_index)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ferrum_silver::ast::ast::Metadata;

    #[test]
    fn wand_identity_is_the_program_structure_index() {
        let truth = Exp::new(ExpKind::TrueLit, Metadata::default());
        let wand = Exp::new(
            ExpKind::MagicWand(truth.clone(), truth),
            Metadata::default(),
        );
        let a = MagicWandIdentifier::from_structure_index(wand.clone(), -1);
        let b = MagicWandIdentifier::from_structure_index(wand.clone(), -1);
        let c = MagicWandIdentifier::from_structure_index(wand, 0);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(a.to_string(), "wand@-1");
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let absent = MagicWandIdentifier::new(a.ghost_free_wand.clone(), &program).unwrap();
        assert_eq!(absent.structure_index, -1);
    }
}

use crate::interfaces::state::chunks::{
    Chunk as ChunkContract, GeneralChunk, MaskHeapChunk, NonQuantifiedChunk, QuantifiedChunk,
};
use crate::resources::resources::{BaseId, ResourceId};
use crate::rules::quantified_chunk_support::InverseFunctions;
use crate::state::store::{AbstractLocalVar, StoreValue};
use crate::state::terms::{
    ResourceKey, Sort, Term, TermFactory, TermKind, UnsupportedTriggerTransform,
};
use ferrum_silver::ast::program::LocalVarDecl;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ChunkIdentifier {
    Basic(BasicChunkIdentifier),
    Wand(MagicWandIdentifier),
}
impl fmt::Display for ChunkIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Basic(id) => id.fmt(f),
            Self::Wand(id) => id.fmt(f),
        }
    }
}
impl From<&ResourceKey> for ChunkIdentifier {
    fn from(resource: &ResourceKey) -> Self {
        match resource {
            ResourceKey::Field(f) => Self::Basic(BasicChunkIdentifier(f.name.clone())),
            ResourceKey::Predicate(p) => Self::Basic(BasicChunkIdentifier(p.name.clone())),
            ResourceKey::Wand(w) => Self::Wand(w.clone()),
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChunkError {
    Transform(UnsupportedTriggerTransform),
    ExpectedWandSnapshot,
}
impl fmt::Display for ChunkError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Transform(error) => error.fmt(f),
            Self::ExpectedWandSnapshot => {
                f.write_str("expected magic-wand snapshot after substitution")
            }
        }
    }
}
impl std::error::Error for ChunkError {}
impl From<UnsupportedTriggerTransform> for ChunkError {
    fn from(value: UnsupportedTriggerTransform) -> Self {
        Self::Transform(value)
    }
}

fn replace(
    factory: &TermFactory,
    term: &Term,
    replacements: &HashMap<Term, Term>,
) -> Result<Term, ChunkError> {
    Ok(factory.replace(term, replacements)?)
}
fn replace_all(
    factory: &TermFactory,
    terms: &[Term],
    replacements: &HashMap<Term, Term>,
) -> Result<Vec<Term>, ChunkError> {
    terms
        .iter()
        .map(|term| replace(factory, term, replacements))
        .collect()
}
fn default_no_perm() -> Exp {
    Exp::new(ExpKind::NoPerm, Default::default())
}
fn condition_exp(condition: Option<Exp>, previous: Option<Exp>) -> Option<Exp> {
    condition.map(|c| {
        Exp::new(
            ExpKind::CondExp(
                c,
                previous.expect("missing permission expression"),
                default_no_perm(),
            ),
            Default::default(),
        )
    })
}
fn binary_exp(
    input: Option<Exp>,
    previous: Option<Exp>,
    kind: fn(Exp, Exp) -> ExpKind,
) -> Option<Exp> {
    input.map(|new| {
        Exp::new(
            kind(previous.expect("missing previous expression"), new),
            Default::default(),
        )
    })
}
fn scale_exp(previous: Option<Exp>, input: Option<Exp>) -> Option<Exp> {
    previous.map(|old| {
        Exp::new(
            ExpKind::PermMul(old, input.expect("missing scaling expression")),
            Default::default(),
        )
    })
}
fn assert_perm(term: &Term) {
    assert_eq!(
        term.sort(),
        &Sort::Perm,
        "chunk permission must have Perm sort"
    );
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicChunk {
    pub(crate) resource_id: BaseId,
    pub(crate) id: BasicChunkIdentifier,
    pub(crate) args: Vec<Term>,
    pub(crate) args_exp: Option<Vec<Exp>>,
    pub(crate) snap: Term,
    pub(crate) snap_exp: Option<Exp>,
    pub(crate) perm: Term,
    pub(crate) perm_exp: Option<Exp>,
    pub(crate) tag: Option<i32>,
}
impl BasicChunk {
    pub fn validate(&self) {
        assert_perm(&self.perm);
        match self.resource_id {
            BaseId::Field => assert_ne!(self.snap.sort(), &Sort::Snap),
            BaseId::Predicate => assert_eq!(self.snap.sort(), &Sort::Snap),
        }
    }
}
impl ChunkContract for BasicChunk {
    fn substitute(
        &self,
        f: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, ChunkError> {
        let mut out = self.clone();
        out.args = replace_all(f, &self.args, replacements)?;
        out.snap = replace(f, &self.snap, replacements)?;
        out.perm = replace(f, &self.perm, replacements)?;
        out.validate();
        Ok(out)
    }
}
impl GeneralChunk for BasicChunk {
    fn resource_id(&self) -> ResourceId {
        self.resource_id.into()
    }
    fn identifier(&self) -> ChunkIdentifier {
        ChunkIdentifier::Basic(self.id.clone())
    }
    fn permission(&self, _: &TermFactory) -> Term {
        self.perm.clone()
    }
    fn permission_exp(&self) -> Option<Exp> {
        self.perm_exp.clone()
    }
    fn tag(&self) -> Option<i32> {
        self.tag
    }
    fn apply_condition(&self, f: &TermFactory, c: Term, e: Option<Exp>) -> Self {
        self.with_permission(
            f.ite(c, self.perm.clone(), f.no_perm()),
            condition_exp(e, self.perm_exp.clone()),
        )
    }
    fn perm_minus(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
        self.with_permission(
            f.perm_minus(self.perm.clone(), p),
            binary_exp(e, self.perm_exp.clone(), ExpKind::PermSub),
        )
    }
    fn perm_plus(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
        self.with_permission(
            f.perm_plus(self.perm.clone(), p),
            binary_exp(e, self.perm_exp.clone(), ExpKind::PermAdd),
        )
    }
    fn perm_scale(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
        self.with_permission(
            f.perm_times(self.perm.clone(), p),
            scale_exp(self.perm_exp.clone(), e),
        )
    }
}
impl NonQuantifiedChunk for BasicChunk {
    fn args(&self) -> &[Term] {
        &self.args
    }
    fn args_exp(&self) -> Option<&[Exp]> {
        self.args_exp.as_deref()
    }
    fn snapshot(&self) -> &Term {
        &self.snap
    }
    fn with_permission(&self, perm: Term, perm_exp: Option<Exp>) -> Self {
        let mut out = self.clone();
        out.perm = perm;
        out.perm_exp = perm_exp;
        out.validate();
        out
    }
    fn with_snapshot(&self, snap: Term, snap_exp: Option<Exp>) -> Self {
        let mut out = self.clone();
        out.snap = snap;
        out.snap_exp = snap_exp;
        out.validate();
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasicMaskHeapChunk {
    pub resource_id: ResourceId,
    pub resource: ResourceKey,
    pub mask: Term,
    pub heap: Term,
}
impl BasicMaskHeapChunk {
    pub fn with_heap(&self, heap: Term) -> Self {
        Self {
            heap,
            ..self.clone()
        }
    }
    /// Source `copy(newMask = ...)` retains the existing heap.
    pub fn with_mask(&self, mask: Term) -> Self {
        Self {
            mask,
            ..self.clone()
        }
    }
    pub fn with_mask_and_heap(&self, mask: Term, heap: Term) -> Self {
        Self {
            mask,
            heap,
            ..self.clone()
        }
    }
}
impl ChunkContract for BasicMaskHeapChunk {
    fn substitute(
        &self,
        f: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, ChunkError> {
        Ok(Self {
            resource_id: self.resource_id,
            resource: self.resource.clone(),
            mask: replace(f, &self.mask, replacements)?,
            heap: replace(f, &self.heap, replacements)?,
        })
    }
}
impl MaskHeapChunk for BasicMaskHeapChunk {
    fn resource_id(&self) -> ResourceId {
        self.resource_id
    }
    fn resource(&self) -> &ResourceKey {
        &self.resource
    }
    fn mask(&self) -> &Term {
        &self.mask
    }
    fn heap(&self) -> &Term {
        &self.heap
    }
}

#[derive(Clone, Debug, Default)]
pub struct ChunkBindings(Vec<(AbstractLocalVar, StoreValue)>);
impl ChunkBindings {
    pub fn new(entries: impl IntoIterator<Item = (AbstractLocalVar, StoreValue)>) -> Self {
        let mut out: Vec<(AbstractLocalVar, StoreValue)> = Vec::new();
        for (key, value) in entries {
            if let Some((old_key, old)) = out.iter_mut().find(|(k, _)| k == &key) {
                *old_key = key;
                *old = value;
            } else {
                out.push((key, value));
            }
        }
        Self(out)
    }
    pub fn iter(&self) -> impl Iterator<Item = &(AbstractLocalVar, StoreValue)> {
        self.0.iter()
    }
}
impl PartialEq for ChunkBindings {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .all(|(k, v)| other.0.iter().any(|(k2, v2)| k == k2 && v == v2))
    }
}
impl Eq for ChunkBindings {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MagicWandChunk {
    pub(crate) id: MagicWandIdentifier,
    pub(crate) bindings: ChunkBindings,
    pub(crate) args: Vec<Term>,
    pub(crate) args_exp: Option<Vec<Exp>>,
    pub(crate) snap: Term,
    pub(crate) perm: Term,
    pub(crate) perm_exp: Option<Exp>,
    pub(crate) tag: Option<i32>,
}
impl MagicWandChunk {
    pub fn validate(&self) {
        assert_perm(&self.perm);
        assert!(
            matches!(self.snap.kind(), TermKind::MagicWandSnapshot(_)),
            "expected magic wand snapshot"
        );
    }
}
// Equality implies the same identifier; omitting other fields preserves the hash contract.
impl Hash for MagicWandChunk {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state);
    }
}
impl ChunkContract for MagicWandChunk {
    fn substitute(
        &self,
        f: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, ChunkError> {
        let mut out = self.clone();
        out.args = replace_all(f, &self.args, replacements)?;
        out.snap = replace(f, &self.snap, replacements)?;
        out.perm = replace(f, &self.perm, replacements)?;
        if !matches!(out.snap.kind(), TermKind::MagicWandSnapshot(_)) {
            return Err(ChunkError::ExpectedWandSnapshot);
        }
        out.validate();
        Ok(out)
    }
}
impl GeneralChunk for MagicWandChunk {
    fn resource_id(&self) -> ResourceId {
        ResourceId::MagicWand
    }
    fn identifier(&self) -> ChunkIdentifier {
        ChunkIdentifier::Wand(self.id.clone())
    }
    fn permission(&self, _: &TermFactory) -> Term {
        self.perm.clone()
    }
    fn permission_exp(&self) -> Option<Exp> {
        self.perm_exp.clone()
    }
    fn tag(&self) -> Option<i32> {
        self.tag
    }
    fn apply_condition(&self, f: &TermFactory, c: Term, e: Option<Exp>) -> Self {
        self.with_permission(
            f.ite(c, self.perm.clone(), f.no_perm()),
            condition_exp(e, self.perm_exp.clone()),
        )
    }
    fn perm_minus(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
        self.with_permission(
            f.perm_minus(self.perm.clone(), p),
            binary_exp(e, self.perm_exp.clone(), ExpKind::PermSub),
        )
    }
    fn perm_plus(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
        self.with_permission(
            f.perm_plus(self.perm.clone(), p),
            binary_exp(e, self.perm_exp.clone(), ExpKind::PermAdd),
        )
    }
    fn perm_scale(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
        self.with_permission(
            f.perm_times(self.perm.clone(), p),
            scale_exp(self.perm_exp.clone(), e),
        )
    }
}
impl NonQuantifiedChunk for MagicWandChunk {
    fn args(&self) -> &[Term] {
        &self.args
    }
    fn args_exp(&self) -> Option<&[Exp]> {
        self.args_exp.as_deref()
    }
    fn snapshot(&self) -> &Term {
        &self.snap
    }
    fn with_permission(&self, perm: Term, perm_exp: Option<Exp>) -> Self {
        let mut out = self.clone();
        out.perm = perm;
        out.perm_exp = perm_exp;
        out.validate();
        out
    }
    fn with_snapshot(&self, snap: Term, snap_exp: Option<Exp>) -> Self {
        assert!(
            snap_exp.is_none(),
            "wand snapshots have no debug expression"
        );
        let mut out = self.clone();
        out.snap = snap;
        out.validate();
        out
    }
}

#[derive(Clone, Debug)]
pub struct QuantifiedFieldChunk {
    pub(crate) id: BasicChunkIdentifier,
    pub(crate) fvf: Term,
    pub(crate) org_condition: Term,
    pub(crate) condition: Term,
    pub(crate) condition_exp: Option<Exp>,
    pub(crate) perm_value: Term,
    pub(crate) perm_value_exp: Option<Exp>,
    pub(crate) invs: Vec<InverseFunctions>,
    pub(crate) singleton_rcvr: Option<Term>,
    pub(crate) singleton_rcvr_exp: Option<Exp>,
    pub(crate) tag: Option<i32>,
    pub(crate) hints: Vec<Term>,
    pub(crate) debugging: bool,
    factory: TermFactory,
    computed_perm: Term,
    computed_perm_exp: Option<Exp>,
    computed_var_exps: Option<Vec<LocalVarDecl>>,
}
// The derived debug variable declarations do not participate in Scala case-class equality.
impl PartialEq for QuantifiedFieldChunk {
    fn eq(&self, b: &Self) -> bool {
        self.id == b.id
            && self.fvf == b.fvf
            && self.org_condition == b.org_condition
            && self.condition == b.condition
            && self.condition_exp == b.condition_exp
            && self.perm_value == b.perm_value
            && self.perm_value_exp == b.perm_value_exp
            && self.invs == b.invs
            && self.singleton_rcvr == b.singleton_rcvr
            && self.singleton_rcvr_exp == b.singleton_rcvr_exp
            && self.tag == b.tag
            && self.hints == b.hints
    }
}
impl Eq for QuantifiedFieldChunk {}
impl QuantifiedFieldChunk {
    pub fn validate(&self) {
        assert!(
            matches!(self.fvf.sort(), Sort::FieldValueFunction { .. }),
            "expected field value function"
        );
        assert_perm(&self.perm_value);
        if self.condition_exp.is_some() {
            assert!(
                self.perm_value_exp.is_some(),
                "missing permission expression"
            );
        }
    }
    pub fn quantified_var_exps(&self) -> Option<Vec<LocalVarDecl>> {
        self.computed_var_exps.clone()
    }
    fn refresh(&mut self, factory: &TermFactory) {
        self.validate();
        self.factory = factory.clone();
        self.computed_perm = factory.ite(
            self.condition.clone(),
            self.perm_value.clone(),
            factory.no_perm(),
        );
        self.computed_perm_exp =
            condition_exp(self.condition_exp.clone(), self.perm_value_exp.clone());
        self.computed_var_exps = self.debugging.then(|| {
            vec![LocalVarDecl::new(
                "r".into(),
                ferrum_silver::ast::r#type::Type::Ref,
                Default::default(),
            )]
        });
    }
    pub fn singleton_arguments(&self) -> Option<Vec<Term>> {
        self.singleton_rcvr.clone().map(|r| vec![r])
    }
    pub fn singleton_argument_exps(&self) -> Option<Vec<Exp>> {
        self.singleton_rcvr_exp.clone().map(|r| vec![r])
    }
    pub fn with_perm(&self, perm: Term, expr: Option<Exp>) -> Self {
        let mut out = self.clone();
        out.perm_value = perm;
        out.perm_value_exp = expr;
        let factory = self.factory.clone();
        out.refresh(&factory);
        out
    }
}
#[derive(Clone, Debug)]
pub struct QuantifiedPredicateChunk {
    pub(crate) id: BasicChunkIdentifier,
    pub(crate) quantified_vars: Vec<Term>,
    pub(crate) quantified_var_exps: Option<Vec<LocalVarDecl>>,
    pub(crate) psf: Term,
    pub(crate) org_condition: Term,
    pub(crate) condition: Term,
    pub(crate) condition_exp: Option<Exp>,
    pub(crate) perm_value: Term,
    pub(crate) perm_value_exp: Option<Exp>,
    pub(crate) invs: Vec<InverseFunctions>,
    pub(crate) singleton_args: Option<Vec<Term>>,
    pub(crate) singleton_arg_exps: Option<Vec<Exp>>,
    pub(crate) tag: Option<i32>,
    pub(crate) hints: Vec<Term>,
    factory: TermFactory,
    computed_perm: Term,
    computed_perm_exp: Option<Exp>,
}
impl PartialEq for QuantifiedPredicateChunk {
    fn eq(&self, b: &Self) -> bool {
        self.id == b.id
            && self.quantified_vars == b.quantified_vars
            && self.quantified_var_exps == b.quantified_var_exps
            && self.psf == b.psf
            && self.org_condition == b.org_condition
            && self.condition == b.condition
            && self.condition_exp == b.condition_exp
            && self.perm_value == b.perm_value
            && self.perm_value_exp == b.perm_value_exp
            && self.invs == b.invs
            && self.singleton_args == b.singleton_args
            && self.singleton_arg_exps == b.singleton_arg_exps
            && self.tag == b.tag
            && self.hints == b.hints
    }
}
impl Eq for QuantifiedPredicateChunk {}

impl QuantifiedPredicateChunk {
    pub fn validate(&self) {
        assert!(
            matches!(self.psf.sort(), Sort::PredicateSnapFunction { .. }),
            "expected predicate snapshot function"
        );
        assert!(
            self.quantified_vars
                .iter()
                .all(|v| matches!(v.kind(), TermKind::Var(_)))
        );
        assert_perm(&self.perm_value);
        if self.condition_exp.is_some() {
            assert!(
                self.perm_value_exp.is_some(),
                "missing permission expression"
            );
        }
    }
    fn refresh(&mut self, factory: &TermFactory) {
        self.validate();
        self.factory = factory.clone();
        self.computed_perm = factory.ite(
            self.condition.clone(),
            self.perm_value.clone(),
            factory.no_perm(),
        );
        self.computed_perm_exp =
            condition_exp(self.condition_exp.clone(), self.perm_value_exp.clone());
    }
    pub fn singleton_arguments(&self) -> Option<&[Term]> {
        self.singleton_args.as_deref()
    }
    pub fn singleton_argument_exps(&self) -> Option<&[Exp]> {
        self.singleton_arg_exps.as_deref()
    }
    pub fn with_perm(&self, perm: Term, expr: Option<Exp>) -> Self {
        let mut out = self.clone();
        out.perm_value = perm;
        out.perm_value_exp = expr;
        let factory = self.factory.clone();
        out.refresh(&factory);
        out
    }
}
macro_rules! impl_quantified_basic {
    ($kind:ty, $snap:ident, $resource:expr) => {
        impl GeneralChunk for $kind {
            fn resource_id(&self) -> ResourceId {
                $resource
            }
            fn identifier(&self) -> ChunkIdentifier {
                ChunkIdentifier::Basic(self.id.clone())
            }
            fn permission(&self, f: &TermFactory) -> Term {
                assert_eq!(
                    f.options().use_flyweight,
                    self.factory.options().use_flyweight,
                    "cannot mix flyweight modes"
                );
                self.computed_perm.clone()
            }
            fn permission_exp(&self) -> Option<Exp> {
                self.computed_perm_exp.clone()
            }
            fn tag(&self) -> Option<i32> {
                self.tag
            }
            fn apply_condition(&self, f: &TermFactory, c: Term, e: Option<Exp>) -> Self {
                let mut out = self.clone();
                out.condition = f.and([c, self.condition.clone()]);
                out.condition_exp = binary_exp(e, self.condition_exp.clone(), |old, new| {
                    ExpKind::And(new, old)
                });
                out.refresh(f);
                out
            }
            fn perm_minus(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
                self.with_perm(
                    f.perm_minus(self.perm_value.clone(), p),
                    binary_exp(e, self.perm_value_exp.clone(), ExpKind::PermSub),
                )
            }
            fn perm_plus(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
                self.with_perm(
                    f.perm_plus(self.perm_value.clone(), p),
                    binary_exp(e, self.perm_value_exp.clone(), ExpKind::PermAdd),
                )
            }
            fn perm_scale(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
                self.with_perm(
                    f.perm_times(self.permission(f), p),
                    scale_exp(self.permission_exp(), e),
                )
            }
        }
    };
}
impl_quantified_basic!(QuantifiedFieldChunk, fvf, ResourceId::Field);
impl_quantified_basic!(QuantifiedPredicateChunk, psf, ResourceId::Predicate);

impl ChunkContract for QuantifiedFieldChunk {
    fn substitute(
        &self,
        f: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, ChunkError> {
        let mut out = self.clone();
        out.fvf = replace(f, &self.fvf, replacements)?;
        out.org_condition = replace(f, &self.org_condition, replacements)?;
        out.condition = replace(f, &self.condition, replacements)?;
        out.perm_value = replace(f, &self.perm_value, replacements)?;
        out.singleton_rcvr = self
            .singleton_rcvr
            .as_ref()
            .map(|t| replace(f, t, replacements))
            .transpose()?;
        out.hints = replace_all(f, &self.hints, replacements)?;
        out.invs = self
            .invs
            .iter()
            .map(|i| i.substitute(f, replacements).map_err(ChunkError::from))
            .collect::<Result<_, _>>()?;
        out.refresh(f);
        Ok(out)
    }
}
impl QuantifiedChunk for QuantifiedFieldChunk {
    fn quantified_vars(&self, f: &TermFactory) -> Vec<Term> {
        vec![f.predef_receiver_var()]
    }
    fn quantified_var_exps(&self) -> Option<Vec<LocalVarDecl>> {
        QuantifiedFieldChunk::quantified_var_exps(self)
    }
    fn inverse_functions(&self) -> &[InverseFunctions] {
        &self.invs
    }
    fn original_condition(&self) -> &Term {
        &self.org_condition
    }
    fn snapshot_map(&self) -> &Term {
        &self.fvf
    }
    fn value_at(&self, f: &TermFactory, args: &[Term]) -> Term {
        assert_eq!(args.len(), 1);
        f.lookup(self.id.0.clone(), self.fvf.clone(), args[0].clone())
    }
    fn with_snapshot_map(&self, snapshot: Term) -> Self {
        let mut out = self.clone();
        out.fvf = snapshot;
        let factory = self.factory.clone();
        out.refresh(&factory);
        out
    }
}
impl ChunkContract for QuantifiedPredicateChunk {
    fn substitute(
        &self,
        f: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, ChunkError> {
        let mut out = self.clone();
        out.psf = replace(f, &self.psf, replacements)?;
        out.org_condition = replace(f, &self.org_condition, replacements)?;
        out.condition = replace(f, &self.condition, replacements)?;
        out.perm_value = replace(f, &self.perm_value, replacements)?;
        out.singleton_args = self
            .singleton_args
            .as_ref()
            .map(|ts| replace_all(f, ts, replacements))
            .transpose()?;
        out.hints = replace_all(f, &self.hints, replacements)?;
        out.invs = self
            .invs
            .iter()
            .map(|i| i.substitute(f, replacements).map_err(ChunkError::from))
            .collect::<Result<_, _>>()?;
        out.refresh(f);
        Ok(out)
    }
}
impl QuantifiedChunk for QuantifiedPredicateChunk {
    fn quantified_vars(&self, _: &TermFactory) -> Vec<Term> {
        self.quantified_vars.clone()
    }
    fn quantified_var_exps(&self) -> Option<Vec<LocalVarDecl>> {
        self.quantified_var_exps.clone()
    }
    fn inverse_functions(&self) -> &[InverseFunctions] {
        &self.invs
    }
    fn original_condition(&self) -> &Term {
        &self.org_condition
    }
    fn snapshot_map(&self) -> &Term {
        &self.psf
    }
    fn value_at(&self, f: &TermFactory, args: &[Term]) -> Term {
        f.predicate_lookup(self.id.0.clone(), self.psf.clone(), args.to_vec())
    }
    fn with_snapshot_map(&self, snapshot: Term) -> Self {
        let mut out = self.clone();
        out.psf = snapshot;
        let factory = self.factory.clone();
        out.refresh(&factory);
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuantifiedMagicWandChunk {
    pub(crate) id: MagicWandIdentifier,
    pub(crate) quantified_vars: Vec<Term>,
    pub(crate) quantified_var_exps: Option<Vec<LocalVarDecl>>,
    pub(crate) wsf: Term,
    pub(crate) org_condition: Term,
    pub(crate) perm: Term,
    pub(crate) perm_exp: Option<Exp>,
    pub(crate) invs: Vec<InverseFunctions>,
    pub(crate) singleton_args: Option<Vec<Term>>,
    pub(crate) singleton_arg_exps: Option<Vec<Exp>>,
    pub(crate) tag: Option<i32>,
    pub(crate) hints: Vec<Term>,
}
impl QuantifiedMagicWandChunk {
    pub fn validate(&self) {
        assert!(
            matches!(self.wsf.sort(), Sort::PredicateSnapFunction { codomain, .. } if **codomain == Sort::MagicWandSnapFunction),
            "expected predicate snapshot function with wand-snapshot codomain"
        );
        assert!(
            self.quantified_vars
                .iter()
                .all(|v| matches!(v.kind(), TermKind::Var(_)))
        );
        assert_perm(&self.perm);
    }
    pub fn singleton_arguments(&self) -> Option<&[Term]> {
        self.singleton_args.as_deref()
    }
    pub fn singleton_argument_exps(&self) -> Option<&[Exp]> {
        self.singleton_arg_exps.as_deref()
    }
    pub fn with_perm(&self, perm: Term, perm_exp: Option<Exp>) -> Self {
        let mut out = self.clone();
        out.perm = perm;
        out.perm_exp = perm_exp;
        out.validate();
        out
    }
}
impl ChunkContract for QuantifiedMagicWandChunk {
    fn substitute(
        &self,
        f: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, ChunkError> {
        let mut out = self.clone();
        out.wsf = replace(f, &self.wsf, replacements)?;
        out.org_condition = replace(f, &self.org_condition, replacements)?;
        out.perm = replace(f, &self.perm, replacements)?;
        out.singleton_args = self
            .singleton_args
            .as_ref()
            .map(|ts| replace_all(f, ts, replacements))
            .transpose()?;
        out.hints = replace_all(f, &self.hints, replacements)?;
        out.invs = self
            .invs
            .iter()
            .map(|i| i.substitute(f, replacements).map_err(ChunkError::from))
            .collect::<Result<_, _>>()?;
        out.validate();
        Ok(out)
    }
}
impl GeneralChunk for QuantifiedMagicWandChunk {
    fn resource_id(&self) -> ResourceId {
        ResourceId::MagicWand
    }
    fn identifier(&self) -> ChunkIdentifier {
        ChunkIdentifier::Wand(self.id.clone())
    }
    fn permission(&self, _: &TermFactory) -> Term {
        self.perm.clone()
    }
    fn permission_exp(&self) -> Option<Exp> {
        self.perm_exp.clone()
    }
    fn tag(&self) -> Option<i32> {
        self.tag
    }
    fn apply_condition(&self, f: &TermFactory, c: Term, e: Option<Exp>) -> Self {
        self.with_perm(
            f.ite(c, self.perm.clone(), f.no_perm()),
            condition_exp(e, self.perm_exp.clone()),
        )
    }
    fn perm_minus(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
        self.with_perm(
            f.perm_minus(self.perm.clone(), p),
            binary_exp(e, self.perm_exp.clone(), ExpKind::PermSub),
        )
    }
    fn perm_plus(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
        self.with_perm(
            f.perm_plus(self.perm.clone(), p),
            binary_exp(e, self.perm_exp.clone(), ExpKind::PermAdd),
        )
    }
    fn perm_scale(&self, f: &TermFactory, p: Term, e: Option<Exp>) -> Self {
        self.with_perm(
            f.perm_times(self.perm.clone(), p),
            scale_exp(self.perm_exp.clone(), e),
        )
    }
}
impl QuantifiedChunk for QuantifiedMagicWandChunk {
    fn quantified_vars(&self, _: &TermFactory) -> Vec<Term> {
        self.quantified_vars.clone()
    }
    fn quantified_var_exps(&self) -> Option<Vec<LocalVarDecl>> {
        self.quantified_var_exps.clone()
    }
    fn inverse_functions(&self) -> &[InverseFunctions] {
        &self.invs
    }
    fn original_condition(&self) -> &Term {
        &self.org_condition
    }
    fn snapshot_map(&self) -> &Term {
        &self.wsf
    }
    fn value_at(&self, f: &TermFactory, args: &[Term]) -> Term {
        f.predicate_lookup(self.id.to_string(), self.wsf.clone(), args.to_vec())
    }
    fn with_snapshot_map(&self, snapshot: Term) -> Self {
        let mut out = self.clone();
        out.wsf = snapshot;
        out.validate();
        out
    }
}

/// Closed representation of the source's concrete chunk classes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Chunk {
    Basic(BasicChunk),
    QuantifiedField(QuantifiedFieldChunk),
    QuantifiedPredicate(QuantifiedPredicateChunk),
    QuantifiedMagicWand(QuantifiedMagicWandChunk),
    MagicWand(MagicWandChunk),
    MaskHeap(BasicMaskHeapChunk),
}
impl Chunk {
    pub fn validate(&self) {
        match self {
            Self::Basic(c) => c.validate(),
            Self::QuantifiedField(c) => c.validate(),
            Self::QuantifiedPredicate(c) => c.validate(),
            Self::QuantifiedMagicWand(c) => c.validate(),
            Self::MagicWand(c) => c.validate(),
            Self::MaskHeap(_) => {}
        }
    }
}
impl ChunkContract for Chunk {
    fn substitute(
        &self,
        f: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, ChunkError> {
        Ok(match self {
            Self::Basic(c) => Self::Basic(c.substitute(f, replacements)?),
            Self::QuantifiedField(c) => Self::QuantifiedField(c.substitute(f, replacements)?),
            Self::QuantifiedPredicate(c) => {
                Self::QuantifiedPredicate(c.substitute(f, replacements)?)
            }
            Self::QuantifiedMagicWand(c) => {
                Self::QuantifiedMagicWand(c.substitute(f, replacements)?)
            }
            Self::MagicWand(c) => Self::MagicWand(c.substitute(f, replacements)?),
            Self::MaskHeap(c) => Self::MaskHeap(c.substitute(f, replacements)?),
        })
    }
}

impl BasicChunk {
    pub fn new(
        resource_id: BaseId,
        id: BasicChunkIdentifier,
        args: Vec<Term>,
        args_exp: Option<Vec<Exp>>,
        snap: Term,
        snap_exp: Option<Exp>,
        perm: Term,
        perm_exp: Option<Exp>,
        tag: Option<i32>,
    ) -> Self {
        let result = Self {
            resource_id,
            id,
            args,
            args_exp,
            snap,
            snap_exp,
            perm,
            perm_exp,
            tag,
        };
        result.validate();
        result
    }
    pub fn resource_id_ref(&self) -> &BaseId {
        &self.resource_id
    }
    pub fn id_ref(&self) -> &BasicChunkIdentifier {
        &self.id
    }
    pub fn args_ref(&self) -> &Vec<Term> {
        &self.args
    }
    pub fn args_exp_ref(&self) -> &Option<Vec<Exp>> {
        &self.args_exp
    }
    pub fn snap_ref(&self) -> &Term {
        &self.snap
    }
    pub fn snap_exp_ref(&self) -> &Option<Exp> {
        &self.snap_exp
    }
    pub fn perm_ref(&self) -> &Term {
        &self.perm
    }
    pub fn perm_exp_ref(&self) -> &Option<Exp> {
        &self.perm_exp
    }
    pub fn tag_ref(&self) -> &Option<i32> {
        &self.tag
    }
}

impl MagicWandChunk {
    pub fn new(
        id: MagicWandIdentifier,
        bindings: ChunkBindings,
        args: Vec<Term>,
        args_exp: Option<Vec<Exp>>,
        snap: Term,
        perm: Term,
        perm_exp: Option<Exp>,
        tag: Option<i32>,
    ) -> Self {
        let result = Self {
            id,
            bindings,
            args,
            args_exp,
            snap,
            perm,
            perm_exp,
            tag,
        };
        result.validate();
        result
    }
    pub fn id_ref(&self) -> &MagicWandIdentifier {
        &self.id
    }
    pub fn bindings_ref(&self) -> &ChunkBindings {
        &self.bindings
    }
    pub fn args_ref(&self) -> &Vec<Term> {
        &self.args
    }
    pub fn args_exp_ref(&self) -> &Option<Vec<Exp>> {
        &self.args_exp
    }
    pub fn snap_ref(&self) -> &Term {
        &self.snap
    }
    pub fn perm_ref(&self) -> &Term {
        &self.perm
    }
    pub fn perm_exp_ref(&self) -> &Option<Exp> {
        &self.perm_exp
    }
    pub fn tag_ref(&self) -> &Option<i32> {
        &self.tag
    }
}

impl QuantifiedFieldChunk {
    pub fn new(
        factory: &TermFactory,
        id: BasicChunkIdentifier,
        fvf: Term,
        org_condition: Term,
        condition: Term,
        condition_exp: Option<Exp>,
        perm_value: Term,
        perm_value_exp: Option<Exp>,
        invs: Vec<InverseFunctions>,
        singleton_rcvr: Option<Term>,
        singleton_rcvr_exp: Option<Exp>,
        tag: Option<i32>,
        hints: Vec<Term>,
        debugging: bool,
    ) -> Self {
        assert!(
            matches!(fvf.sort(), Sort::FieldValueFunction { .. }),
            "expected field value function"
        );
        assert_perm(&perm_value);
        let computed_perm = factory.ite(condition.clone(), perm_value.clone(), factory.no_perm());
        let computed_perm_exp = self::condition_exp(condition_exp.clone(), perm_value_exp.clone());
        let result = Self {
            id,
            fvf,
            org_condition,
            condition,
            condition_exp,
            perm_value,
            perm_value_exp,
            invs,
            singleton_rcvr,
            singleton_rcvr_exp,
            tag,
            hints,
            factory: factory.clone(),
            computed_perm,
            computed_perm_exp,
            debugging,
            computed_var_exps: debugging.then(|| {
                vec![LocalVarDecl::new(
                    "r".into(),
                    ferrum_silver::ast::r#type::Type::Ref,
                    Default::default(),
                )]
            }),
        };
        result.validate();
        result
    }
    pub fn id_ref(&self) -> &BasicChunkIdentifier {
        &self.id
    }
    pub fn fvf_ref(&self) -> &Term {
        &self.fvf
    }
    pub fn org_condition_ref(&self) -> &Term {
        &self.org_condition
    }
    pub fn condition_ref(&self) -> &Term {
        &self.condition
    }
    pub fn condition_exp_ref(&self) -> &Option<Exp> {
        &self.condition_exp
    }
    pub fn perm_value_ref(&self) -> &Term {
        &self.perm_value
    }
    pub fn perm_value_exp_ref(&self) -> &Option<Exp> {
        &self.perm_value_exp
    }
    pub fn invs_ref(&self) -> &Vec<InverseFunctions> {
        &self.invs
    }
    pub fn singleton_rcvr_ref(&self) -> &Option<Term> {
        &self.singleton_rcvr
    }
    pub fn singleton_rcvr_exp_ref(&self) -> &Option<Exp> {
        &self.singleton_rcvr_exp
    }
    pub fn tag_ref(&self) -> &Option<i32> {
        &self.tag
    }
    pub fn hints_ref(&self) -> &Vec<Term> {
        &self.hints
    }
    pub fn debugging_ref(&self) -> &bool {
        &self.debugging
    }
}

impl QuantifiedPredicateChunk {
    pub fn new(
        factory: &TermFactory,
        id: BasicChunkIdentifier,
        quantified_vars: Vec<Term>,
        quantified_var_exps: Option<Vec<LocalVarDecl>>,
        psf: Term,
        org_condition: Term,
        condition: Term,
        condition_exp: Option<Exp>,
        perm_value: Term,
        perm_value_exp: Option<Exp>,
        invs: Vec<InverseFunctions>,
        singleton_args: Option<Vec<Term>>,
        singleton_arg_exps: Option<Vec<Exp>>,
        tag: Option<i32>,
        hints: Vec<Term>,
    ) -> Self {
        assert!(
            matches!(psf.sort(), Sort::PredicateSnapFunction { .. }),
            "expected predicate snapshot function"
        );
        assert!(
            quantified_vars
                .iter()
                .all(|v| matches!(v.kind(), TermKind::Var(_)))
        );
        assert_perm(&perm_value);
        let computed_perm = factory.ite(condition.clone(), perm_value.clone(), factory.no_perm());
        let computed_perm_exp = self::condition_exp(condition_exp.clone(), perm_value_exp.clone());
        let result = Self {
            id,
            quantified_vars,
            quantified_var_exps,
            psf,
            org_condition,
            condition,
            condition_exp,
            perm_value,
            perm_value_exp,
            invs,
            singleton_args,
            singleton_arg_exps,
            tag,
            hints,
            factory: factory.clone(),
            computed_perm,
            computed_perm_exp,
        };
        result.validate();
        result
    }
    pub fn id_ref(&self) -> &BasicChunkIdentifier {
        &self.id
    }
    pub fn quantified_vars_ref(&self) -> &Vec<Term> {
        &self.quantified_vars
    }
    pub fn quantified_var_exps_ref(&self) -> &Option<Vec<LocalVarDecl>> {
        &self.quantified_var_exps
    }
    pub fn psf_ref(&self) -> &Term {
        &self.psf
    }
    pub fn org_condition_ref(&self) -> &Term {
        &self.org_condition
    }
    pub fn condition_ref(&self) -> &Term {
        &self.condition
    }
    pub fn condition_exp_ref(&self) -> &Option<Exp> {
        &self.condition_exp
    }
    pub fn perm_value_ref(&self) -> &Term {
        &self.perm_value
    }
    pub fn perm_value_exp_ref(&self) -> &Option<Exp> {
        &self.perm_value_exp
    }
    pub fn invs_ref(&self) -> &Vec<InverseFunctions> {
        &self.invs
    }
    pub fn singleton_args_ref(&self) -> &Option<Vec<Term>> {
        &self.singleton_args
    }
    pub fn singleton_arg_exps_ref(&self) -> &Option<Vec<Exp>> {
        &self.singleton_arg_exps
    }
    pub fn tag_ref(&self) -> &Option<i32> {
        &self.tag
    }
    pub fn hints_ref(&self) -> &Vec<Term> {
        &self.hints
    }
}

impl QuantifiedMagicWandChunk {
    pub fn new(
        id: MagicWandIdentifier,
        quantified_vars: Vec<Term>,
        quantified_var_exps: Option<Vec<LocalVarDecl>>,
        wsf: Term,
        org_condition: Term,
        perm: Term,
        perm_exp: Option<Exp>,
        invs: Vec<InverseFunctions>,
        singleton_args: Option<Vec<Term>>,
        singleton_arg_exps: Option<Vec<Exp>>,
        tag: Option<i32>,
        hints: Vec<Term>,
    ) -> Self {
        let result = Self {
            id,
            quantified_vars,
            quantified_var_exps,
            wsf,
            org_condition,
            perm,
            perm_exp,
            invs,
            singleton_args,
            singleton_arg_exps,
            tag,
            hints,
        };
        result.validate();
        result
    }
    pub fn id_ref(&self) -> &MagicWandIdentifier {
        &self.id
    }
    pub fn quantified_vars_ref(&self) -> &Vec<Term> {
        &self.quantified_vars
    }
    pub fn quantified_var_exps_ref(&self) -> &Option<Vec<LocalVarDecl>> {
        &self.quantified_var_exps
    }
    pub fn wsf_ref(&self) -> &Term {
        &self.wsf
    }
    pub fn org_condition_ref(&self) -> &Term {
        &self.org_condition
    }
    pub fn perm_ref(&self) -> &Term {
        &self.perm
    }
    pub fn perm_exp_ref(&self) -> &Option<Exp> {
        &self.perm_exp
    }
    pub fn invs_ref(&self) -> &Vec<InverseFunctions> {
        &self.invs
    }
    pub fn singleton_args_ref(&self) -> &Option<Vec<Term>> {
        &self.singleton_args
    }
    pub fn singleton_arg_exps_ref(&self) -> &Option<Vec<Exp>> {
        &self.singleton_arg_exps
    }
    pub fn tag_ref(&self) -> &Option<i32> {
        &self.tag
    }
    pub fn hints_ref(&self) -> &Vec<Term> {
        &self.hints
    }
}

#[cfg(test)]
mod chunk_behavior_tests {
    use super::*;
    use crate::state::identifiers::Identifier;
    use crate::state::terms::TermOptions;

    #[test]
    fn quantified_field_scale_uses_conditional_permission_and_caches_it() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let condition = f.var(Identifier::new("c"), Sort::Bool, false);
        let value = f.var(Identifier::new("p"), Sort::Perm, false);
        let multiplier = f.var(Identifier::new("q"), Sort::Perm, false);
        let fvf = f.var(
            Identifier::new("fvf"),
            Sort::FieldValueFunction {
                codomain: Box::new(Sort::Int),
                field_name: "f".into(),
            },
            false,
        );
        let chunk = QuantifiedFieldChunk::new(
            &f,
            BasicChunkIdentifier("f".into()),
            fvf,
            condition.clone(),
            condition,
            None,
            value,
            None,
            vec![],
            None,
            None,
            None,
            vec![],
            true,
        );
        let first = chunk.permission(&f);
        let second = chunk.permission(&f);
        assert!(first.ptr_eq(&second));
        let scaled = chunk.perm_scale(&f, multiplier.clone(), None);
        assert_eq!(scaled.perm_value_ref(), &f.perm_times(first, multiplier));
        assert!(
            chunk.quantified_var_exps().unwrap()[0]
                .same_node(&chunk.quantified_var_exps().unwrap()[0])
        );
    }
}
