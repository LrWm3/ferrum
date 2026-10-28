// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Symbolic state operations from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/state/State.scala
//! Status: state data, resource queries, strict and conditional merges implemented;
//! supporter-owned data and join mode use explicit type parameters until connected.

use super::chunks::{BasicMaskHeapChunk, Chunk};
use super::heap::{Heap, ListBackedHeap};
use super::store::{MapBackedStore, Store};
use super::terms::{ResourceKey, Sort, Term, TermFactory};
use crate::interfaces::state::chunks::GeneralChunk;
use crate::resources::resources::ResourceId;
use ferrum_silver::ast::expression::{Exp, ExpKind};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateMergeError {
    NonConditionalizableChunk,
    IncompatibleStoreSorts,
    MismatchedFields(Vec<&'static str>),
    UnequalHeapStackLengths,
}
impl std::fmt::Display for StateMergeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "state merge failed: {self:?}")
    }
}
impl std::error::Error for StateMergeError {}

fn conditionalize(
    chunk: &Chunk,
    factory: &TermFactory,
    condition: &Term,
    expression: &Option<Exp>,
) -> Result<Chunk, StateMergeError> {
    Ok(match chunk {
        Chunk::Basic(c) => {
            Chunk::Basic(c.apply_condition(factory, condition.clone(), expression.clone()))
        }
        Chunk::QuantifiedField(c) => Chunk::QuantifiedField(c.apply_condition(
            factory,
            condition.clone(),
            expression.clone(),
        )),
        Chunk::QuantifiedPredicate(c) => Chunk::QuantifiedPredicate(c.apply_condition(
            factory,
            condition.clone(),
            expression.clone(),
        )),
        Chunk::QuantifiedMagicWand(c) => Chunk::QuantifiedMagicWand(c.apply_condition(
            factory,
            condition.clone(),
            expression.clone(),
        )),
        Chunk::MagicWand(c) => {
            Chunk::MagicWand(c.apply_condition(factory, condition.clone(), expression.clone()))
        }
        Chunk::MaskHeap(_) => return Err(StateMergeError::NonConditionalizableChunk),
    })
}
/// Source conditionalizes every chunk and rejects non-general chunks.
pub fn conditionalize_heap(
    heap: &impl Heap,
    factory: &TermFactory,
    condition: &Term,
    expression: &Option<Exp>,
) -> Result<ListBackedHeap, StateMergeError> {
    Ok(ListBackedHeap::from_chunks(
        heap.values()
            .iter()
            .map(|c| conditionalize(c, factory, condition, expression))
            .collect::<Result<Vec<_>, _>>()?,
    ))
}
/// Preserves source duplicate and equality handling: shared general chunks come
/// first; unique chunks receive the respective branch guards; mask chunks merge
/// by resource and use the first guard for both mask and heap ITEs.
pub fn merge_heap(
    h1: &impl Heap,
    cond1: &Term,
    exp1: &Option<Exp>,
    h2: &impl Heap,
    cond2: &Term,
    exp2: &Option<Exp>,
    f: &TermFactory,
) -> Result<ListBackedHeap, StateMergeError> {
    let general1: Vec<_> = h1
        .values()
        .iter()
        .filter(|c| !matches!(c, Chunk::MaskHeap(_)))
        .collect();
    let general2: Vec<_> = h2
        .values()
        .iter()
        .filter(|c| !matches!(c, Chunk::MaskHeap(_)))
        .collect();
    let common: Vec<_> = general1
        .iter()
        .filter(|c| general2.contains(c))
        .copied()
        .collect();
    let mut result: Vec<Chunk> = common.iter().map(|c| (*c).clone()).collect();
    for chunk in &general1 {
        if !general2.contains(chunk) {
            result.push(conditionalize(chunk, f, cond1, exp1)?);
        }
    }
    for chunk in &general2 {
        if !common.contains(chunk) {
            result.push(conditionalize(chunk, f, cond2, exp2)?);
        }
    }
    fn masks(heap: &impl Heap) -> Vec<((ResourceId, ResourceKey), BasicMaskHeapChunk)> {
        let mut out: Vec<((ResourceId, ResourceKey), BasicMaskHeapChunk)> = Vec::new();
        for chunk in heap.values() {
            if let Chunk::MaskHeap(c) = chunk {
                let key = (c.resource_id, c.resource.clone());
                if let Some((old_key, old)) = out.iter_mut().find(|(k, _)| k == &key) {
                    *old_key = key;
                    *old = c.clone();
                } else {
                    out.push((key, c.clone()));
                }
            }
        }
        out
    }
    let first = masks(h1);
    let second = masks(h2);
    let mut keys: Vec<_> = first.iter().map(|(key, _)| key.clone()).collect();
    for (key, _) in &second {
        if !keys.contains(key) {
            keys.push(key.clone());
        }
    }
    for key in keys {
        let a = first.iter().find(|(k, _)| k == &key).map(|(_, c)| c);
        let b = second.iter().find(|(k, _)| k == &key).map(|(_, c)| c);
        let chunk = match (a, b) {
            (Some(a), Some(b)) if a == b => a.clone(),
            (Some(a), Some(b)) => a.with_mask_and_heap(
                f.ite(cond1.clone(), a.mask.clone(), b.mask.clone()),
                f.ite(cond1.clone(), a.heap.clone(), b.heap.clone()),
            ),
            (Some(a), None) => a.clone(),
            (None, Some(b)) => b.clone(),
            (None, None) => unreachable!(),
        };
        result.push(Chunk::MaskHeap(chunk));
    }
    Ok(ListBackedHeap::from_chunks(result))
}
/// Store branch merge drops keys missing on either branch and retains the first
/// debug expression when the symbolic values compare equal.
pub fn merge_store(
    g1: &impl Store,
    cond1: &Term,
    exp1: &Option<Exp>,
    g2: &impl Store,
    f: &TermFactory,
) -> Result<MapBackedStore, StateMergeError> {
    let mut result = Vec::new();
    for (key, (t1, e1)) in g1.values() {
        let Some((_, (t2, e2))) = g2.values().iter().find(|(k, _)| k == key) else {
            continue;
        };
        let value = if t1 == t2 {
            (t1.clone(), e1.clone())
        } else {
            if t1.sort() != t2.sort() {
                return Err(StateMergeError::IncompatibleStoreSorts);
            }
            let debug = exp1.as_ref().map(|condition| {
                Exp::new(
                    ExpKind::CondExp(
                        condition.clone(),
                        e1.clone().expect("missing first debug expression"),
                        e2.clone().expect("missing second debug expression"),
                    ),
                    Default::default(),
                )
            });
            (f.ite(cond1.clone(), t1.clone(), t2.clone()), debug)
        };
        result.push((key.clone(), value));
    }
    Ok(MapBackedStore::from_bindings(result))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resources::resources::BaseId;
    use crate::state::chunks::{BasicChunk, BasicChunkIdentifier};
    use crate::state::identifiers::Identifier;
    use crate::state::terms::{Sort, TermOptions};
    #[test]
    fn merges_retain_first_quantified_permission_tag() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let program = ferrum_silver::ast::program::Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Default::default(),
        );
        let mut left = State::<(), (), ()>::new(
            program,
            OrderedMap::new(),
            OrderedMap::new(),
            (),
            &f,
            false,
            false,
        );
        left.qp_tag = Some(1);
        let mut right = left.clone();
        right.qp_tag = Some(2);
        assert_eq!(
            left.merge_unconditional(&right, &mut |_| {})
                .unwrap()
                .qp_tag,
            Some(1)
        );
        let t = f.boolean(true);
        assert_eq!(
            left.merge_conditional(&t, &None, &right, &t, &None, &f, &mut |_| {})
                .unwrap()
                .qp_tag,
            Some(1)
        );
    }
    #[test]
    fn heap_merge_retains_shared_chunks_and_guards_unique_chunks() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let c = f.var(Identifier::new("c"), Sort::Bool, false);
        let mk = |n| {
            Chunk::Basic(BasicChunk::new(
                BaseId::Field,
                BasicChunkIdentifier("f".into()),
                vec![],
                None,
                f.int_literal(n),
                None,
                f.full_perm(),
                None,
                None,
            ))
        };
        let shared = mk(1);
        let unique = mk(2);
        let left = ListBackedHeap::from_chunks([shared.clone(), unique]);
        let right = ListBackedHeap::from_chunks([shared.clone()]);
        let merged = merge_heap(&left, &c, &None, &right, &f.not(c.clone()), &None, &f).unwrap();
        assert_eq!(merged.values()[0], shared);
        match &merged.values()[1] {
            Chunk::Basic(b) => assert_eq!(b.permission(&f), f.ite(c, f.full_perm(), f.no_perm())),
            _ => panic!("expected basic chunk"),
        }
    }
}

use super::chunks::MagicWandIdentifier;
use super::package::{OrderedMap, PmCache, SsCache};
use super::snapshot_map_cache::SnapshotMapCache;
use super::store::AbstractLocalVar;
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::decider::path_conditions::{LayeredPathConditionStack, RecordedPathConditions};
use crate::supporters::functions::function_recorder::FunctionRecorder;
use ferrum_silver::ast::program::{Field, Member, Predicate, Program};
use ferrum_silver::ast::statement::Stmt;
use ferrum_silver::cfg::silver::silver_cfg::SilverCfg;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HeapCause {
    InhalePre,
    ExhalePost,
    InhaleInv,
    ExhaleInv,
    StateMerge,
    CreateLabel,
    StateConsolidation,
    ExecStmt(Stmt),
    EvalExp(Exp),
}
#[derive(Clone, Debug)]
pub struct IntermediateHeapRecord {
    pub heap: Arc<ListBackedHeap>,
    pub intermediate_cause: Option<HeapCause>,
    pub new_branch_conditions: Vec<(Exp, Term)>,
}
#[derive(Clone, Debug)]
pub struct HeapRecord {
    pub heap: Arc<ListBackedHeap>,
    pub parent_label: String,
    pub cause: HeapCause,
    pub branch_conditions: Vec<(Exp, Term)>,
    pub intermediate_heaps: OrderedMap<String, IntermediateHeapRecord>,
}
#[derive(Clone, Debug)]
pub struct TemporaryHeapRecord {
    pub label: String,
    pub cause: HeapCause,
    pub path_conditions: Arc<LayeredPathConditionStack>,
    pub intermediate_heaps: OrderedMap<String, IntermediateHeapRecord>,
}

/// Source State, parameterized only over its not-yet-connected PredicateData,
/// FunctionData and JoinMode owners. Heap/store handles preserve source reference
/// identity when states are cloned; program/AST values retain structural equality.
#[derive(Debug)]
pub struct State<P, D, J> {
    pub g: Arc<MapBackedStore>,
    pub h: Arc<ListBackedHeap>,
    pub program: Program,
    pub current_member: Option<Member>,
    pub current_block: Option<(String, i32)>,
    pub predicate_data: OrderedMap<String, Arc<P>>,
    pub function_data: OrderedMap<String, Arc<D>>,
    pub old_heaps: OrderedMap<String, Arc<ListBackedHeap>>,
    pub debug_old_heaps: OrderedMap<String, HeapRecord>,
    pub temporary_heap_record: Option<TemporaryHeapRecord>,
    pub parallelize_branches: bool,
    pub record_visited: bool,
    pub visited: Vec<Predicate>,
    pub method_cfg: Option<Arc<SilverCfg>>,
    pub invariant_contexts: Vec<Arc<ListBackedHeap>>,
    pub constrainable_arps: InsertionOrderedSet<Term>,
    pub quantified_variables: Vec<(Term, Option<AbstractLocalVar>)>,
    pub packaging_wand_snapshots: Vec<(Term, Option<AbstractLocalVar>)>,
    pub retrying: bool,
    pub under_join: bool,
    pub function_recorder: FunctionRecorder<D>,
    pub conserving_snapshot_generation: bool,
    pub record_possible_triggers: bool,
    pub possible_triggers: OrderedMap<Exp, Term>,
    pub trigger_exp: bool,
    pub partially_consumed_heap: Option<Arc<ListBackedHeap>>,
    pub permission_scaling_factor: Term,
    pub permission_scaling_factor_exp: Option<Exp>,
    pub is_eval_in_old: bool,
    pub reserve_heaps: Vec<Arc<ListBackedHeap>>,
    pub reserve_cfgs: Vec<Arc<SilverCfg>>,
    pub exhale_ext: bool,
    pub is_in_package: bool,
    pub ss_cache: SsCache,
    pub assert_read_access_only: bool,
    pub qp_fields: Vec<Field>,
    pub qp_predicates: Vec<Predicate>,
    pub qp_magic_wands: Vec<MagicWandIdentifier>,
    pub perm_locations: Vec<ResourceKey>,
    pub sm_cache: SnapshotMapCache,
    pub pm_cache: PmCache,
    pub sm_domain_needed: bool,
    pub qp_tag: Option<i32>,
    pub predicate_snap_map: OrderedMap<String, Sort>,
    pub predicate_formal_var_map: OrderedMap<String, Vec<Term>>,
    pub retry_level: i32,
    pub heap_dependent_triggers: Vec<ResourceKey>,
    pub more_complete_exhale: bool,
    pub more_complete_exhale_qp: bool,
    pub more_joins: J,
    pub respect_function_pre_perm_amounts: bool,
}

impl<P, D, J: Clone> Clone for State<P, D, J> {
    fn clone(&self) -> Self {
        Self {
            g: self.g.clone(),
            h: self.h.clone(),
            program: self.program.clone(),
            current_member: self.current_member.clone(),
            current_block: self.current_block.clone(),
            predicate_data: self.predicate_data.clone(),
            function_data: self.function_data.clone(),
            old_heaps: self.old_heaps.clone(),
            debug_old_heaps: self.debug_old_heaps.clone(),
            temporary_heap_record: self.temporary_heap_record.clone(),
            parallelize_branches: self.parallelize_branches.clone(),
            record_visited: self.record_visited.clone(),
            visited: self.visited.clone(),
            method_cfg: self.method_cfg.clone(),
            invariant_contexts: self.invariant_contexts.clone(),
            constrainable_arps: self.constrainable_arps.clone(),
            quantified_variables: self.quantified_variables.clone(),
            packaging_wand_snapshots: self.packaging_wand_snapshots.clone(),
            retrying: self.retrying.clone(),
            under_join: self.under_join.clone(),
            function_recorder: self.function_recorder.clone(),
            conserving_snapshot_generation: self.conserving_snapshot_generation.clone(),
            record_possible_triggers: self.record_possible_triggers.clone(),
            possible_triggers: self.possible_triggers.clone(),
            trigger_exp: self.trigger_exp.clone(),
            partially_consumed_heap: self.partially_consumed_heap.clone(),
            permission_scaling_factor: self.permission_scaling_factor.clone(),
            permission_scaling_factor_exp: self.permission_scaling_factor_exp.clone(),
            is_eval_in_old: self.is_eval_in_old.clone(),
            reserve_heaps: self.reserve_heaps.clone(),
            reserve_cfgs: self.reserve_cfgs.clone(),
            exhale_ext: self.exhale_ext.clone(),
            is_in_package: self.is_in_package.clone(),
            ss_cache: self.ss_cache.clone(),
            assert_read_access_only: self.assert_read_access_only.clone(),
            qp_fields: self.qp_fields.clone(),
            qp_predicates: self.qp_predicates.clone(),
            qp_magic_wands: self.qp_magic_wands.clone(),
            perm_locations: self.perm_locations.clone(),
            sm_cache: self.sm_cache.clone(),
            pm_cache: self.pm_cache.clone(),
            sm_domain_needed: self.sm_domain_needed.clone(),
            qp_tag: self.qp_tag.clone(),
            predicate_snap_map: self.predicate_snap_map.clone(),
            predicate_formal_var_map: self.predicate_formal_var_map.clone(),
            retry_level: self.retry_level.clone(),
            heap_dependent_triggers: self.heap_dependent_triggers.clone(),
            more_complete_exhale: self.more_complete_exhale.clone(),
            more_complete_exhale_qp: self.more_complete_exhale_qp.clone(),
            more_joins: self.more_joins.clone(),
            respect_function_pre_perm_amounts: self.respect_function_pre_perm_amounts.clone(),
        }
    }
}

impl<P, D, J: Clone + PartialEq> State<P, D, J> {
    /// Source defaults plus explicit config values and the concrete supporter data.
    pub fn new(
        program: Program,
        predicate_data: OrderedMap<String, Arc<P>>,
        function_data: OrderedMap<String, Arc<D>>,
        more_joins: J,
        factory: &TermFactory,
        debugging: bool,
        respect_function_pre_perm_amounts: bool,
    ) -> Self {
        Self {
            g: Arc::new(MapBackedStore::new()),
            h: Arc::new(ListBackedHeap::new()),
            program,
            current_member: None,
            current_block: None,
            predicate_data,
            function_data,
            old_heaps: OrderedMap::new(),
            debug_old_heaps: OrderedMap::new(),
            temporary_heap_record: None,
            parallelize_branches: false,
            record_visited: false,
            visited: vec![],
            method_cfg: None,
            invariant_contexts: vec![],
            constrainable_arps: InsertionOrderedSet::new(),
            quantified_variables: vec![],
            packaging_wand_snapshots: vec![],
            retrying: false,
            under_join: false,
            function_recorder: FunctionRecorder::Noop,
            conserving_snapshot_generation: false,
            record_possible_triggers: false,
            possible_triggers: OrderedMap::new(),
            trigger_exp: false,
            partially_consumed_heap: None,
            permission_scaling_factor: factory.full_perm(),
            permission_scaling_factor_exp: debugging
                .then(|| Exp::new(ExpKind::FullPerm, Default::default())),
            is_eval_in_old: false,
            reserve_heaps: vec![],
            reserve_cfgs: vec![],
            exhale_ext: false,
            is_in_package: false,
            ss_cache: SsCache::new(),
            assert_read_access_only: false,
            qp_fields: vec![],
            qp_predicates: vec![],
            qp_magic_wands: vec![],
            perm_locations: vec![],
            sm_cache: SnapshotMapCache::empty(),
            pm_cache: PmCache::new(),
            sm_domain_needed: false,
            qp_tag: None,
            predicate_snap_map: OrderedMap::new(),
            predicate_formal_var_map: OrderedMap::new(),
            retry_level: 0,
            heap_dependent_triggers: vec![],
            more_complete_exhale: false,
            more_complete_exhale_qp: false,
            more_joins,
            respect_function_pre_perm_amounts,
        }
    }
    pub fn is_method_verification(&self) -> bool {
        self.current_member
            .as_ref()
            .is_none_or(|m| matches!(m, Member::Method(_)))
    }
    pub fn may_assume_upper_bounds(&self) -> bool {
        !matches!(self.current_member, Some(Member::Function(_)))
            || self.respect_function_pre_perm_amounts
    }
    pub fn is_last_retry(&self) -> bool {
        self.retry_level == 0
    }
    pub fn is_recording_heaps(&self) -> bool {
        self.temporary_heap_record.is_some()
    }
    #[must_use]
    pub fn set_current_block(&self, block: (String, i32)) -> Self {
        let mut out = self.clone();
        out.current_block = Some(block);
        out
    }
    #[must_use]
    pub fn inc_cycle_counter(&self, pred: Predicate) -> Self {
        let mut out = self.clone();
        if out.record_visited {
            out.visited.insert(0, pred);
        }
        out
    }
    #[must_use]
    pub fn dec_cycle_counter(&self, member: &Member) -> Self {
        let mut out = self.clone();
        if out.record_visited {
            let Member::Predicate(pred) = member else {
                panic!("visited predicate absent")
            };
            let mut matching: Vec<_> = out.visited.iter().filter(|p| *p == pred).cloned().collect();
            assert!(!matching.is_empty(), "visited predicate absent");
            matching.remove(0);
            matching.extend(out.visited.iter().filter(|p| *p != pred).cloned());
            out.visited = matching;
        }
        out
    }
    pub fn cycles(&self, member: &Member) -> usize {
        match member {
            Member::Predicate(p) => self.visited.iter().filter(|v| *v == p).count(),
            _ => 0,
        }
    }
    #[must_use]
    pub fn set_constrainable(
        &self,
        vars: impl IntoIterator<Item = Term>,
        constrainable: bool,
    ) -> Self {
        let mut out = self.clone();
        for v in vars {
            out.constrainable_arps = if constrainable {
                out.constrainable_arps.incl(v)
            } else {
                out.constrainable_arps.excl(&v)
            };
        }
        out
    }
    #[must_use]
    pub fn scale_permission_factor(
        &self,
        permission: Term,
        exp: Option<Exp>,
        factory: &TermFactory,
    ) -> Self {
        let mut out = self.clone();
        out.permission_scaling_factor =
            factory.perm_times(permission, self.permission_scaling_factor.clone());
        out.permission_scaling_factor_exp =
            self.permission_scaling_factor_exp.as_ref().map(|old| {
                let new = exp.as_ref().expect("missing scaling debug expression");
                Exp::new(
                    ExpKind::PermMul(new.clone(), old.clone()),
                    new.metadata().clone(),
                )
            });
        out
    }
    pub fn relevant_quantified_variables(
        &self,
        predicate: impl Fn(&Term) -> bool,
    ) -> Vec<(Term, Option<AbstractLocalVar>)> {
        let mut vars = self.function_recorder.arguments().unwrap_or_default();
        vars.extend(
            self.packaging_wand_snapshots
                .iter()
                .filter(|(v, _)| predicate(v))
                .cloned(),
        );
        vars.extend(
            self.quantified_variables
                .iter()
                .filter(|(v, _)| predicate(v))
                .cloned(),
        );
        vars
    }
    pub fn all_relevant_quantified_variables(&self) -> Vec<(Term, Option<AbstractLocalVar>)> {
        let mut vars = self.function_recorder.arguments().unwrap_or_default();
        vars.extend(self.packaging_wand_snapshots.clone());
        vars.extend(self.quantified_variables.clone());
        vars
    }
    pub fn relevant_quantified_variables_in(
        &self,
        terms: &[Term],
    ) -> Result<Vec<(Term, Option<AbstractLocalVar>)>, super::terms::UnsupportedSubterms> {
        let mut result = self.function_recorder.arguments().unwrap_or_default();
        for (var, exp) in self
            .packaging_wand_snapshots
            .iter()
            .chain(&self.quantified_variables)
        {
            let mut found = false;
            for term in terms {
                if term.contains(var)? {
                    found = true;
                    break;
                }
            }
            if found {
                result.push((var.clone(), exp.clone()));
            }
        }
        Ok(result)
    }
    pub fn preserve_after_local_evaluation(&self, post: &Self) -> Self {
        let mut out = self.clone();
        out.debug_old_heaps = post.debug_old_heaps.clone();
        out.temporary_heap_record = post.temporary_heap_record.clone();
        out.function_recorder = post.function_recorder.clone();
        out.possible_triggers = post.possible_triggers.clone();
        out.sm_cache = post.sm_cache.clone();
        out.constrainable_arps = post.constrainable_arps.clone();
        out
    }
}

fn same_arc<T>(a: &Option<Arc<T>>, b: &Option<Arc<T>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => Arc::ptr_eq(a, b),
        _ => false,
    }
}
fn same_arc_seq<T>(a: &[Arc<T>], b: &[Arc<T>]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| Arc::ptr_eq(x, y))
}
fn same_arc_map<T>(a: &OrderedMap<String, Arc<T>>, b: &OrderedMap<String, Arc<T>>) -> bool {
    a.iter().count() == b.iter().count()
        && a.iter()
            .all(|(key, value)| b.get(key).is_some_and(|other| Arc::ptr_eq(value, other)))
}
fn same_set<T: Eq>(a: &[T], b: &[T]) -> bool {
    a.iter().all(|x| b.contains(x)) && b.iter().all(|x| a.contains(x))
}
fn distinct_union<T: Eq + Clone>(a: &[T], b: &[T]) -> Vec<T> {
    let mut result = Vec::new();
    for value in a.iter().chain(b) {
        if !result.contains(value) {
            result.push(value.clone());
        }
    }
    result
}
fn merge_debug_heaps(
    a: &OrderedMap<String, HeapRecord>,
    b: &OrderedMap<String, HeapRecord>,
) -> OrderedMap<String, HeapRecord> {
    let mut result = a.clone();
    for (key, other) in b.iter() {
        if let Some(first) = result.get(key) {
            let mut merged = first.clone();
            merged.intermediate_heaps = first.intermediate_heaps.union(&other.intermediate_heaps);
            result.insert(key.clone(), merged);
        } else {
            result.insert(key.clone(), other.clone());
        }
    }
    result
}
fn merge_temporary(
    a: &Option<TemporaryHeapRecord>,
    b: &Option<TemporaryHeapRecord>,
    warn: &mut impl FnMut(String),
) -> Option<TemporaryHeapRecord> {
    match (a, b) {
        (Some(a), Some(b)) if a.label == b.label && a.cause == b.cause => {
            let mut result = a.clone();
            result.intermediate_heaps = a.intermediate_heaps.union(&b.intermediate_heaps);
            Some(result)
        }
        (Some(a), Some(b)) => {
            warn(format!(
                "Attempted to merge states with different temporary heap records: {} and {}",
                a.label, b.label
            ));
            None
        }
        (Some(a), None) => Some(a.clone()),
        (None, Some(b)) => Some(b.clone()),
        (None, None) => None,
    }
}
impl<P, D, J: Clone + PartialEq> State<P, D, J> {
    fn check_merge(&self, other: &Self, joined: bool) -> Result<(), StateMergeError> {
        let mut mismatches = Vec::new();
        macro_rules! equal {
            ($field:ident) => {
                if self.$field != other.$field {
                    mismatches.push(stringify!($field));
                }
            };
        }
        macro_rules! same {
            ($condition:expr, $name:literal) => {
                if !$condition {
                    mismatches.push($name);
                }
            };
        }
        if !joined {
            same!(Arc::ptr_eq(&self.g, &other.g), "g");
            same!(Arc::ptr_eq(&self.h, &other.h), "h");
        }
        equal!(program);
        equal!(current_member);
        equal!(current_block);
        same!(
            same_arc_map(&self.predicate_data, &other.predicate_data),
            "predicate_data"
        );
        same!(
            same_arc_map(&self.function_data, &other.function_data),
            "function_data"
        );
        equal!(parallelize_branches);
        equal!(record_visited);
        equal!(visited);
        same!(same_arc(&self.method_cfg, &other.method_cfg), "method_cfg");
        if !joined {
            same!(
                same_arc_seq(&self.invariant_contexts, &other.invariant_contexts),
                "invariant_contexts"
            );
        }
        if joined {
            equal!(quantified_variables);
            equal!(packaging_wand_snapshots);
        }
        equal!(retrying);
        equal!(under_join);
        equal!(conserving_snapshot_generation);
        equal!(record_possible_triggers);
        if !joined {
            same!(
                same_arc(
                    &self.partially_consumed_heap,
                    &other.partially_consumed_heap
                ),
                "partially_consumed_heap"
            );
        }
        equal!(permission_scaling_factor);
        equal!(permission_scaling_factor_exp);
        equal!(is_eval_in_old);
        if !joined {
            same!(
                same_arc_seq(&self.reserve_heaps, &other.reserve_heaps),
                "reserve_heaps"
            );
        }
        same!(
            same_arc_seq(&self.reserve_cfgs, &other.reserve_cfgs),
            "reserve_cfgs"
        );
        equal!(exhale_ext);
        equal!(is_in_package);
        equal!(assert_read_access_only);
        same!(same_set(&self.qp_fields, &other.qp_fields), "qp_fields");
        same!(
            same_set(&self.qp_predicates, &other.qp_predicates),
            "qp_predicates"
        );
        same!(
            same_set(&self.qp_magic_wands, &other.qp_magic_wands),
            "qp_magic_wands"
        );
        same!(
            same_set(&self.perm_locations, &other.perm_locations),
            "perm_locations"
        );
        if !joined {
            equal!(sm_domain_needed);
        }
        // Scala's `qpTag1` pattern is an unbackticked binding in both merge
        // arms, so the second tag is unconstrained and the first is retained.
        equal!(predicate_snap_map);
        equal!(predicate_formal_var_map);
        equal!(retry_level);
        same!(
            same_set(
                &self.heap_dependent_triggers,
                &other.heap_dependent_triggers
            ),
            "heap_dependent_triggers"
        );
        equal!(more_joins);
        equal!(respect_function_pre_perm_amounts);
        if mismatches.is_empty() {
            Ok(())
        } else {
            Err(StateMergeError::MismatchedFields(mismatches))
        }
    }
    /// The source's strict merge requires the same store and heap instances.
    pub fn merge_unconditional(
        &self,
        other: &Self,
        warn: &mut impl FnMut(String),
    ) -> Result<Self, StateMergeError> {
        self.check_merge(other, false)?;
        let mut out = self.clone();
        out.old_heaps = self.old_heaps.union(&other.old_heaps);
        out.debug_old_heaps = merge_debug_heaps(&self.debug_old_heaps, &other.debug_old_heaps);
        out.temporary_heap_record = merge_temporary(
            &self.temporary_heap_record,
            &other.temporary_heap_record,
            warn,
        );
        out.function_recorder = self.function_recorder.merge(&other.function_recorder);
        out.possible_triggers = self.possible_triggers.union(&other.possible_triggers);
        out.trigger_exp = self.trigger_exp && other.trigger_exp;
        out.constrainable_arps = self
            .constrainable_arps
            .iter()
            .chain(other.constrainable_arps.iter())
            .cloned()
            .collect();
        out.quantified_variables =
            distinct_union(&self.quantified_variables, &other.quantified_variables);
        out.packaging_wand_snapshots = distinct_union(
            &self.packaging_wand_snapshots,
            &other.packaging_wand_snapshots,
        );
        out.ss_cache = self.ss_cache.union(&other.ss_cache);
        out.sm_cache = self.sm_cache.union(&other.sm_cache);
        out.pm_cache = self.pm_cache.union(&other.pm_cache);
        out.more_complete_exhale = self.more_complete_exhale || other.more_complete_exhale;
        out.more_complete_exhale_qp = self.more_complete_exhale_qp || other.more_complete_exhale_qp;
        Ok(out)
    }
    /// Join two states under mutually exclusive branch conditions.
    pub fn merge_conditional(
        &self,
        cond1: &Term,
        exp1: &Option<Exp>,
        other: &Self,
        cond2: &Term,
        exp2: &Option<Exp>,
        f: &TermFactory,
        warn: &mut impl FnMut(String),
    ) -> Result<Self, StateMergeError> {
        self.check_merge(other, true)?;
        if self.invariant_contexts.len() != other.invariant_contexts.len()
            || self.reserve_heaps.len() != other.reserve_heaps.len()
        {
            return Err(StateMergeError::UnequalHeapStackLengths);
        }
        let mut out = self.clone();
        out.debug_old_heaps = merge_debug_heaps(&self.debug_old_heaps, &other.debug_old_heaps);
        out.temporary_heap_record = merge_temporary(
            &self.temporary_heap_record,
            &other.temporary_heap_record,
            warn,
        );
        out.function_recorder = self.function_recorder.merge(&other.function_recorder);
        out.possible_triggers = self.possible_triggers.union(&other.possible_triggers);
        out.trigger_exp = self.trigger_exp && other.trigger_exp;
        out.constrainable_arps = self
            .constrainable_arps
            .iter()
            .chain(other.constrainable_arps.iter())
            .cloned()
            .collect();
        out.sm_domain_needed = self.sm_domain_needed || other.sm_domain_needed;
        out.g = Arc::new(merge_store(
            self.g.as_ref(),
            cond1,
            exp1,
            other.g.as_ref(),
            f,
        )?);
        out.h = Arc::new(merge_heap(
            self.h.as_ref(),
            cond1,
            exp1,
            other.h.as_ref(),
            cond2,
            exp2,
            f,
        )?);
        out.partially_consumed_heap = match (
            &self.partially_consumed_heap,
            &other.partially_consumed_heap,
        ) {
            (None, None) => None,
            (Some(a), None) => Some(Arc::new(conditionalize_heap(a.as_ref(), f, cond1, exp1)?)),
            (None, Some(b)) => Some(Arc::new(conditionalize_heap(b.as_ref(), f, cond2, exp2)?)),
            (Some(a), Some(b)) => Some(Arc::new(merge_heap(
                a.as_ref(),
                cond1,
                exp1,
                b.as_ref(),
                cond2,
                exp2,
                f,
            )?)),
        };
        let mut old = OrderedMap::new();
        for (key, a) in self.old_heaps.iter() {
            if let Some(b) = other.old_heaps.get(key) {
                old.insert(
                    key.clone(),
                    Arc::new(merge_heap(
                        a.as_ref(),
                        cond1,
                        exp1,
                        b.as_ref(),
                        cond2,
                        exp2,
                        f,
                    )?),
                );
            }
        }
        out.old_heaps = old;
        out.invariant_contexts = self
            .invariant_contexts
            .iter()
            .zip(&other.invariant_contexts)
            .map(|(a, b)| {
                merge_heap(a.as_ref(), cond1, exp1, b.as_ref(), cond2, exp2, f).map(Arc::new)
            })
            .collect::<Result<_, _>>()?;
        out.reserve_heaps = self
            .reserve_heaps
            .iter()
            .zip(&other.reserve_heaps)
            .map(|(a, b)| {
                merge_heap(a.as_ref(), cond1, exp1, b.as_ref(), cond2, exp2, f).map(Arc::new)
            })
            .collect::<Result<_, _>>()?;
        out.ss_cache = self.ss_cache.union(&other.ss_cache);
        out.sm_cache = self.sm_cache.union(&other.sm_cache);
        out.pm_cache = self.pm_cache.union(&other.pm_cache);
        Ok(out)
    }
    pub fn merge_recorded(
        &self,
        pc1: &RecordedPathConditions,
        other: &Self,
        pc2: &RecordedPathConditions,
        f: &TermFactory,
        debugging: bool,
        warn: &mut impl FnMut(String),
    ) -> Result<Self, StateMergeError> {
        fn big_and(exps: Vec<Exp>) -> Exp {
            let mut it = exps.into_iter();
            let Some(first) = it.next() else {
                return Exp::new(ExpKind::TrueLit, Default::default());
            };
            it.fold(first, |a, b| {
                let m = a.metadata().clone();
                Exp::new(
                    ExpKind::And(a, b),
                    ferrum_silver::ast::ast::Metadata {
                        position: m.position,
                        info: m.info,
                        error_trafo: Default::default(),
                    },
                )
            })
        }
        let c1 = f.and(pc1.branch_conditions());
        let c2 = f.and(pc2.branch_conditions());
        let e1 = debugging.then(|| {
            big_and(
                pc1.branch_condition_exps()
                    .into_iter()
                    .map(|(_, final_exp)| final_exp.expect("missing final branch expression"))
                    .collect(),
            )
        });
        let e2 = debugging.then(|| {
            big_and(
                pc2.branch_condition_exps()
                    .into_iter()
                    .map(|(_, final_exp)| final_exp.expect("missing final branch expression"))
                    .collect(),
            )
        });
        self.merge_conditional(&c1, &e1, other, &c2, &e2, f, warn)
    }
}

use super::symbol_converter::{DefaultSymbolConverter, SymbolConversionError};
use crate::rules::quantified_chunk_support::SnapshotResource;
use ferrum_silver::ast::expression::ExpressionTypeError;
use ferrum_silver::ast::program::LocalVarDecl;
use ferrum_silver::ast::utility::expressions::MagicWandError;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StateResourceError {
    Wand(MagicWandError),
    Type(ExpressionTypeError),
    Symbol(SymbolConversionError),
    MissingPredicateFormals(String),
}
impl From<MagicWandError> for StateResourceError {
    fn from(e: MagicWandError) -> Self {
        Self::Wand(e)
    }
}
impl From<ExpressionTypeError> for StateResourceError {
    fn from(e: ExpressionTypeError) -> Self {
        Self::Type(e)
    }
}
impl From<SymbolConversionError> for StateResourceError {
    fn from(e: SymbolConversionError) -> Self {
        Self::Symbol(e)
    }
}
impl std::fmt::Display for StateResourceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "state resource error: {self:?}")
    }
}
impl std::error::Error for StateResourceError {}
impl<P, D, J: Clone + PartialEq> State<P, D, J> {
    fn resource_key(&self, resource: &SnapshotResource) -> Result<ResourceKey, StateResourceError> {
        Ok(match resource {
            SnapshotResource::Field(f) => ResourceKey::Field(f.clone()),
            SnapshotResource::Predicate(p) => ResourceKey::Predicate(p.clone()),
            SnapshotResource::Wand(w) => {
                ResourceKey::Wand(MagicWandIdentifier::new(w.clone(), &self.program)?)
            }
        })
    }
    pub fn is_used_as_trigger(
        &self,
        resource: &SnapshotResource,
    ) -> Result<bool, StateResourceError> {
        Ok(self
            .heap_dependent_triggers
            .contains(&self.resource_key(resource)?))
    }
    pub fn is_quantified_resource(
        &self,
        resource: &SnapshotResource,
    ) -> Result<bool, StateResourceError> {
        Ok(match resource {
            SnapshotResource::Field(f) => self.qp_fields.contains(f.as_ref()),
            SnapshotResource::Predicate(p) => self.qp_predicates.contains(p.as_ref()),
            SnapshotResource::Wand(w) => self
                .qp_magic_wands
                .contains(&MagicWandIdentifier::new(w.clone(), &self.program)?),
        })
    }
    pub fn formal_arg_vars(
        &self,
        resource: &SnapshotResource,
        converter: &DefaultSymbolConverter,
        factory: &TermFactory,
    ) -> Result<Vec<Term>, StateResourceError> {
        Ok(match resource {
            SnapshotResource::Field(_) => vec![factory.predef_receiver_var()],
            SnapshotResource::Predicate(p) => {
                self.predicate_formal_var_map
                    .get(&p.name)
                    .cloned()
                    .ok_or_else(|| StateResourceError::MissingPredicateFormals(p.name.clone()))?
            }
            SnapshotResource::Wand(w) => w
                .magic_wand_subexpressions(&self.program)?
                .iter()
                .enumerate()
                .map(|(i, exp)| {
                    Ok(factory.var(
                        super::identifiers::Identifier::new(format!("x{i}")),
                        converter.to_sort(&exp.typ()?)?,
                        false,
                    ))
                })
                .collect::<Result<Vec<_>, StateResourceError>>()?,
        })
    }
    pub fn formal_arg_decls(
        &self,
        resource: &SnapshotResource,
    ) -> Result<Vec<LocalVarDecl>, StateResourceError> {
        Ok(match resource {
            SnapshotResource::Field(_) => vec![LocalVarDecl::new(
                "r".into(),
                ferrum_silver::ast::r#type::Type::Ref,
                Default::default(),
            )],
            SnapshotResource::Predicate(p) => p.formal_args.clone(),
            SnapshotResource::Wand(w) => w
                .magic_wand_subexpressions(&self.program)?
                .iter()
                .enumerate()
                .map(|(i, exp)| {
                    Ok(LocalVarDecl::new(
                        format!("x{i}"),
                        exp.typ()?,
                        Default::default(),
                    ))
                })
                .collect::<Result<Vec<_>, StateResourceError>>()?,
        })
    }
    /// Delegates capture-avoiding AST substitution to the Silver Sanitizer.
    /// Missing stored debug expressions fail before invoking it, as upstream does.
    pub fn substitute_vars_in_exp<E>(
        &self,
        exp: &Exp,
        sanitize: &impl Fn(&Exp, &OrderedMap<String, Exp>) -> Result<Exp, E>,
    ) -> Result<Exp, E> {
        let mut replacements = OrderedMap::new();
        for (var, (_, value)) in self.g.values() {
            let name = match var.expression().kind() {
                ExpKind::LocalVar(v) => v.name.clone(),
                ExpKind::Result(_) => "result".into(),
                ExpKind::LocalVarWithVersion(name, _) => name.clone(),
                _ => unreachable!("validated store key"),
            };
            replacements.insert(
                name,
                value.clone().expect("missing stored debug expression"),
            );
        }
        sanitize(exp, &replacements)
    }
}

#[cfg(test)]
mod state_join_tests {
    use super::*;
    use crate::state::identifiers::Identifier;
    use crate::state::store::AbstractLocalVar;
    use crate::state::terms::{Sort, TermOptions};
    use ferrum_silver::ast::{ast::Metadata, expression::LocalVar, r#type::Type};
    fn program() -> Program {
        Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        )
    }
    #[test]
    fn strict_merge_observes_store_identity_and_conditional_join_drops_unshared_keys() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let state = State::<(), (), u8>::new(
            program(),
            OrderedMap::new(),
            OrderedMap::new(),
            0,
            &f,
            false,
            false,
        );
        assert!(
            state
                .merge_unconditional(&state.clone(), &mut |_| {})
                .is_ok()
        );
        let mut other = state.clone();
        other.g = Arc::new(MapBackedStore::new());
        assert!(matches!(
            state.merge_unconditional(&other, &mut |_| {}),
            Err(StateMergeError::MismatchedFields(_))
        ));
        let var = |name: &str| {
            AbstractLocalVar::new(Exp::new(
                ExpKind::LocalVar(LocalVar::new(name.into(), Type::Int, Metadata::default())),
                Metadata::default(),
            ))
        };
        let x = var("x");
        let y = var("y");
        let mut left = state.clone();
        let mut right = state;
        left.g = Arc::new(MapBackedStore::from_bindings([
            (x.clone(), (f.int_literal(1), None)),
            (y.clone(), (f.int_literal(7), None)),
        ]));
        right.g = Arc::new(MapBackedStore::from_bindings([(
            x.clone(),
            (f.int_literal(2), None),
        )]));
        let cond = f.var(Identifier::new("c"), Sort::Bool, false);
        let joined = left
            .merge_conditional(
                &cond,
                &None,
                &right,
                &f.not(cond.clone()),
                &None,
                &f,
                &mut |_| {},
            )
            .unwrap();
        assert_eq!(
            joined.g.at(&x),
            &f.ite(cond, f.int_literal(1), f.int_literal(2))
        );
        assert!(joined.g.get(&y).is_none());
    }
}

/// Mirrors Utils.conflictFreeUnion, including its upstream behavior of visiting
/// only keys from the first map; a conflicting value aborts the operation.
pub fn conflict_free_union_or_abort<K: Eq + Clone, V: Eq + Clone>(
    first: &OrderedMap<K, V>,
    second: &OrderedMap<K, V>,
) -> Result<OrderedMap<K, V>, StateMergeError> {
    let mut result = OrderedMap::new();
    for (key, value) in first.iter() {
        if second.get(key).is_some_and(|other| other != value) {
            return Err(StateMergeError::MismatchedFields(vec!["contexts"]));
        }
        result.insert(key.clone(), value.clone());
    }
    Ok(result)
}
/// Merge matching optional contexts; a one-sided context is an error.
pub fn merge_optional<T>(
    first: Option<T>,
    second: Option<T>,
    merge: impl FnOnce(T, T) -> Result<T, StateMergeError>,
) -> Result<Option<T>, StateMergeError> {
    match (first, second) {
        (Some(a), Some(b)) => Ok(Some(merge(a, b)?)),
        (None, None) => Ok(None),
        _ => Err(StateMergeError::MismatchedFields(vec!["contexts"])),
    }
}
