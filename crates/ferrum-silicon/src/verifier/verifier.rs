// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Verifier error accounting and debug heap recording from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/verifier/Verifier.scala.
//! Status: debug heap algorithms and error limits implemented. Worker service assembly and
//! wand-aware evaluation heap selection are supplied by the verifier context; callers pass the
//! actual evaluation heap and the source-compatible chunk renderer explicitly.

use crate::decider::path_conditions::LayeredPathConditionStack;
use crate::state::{
    chunks::Chunk,
    heap::ListBackedHeap,
    package::OrderedMap,
    state::{HeapCause, HeapRecord, IntermediateHeapRecord, State, TemporaryHeapRecord},
    terms::Term,
};
use ferrum_silver::ast::{expression::Exp, position::Position};
use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

pub const PRE_STATE_LABEL: &str = "old";
#[derive(Default)]
pub struct VerifierErrorCount(AtomicUsize);
impl VerifierErrorCount {
    pub fn increment(&self) -> usize {
        self.0.fetch_add(1, Ordering::SeqCst) + 1
    }
    pub fn report_further_errors(&self, limit: usize) -> bool {
        limit == 0 || limit > self.0.load(Ordering::SeqCst)
    }
}
#[derive(Default)]
pub struct DebugHeapRecorder {
    counter: AtomicUsize,
}
impl DebugHeapRecorder {
    pub fn label<P, D, J, E>(
        &self,
        state: &State<P, D, J>,
        heap: &ListBackedHeap,
        render: &impl Fn(&Chunk) -> Result<String, E>,
    ) -> Result<Option<String>, E> {
        let mut labelled = None;
        let mut debug = None;
        for (label, record) in state.debug_old_heaps.iter() {
            if heap.equal_chunks_by(record.heap.as_ref(), render)? {
                if label.contains("debug") {
                    debug = Some(label.clone());
                } else {
                    labelled = Some(label.clone());
                }
            }
        }
        if labelled.is_some() {
            return Ok(labelled);
        }
        if debug.is_some() {
            return Ok(debug);
        }
        for (_, record) in state.debug_old_heaps.iter() {
            for (label, child) in record.intermediate_heaps.iter() {
                if heap.equal_chunks_by(child.heap.as_ref(), render)? {
                    return Ok(Some(label.clone()));
                }
            }
        }
        if let Some(temp) = &state.temporary_heap_record {
            for (label, child) in temp.intermediate_heaps.iter() {
                if heap.equal_chunks_by(child.heap.as_ref(), render)? {
                    return Ok(Some(label.clone()));
                }
            }
        }
        Ok(None)
    }
    pub fn old_label<P, D, J, E>(
        &self,
        state: &State<P, D, J>,
        heap: &ListBackedHeap,
        position: &Position,
        render: &impl Fn(&Chunk) -> Result<String, E>,
    ) -> Result<String, E> {
        let label = self
            .label(state, heap, render)?
            .unwrap_or_else(|| "unrecordedHeap".into());
        let pos = position
            .line_column()
            .map(|p| format!("l:{}.{}", p.line(), p.column()))
            .unwrap_or_else(|| "l:unknown".into());
        Ok(format!("{label}#{pos}"))
    }
    pub(crate) fn label_or_new<P, D, J, E>(
        &self,
        state: &State<P, D, J>,
        heap: &ListBackedHeap,
        render: &impl Fn(&Chunk) -> Result<String, E>,
    ) -> Result<(String, bool), E> {
        Ok(match self.label(state, heap, render)? {
            Some(label) => (label, false),
            None => (
                format!("debug@{}", self.counter.fetch_add(1, Ordering::SeqCst)),
                true,
            ),
        })
    }
    pub fn record_heap<P, D, J, E>(
        &self,
        state: &mut State<P, D, J>,
        heap: Arc<ListBackedHeap>,
        current_label: Option<String>,
        parent_label: String,
        cause: HeapCause,
        old: &LayeredPathConditionStack,
        new: &LayeredPathConditionStack,
        render: &impl Fn(&Chunk) -> Result<String, E>,
    ) -> Result<(), E> {
        let label = match current_label {
            Some(label) => label,
            None => {
                let (label, fresh) = self.label_or_new(state, &heap, render)?;
                if !fresh {
                    return Ok(());
                }
                label
            }
        };
        state.debug_old_heaps.insert(
            label,
            HeapRecord {
                heap,
                parent_label,
                cause,
                branch_conditions: branch_diff(old, new),
                intermediate_heaps: OrderedMap::new(),
            },
        );
        Ok(())
    }
    pub fn start_key_heap<P, D, J>(
        &self,
        state: &mut State<P, D, J>,
        label: String,
        cause: HeapCause,
        path_conditions: Arc<LayeredPathConditionStack>,
    ) {
        state.temporary_heap_record = Some(TemporaryHeapRecord {
            label,
            cause,
            path_conditions,
            intermediate_heaps: OrderedMap::new(),
        });
    }
    pub fn record_intermediate<P, D, J, E>(
        &self,
        state: &mut State<P, D, J>,
        heap: Arc<ListBackedHeap>,
        new: &LayeredPathConditionStack,
        cause: Option<HeapCause>,
        render: &impl Fn(&Chunk) -> Result<String, E>,
    ) -> Result<(), E> {
        assert!(
            state.temporary_heap_record.is_some(),
            "recordIntermediateHeap called but no temporaryHeapRecord"
        );
        let (label, fresh) = self.label_or_new(state, &heap, render)?;
        if !fresh {
            return Ok(());
        }
        let temp = state.temporary_heap_record.as_mut().expect("checked");
        temp.intermediate_heaps.insert(
            label,
            IntermediateHeapRecord {
                heap,
                intermediate_cause: cause,
                new_branch_conditions: branch_diff(&temp.path_conditions, new),
            },
        );
        Ok(())
    }
    pub(crate) fn record_fresh_intermediate<P, D, J>(
        &self,
        state: &mut State<P, D, J>,
        label: String,
        heap: Arc<ListBackedHeap>,
        new: &LayeredPathConditionStack,
        cause: Option<HeapCause>,
    ) {
        let temp = state
            .temporary_heap_record
            .as_mut()
            .expect("key heap checked");
        temp.intermediate_heaps.insert(
            label,
            IntermediateHeapRecord {
                heap,
                intermediate_cause: cause,
                new_branch_conditions: branch_diff(&temp.path_conditions, new),
            },
        );
    }
    pub fn finish_key_heap<P, D, J, E>(
        &self,
        state: &mut State<P, D, J>,
        heap: Arc<ListBackedHeap>,
        new: &LayeredPathConditionStack,
        render: &impl Fn(&Chunk) -> Result<String, E>,
    ) -> Result<(), E> {
        assert!(
            state.temporary_heap_record.is_some(),
            "finishKeyHeap called but no temporaryHeapRecord"
        );
        self.finish_key_heap_with_probe(state, heap.clone(), &heap, new, render)
    }
    pub(crate) fn finish_key_heap_with_probe<P, D, J, E>(
        &self,
        state: &mut State<P, D, J>,
        heap: Arc<ListBackedHeap>,
        probe: &ListBackedHeap,
        new: &LayeredPathConditionStack,
        render: &impl Fn(&Chunk) -> Result<String, E>,
    ) -> Result<(), E> {
        let (label, fresh) = self.label_or_new(state, probe, render)?;
        let temp = state
            .temporary_heap_record
            .take()
            .expect("key heap checked");
        let in_temp = temp.intermediate_heaps.get(&label).is_some();
        if !fresh
            && !in_temp
            && let Some(existing) = state.debug_old_heaps.get(&label)
        {
            let mut updated = existing.clone();
            updated.intermediate_heaps = updated.intermediate_heaps.union(&temp.intermediate_heaps);
            state.debug_old_heaps.insert(label, updated);
        } else {
            let mut children = OrderedMap::new();
            for (key, value) in temp.intermediate_heaps.iter() {
                if !in_temp || key != &label {
                    children.insert(key.clone(), value.clone());
                }
            }
            state.debug_old_heaps.insert(
                label,
                HeapRecord {
                    heap,
                    parent_label: temp.label,
                    cause: temp.cause,
                    branch_conditions: branch_diff(&temp.path_conditions, new),
                    intermediate_heaps: children,
                },
            );
        }
        Ok(())
    }
    pub fn merge_heap_record<P, D, J>(
        &self,
        state: &mut State<P, D, J>,
        label: String,
        record: HeapRecord,
    ) {
        if let Some(existing) = state.debug_old_heaps.get(&label) {
            let mut updated = existing.clone();
            updated.intermediate_heaps = record
                .intermediate_heaps
                .union(&existing.intermediate_heaps);
            state.debug_old_heaps.insert(label, updated);
        } else {
            state.debug_old_heaps.insert(label, record);
        }
    }
}
fn branch_diff(
    old: &LayeredPathConditionStack,
    new: &LayeredPathConditionStack,
) -> Vec<(Exp, Term)> {
    fn pairs(stack: &LayeredPathConditionStack) -> Vec<(Exp, Term)> {
        let recorded = stack.recorded();
        recorded
            .branch_condition_exps()
            .into_iter()
            .map(|(exp, _)| exp)
            .zip(recorded.branch_conditions())
            .collect()
    }
    let old = pairs(old);
    pairs(new)
        .into_iter()
        .filter(|pair| !old.contains(pair))
        .collect()
}
