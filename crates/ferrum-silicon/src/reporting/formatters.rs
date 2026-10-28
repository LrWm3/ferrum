//! State formatting for debugger and symbolic-execution logs.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/reporting/Formatters.scala
//! Status: source layout, term filters and JSON-like text are implemented. Term,
//! chunk and AST rendering are supplied by a fallible renderer until their full
//! source-compatible Display implementations are available.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::decider::path_conditions::RecordedPathConditions;
use crate::state::{
    chunks::Chunk,
    heap::{Heap, ListBackedHeap},
    state::State,
    store::{MapBackedStore, Store},
    terms::{Term, TermKind},
};
use ferrum_silver::ast::{expression::Exp, r#type::Type};

/// Source `toString` calls, kept fallible until complete printer implementations exist.
pub trait StateRenderer {
    type Error;
    fn term(&self, term: &Term) -> Result<String, Self::Error>;
    fn expression(&self, expression: &Exp) -> Result<String, Self::Error>;
    fn typ(&self, typ: &Type) -> Result<String, Self::Error>;
    fn chunk(&self, chunk: &Chunk) -> Result<String, Self::Error>;
}
/// Source hides built-in equalities involving a Combine, and `not(x == null)`
/// when null is the right operand. Other equalities and reversed null are retained.
pub fn visible_path_condition(term: &Term) -> bool {
    match term.kind() {
        TermKind::BuiltinEquals(left, right) => {
            !matches!(left.kind(), TermKind::Combine(..))
                && !matches!(right.kind(), TermKind::Combine(..))
        }
        TermKind::Not(inner) => {
            !matches!(inner.kind(), TermKind::BuiltinEquals(_, right) if matches!(right.kind(), TermKind::Null))
        }
        _ => true,
    }
}
pub struct DefaultStateFormatter<R> {
    pub renderer: R,
    pub trace_enabled: bool,
}
impl<R: StateRenderer> DefaultStateFormatter<R> {
    pub fn format_store(&self, store: &MapBackedStore) -> Result<String, R::Error> {
        let entries = store
            .values()
            .iter()
            .map(|(key, (term, expression))| {
                let extra = match expression {
                    Some(e) => format!("Some({})", self.renderer.expression(e)?),
                    None => "None".into(),
                };
                Ok(format!(
                    "({},({},{}))",
                    self.renderer.expression(key.expression())?,
                    self.renderer.term(term)?,
                    extra
                ))
            })
            .collect::<Result<Vec<_>, R::Error>>()?;
        Ok(format!("({})", entries.join(", ")))
    }
    pub fn format_heap(&self, heap: &ListBackedHeap) -> Result<String, R::Error> {
        Ok(format!(
            "({})",
            heap.values()
                .iter()
                .map(|c| self.renderer.chunk(c))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        ))
    }
    pub fn format_conditions<'a>(
        &self,
        pcs: impl IntoIterator<Item = &'a Term>,
    ) -> Result<String, R::Error> {
        Ok(format!(
            "({})",
            pcs.into_iter()
                .filter(|term| visible_path_condition(term))
                .map(|term| self.renderer.term(term))
                .collect::<Result<Vec<_>, _>>()?
                .join(", ")
        ))
    }
    pub fn format_state<P, D, J>(
        &self,
        state: &State<P, D, J>,
        pcs: &RecordedPathConditions,
    ) -> Result<String, R::Error> {
        let old = state
            .old_heaps
            .iter()
            .map(|(name, heap)| Ok(format!("{}: {}", name, self.format_heap(heap)?)))
            .collect::<Result<Vec<_>, R::Error>>()?
            .join(",\n");
        let conditions = if self.trace_enabled {
            format!("{}\n", self.format_conditions(pcs.assumptions().iter())?)
        } else {
            String::new()
        };
        Ok(format!(
            "Store: {},\nHeap: {},\nOHs: ({}),\nPCs: {})",
            self.format_store(&state.g)?,
            self.format_heap(&state.h)?,
            old,
            conditions
        ))
    }
    /// Exact source JSON-like formatting, including its lack of string escaping.
    pub fn to_json<P, D, J>(
        &self,
        state: &State<P, D, J>,
        pcs: &[Term],
    ) -> Result<String, R::Error> {
        let store = state
            .g
            .term_values()
            .map(|(key, term)| {
                let typ = key
                    .expression()
                    .typ()
                    .expect("AbstractLocalVar always has a type");
                Ok(format!(
                    "{{\"value\":\"{} -> {}\",\"type\":\"{}\"}}",
                    self.renderer.expression(key.expression())?,
                    self.renderer.term(term)?,
                    self.renderer.typ(&typ)?
                ))
            })
            .collect::<Result<Vec<_>, R::Error>>()?
            .join(",");
        let heap = self.json_heap(&state.h)?;
        let old = match state.old_heaps.get(&"old".to_string()) {
            Some(h) => self.json_heap(h)?,
            None => "[]".into(),
        };
        let mut seen = Vec::<&Term>::new();
        let mut conditions = Vec::new();
        for term in pcs {
            if visible_path_condition(term) && !seen.contains(&term) {
                seen.push(term);
                conditions.push(format!("\"{}\"", self.renderer.term(term)?));
            }
        }
        let conditions = conditions.join(",");
        Ok(format!(
            "{{\"store\":[{}],\"heap\":{},\"oldHeap\":{},\"pcs\":[{}]}}",
            store, heap, old, conditions
        ))
    }
    fn json_heap(&self, heap: &ListBackedHeap) -> Result<String, R::Error> {
        Ok(format!(
            "[{}]",
            heap.values()
                .iter()
                .map(|c| self.renderer.chunk(c).map(|s| format!("\"{}\"", s)))
                .collect::<Result<Vec<_>, _>>()?
                .join(",")
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::{
        identifiers::Identifier,
        terms::{Sort, TermFactory, TermOptions},
    };
    #[test]
    fn filter_hides_only_source_null_orientation_and_combine_equalities() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let x = f.var(Identifier::new("x"), Sort::Ref, false);
        let hidden = f.not(f.builtin_equals(x.clone(), f.null()));
        let reversed = f.not(f.builtin_equals(f.null(), x));
        let a = f.var(Identifier::new("a"), Sort::Snap, false);
        let b = f.var(Identifier::new("b"), Sort::Snap, false);
        let combined = f.builtin_equals(f.combine(a.clone(), b), a);
        assert!(!visible_path_condition(&hidden));
        assert!(visible_path_condition(&reversed));
        assert!(!visible_path_condition(&combined));
    }
}
