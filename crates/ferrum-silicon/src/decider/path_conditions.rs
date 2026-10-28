// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Scoped path conditions from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/decider/PathConditions.scala
//! Status: layered assumptions, scopes, marks, quantified and debug projections implemented;
//! debug expression projection requires the real Silver simplifier callback.

use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet as OrderedSet;
use crate::debugger::debug_exp::DebugExp;
use crate::state::terms::{
    Declaration, Quantifier, Term, TermFactory, TermKind, Trigger, UnsupportedSubterms,
    UnsupportedTriggerTransform,
};
use ferrum_silver::ast::expression::{Exp, ExpKind, Trigger as AstTrigger};
use std::collections::HashMap;

pub type Mark = i32;
fn union<T: Clone + Eq + std::hash::Hash>(a: &OrderedSet<T>, b: &OrderedSet<T>) -> OrderedSet<T> {
    a.iter().chain(b.iter()).cloned().collect()
}
fn insert<T: Clone + Eq + std::hash::Hash>(set: &mut OrderedSet<T>, value: T) {
    *set = set.incl(value);
}

pub fn is_global(t: &Term) -> bool {
    match t.kind() {
        TermKind::Quantification { is_global, .. }
        | TermKind::HasDomain(_, _, is_global)
        | TermKind::HasPredicateDomain(_, _, is_global) => *is_global,
        TermKind::IsReadPermVar(_) => true,
        _ => false,
    }
}

#[derive(Clone, Debug, Default)]
struct Layer {
    branch: Option<Term>,
    branch_exp: Option<(Exp, Option<Exp>)>,
    global: OrderedSet<Term>,
    local: OrderedSet<Term>,
    global_defs: OrderedSet<Term>,
    local_defs: OrderedSet<Term>,
    global_debug: OrderedSet<DebugExp>,
    local_debug: OrderedSet<DebugExp>,
    global_debug_defs: OrderedSet<DebugExp>,
    local_debug_defs: OrderedSet<DebugExp>,
    declarations: OrderedSet<Declaration>,
    debug_stack: Vec<OrderedSet<DebugExp>>,
    inherited_debug: OrderedSet<DebugExp>,
}
impl Layer {
    fn assumptions(&self) -> OrderedSet<Term> {
        union(&self.global, &self.local)
    }
    fn add(&mut self, term: Term, definition: bool) {
        assert!(
            !matches!(term.kind(), TermKind::And(_)),
            "conjunction must be split"
        );
        if is_global(&term) {
            insert(&mut self.global, term.clone());
            if definition {
                insert(&mut self.global_defs, term);
            }
        } else {
            insert(&mut self.local, term.clone());
            if definition {
                insert(&mut self.local_defs, term);
            }
        }
    }
    fn definitions_only(&self) -> Self {
        Self {
            global: self.global_defs.clone(),
            local: self.local_defs.clone(),
            global_defs: self.global_defs.clone(),
            local_defs: self.local_defs.clone(),
            global_debug: self.global_debug_defs.clone(),
            local_debug: self.local_debug_defs.clone(),
            global_debug_defs: self.global_debug_defs.clone(),
            local_debug_defs: self.local_debug_defs.clone(),
            declarations: self.declarations.clone(),
            ..Self::default()
        }
    }
    fn add_debug(&mut self, debug: DebugExp) {
        if debug.is_global() {
            insert(&mut self.global_debug, debug);
        } else if let Some(open) = self.debug_stack.last_mut() {
            insert(open, debug);
        } else {
            insert(&mut self.local_debug, debug);
        }
    }
    fn open_debug(&self, still_open: &OrderedSet<DebugExp>) -> OrderedSet<DebugExp> {
        self.debug_stack
            .iter()
            .rev()
            .flat_map(|s| s.iter())
            .filter(|e| !self.inherited_debug.contains(e) && still_open.contains(e))
            .cloned()
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathError {
    UnknownMark(Mark),
    InvalidMark(Mark),
    NoScope,
    NoLayer,
    NoDebugSubexpression,
    Traversal(UnsupportedSubterms),
    Transform(UnsupportedTriggerTransform),
}
impl From<UnsupportedSubterms> for PathError {
    fn from(e: UnsupportedSubterms) -> Self {
        Self::Traversal(e)
    }
}
impl From<UnsupportedTriggerTransform> for PathError {
    fn from(e: UnsupportedTriggerTransform) -> Self {
        Self::Transform(e)
    }
}
impl std::fmt::Display for PathError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "path-condition error: {self:?}")
    }
}
impl std::error::Error for PathError {}

/// Immutable snapshot. Layers are stored oldest-first; source stack views are newest-first.
#[derive(Clone, Debug)]
pub struct RecordedPathConditions {
    layers: Vec<Layer>,
}
impl RecordedPathConditions {
    pub fn branch_conditions(&self) -> Vec<Term> {
        self.layers
            .iter()
            .rev()
            .filter_map(|l| l.branch.clone())
            .collect()
    }
    pub fn branch_condition_exps(&self) -> Vec<(Exp, Option<Exp>)> {
        self.layers
            .iter()
            .rev()
            .filter_map(|l| l.branch_exp.clone())
            .collect()
    }
    pub fn assumptions(&self) -> OrderedSet<Term> {
        self.layers
            .iter()
            .rev()
            .flat_map(|l| l.assumptions().into_iter())
            .collect()
    }
    pub fn defining_assumptions(&self) -> OrderedSet<Term> {
        self.layers
            .iter()
            .rev()
            .flat_map(|l| l.global_defs.iter())
            .chain(self.layers.iter().rev().flat_map(|l| l.local_defs.iter()))
            .cloned()
            .collect()
    }
    pub fn declarations(&self) -> OrderedSet<Declaration> {
        self.layers
            .iter()
            .rev()
            .flat_map(|l| l.declarations.iter())
            .cloned()
            .collect()
    }
    pub fn contains(&self, term: &Term) -> bool {
        assert!(
            !matches!(term.kind(), TermKind::And(_)),
            "conjunction must be split"
        );
        self.layers.iter().any(|l| {
            if is_global(term) {
                l.global.contains(term)
            } else {
                l.local.contains(term) || l.branch.as_ref() == Some(term)
            }
        })
    }
    pub fn definitions_only(&self) -> Self {
        Self {
            layers: self.layers.iter().map(Layer::definitions_only).collect(),
        }
    }
    fn non_global_debug(&self) -> Vec<OrderedSet<DebugExp>> {
        let still_open: OrderedSet<_> = self
            .layers
            .last()
            .map(|l| {
                l.debug_stack
                    .iter()
                    .rev()
                    .flat_map(|s| s.iter())
                    .cloned()
                    .collect()
            })
            .unwrap_or_default();
        self.layers
            .iter()
            .rev()
            .map(|l| union(&l.local_debug, &l.open_debug(&still_open)))
            .collect()
    }
    pub fn assumption_exps(&self) -> OrderedSet<DebugExp> {
        self.layers
            .iter()
            .rev()
            .flat_map(|l| l.global_debug.iter().cloned())
            .chain(self.non_global_debug().into_iter().flatten())
            .collect()
    }
    pub fn defining_assumption_exps(&self) -> OrderedSet<DebugExp> {
        self.layers
            .iter()
            .rev()
            .flat_map(|l| l.global_debug_defs.iter())
            .chain(
                self.layers
                    .iter()
                    .rev()
                    .flat_map(|l| l.local_debug_defs.iter()),
            )
            .cloned()
            .collect()
    }
    pub fn conditionalized(&self, f: &TermFactory) -> Vec<Term> {
        let mut unconditional = Vec::new();
        let mut conditional = Vec::new();
        let mut lhs = f.boolean(true);
        for layer in &self.layers {
            unconditional.extend(layer.global.iter().cloned());
            if let Some(condition) = &layer.branch {
                lhs = f.and([lhs, condition.clone()]);
            }
            conditional.push(f.implies(lhs.clone(), f.and(layer.local.iter().cloned())));
        }
        unconditional.extend(conditional);
        unconditional
    }
    pub fn quantified(
        &self,
        f: &TermFactory,
        quantifier: Quantifier,
        qvars: &[Term],
        triggers: &[Trigger],
        name: &str,
        is_global: bool,
        ignore: &Term,
    ) -> Result<(Vec<Term>, Vec<Term>), PathError> {
        let ignores = ignore.top_level_conjuncts();
        let mut globals = Vec::new();
        let mut quantified = Vec::new();
        for layer in self.layers.iter().rev() {
            let branch = layer.branch.clone().unwrap_or_else(|| f.boolean(true));
            let mut local = Vec::new();
            let mut lifted = Vec::new();
            let branch_depends = qvars.iter().try_fold(false, |any, v| {
                Ok::<_, UnsupportedSubterms>(any || branch.contains(v)?)
            })?;
            for assumption in &layer.local {
                if ignores.contains(assumption) {
                    continue;
                }
                let depends = if branch_depends {
                    true
                } else {
                    qvars.iter().try_fold(false, |any, v| {
                        Ok::<_, UnsupportedSubterms>(any || assumption.contains(v)?)
                    })?
                };
                if !branch_depends && !depends {
                    lifted.push(f.implies(branch.clone(), assumption.clone()));
                } else {
                    local.push(assumption.clone());
                }
            }
            globals.extend(layer.global.iter().cloned());
            globals.extend(lifted);
            quantified.push(f.quantification(
                quantifier,
                qvars.to_vec(),
                f.implies(branch, f.and(local)),
                triggers.to_vec(),
                name.into(),
                is_global,
                None,
            )?);
        }
        Ok((globals, quantified))
    }
}

impl RecordedPathConditions {
    pub fn conditionalized_exp<E>(
        &self,
        f: &TermFactory,
        simplify: &impl Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<Vec<DebugExp>, E> {
        let locals = self.non_global_debug();
        let mut unconditional = Vec::new();
        let mut conditional = Vec::new();
        let mut lhs = f.boolean(true);
        let mut lhs_exp = Exp::new(ExpKind::TrueLit, Default::default());
        let mut lhs_new = lhs_exp.clone();
        for (layer, local) in self.layers.iter().zip(locals.iter().rev()) {
            unconditional.extend(layer.global_debug.iter().cloned());
            if let Some((old, new)) = &layer.branch_exp {
                lhs = f.and([
                    lhs,
                    layer
                        .branch
                        .as_ref()
                        .expect("branch expression without branch condition")
                        .clone(),
                ]);
                let new = new.as_ref().expect("missing final branch expression");
                lhs_exp = if matches!(lhs_exp.kind(), ExpKind::TrueLit) {
                    old.clone()
                } else {
                    Exp::new(ExpKind::And(lhs_exp, old.clone()), Default::default())
                };
                lhs_new = if matches!(lhs_new.kind(), ExpKind::TrueLit) {
                    new.clone()
                } else {
                    Exp::new(ExpKind::And(lhs_new, new.clone()), Default::default())
                };
            }
            if !local.is_empty() && !matches!(lhs_exp.kind(), ExpKind::TrueLit) {
                conditional.push(DebugExp::create(
                    None,
                    Some(lhs_exp.clone()),
                    Some(lhs_new.clone()),
                    Some(lhs.clone()),
                    false,
                    local.clone(),
                    true,
                    simplify,
                )?);
            } else {
                conditional.extend(local.iter().cloned());
            }
        }
        unconditional.extend(conditional);
        Ok(unconditional)
    }
    pub fn quantified_exp<E>(
        &self,
        quantifier: Quantifier,
        qvars: Vec<Exp>,
        term_qvars: Vec<Term>,
        triggers: Vec<AstTrigger>,
        term_triggers: Vec<Trigger>,
        _ignore: &Term,
        simplify: &impl Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<(OrderedSet<DebugExp>, OrderedSet<DebugExp>), E> {
        let locals = self.non_global_debug();
        let mut globals = OrderedSet::new();
        let mut non_globals = OrderedSet::new();
        for (layer, local) in self.layers.iter().rev().zip(locals) {
            for debug in &layer.global_debug {
                insert(&mut globals, debug.clone());
            }
            let item = if let Some((old, new)) = &layer.branch_exp {
                let body = if matches!(old.kind(), ExpKind::TrueLit) {
                    local
                } else {
                    let implication = DebugExp::create(
                        None,
                        Some(old.clone()),
                        Some(
                            new.as_ref()
                                .expect("missing final branch expression")
                                .clone(),
                        ),
                        layer.branch.clone(),
                        false,
                        local,
                        true,
                        simplify,
                    )?;
                    [implication].into_iter().collect()
                };
                DebugExp::quantified(
                    None,
                    false,
                    body,
                    if quantifier == Quantifier::Forall {
                        "QA".into()
                    } else {
                        "QE".into()
                    },
                    qvars.clone(),
                    term_qvars.clone(),
                    triggers.clone(),
                    term_triggers.clone(),
                )
            } else {
                DebugExp::group("quantifiedExp".into(), local)
            };
            insert(&mut non_globals, item);
        }
        Ok((globals, non_globals))
    }
}

#[derive(Clone, Debug)]
pub struct LayeredPathConditionStack {
    layers: Vec<Layer>,
    marks: HashMap<Mark, usize>,
    scope_marks: Vec<Mark>,
    next_mark: i32,
    all_assumptions: OrderedSet<Term>,
    debugging: bool,
}
impl LayeredPathConditionStack {
    pub fn new(debugging: bool) -> Self {
        let mut stack = Self {
            layers: Vec::new(),
            marks: HashMap::new(),
            scope_marks: Vec::new(),
            next_mark: 0,
            all_assumptions: OrderedSet::new(),
            debugging,
        };
        stack.push_scope();
        stack
    }
    fn push_layer(&mut self) -> Mark {
        let mark = self.next_mark;
        self.next_mark = self.next_mark.wrapping_add(1);
        self.marks.insert(mark, self.layers.len());
        let stack = if self.debugging {
            self.layers
                .last()
                .map(|l| l.debug_stack.clone())
                .unwrap_or_default()
        } else {
            Vec::new()
        };
        let inherited_debug = stack.iter().rev().flat_map(|s| s.iter()).cloned().collect();
        self.layers.push(Layer {
            debug_stack: stack,
            inherited_debug,
            ..Layer::default()
        });
        mark
    }
    pub fn push_scope(&mut self) {
        let mark = self.push_layer();
        self.scope_marks.push(mark);
    }
    pub fn mark(&mut self) -> Mark {
        self.push_layer()
    }
    pub fn pop_scope(&mut self) -> Result<(), PathError> {
        let mark = self.scope_marks.pop().ok_or(PathError::NoScope)?;
        self.pop_until_mark(mark)
    }
    pub fn pop_until_mark(&mut self, mark: Mark) -> Result<(), PathError> {
        let target = *self.marks.get(&mark).ok_or(PathError::UnknownMark(mark))?;
        if target >= self.layers.len() {
            return Err(PathError::InvalidMark(mark));
        }
        self.marks.remove(&mark);
        while self.layers.len() > target {
            let layer = self.layers.pop().expect("checked layer length");
            for term in &layer.assumptions() {
                self.all_assumptions = self.all_assumptions.excl(term);
            }
        }
        Ok(())
    }
    pub fn after(&self, mark: Mark) -> Result<RecordedPathConditions, PathError> {
        let target = *self.marks.get(&mark).ok_or(PathError::UnknownMark(mark))?;
        if target > self.layers.len() {
            return Err(PathError::InvalidMark(mark));
        }
        Ok(RecordedPathConditions {
            layers: self.layers[target..].to_vec(),
        })
    }
    /// Branch-worker replay visits the source stack from oldest layer to newest.
    pub fn replay_layers(&self) -> Vec<OrderedSet<Term>> {
        self.layers.iter().map(Layer::assumptions).collect()
    }
    pub fn recorded(&self) -> RecordedPathConditions {
        RecordedPathConditions {
            layers: self.layers.clone(),
        }
    }
    pub fn definitions_only(&self) -> Self {
        let mut result = self.clone();
        result.layers = self.layers.iter().map(Layer::definitions_only).collect();
        result.all_assumptions = self
            .layers
            .iter()
            .rev()
            .flat_map(|l| l.global_defs.iter())
            .chain(self.layers.iter().rev().flat_map(|l| l.local_defs.iter()))
            .cloned()
            .collect();
        result
    }
    pub fn assumptions(&self) -> &OrderedSet<Term> {
        &self.all_assumptions
    }
    pub fn contains(&self, assumption: &Term) -> bool {
        self.all_assumptions.contains(assumption)
    }
    pub fn add(&mut self, term: &Term) -> Result<(), PathError> {
        self.add_internal(term, false)
    }
    pub fn add_definition(&mut self, term: &Term) -> Result<(), PathError> {
        self.add_internal(term, true)
    }
    fn add_internal(&mut self, term: &Term, definition: bool) -> Result<(), PathError> {
        let layer = self.layers.last_mut().ok_or(PathError::NoLayer)?;
        for conjunct in term.top_level_conjuncts() {
            layer.add(conjunct.clone(), definition);
            insert(&mut self.all_assumptions, conjunct);
        }
        Ok(())
    }
    pub fn add_declaration(&mut self, decl: Declaration) -> Result<(), PathError> {
        insert(
            &mut self
                .layers
                .last_mut()
                .ok_or(PathError::NoLayer)?
                .declarations,
            decl,
        );
        Ok(())
    }
    pub fn set_branch_condition(
        &mut self,
        term: Term,
        expression: (Exp, Option<Exp>),
    ) -> Result<(), PathError> {
        let layer = self.layers.last_mut().ok_or(PathError::NoLayer)?;
        assert!(layer.branch.is_none(), "branch condition already set");
        layer.branch = Some(term);
        assert!(layer.branch_exp.is_none(), "branch expression already set");
        layer.branch_exp = Some(expression);
        Ok(())
    }
    pub fn start_debug_subexpression(&mut self) -> Result<(), PathError> {
        self.layers
            .last_mut()
            .ok_or(PathError::NoLayer)?
            .debug_stack
            .push(OrderedSet::new());
        Ok(())
    }
    pub fn finish_debug_subexpression(&mut self, description: String) -> Result<(), PathError> {
        let layer = self.layers.last_mut().ok_or(PathError::NoLayer)?;
        let children = layer
            .debug_stack
            .pop()
            .ok_or(PathError::NoDebugSubexpression)?;
        if !children.is_empty() {
            layer.add_debug(DebugExp::group(description, children));
        }
        Ok(())
    }
    pub fn add_debug_exp(&mut self, exp: DebugExp) -> Result<(), PathError> {
        self.layers
            .last_mut()
            .ok_or(PathError::NoLayer)?
            .add_debug(exp);
        Ok(())
    }
    pub fn add_non_global_debug_exp(&mut self, exp: DebugExp) -> Result<(), PathError> {
        insert(
            &mut self
                .layers
                .last_mut()
                .ok_or(PathError::NoLayer)?
                .local_debug,
            exp,
        );
        Ok(())
    }
    pub fn add_global_debug_exp(&mut self, exp: DebugExp) -> Result<(), PathError> {
        insert(
            &mut self
                .layers
                .last_mut()
                .ok_or(PathError::NoLayer)?
                .global_debug,
            exp,
        );
        Ok(())
    }
    pub fn is_empty(&self) -> bool {
        self.layers.iter().all(|l| l.branch.is_none())
            && self.all_assumptions.is_empty()
            && self.marks.keys().all(|m| self.scope_marks.contains(m))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::identifiers::Identifier;
    use crate::state::terms::{Sort, TermOptions};
    fn factory() -> TermFactory {
        TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        })
    }
    #[test]
    fn mark_snapshot_and_pop_keep_source_duplicate_cache_behavior() {
        let f = factory();
        let a = f.var(Identifier::new("a"), Sort::Bool, false);
        let mut stack = LayeredPathConditionStack::new(false);
        stack.add(&a).unwrap();
        let mark = stack.mark();
        stack.add(&a).unwrap();
        assert!(stack.after(mark).unwrap().contains(&a));
        stack.pop_until_mark(mark).unwrap();
        // Upstream removes popped assumptions from its flat cache even if an older layer also has them.
        assert!(!stack.contains(&a));
        assert!(stack.recorded().contains(&a));
    }
    #[test]
    fn conditionalized_accumulates_branches_oldest_first() {
        let f = factory();
        let a = f.var(Identifier::new("a"), Sort::Bool, false);
        let b = f.var(Identifier::new("b"), Sort::Bool, false);
        let exp = Exp::new(ExpKind::TrueLit, Default::default());
        let mut stack = LayeredPathConditionStack::new(false);
        stack
            .set_branch_condition(a.clone(), (exp.clone(), Some(exp)))
            .unwrap();
        stack.push_scope();
        stack.add(&b).unwrap();
        let result = stack.recorded().conditionalized(&f);
        assert_eq!(result, vec![f.boolean(true), f.implies(a, b)]);
    }
}
