// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Function and predicate recording from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/FunctionRecorder.scala
//! Status: actual/noop recorders, depth/context rules, snapshot joining and merge implemented.
//! FunctionData is carried by its real owner through the generic Arc handle.

use crate::rules::quantified_chunk_support::{
    InverseFunctions, PermMapDefinition, SnapshotMapDefinition,
};
use crate::state::store::AbstractLocalVar;
use crate::state::terms::{
    ApplicableKind, ApplicationTarget, Declaration, DeclarationKind, Term, TermFactory, TermKind,
};
use ferrum_silver::ast::expression::{Exp, ExpKind};
use ferrum_silver::ast::program::Predicate;
use std::sync::Arc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExpContext {
    Let(Exp),
    Quantifier(Exp),
}
#[derive(Debug)]
pub enum RecorderOwner<D> {
    Function {
        data: Arc<D>,
        arguments: Vec<(Term, Option<AbstractLocalVar>)>,
    },
    Predicate {
        predicate: Arc<Predicate>,
        arguments: Vec<Term>,
    },
}
impl<D> Clone for RecorderOwner<D> {
    fn clone(&self) -> Self {
        match self {
            Self::Function { data, arguments } => Self::Function {
                data: Arc::clone(data),
                arguments: arguments.clone(),
            },
            Self::Predicate {
                predicate,
                arguments,
            } => Self::Predicate {
                predicate: Arc::clone(predicate),
                arguments: arguments.clone(),
            },
        }
    }
}

impl<D> RecorderOwner<D> {
    pub fn arguments(&self) -> Vec<(Term, Option<AbstractLocalVar>)> {
        match self {
            Self::Function { arguments, .. } => arguments.clone(),
            Self::Predicate { arguments, .. } => {
                arguments.iter().cloned().map(|v| (v, None)).collect()
            }
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotKey {
    pub expression: Exp,
    pub context: Vec<ExpContext>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GuardedSnapshot {
    pub guards: Vec<Term>,
    pub snapshot: Term,
}
#[derive(Debug)]
pub struct ActualFunctionRecorder<D> {
    pub owner: RecorderOwner<D>,
    pub loc_to_snaps: Vec<(SnapshotKey, Vec<GuardedSnapshot>)>,
    pub fapp_to_snaps: Vec<(SnapshotKey, Vec<GuardedSnapshot>)>,
    pub fresh_fvfs_and_domains: Vec<SnapshotMapDefinition>,
    pub fresh_perm_maps: Vec<PermMapDefinition>,
    pub fresh_field_invs: Vec<InverseFunctions>,
    pub fresh_constrained_vars: Vec<(Term, Term)>,
    pub fresh_constraints: Vec<Term>,
    pub fresh_snapshots: Vec<ApplicationTarget>,
    pub fresh_path_symbols: Vec<ApplicationTarget>,
    pub fresh_macros: Vec<Declaration>,
    pub depth: i32,
    pub context: Vec<ExpContext>,
}
#[derive(Debug)]
pub enum FunctionRecorder<D> {
    Noop,
    Actual(ActualFunctionRecorder<D>),
}
impl<D> Clone for ActualFunctionRecorder<D> {
    fn clone(&self) -> Self {
        Self {
            owner: self.owner.clone(),
            loc_to_snaps: self.loc_to_snaps.clone(),
            fapp_to_snaps: self.fapp_to_snaps.clone(),
            fresh_fvfs_and_domains: self.fresh_fvfs_and_domains.clone(),
            fresh_perm_maps: self.fresh_perm_maps.clone(),
            fresh_field_invs: self.fresh_field_invs.clone(),
            fresh_constrained_vars: self.fresh_constrained_vars.clone(),
            fresh_constraints: self.fresh_constraints.clone(),
            fresh_snapshots: self.fresh_snapshots.clone(),
            fresh_path_symbols: self.fresh_path_symbols.clone(),
            fresh_macros: self.fresh_macros.clone(),
            depth: self.depth,
            context: self.context.clone(),
        }
    }
}
impl<D> Clone for FunctionRecorder<D> {
    fn clone(&self) -> Self {
        match self {
            Self::Noop => Self::Noop,
            Self::Actual(r) => Self::Actual(r.clone()),
        }
    }
}

fn insert<T: Eq>(out: &mut Vec<T>, value: T) {
    if !out.contains(&value) {
        out.push(value);
    }
}
fn extend<T: Eq + Clone>(out: &mut Vec<T>, other: &[T]) {
    for value in other {
        insert(out, value.clone());
    }
}
fn is_function(target: &ApplicationTarget) -> bool {
    match target {
        ApplicationTarget::Variable(v) => matches!(v.kind(), TermKind::Var(_)),
        ApplicationTarget::Function(f) => f.data().kind != ApplicableKind::Macro,
    }
}

impl<D> FunctionRecorder<D> {
    pub fn actual(owner: RecorderOwner<D>) -> Self {
        Self::Actual(ActualFunctionRecorder {
            owner,
            loc_to_snaps: vec![],
            fapp_to_snaps: vec![],
            fresh_fvfs_and_domains: vec![],
            fresh_perm_maps: vec![],
            fresh_field_invs: vec![],
            fresh_constrained_vars: vec![],
            fresh_constraints: vec![],
            fresh_snapshots: vec![],
            fresh_path_symbols: vec![],
            fresh_macros: vec![],
            depth: 0,
            context: vec![],
        })
    }
    pub fn arguments(&self) -> Option<Vec<(Term, Option<AbstractLocalVar>)>> {
        match self {
            Self::Noop => None,
            Self::Actual(r) => Some(r.owner.arguments()),
        }
    }
    pub fn depth(&self) -> i32 {
        match self {
            Self::Noop => 0,
            Self::Actual(r) => r.depth,
        }
    }
    pub fn change_depth_by(&self, delta: i32) -> Self {
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            r.depth = r.depth.wrapping_add(delta);
        }
        out
    }
    pub fn enter_let(&self, exp: Exp) -> Self {
        assert!(matches!(exp.kind(), ExpKind::Let(..)));
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            r.context.push(ExpContext::Let(exp));
        }
        out
    }
    pub fn enter_quantified(&self, exp: Exp) -> Self {
        assert!(matches!(
            exp.kind(),
            ExpKind::Forall(..) | ExpKind::Exists(..) | ExpKind::ForPerm(..)
        ));
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            r.context.push(ExpContext::Quantifier(exp));
        }
        out
    }
    pub fn leave_let(&self, exp: &Exp) -> Self {
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            assert_eq!(r.context.last(), Some(&ExpContext::Let(exp.clone())));
            r.context.pop();
        }
        out
    }
    pub fn leave_quantified(&self, exp: &Exp) -> Self {
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            assert_eq!(r.context.last(), Some(&ExpContext::Quantifier(exp.clone())));
            r.context.pop();
        }
        out
    }
    fn record_expression(&self, exp: Exp, guards: Vec<Term>, snap: Term, location: bool) -> Self {
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            if r.depth == 0 {
                let key = SnapshotKey {
                    expression: exp,
                    context: r.context.clone(),
                };
                let map = if location {
                    &mut r.loc_to_snaps
                } else {
                    &mut r.fapp_to_snaps
                };
                let item = GuardedSnapshot {
                    guards,
                    snapshot: snap,
                };
                if let Some((old_key, entries)) = map.iter_mut().find(|(k, _)| k == &key) {
                    *old_key = key;
                    insert(entries, item);
                } else {
                    map.push((key, vec![item]));
                }
            }
        }
        out
    }
    pub fn record_location_snapshot(&self, location: Exp, guards: Vec<Term>, snap: Term) -> Self {
        assert!(matches!(
            location.kind(),
            ExpKind::FieldAccess(_) | ExpKind::PredicateAccess(_)
        ));
        self.record_expression(location, guards, snap, true)
    }
    pub fn record_function_snapshot(&self, app: Exp, guards: Vec<Term>, snap: Term) -> Self {
        assert!(matches!(app.kind(), ExpKind::FuncApp(..)));
        self.record_expression(app, guards, snap, false)
    }
    pub fn record_fvf_and_domain(&self, value: SnapshotMapDefinition) -> Self {
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            if r.depth <= 2 {
                insert(&mut r.fresh_fvfs_and_domains, value);
            }
        }
        out
    }
    pub fn record_perm_map(&self, value: PermMapDefinition) -> Self {
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            if r.depth <= 2 {
                insert(&mut r.fresh_perm_maps, value);
            }
        }
        out
    }
    pub fn record_field_inv(&self, value: InverseFunctions) -> Self {
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            if r.depth <= 2 {
                insert(&mut r.fresh_field_invs, value);
            }
        }
        out
    }
    pub fn record_constrained_var(&self, var: Term, constraint: Term) -> Self {
        assert!(matches!(var.kind(), TermKind::Var(_)));
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            if r.depth <= 2 {
                insert(&mut r.fresh_constrained_vars, (var, constraint));
            }
        }
        out
    }
    pub fn record_constraint(&self, value: Term) -> Self {
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            if r.depth <= 2 {
                insert(&mut r.fresh_constraints, value);
            }
        }
        out
    }
    pub fn record_fresh_snapshot(&self, value: ApplicationTarget) -> Self {
        assert!(is_function(&value));
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            if r.depth <= 3 {
                insert(&mut r.fresh_snapshots, value);
            }
        }
        out
    }
    pub fn record_path_symbol(&self, value: ApplicationTarget) -> Self {
        assert!(is_function(&value));
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            if r.depth <= 2 {
                insert(&mut r.fresh_path_symbols, value);
            }
        }
        out
    }
    pub fn record_fresh_macro(&self, value: Declaration) -> Self {
        assert!(matches!(value.kind(), DeclarationKind::Macro { .. }));
        let mut out = self.clone();
        if let Self::Actual(r) = &mut out {
            if r.depth <= 1 {
                insert(&mut r.fresh_macros, value);
            }
        }
        out
    }
    pub fn merge(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Noop, Self::Noop) => Self::Noop,
            (Self::Actual(a), _) if a.depth > 1 => self.clone(),
            (Self::Actual(a), Self::Actual(b)) => {
                let mut out = a.clone();
                if a.depth == 0 {
                    merge_recordings(&mut out.loc_to_snaps, &b.loc_to_snaps);
                    merge_recordings(&mut out.fapp_to_snaps, &b.fapp_to_snaps);
                }
                extend(&mut out.fresh_fvfs_and_domains, &b.fresh_fvfs_and_domains);
                extend(&mut out.fresh_perm_maps, &b.fresh_perm_maps);
                extend(&mut out.fresh_field_invs, &b.fresh_field_invs);
                extend(&mut out.fresh_constrained_vars, &b.fresh_constrained_vars);
                extend(&mut out.fresh_constraints, &b.fresh_constraints);
                extend(&mut out.fresh_snapshots, &b.fresh_snapshots);
                extend(&mut out.fresh_path_symbols, &b.fresh_path_symbols);
                extend(&mut out.fresh_macros, &b.fresh_macros);
                Self::Actual(out)
            }
            _ => panic!("incompatible function recorder kinds"),
        }
    }
    pub fn location_snapshots(&self, f: &TermFactory) -> Vec<(SnapshotKey, Term)> {
        match self {
            Self::Noop => vec![],
            Self::Actual(r) => r
                .loc_to_snaps
                .iter()
                .map(|(key, values)| (key.clone(), guarded_to_term(f, values, None)))
                .collect(),
        }
    }
    pub fn function_snapshots(&self, f: &TermFactory) -> Vec<(SnapshotKey, Term)> {
        match self {
            Self::Noop => vec![],
            Self::Actual(r) => r
                .fapp_to_snaps
                .iter()
                .map(|(key, values)| (key.clone(), guarded_to_term(f, values, None)))
                .collect(),
        }
    }
}
fn merge_recordings(
    target: &mut Vec<(SnapshotKey, Vec<GuardedSnapshot>)>,
    other: &[(SnapshotKey, Vec<GuardedSnapshot>)],
) {
    for (key, values) in other {
        if let Some((old_key, old)) = target.iter_mut().find(|(k, _)| k == key) {
            *old_key = key.clone();
            extend(old, values);
        } else {
            target.push((key.clone(), values.clone()));
        }
    }
}
fn guarded_to_term(f: &TermFactory, snaps: &[GuardedSnapshot], alternative: Option<Term>) -> Term {
    assert!(!snaps.is_empty());
    if snaps.len() == 1 {
        return match alternative {
            Some(alt) => {
                let mut unique = Vec::new();
                for g in &snaps[0].guards {
                    insert(&mut unique, g.clone());
                }
                f.ite(f.and(unique), snaps[0].snapshot.clone(), alt)
            }
            None => snaps[0].snapshot.clone(),
        };
    }
    if snaps[0].guards.is_empty() {
        return snaps[0].snapshot.clone();
    }
    let first = snaps[0].guards[0].clone();
    let negated = f.not(first.clone());
    let mut one = Vec::new();
    let mut two = Vec::new();
    let mut three = Vec::new();
    for snap in snaps {
        match snap.guards.first() {
            Some(g) if g == &first => insert(
                &mut one,
                GuardedSnapshot {
                    guards: snap.guards[1..].to_vec(),
                    snapshot: snap.snapshot.clone(),
                },
            ),
            Some(g) if g == &negated => insert(
                &mut two,
                GuardedSnapshot {
                    guards: snap.guards[1..].to_vec(),
                    snapshot: snap.snapshot.clone(),
                },
            ),
            _ => insert(&mut three, snap.clone()),
        }
    }
    let alt = if three.is_empty() {
        alternative
    } else {
        Some(guarded_to_term(f, &three, alternative))
    };
    if !one.is_empty() && !two.is_empty() {
        f.ite(
            first,
            guarded_to_term(f, &one, alt.clone()),
            guarded_to_term(f, &two, alt),
        )
    } else {
        let (guard, part) = if !one.is_empty() {
            (first, one)
        } else {
            (negated, two)
        };
        match alt {
            Some(alt) => f.ite(guard, guarded_to_term(f, &part, Some(alt.clone())), alt),
            None => guarded_to_term(f, &part, None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::identifiers::Identifier;
    use crate::state::terms::{Sort, TermOptions};
    use ferrum_silver::ast::ast::Metadata;
    #[test]
    fn opposing_guards_join_as_ite_and_depth_controls_recording() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let owner = RecorderOwner::<()>::Predicate {
            predicate: Arc::new(Predicate::new(ferrum_silver::ast::program::PredicateData {
                name: "p".into(),
                formal_args: vec![],
                body: None,
                meta: Metadata::default(),
            })),
            arguments: vec![],
        };
        let recorder = FunctionRecorder::actual(owner);
        let app = Exp::new(ExpKind::FuncApp("f".into(), vec![]), Metadata::default());
        let guard = f.var(Identifier::new("g"), Sort::Bool, false);
        let first = f.int_literal(1);
        let second = f.int_literal(2);
        let recorder = recorder
            .record_function_snapshot(app.clone(), vec![guard.clone()], first.clone())
            .record_function_snapshot(app.clone(), vec![f.not(guard.clone())], second.clone());
        assert_eq!(
            recorder.function_snapshots(&f)[0].1,
            f.ite(guard, first, second)
        );
        let deep =
            recorder
                .change_depth_by(1)
                .record_function_snapshot(app, vec![], f.int_literal(3));
        assert_eq!(deep.function_snapshots(&f), recorder.function_snapshots(&f));
    }
}
