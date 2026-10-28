// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

//! Debug expression trees from
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/DebugExp.scala
//! Status: identity, construction, global classification, term collection and tree editing
//! implemented; rendering accepts explicit Silver expression and Silicon term printers. Expression-bearing
//! construction explicitly requires the upstream simplifier rather than skipping it.

use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::state::terms::{
    Quantifier, Term, TermFactory, TermKind, Trigger, UnsupportedTriggerTransform,
};
use ferrum_silver::ast::expression::{Exp, Trigger as AstTrigger};
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::{
    Arc,
    atomic::{AtomicI32, Ordering},
};

static IDS: AtomicI32 = AtomicI32::new(0);
#[derive(Clone, Debug)]
pub enum DebugExpKind {
    Plain,
    Implication,
    Quantified {
        quantifier: String,
        qvars: Vec<Exp>,
        term_qvars: Vec<Term>,
        triggers: Vec<AstTrigger>,
        term_triggers: Vec<Trigger>,
    },
}
#[derive(Debug)]
struct DebugNode {
    id: i32,
    description: Option<String>,
    original_exp: Option<Exp>,
    final_exp: Option<Exp>,
    term: Option<Term>,
    internal: bool,
    children: InsertionOrderedSet<DebugExp>,
    kind: DebugExpKind,
}
/// Equality is node identity, not ID or expression equality.
#[derive(Clone, Debug)]
pub struct DebugExp(Arc<DebugNode>);
impl PartialEq for DebugExp {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl Eq for DebugExp {}
impl Hash for DebugExp {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Arc::as_ptr(&self.0).hash(state);
    }
}
impl DebugExp {
    fn create_raw(
        id: i32,
        description: Option<String>,
        original_exp: Option<Exp>,
        final_exp: Option<Exp>,
        term: Option<Term>,
        internal: bool,
        children: InsertionOrderedSet<DebugExp>,
        kind: DebugExpKind,
    ) -> Self {
        Self(Arc::new(DebugNode {
            id,
            description,
            original_exp,
            final_exp,
            term,
            internal,
            children,
            kind,
        }))
    }
    /// The supplied callback must perform `Simplifier.simplify(exp, true)`.
    pub fn create<E>(
        description: Option<String>,
        original_exp: Option<Exp>,
        final_exp: Option<Exp>,
        term: Option<Term>,
        internal: bool,
        children: InsertionOrderedSet<DebugExp>,
        implication: bool,
        simplify: &impl Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<Self, E> {
        let original_exp = original_exp.as_ref().map(simplify).transpose()?;
        let final_exp = final_exp.as_ref().map(simplify).transpose()?;
        Ok(Self::create_raw(
            IDS.fetch_add(1, Ordering::Relaxed),
            description,
            original_exp,
            final_exp,
            term,
            internal,
            children,
            if implication {
                DebugExpKind::Implication
            } else {
                DebugExpKind::Plain
            },
        ))
    }
    pub fn group(description: String, children: InsertionOrderedSet<DebugExp>) -> Self {
        Self::create_raw(
            IDS.fetch_add(1, Ordering::Relaxed),
            Some(description),
            None,
            None,
            None,
            false,
            children,
            DebugExpKind::Plain,
        )
    }
    pub fn quantified(
        description: Option<String>,
        internal: bool,
        children: InsertionOrderedSet<DebugExp>,
        quantifier: String,
        qvars: Vec<Exp>,
        term_qvars: Vec<Term>,
        triggers: Vec<AstTrigger>,
        term_triggers: Vec<Trigger>,
    ) -> Self {
        Self::create_raw(
            IDS.fetch_add(1, Ordering::Relaxed),
            description,
            None,
            None,
            None,
            internal,
            children,
            DebugExpKind::Quantified {
                quantifier,
                qvars,
                term_qvars,
                triggers,
                term_triggers,
            },
        )
    }
    pub fn id(&self) -> i32 {
        self.0.id
    }
    pub fn description(&self) -> Option<&str> {
        self.0.description.as_deref()
    }
    pub fn original_exp(&self) -> Option<&Exp> {
        self.0.original_exp.as_ref()
    }
    pub fn final_exp(&self) -> Option<&Exp> {
        self.0.final_exp.as_ref()
    }
    pub fn term(&self) -> Option<&Term> {
        self.0.term.as_ref()
    }
    pub fn is_internal(&self) -> bool {
        self.0.internal
    }
    pub fn children(&self) -> &InsertionOrderedSet<DebugExp> {
        &self.0.children
    }
    pub fn kind(&self) -> &DebugExpKind {
        &self.0.kind
    }
    pub fn is_global(&self) -> bool {
        self.term().is_none_or(|t| match t.kind() {
            TermKind::Quantification { is_global, .. }
            | TermKind::HasDomain(_, _, is_global)
            | TermKind::HasPredicateDomain(_, _, is_global) => *is_global,
            TermKind::IsReadPermVar(_) => true,
            _ => false,
        }) && self.children().iter().all(Self::is_global)
    }
    /// Source returns a fresh plain DebugExp retaining its ID (even for subclasses).
    pub fn with_term(&self, term: Term) -> Self {
        Self::create_raw(
            self.id(),
            self.0.description.clone(),
            self.0.original_exp.clone(),
            self.0.final_exp.clone(),
            Some(term),
            self.0.internal,
            self.0.children.clone(),
            DebugExpKind::Plain,
        )
    }
    pub fn remove_children_by_id(&self, ids: &[i32]) -> Self {
        let children = self
            .children()
            .iter()
            .filter(|c| !ids.contains(&c.id()))
            .map(|c| c.remove_children_by_id(ids))
            .collect();
        Self::create_raw(
            self.id(),
            self.0.description.clone(),
            self.0.original_exp.clone(),
            self.0.final_exp.clone(),
            self.0.term.clone(),
            self.0.internal,
            children,
            DebugExpKind::Plain,
        )
    }
    pub fn find_by_id(&self, id: i32, visited: &mut HashSet<DebugExp>) -> Option<DebugExp> {
        if !visited.insert(self.clone()) {
            return None;
        }
        if self.id() == id {
            return Some(self.clone());
        }
        self.children()
            .iter()
            .find_map(|c| c.find_by_id(id, visited))
    }
    pub fn all_terms(
        &self,
        factory: &TermFactory,
        visited: &mut HashSet<DebugExp>,
    ) -> Result<Vec<Term>, UnsupportedTriggerTransform> {
        if !visited.insert(self.clone()) {
            return Ok(vec![]);
        }
        let mut children = Vec::new();
        for child in self.children() {
            children.extend(child.all_terms(factory, visited)?);
        }
        match self.kind() {
            DebugExpKind::Plain => {
                let mut out = self.term().cloned().into_iter().collect::<Vec<_>>();
                out.extend(children);
                Ok(out)
            }
            DebugExpKind::Implication => Ok(vec![
                factory.implies(
                    self.term()
                        .expect("implication debug expression requires a term")
                        .clone(),
                    factory.and(children),
                ),
            ]),
            DebugExpKind::Quantified {
                quantifier,
                term_qvars,
                term_triggers,
                ..
            } => {
                let q = if quantifier == "QA" {
                    Quantifier::Forall
                } else {
                    Quantifier::Exists
                };
                Ok(vec![factory.quantification(
                    q,
                    term_qvars.clone(),
                    factory.and(children),
                    term_triggers.clone(),
                    TermFactory::quantification_default_name(),
                    false,
                    None,
                )?])
            }
        }
    }
}
impl DebugExp {
    /// Render using source-compatible Silver and Silicon printers supplied by the caller.
    pub fn render<E>(
        &self,
        config: &DebugExpPrintConfiguration,
        render_exp: &impl Fn(&Exp) -> Result<String, E>,
        render_term: &impl Fn(&Term) -> Result<String, E>,
    ) -> Result<String, E> {
        self.render_at(0, config.hierarchy_level, config, render_exp, render_term)
    }
    fn render_at<E>(
        &self,
        depth: i32,
        max_depth: i32,
        config: &DebugExpPrintConfiguration,
        render_exp: &impl Fn(&Exp) -> Result<String, E>,
        render_term: &impl Fn(&Term) -> Result<String, E>,
    ) -> Result<String, E> {
        if self.is_internal() && !config.print_internal {
            return Ok(String::new());
        }
        let max_depth = max_depth.max(*config.per_id_levels.get(&self.id()).unwrap_or(&0));
        let top = || -> Result<String, E> {
            let display = if config.print_internal_terms {
                self.term().map(render_term).transpose()?
            } else {
                self.final_exp().map(render_exp).transpose()?
            };
            let delimiter = if display.is_some() && self.description().is_some() {
                ": "
            } else {
                ""
            };
            Ok(format!(
                "\n\t{}[{}] {}{}{}",
                "\t".repeat(depth.max(0) as usize),
                self.id(),
                self.description().unwrap_or(""),
                delimiter,
                display.unwrap_or_default()
            ))
        };
        let children = || -> Result<String, E> {
            let visible: Vec<_> = self
                .children()
                .iter()
                .filter(|c| config.print_internal || !c.is_internal())
                .collect();
            if visible.is_empty() {
                return Ok(String::new());
            }
            if max_depth <= depth {
                return Ok("[...]".into());
            }
            let shown = if config.children_to_show > 0 {
                visible.len().min(config.children_to_show as usize)
            } else {
                visible.len()
            };
            let mut out = String::new();
            for child in visible.iter().take(shown) {
                out.push_str(&child.render_at(
                    depth + 1,
                    max_depth,
                    config,
                    render_exp,
                    render_term,
                )?);
            }
            if shown < visible.len() {
                out.push_str(&format!(
                    "\n\t{}[...]",
                    "\t".repeat((depth + 1).max(0) as usize)
                ));
            }
            Ok(out)
        };
        match self.kind() {
            DebugExpKind::Plain => Ok(format!("{}{}", top()?, children()?)),
            DebugExpKind::Implication if self.children().is_empty() => Ok("true".into()),
            DebugExpKind::Implication => Ok(format!("{} ==> {}", top()?, children()?)),
            DebugExpKind::Quantified {
                quantifier, qvars, ..
            } if !qvars.is_empty() => {
                let vars = qvars
                    .iter()
                    .map(render_exp)
                    .collect::<Result<Vec<_>, _>>()?
                    .join(", ");
                Ok(format!(
                    "\n\t{}[{}] {} {} :: {}",
                    "\t".repeat(depth.max(0) as usize),
                    self.id(),
                    if quantifier == "QA" {
                        "forall"
                    } else {
                        "exists"
                    },
                    vars,
                    children()?
                ))
            }
            DebugExpKind::Quantified { .. } => top(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DebugExpPrintConfiguration {
    pub print_internal: bool,
    pub children_to_show: i32,
    pub hierarchy_level: i32,
    pub per_id_levels: HashMap<i32, i32>,
    pub print_axioms: bool,
    pub print_internal_terms: bool,
    pub print_old_heaps: bool,
}
impl Default for DebugExpPrintConfiguration {
    fn default() -> Self {
        Self {
            print_internal: false,
            children_to_show: 5,
            hierarchy_level: 2,
            per_id_levels: HashMap::new(),
            print_axioms: false,
            print_internal_terms: false,
            print_old_heaps: false,
        }
    }
}
impl DebugExpPrintConfiguration {
    pub fn set_hierarchy_level(&mut self, level: &str) {
        match level {
            "full" => self.hierarchy_level = 100,
            "top" => self.hierarchy_level = 0,
            _ => {
                if let Ok(n) = level.parse() {
                    self.hierarchy_level = n
                }
            }
        }
    }
    /// Returns false for the source's "invalid input" cases; malformed individual IDs are ignored.
    pub fn add_hierarchy_levels(&mut self, input: &str) -> bool {
        let mut parts = input.split("->");
        let Some(ids) = parts.next() else {
            return false;
        };
        let Some(level) = parts.next().and_then(|s| s.trim().parse::<i32>().ok()) else {
            return false;
        };
        for id in ids.split(',').filter_map(|s| s.trim().parse::<i32>().ok()) {
            self.per_id_levels.insert(id, level);
        }
        true
    }
}
#[derive(Clone, Debug)]
pub struct DebugAxiom {
    pub description: String,
    pub terms: InsertionOrderedSet<Term>,
}
