//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/sif/SIFExtendedTransformer.scala
//!
//! Purpose:
//! Translate relational SIF programs into a two-execution product program.
//!
//! Planned Rust structure:
//! Port Config, NameTransformer, transform, relational-predicate dependency closure and
//! field/domain/function/predicate/method translation; TranslationContext and
//! MethodControlFlowVars; expression/assertion, statement, loop, try/catch, lowness and helper
//! groups.
//!
//! Behavior to preserve:
//! Clear primedNames, used names, fields and predicates per transform, then rebuild relational
//! predicate closure in both dependency directions. Other singleton state, including
//! primedNamesPerMethod, configured replacements and domainFuncsToDuplicate, is not cleared
//! there. Duplicate fields, heap-dependent functions and predicates, and report unsupported
//! relational domain/function assertions. Preserve options for control-flow and sequential
//! optimization, restriction of active variables, selective methods, all-low functions,
//! experimental rel/goto, Nagini adaptations, timing and callbacks. Duplicate method
//! inputs/outputs, translate pre/postconditions and termination channels, and preserve
//! active-execution flags. Translate assignments, calls, allocation, branches, assertions,
//! inhale/exhale, fold/unfold, refute and control-flow extensions in source order; loops retain
//! bypass, idle, target-preservation and reconstruction logic, and try/finally saves and restores
//! control flags. Translate relational low/event/exit, quantifiers, dynamic checks and predicate
//! low functions with original versus primed expressions and backtransformed errors. Preserve
//! unsupported-feature reports and source-specific naming/triggers.
//!
//! Integration:
//! plugin::sif::{sif_ast_extensions,sif_error,sif_plugin},
//! plugin::standard::{predicateinstance,refute}, ast::utility::{simplifier,rewriter} and
//! verifier diagnostics.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for product-state independence, ordered collections, metadata and
//! explicit contexts; JVM singleton state replacement remains provisional.
//!
//! Open decisions:
//! Reconcile configuration lifetime and resets, source graph/set ordering, loop-reconstruction
//! assumptions and primed-name scope with SIF consumers and AST; do not silently repair upstream
//! TODOs.
//!
//! Status: partial; source configuration defaults, name generation and relational predicate
//! dependency closure are implemented. Product-program transformation remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2025 ETH Zurich.

use crate::ast::expression::{Exp, ExpKind};
use crate::ast::program::{Predicate, Program};
use crate::ast::utility::nodes::{Node, TraversalError, subnodes};
use std::collections::{HashMap, HashSet, VecDeque};

/// Source switches for product-program construction. Other configuration
/// hooks and actual transformation passes remain separate.
#[derive(Clone, Debug)]
pub struct SifConfig {
    pub optimize_control_flow: bool,
    pub optimize_sequential: bool,
    pub optimize_restrict_active_vars: bool,
    pub only_transform_relational_methods: bool,
    pub generate_all_low_functions: bool,
    pub enable_experimental_features: bool,
    pub enable_goto_low_event_encoding: bool,
    pub enable_nagini_features: bool,
}
impl Default for SifConfig {
    fn default() -> Self {
        Self {
            optimize_control_flow: true,
            optimize_sequential: true,
            optimize_restrict_active_vars: true,
            only_transform_relational_methods: false,
            generate_all_low_functions: false,
            enable_experimental_features: false,
            enable_goto_low_event_encoding: false,
            enable_nagini_features: false,
        }
    }
}
#[derive(Clone, Debug, Default)]
pub struct NameTransformer {
    used: HashSet<String>,
}
impl NameTransformer {
    pub fn mark_used(&mut self, names: impl IntoIterator<Item = String>) {
        self.used.extend(names);
    }
    pub fn clear_used_names(&mut self) {
        self.used.clear();
    }
    pub fn get_unused_name(&mut self, name: &str) -> String {
        if self.used.insert(name.to_owned()) {
            return name.to_owned();
        }
        let mut index = 0i32;
        loop {
            let candidate = format!("{name}_{index}");
            if self.used.insert(candidate.clone()) {
                return candidate;
            }
            index = index.wrapping_add(1);
        }
    }
    pub fn primed_field_name(name: &str) -> String {
        format!("{name}$_p")
    }
    pub fn predicate_low_name(name: &str) -> String {
        format!("{name}$_low")
    }
    pub fn is_predicate_low_name(name: &str) -> bool {
        name.ends_with("$_low")
    }
    pub fn predicate_all_low_name(name: &str) -> String {
        format!("{name}$_all_low")
    }
    pub fn is_predicate_all_low_name(name: &str) -> bool {
        name.ends_with("$_all_low")
    }
    pub fn has_predicate_low(predicate: &Predicate, relational: &HashSet<String>) -> bool {
        predicate.body.is_some() && relational.contains(&predicate.name)
    }
    pub fn has_predicate_all_low(predicate: &Predicate, config: &SifConfig) -> bool {
        predicate.body.is_some() && config.generate_all_low_functions
    }
}
/// Source direct relationality checks low, lowEvent, rel and optional Nagini
/// domain operators, independently of predicate dependencies.
pub fn is_directly_unary(expression: &Exp, config: &SifConfig) -> Result<bool, TraversalError> {
    use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
    fn visit(node: &Node, config: &SifConfig) -> Result<bool, TraversalError> {
        if let Node::Exp(exp) = node {
            match exp.kind() {
                ExpKind::Extension(extension)
                    if matches!(
                        extension.0.as_any().downcast_ref::<SifExpression>(),
                        Some(SifExpression {
                            kind: SifExpressionKind::Low { .. }
                                | SifExpressionKind::LowEvent
                                | SifExpressionKind::Rel { .. },
                            ..
                        })
                    ) =>
                {
                    return Ok(false);
                }
                ExpKind::DomainFuncApp(name, args, _)
                    if config.enable_nagini_features
                        && (name == "Low" || (name == "LowEvent" && args.is_empty())) =>
                {
                    return Ok(false);
                }
                _ => {}
            }
        }
        for child in subnodes(node)? {
            if !visit(&child, config)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    visit(&Node::Exp(expression.clone()), config)
}
/// Source unary classification additionally checks referenced relational predicates.
pub fn is_unary(
    expression: &Exp,
    config: &SifConfig,
    program: &Program,
    relational: &HashSet<String>,
) -> Result<bool, RelationalPredicateError> {
    if !is_directly_unary(expression, config).map_err(RelationalPredicateError::Traversal)? {
        return Ok(false);
    }
    fn visit(
        node: &Node,
        program: &Program,
        relational: &HashSet<String>,
    ) -> Result<bool, RelationalPredicateError> {
        let name = match node {
            Node::PredicateAccess(p) => Some(&p.predicate_name),
            Node::Exp(e) => match e.kind() {
                ExpKind::PredicateAccess(p) => Some(&p.predicate_name),
                _ => None,
            },
            _ => None,
        };
        if let Some(name) = name {
            if !program.predicates.iter().any(|p| p.name == *name) {
                return Err(RelationalPredicateError::MissingPredicate(name.clone()));
            }
            if relational.contains(name) {
                return Ok(false);
            }
        }
        for child in subnodes(node).map_err(RelationalPredicateError::Traversal)? {
            if !visit(&child, program, relational)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
    visit(&Node::Exp(expression.clone()), program, relational)
}

#[derive(Debug)]
pub enum RelationalPredicateError {
    Traversal(TraversalError),
    MissingPredicate(String),
}
/// Compute the closure of directly relational predicates under both directions
/// of predicate-body access dependencies. `is_directly_unary` must implement the
/// transformer's full relational-expression analysis.
pub fn collect_relational_predicates(
    program: &Program,
    mut is_directly_unary: impl FnMut(&Exp) -> Result<bool, RelationalPredicateError>,
) -> Result<HashSet<String>, RelationalPredicateError> {
    fn collect(node: &Node, names: &mut Vec<String>) -> Result<(), RelationalPredicateError> {
        if let Node::Exp(exp) = node {
            if let ExpKind::PredicateAccessPredicate(p) = exp.kind() {
                names.push(p.location.predicate_name.clone());
            }
        }
        for child in subnodes(node).map_err(RelationalPredicateError::Traversal)? {
            collect(&child, names)?;
        }
        Ok(())
    }
    let mut relational = HashSet::new();
    let mut dependencies: HashMap<String, HashSet<String>> = HashMap::new();
    let mut reverse: HashMap<String, HashSet<String>> = HashMap::new();
    for predicate in &program.predicates {
        if let Some(body) = &predicate.body {
            if !is_directly_unary(body)? {
                relational.insert(predicate.name.clone());
            }
            let mut names = Vec::new();
            collect(&Node::Exp(body.clone()), &mut names)?;
            for name in names {
                dependencies
                    .entry(name.clone())
                    .or_default()
                    .insert(predicate.name.clone());
                reverse
                    .entry(predicate.name.clone())
                    .or_default()
                    .insert(name);
            }
        }
    }
    let mut queue: VecDeque<_> = relational.iter().cloned().collect();
    while let Some(name) = queue.pop_front() {
        for next in dependencies
            .get(&name)
            .into_iter()
            .flatten()
            .chain(reverse.get(&name).into_iter().flatten())
        {
            if relational.insert(next.clone()) {
                if !program.predicates.iter().any(|p| p.name == *next) {
                    return Err(RelationalPredicateError::MissingPredicate(next.clone()));
                }
                queue.push_back(next.clone());
            }
        }
    }
    Ok(relational)
}

/// Source convenience entry point using its concrete direct-unary classifier.
pub fn source_relational_predicates(
    program: &Program,
    config: &SifConfig,
) -> Result<HashSet<String>, RelationalPredicateError> {
    collect_relational_predicates(program, |exp| {
        is_directly_unary(exp, config).map_err(RelationalPredicateError::Traversal)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn relational_predicate_closure_includes_callers_and_callees() {
        use super::super::sif_ast_extensions::{SifExpression, SifExpressionKind};
        use crate::ast::{
            ast::Metadata,
            expression::{ExpKind, PredicateAccess},
            program::{Predicate, PredicateData, Program},
            statement::PredicateAccessPredicate,
        };
        let meta = Metadata::default();
        let low = SifExpression {
            kind: SifExpressionKind::Low {
                exp: Exp::new(ExpKind::TrueLit, meta.clone()),
                comparator: None,
                type_variables: Default::default(),
            },
            meta: meta.clone(),
        }
        .expression()
        .unwrap();
        let access = PredicateAccess::new(vec![], "p".into(), meta.clone());
        let call = Exp::new(
            ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                access,
                None,
                meta.clone(),
            )),
            meta.clone(),
        );
        let predicate = |name: &str, body| {
            Predicate::new(PredicateData {
                name: name.into(),
                formal_args: vec![],
                body: Some(body),
                meta: meta.clone(),
            })
        };
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![predicate("p", low), predicate("q", call)],
            vec![],
            vec![],
            meta,
        );
        let found = source_relational_predicates(&program, &SifConfig::default()).unwrap();
        assert_eq!(found, HashSet::from(["p".to_owned(), "q".to_owned()]));
    }
    #[test]
    fn fresh_names_use_source_suffix_sequence() {
        let mut names = NameTransformer::default();
        names.mark_used(vec!["x".into(), "x_0".into()]);
        assert_eq!(names.get_unused_name("x"), "x_1");
        assert_eq!(names.get_unused_name("x"), "x_2");
        assert_eq!(NameTransformer::primed_field_name("f"), "f$_p");
        assert!(NameTransformer::is_predicate_all_low_name("p$_all_low"));
    }
}
