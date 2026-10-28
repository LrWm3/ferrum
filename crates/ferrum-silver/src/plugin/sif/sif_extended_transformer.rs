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
//! dependency closure and pure-method product construction with local assignments and pure
//! inhale/exhale, conditionals, calls, fields, allocation and heap-independent functions are
//! implemented, including heap-dependent functions and relational predicate low functions,
//! direct assertions, selected implications and fold/unfold checks. Unsupported relational
//! contexts and unconnected control transfers fail explicitly. Optimized loops,
//! return control/reconstruction and AST termination-channel checks are connected.

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
        assert!(matches!(
            predicate_unary_body(program.predicates[0].body.as_ref().unwrap(), &program)
                .unwrap()
                .kind(),
            ExpKind::TrueLit
        ));
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

    #[test]
    fn declassification_inhales_equality_only_when_both_executions_active() {
        use super::super::sif_ast_extensions::{SifStatement, SifStatementKind};
        use crate::ast::{
            ast::Metadata,
            expression::LocalVar,
            statement::{Stmt, StmtKind},
            r#type::Type,
        };
        let meta = Metadata::default();
        let variable = |name: &str, typ| {
            Exp::new(
                ExpKind::LocalVar(LocalVar::new(name.into(), typ, meta.clone())),
                meta.clone(),
            )
        };
        let first = variable("p1", Type::Bool);
        let second = variable("p2", Type::Bool);
        let x = variable("x", Type::Int);
        let declassify = SifStatement {
            kind: SifStatementKind::Declassify(x),
            meta: meta.clone(),
        }
        .statement()
        .unwrap();
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![declassify],
                declarations: vec![],
            },
            meta,
        );
        let product = sif_assertion_block(
            &body,
            &first,
            &second,
            &mut HashMap::from([("x".into(), "x_0".into())]),
            &HashMap::new(),
            &HashSet::new(),
            None,
            &mut NameTransformer::default(),
        )
        .unwrap();
        let StmtKind::Seqn { statements, .. } = product.kind() else {
            panic!("expected block")
        };
        let StmtKind::Inhale(exp) = statements[0].kind() else {
            panic!("expected inhale")
        };
        let ExpKind::Implies(active, equality) = exp.kind() else {
            panic!("expected guarded equality")
        };
        assert!(matches!(active.kind(), ExpKind::And(a, b) if a == &first && b == &second));
        assert!(
            matches!(equality.kind(), ExpKind::EqCmp(a, b) if matches!(a.kind(), ExpKind::LocalVar(v) if v.name == "x") && matches!(b.kind(), ExpKind::LocalVar(v) if v.name == "x_0"))
        );
    }

    #[test]
    fn false_inhale_is_guarded_in_optimized_sequence() {
        use crate::ast::{
            ast::Metadata,
            statement::{Stmt, StmtKind},
        };
        let meta = Metadata::default();
        let original = Stmt::new(
            StmtKind::Inhale(Exp::new(ExpKind::FalseLit, meta.clone())),
            meta.clone(),
        );
        let block = Stmt::new(
            StmtKind::Seqn {
                statements: vec![original.clone()],
                declarations: vec![],
            },
            meta.clone(),
        );
        let inactive = Exp::new(ExpKind::FalseLit, meta);
        let product = sif_assertion_block(
            &block,
            &inactive,
            &inactive,
            &mut HashMap::new(),
            &HashMap::new(),
            &HashSet::new(),
            None,
            &mut NameTransformer::default(),
        )
        .unwrap();
        let StmtKind::Seqn { statements, .. } = product.kind() else {
            panic!("outer block")
        };
        let StmtKind::Seqn {
            statements: group, ..
        } = statements[0].kind()
        else {
            panic!("optimized group")
        };
        assert!(
            matches!(group[0].kind(), StmtKind::If { condition, .. } if condition == &inactive)
        );
        assert!(
            matches!(group[1].kind(), StmtKind::If { condition, .. } if condition == &inactive)
        );
    }

    #[test]
    fn relational_predicate_helper_uses_both_predicates_and_primed_arguments() {
        use super::super::sif_ast_extensions::{SifExpression, SifExpressionKind};
        use crate::ast::{
            ast::Metadata,
            expression::ExpKind,
            program::{LocalVarDecl, PredicateData},
            r#type::Type,
        };
        let meta = Metadata::default();
        let x = LocalVarDecl::new("x".into(), Type::Int, meta.clone());
        let value = Exp::new(ExpKind::LocalVar(x.local_var()), meta.clone());
        let low = SifExpression {
            kind: SifExpressionKind::Low {
                exp: value,
                comparator: None,
                type_variables: Default::default(),
            },
            meta: meta.clone(),
        }
        .expression()
        .unwrap();
        let pred = Predicate::new(PredicateData {
            name: "P".into(),
            formal_args: vec![x],
            body: Some(low),
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![pred.clone()],
            vec![],
            vec![],
            meta,
        );
        let mut generator = NameTransformer::default();
        generator.mark_used(["x".to_owned(), "P".to_owned()]);
        let helper = predicate_low_function(
            &pred,
            &HashMap::from([("P".into(), "P_0".into())]),
            &HashMap::new(),
            &program,
            &mut generator,
        )
        .unwrap();
        assert_eq!(helper.name, "P$_low");
        assert_eq!(
            helper
                .formal_args
                .iter()
                .map(|a| a.name.as_str())
                .collect::<Vec<_>>(),
            ["x", "x_0"]
        );
        assert_eq!(helper.pres.len(), 2);
        assert!(has_low_predicate(&helper.pres[0], &HashSet::from(["P".to_owned()])).unwrap());
        let projected = predicate_low_only(
            &helper.pres[0],
            &HashSet::from(["P".to_owned()]),
            &HashMap::from([("P".into(), "P_0".into()), ("x".into(), "x_0".into())]),
            &HashMap::new(),
        )
        .unwrap();
        assert!(matches!(projected.kind(), ExpKind::FuncApp(name, _) if name == "P$_low"));
        let ExpKind::Unfolding(_, nested) = helper.body.as_ref().unwrap().kind() else {
            panic!("outer unfolding")
        };
        let ExpKind::Unfolding(_, equality) = nested.kind() else {
            panic!("inner unfolding")
        };
        assert!(
            matches!(equality.kind(), ExpKind::EqCmp(a, b) if matches!(a.kind(), ExpKind::LocalVar(v) if v.name == "x") && matches!(b.kind(), ExpKind::LocalVar(v) if v.name == "x_0"))
        );
        let active = Exp::new(ExpKind::TrueLit, Metadata::default());
        let assertion = predicate_low_assertion(
            &helper.pres[0],
            &active,
            &active,
            &HashMap::from([("P".into(), "P_0".into()), ("x".into(), "x_0".into())]),
            &HashMap::new(),
        )
        .unwrap();
        let ExpKind::And(_, low_part) = assertion.kind() else {
            panic!("predicate assertion")
        };
        let ExpKind::Implies(_, call) = low_part.kind() else {
            panic!("low guard")
        };
        assert!(
            matches!(call.kind(), ExpKind::FuncApp(name, args) if name == "P$_low" && args.len() == 2 && matches!(args[1].kind(), ExpKind::LocalVar(v) if v.name == "x_0"))
        );
    }

    #[test]
    fn low_check_assertion_maps_to_original_fold_error() {
        use crate::ast::{
            ast::{ErrorTransformation, Metadata},
            expression::PredicateAccess,
            statement::{PredicateAccessPredicate, Stmt, StmtKind},
        };
        use crate::verifier::{
            verification_error::{
                ErrorReason, NativeErrorNodeRenderer, RenderedVerificationError, VerificationError,
                VerificationErrorKind,
            },
            verification_result::VerificationDiagnostic,
        };
        use std::sync::Arc;
        let meta = Metadata::default();
        let access = PredicateAccessPredicate::new(
            PredicateAccess::new(vec![], "P".into(), meta.clone()),
            None,
            meta.clone(),
        );
        let fold = Stmt::new(StmtKind::Fold(access), meta.clone());
        let assertion = Stmt::new(
            StmtKind::Assert(Exp::new(ExpKind::FalseLit, meta)),
            Default::default(),
        );
        let original: Arc<dyn VerificationDiagnostic> = Arc::new(
            RenderedVerificationError::new(
                VerificationError::new(
                    VerificationErrorKind::AssertFailed(assertion),
                    ErrorReason::Dummy,
                ),
                Arc::new(NativeErrorNodeRenderer),
            )
            .unwrap(),
        );
        let mapped = PredicateLowCheckTrafo {
            statement: fold.clone(),
        }
        .transform_error(&original)
        .unwrap()
        .unwrap();
        let mapped = mapped
            .as_any()
            .downcast_ref::<RenderedVerificationError>()
            .unwrap();
        assert!(
            matches!(&mapped.error().kind, VerificationErrorKind::FoldFailed(stmt) if stmt.same_node(&fold))
        );
        assert_eq!(mapped.error().reason.id(), "sif.fold");
    }

    #[test]
    fn loop_exhale_guard_does_not_rewrite_replaced_nested_nodes() {
        use crate::ast::ast::Metadata;
        let meta = Metadata::default();
        let t = Exp::new(ExpKind::TrueLit, meta.clone());
        let f = Exp::new(ExpKind::FalseLit, meta.clone());
        let inner = Exp::new(ExpKind::InhaleExhaleExp(t.clone(), f.clone()), meta.clone());
        let outer = Exp::new(ExpKind::InhaleExhaleExp(inner.clone(), t.clone()), meta);
        let guarded = guard_loop_exhales(&outer, &f).unwrap();
        let ExpKind::InhaleExhaleExp(first, second) = guarded.kind() else {
            panic!("outer")
        };
        assert!(first.same_node(&inner));
        assert!(matches!(second.kind(), ExpKind::Implies(_, value) if value.same_node(&t)));
    }

    #[test]
    fn termination_channel_builds_checks_and_old_postcondition() {
        use super::super::{
            sif_ast_extensions::{SifExpression, SifExpressionKind},
            sif_plugin::SifTransformer,
        };
        use crate::ast::{
            ast::Metadata,
            expression::ExpKind,
            program::{LocalVarDecl, Method, MethodData},
            r#type::Type,
        };
        let meta = Metadata::default();
        let flag = LocalVarDecl::new("flag".into(), Type::Bool, meta.clone());
        let condition = Exp::new(ExpKind::LocalVar(flag.local_var()), meta.clone());
        let termination = SifExpression {
            kind: SifExpressionKind::Terminates { condition },
            meta: meta.clone(),
        }
        .expression()
        .unwrap();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![flag],
            formal_returns: vec![],
            pres: vec![termination],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let input = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let output = NativeSifTransformer.transform(input, false).unwrap();
        assert_eq!(output.methods[0].pres.len(), 2);
        assert_eq!(output.methods[0].posts.len(), 1);
        assert!(matches!(output.methods[0].posts[0].kind(), ExpKind::Old(_)));
        assert!(
            !output.methods[0].pres[0]
                .metadata()
                .error_trafo
                .error
                .is_empty()
        );
        assert!(
            !output.methods[0].pres[1]
                .metadata()
                .error_trafo
                .reason
                .is_empty()
        );
    }

    #[test]
    fn termination_channel_error_preserves_source_reason_family() {
        use super::super::{
            sif_ast_extensions::{SifExpression, SifExpressionKind},
            sif_error::{SifError, SifTerminationReasonKind},
        };
        use crate::ast::{
            ast::{ErrorTransformation, Metadata},
            statement::{Stmt, StmtKind},
        };
        use crate::verifier::{
            verification_error::{
                ErrorReason, NativeErrorNodeRenderer, RenderedVerificationError, VerificationError,
                VerificationErrorKind,
            },
            verification_result::VerificationDiagnostic,
        };
        use std::sync::Arc;
        let meta = Metadata::default();
        let expression = SifExpression {
            kind: SifExpressionKind::Terminates {
                condition: Exp::new(ExpKind::TrueLit, meta.clone()),
            },
            meta: meta.clone(),
        }
        .expression()
        .unwrap();
        let assertion = Stmt::new(
            StmtKind::Assert(Exp::new(ExpKind::FalseLit, meta)),
            Default::default(),
        );
        let source: Arc<dyn VerificationDiagnostic> = Arc::new(
            RenderedVerificationError::new(
                VerificationError::new(
                    VerificationErrorKind::AssertFailed(assertion),
                    ErrorReason::Dummy,
                ),
                Arc::new(NativeErrorNodeRenderer),
            )
            .unwrap(),
        );
        let trafo = TerminationChannelTrafo {
            offending_node: Node::Exp(expression.clone()),
            expression,
            reason: SifTerminationReasonKind::ConditionNotLow,
        };
        let transformed = trafo.transform_error(&source).unwrap().unwrap();
        assert!(transformed.as_any().is::<SifError>());
        assert_eq!(
            transformed.full_id(),
            "termination_channel_check.failed:sif_termination.condition_not_low"
        );
        assert_eq!(
            trafo
                .transform_reason(&ErrorReason::Dummy)
                .unwrap()
                .unwrap()
                .id(),
            "sif_termination.condition_not_low"
        );
    }

    #[test]
    fn loop_termination_channel_builds_checks_and_condition_snapshot() {
        use super::super::{
            sif_ast_extensions::{SifExpression, SifExpressionKind},
            sif_plugin::SifTransformer,
        };
        use crate::ast::{
            ast::Metadata,
            program::{LocalVarDecl, Method, MethodData},
            statement::{Stmt, StmtKind},
            r#type::Type,
        };
        let meta = Metadata::default();
        let flag = LocalVarDecl::new("flag".into(), Type::Bool, meta.clone());
        let condition = Exp::new(ExpKind::LocalVar(flag.local_var()), meta.clone());
        let termination = SifExpression {
            kind: SifExpressionKind::Terminates { condition },
            meta: meta.clone(),
        }
        .expression()
        .unwrap();
        let empty = Stmt::new(
            StmtKind::Seqn {
                statements: vec![],
                declarations: vec![],
            },
            meta.clone(),
        );
        let loop_stmt = Stmt::new(
            StmtKind::While {
                condition: Exp::new(ExpKind::FalseLit, meta.clone()),
                invariants: vec![termination],
                body: empty,
            },
            meta.clone(),
        );
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![loop_stmt],
                declarations: vec![],
            },
            meta.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![flag],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: meta.clone(),
        });
        let input = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let output = NativeSifTransformer.transform(input, false).unwrap();
        fn contains_flag(node: &Node) -> bool {
            if matches!(node, Node::LocalVar(var) if var.name == "flag" || var.name == "flag_0") {
                return true;
            }
            if matches!(node, Node::Exp(exp) if matches!(exp.kind(), ExpKind::LocalVar(var) if var.name == "flag" || var.name == "flag_0"))
            {
                return true;
            }
            subnodes(node).unwrap().iter().any(contains_flag)
        }
        fn visit(node: &Node, checks: &mut usize, loops: &mut usize) {
            if let Node::Stmt(stmt) = node {
                match stmt.kind() {
                    StmtKind::Assert(_) => *checks += 1,
                    StmtKind::While { invariants, .. } => {
                        *loops += 1;
                        assert!(!invariants.is_empty());
                        assert!(
                            invariants
                                .iter()
                                .all(|e| !contains_flag(&Node::Exp(e.clone()))),
                            "tightness invariant must use the false loop guard, not the flag termination condition"
                        );
                    }
                    _ => {}
                }
            }
            for child in subnodes(node).unwrap() {
                visit(&child, checks, loops);
            }
        }
        let (mut checks, mut loops) = (0, 0);
        visit(&Node::Program(output), &mut checks, &mut loops);
        assert_eq!((checks, loops), (2, 1));
    }

    #[test]
    fn return_control_guards_subsequent_assertions() {
        use super::super::{
            sif_ast_extensions::{SifStatement, SifStatementKind},
            sif_plugin::SifTransformer,
        };
        use crate::ast::{
            ast::Metadata,
            program::{LocalVarDecl, Method, MethodData},
            statement::{Stmt, StmtKind},
            r#type::Type,
        };
        let meta = Metadata::default();
        let arg = LocalVarDecl::new("x".into(), Type::Int, meta.clone());
        let result = LocalVarDecl::new("r".into(), Type::Int, meta.clone());
        let ret = SifStatement {
            kind: SifStatementKind::Return {
                exp: Some(Exp::new(ExpKind::LocalVar(arg.local_var()), meta.clone())),
                result_var: Some(result.local_var()),
            },
            meta: meta.clone(),
        }
        .statement()
        .unwrap();
        let assertion = Stmt::new(
            StmtKind::Assert(Exp::new(ExpKind::FalseLit, meta.clone())),
            meta.clone(),
        );
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![ret, assertion],
                declarations: vec![],
            },
            meta.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![arg],
            formal_returns: vec![result],
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: meta.clone(),
        });
        let input = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let output = NativeSifTransformer.transform(input, false).unwrap();
        let StmtKind::Seqn {
            declarations,
            statements,
        } = output.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!("method body")
        };
        assert_eq!(declarations.len(), 2);
        assert!(
            matches!(statements[1].kind(), StmtKind::LocalVarAssign { lhs, .. } if lhs.name == "ret1")
        );
        assert!(
            matches!(statements[2].kind(), StmtKind::LocalVarAssign { lhs, .. } if lhs.name == "ret2")
        );
        let rendered = crate::ast::pretty::pretty_printer::pretty(
            75,
            &crate::ast::pretty::pretty_printer::show_program(&output).unwrap(),
        );
        assert!(
            rendered.contains("ret1 := true") && rendered.contains("ret2 := true"),
            "{rendered}"
        );
        assert!(
            rendered.contains("!ret1") && rendered.contains("!ret2"),
            "{rendered}"
        );
    }

    #[test]
    fn return_in_loop_builds_source_reconstruction() {
        use super::super::{
            sif_ast_extensions::{
                SifExpression, SifExpressionKind, SifStatement, SifStatementKind,
            },
            sif_plugin::SifTransformer,
        };
        use crate::ast::{
            ast::Metadata,
            program::{Method, MethodData},
            statement::{Stmt, StmtKind},
        };
        let meta = Metadata::default();
        let ret = SifStatement {
            kind: SifStatementKind::Return {
                exp: None,
                result_var: None,
            },
            meta: meta.clone(),
        }
        .statement()
        .unwrap();
        let empty = Stmt::new(
            StmtKind::Seqn {
                statements: vec![ret],
                declarations: vec![],
            },
            meta.clone(),
        );
        let event = SifExpression {
            kind: SifExpressionKind::LowEvent,
            meta: meta.clone(),
        }
        .expression()
        .unwrap();
        let termination = SifExpression {
            kind: SifExpressionKind::Terminates {
                condition: Exp::new(ExpKind::FalseLit, meta.clone()),
            },
            meta: meta.clone(),
        }
        .expression()
        .unwrap();
        let loop_stmt = Stmt::new(
            StmtKind::While {
                condition: Exp::new(ExpKind::FalseLit, meta.clone()),
                invariants: vec![event, termination],
                body: empty,
            },
            meta.clone(),
        );
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![loop_stmt],
                declarations: vec![],
            },
            meta.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: meta.clone(),
        });
        let input = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let output = NativeSifTransformer.transform(input, false).unwrap();
        let rendered = crate::ast::pretty::pretty_printer::pretty(
            75,
            &crate::ast::pretty::pretty_printer::show_program(&output).unwrap(),
        );
        assert!(
            rendered.contains("Loop Reconstruction")
                && rendered.contains("oldret1")
                && rendered.contains("oldret2"),
            "{rendered}"
        );
    }
}

/// Concrete source product construction for a pure method fragment. Every other
/// source product is rejected until its corresponding transformer is implemented.
#[derive(Default)]
pub struct NativeSifTransformer;

/// Convert a generated low-check assertion failure to the original fold or unfold error.
#[derive(Debug)]
pub struct PredicateLowCheckTrafo {
    pub statement: crate::ast::statement::Stmt,
}

/// Source error/reason transformations for SIF termination-channel checks.
#[derive(Debug)]
pub struct TerminationChannelTrafo {
    pub expression: Exp,
    pub offending_node: Node,
    pub reason: super::sif_error::SifTerminationReasonKind,
}
impl TerminationChannelTrafo {
    fn reason(
        &self,
    ) -> Result<
        crate::verifier::verification_error::ErrorReason,
        crate::verifier::verification_result::DiagnosticError,
    > {
        use crate::verifier::verification_error::{ErrorReason, ExtensionErrorReasonHandle};
        Ok(ErrorReason::Extension(ExtensionErrorReasonHandle(
            std::sync::Arc::new(super::sif_error::SifTerminationReason::new(
                self.reason,
                self.expression.clone(),
            )?),
        )))
    }
}
impl crate::ast::ast::ErrorTransformation for TerminationChannelTrafo {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn transform_error(
        &self,
        diagnostic: &std::sync::Arc<
            dyn crate::verifier::verification_result::VerificationDiagnostic,
        >,
    ) -> Result<
        Option<std::sync::Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        use crate::verifier::verification_error::RenderedVerificationError;
        use crate::verifier::verification_result::DiagnosticError;
        let renderer = if let Some(error) = diagnostic.as_any().downcast_ref::<RenderedVerificationError>() {
            error.renderer()
        } else if let Some(error) = diagnostic.as_any().downcast_ref::<super::sif_error::SifError>() {
            error.renderer.clone()
        } else if let Some(error) = diagnostic.as_any().downcast_ref::<crate::plugin::standard::termination::termination_errors::TerminationError>() {
            error.renderer.clone()
        } else if let Some(error) = diagnostic.as_any().downcast_ref::<crate::plugin::standard::predicateinstance::predicate_instance_errors::PredicateInstanceNoAccess>() {
            error.renderer.clone()
        } else if let Some(error) = diagnostic.as_any().downcast_ref::<crate::plugin::standard::refute::refute_errors::RefuteFailed>() {
            error.renderer.clone()
        } else {
            return Err(DiagnosticError::Unsupported("SIF termination diagnostic renderer"));
        };
        Ok(Some(std::sync::Arc::new(super::sif_error::SifError::new(
            super::sif_error::SifErrorKind::TerminationChannel,
            self.offending_node.clone(),
            self.reason()?,
            false,
            renderer,
        )?)))
    }
    fn transform_reason(
        &self,
        _reason: &crate::verifier::verification_error::ErrorReason,
    ) -> Result<
        Option<crate::verifier::verification_error::ErrorReason>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Ok(Some(self.reason()?))
    }
}
impl crate::ast::ast::ErrorTransformation for PredicateLowCheckTrafo {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn transform_error(
        &self,
        diagnostic: &std::sync::Arc<
            dyn crate::verifier::verification_result::VerificationDiagnostic,
        >,
    ) -> Result<
        Option<std::sync::Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        use super::sif_error::{SifReason, SifReasonKind};
        use crate::ast::statement::StmtKind;
        use crate::verifier::verification_error::{
            ErrorReason, ExtensionErrorReasonHandle, RenderedVerificationError, VerificationError,
            VerificationErrorKind,
        };
        let Some(original) = diagnostic
            .as_any()
            .downcast_ref::<RenderedVerificationError>()
        else {
            return Ok(None);
        };
        if !matches!(
            original.error().kind,
            VerificationErrorKind::AssertFailed(_)
        ) {
            return Ok(None);
        }
        let (kind, reason) = match self.statement.kind() {
            StmtKind::Fold(_) => (
                VerificationErrorKind::FoldFailed(self.statement.clone()),
                SifReasonKind::FoldNotLow,
            ),
            StmtKind::Unfold(_) => (
                VerificationErrorKind::UnfoldFailed(self.statement.clone()),
                SifReasonKind::UnfoldNotLow,
            ),
            _ => {
                return Err(
                    crate::verifier::verification_result::DiagnosticError::InvalidNode(
                        "SIF low check statement",
                    ),
                );
            }
        };
        let reason = ErrorReason::Extension(ExtensionErrorReasonHandle(std::sync::Arc::new(
            SifReason::new(reason, self.statement.clone())?,
        )));
        let replacement = RenderedVerificationError::new(
            VerificationError::new(kind, reason),
            original.renderer(),
        )?;
        Ok(Some(std::sync::Arc::new(replacement)))
    }
}

fn sif_supported_type(typ: &crate::ast::r#type::Type) -> bool {
    use crate::ast::r#type::Type;
    match typ {
        Type::Int | Type::Bool | Type::Ref | Type::Perm => true,
        Type::Seq(inner) | Type::Set(inner) | Type::Multiset(inner) => sif_supported_type(inner),
        Type::Map(pair) => sif_supported_type(&pair.0) && sif_supported_type(&pair.1),
        Type::Domain(domain) => domain.partial_type_vars.values().all(sif_supported_type),
        Type::Var(_) | Type::Backend(_) => true,
        _ => false,
    }
}

fn sif_forward_meta(node: Node, meta: &crate::ast::ast::Metadata) -> crate::ast::ast::Metadata {
    use crate::ast::ast::{ErrorTrafo, PreviousNode};
    let mut result = meta.clone();
    result.error_trafo = ErrorTrafo::trafos(
        meta.error_trafo.error.clone(),
        meta.error_trafo.reason.clone(),
        Some(std::sync::Arc::new(PreviousNode(node))),
    );
    result
}

/// Translate the relational contribution of a predicate body to the source low-function body.
/// Callers must construct both predicate instances and supply the source primed-name map.
pub fn predicate_low_body(
    expression: &Exp,
    names: &HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
    program: &Program,
) -> Result<Exp, String> {
    use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
    use crate::ast::{ast::Metadata, expression::ExpExtra, r#type::Type};
    let meta = expression.metadata().clone();
    let transformed = match expression.kind() {
        ExpKind::Extension(extension) => match extension.0.as_any().downcast_ref::<SifExpression>()
        {
            Some(SifExpression {
                kind:
                    SifExpressionKind::Low {
                        exp,
                        comparator: None,
                        ..
                    },
                ..
            }) => Exp::new(
                ExpKind::EqCmp(exp.clone(), sif_pure_expression(exp, true, names, fields)?),
                sif_forward_meta(Node::Exp(expression.clone()), &meta),
            ),
            Some(SifExpression {
                kind: SifExpressionKind::Low { .. },
                ..
            }) => return Err("SIF predicate low comparator is unsupported".into()),
            _ => Exp::new(ExpKind::TrueLit, Metadata::default()),
        },
        ExpKind::PredicateAccessPredicate(access) => {
            if program
                .find_predicate_optionally(&access.location.predicate_name)
                .is_none_or(|p| p.body.is_none())
            {
                return Err(format!(
                    "SIF low function requires predicate body: {}",
                    access.location.predicate_name
                ));
            }
            let mut arguments = access.location.args.clone();
            arguments.extend(
                access
                    .location
                    .args
                    .iter()
                    .map(|a| sif_pure_expression(a, true, names, fields))
                    .collect::<Result<Vec<_>, _>>()?,
            );
            let mut function_meta = meta.clone();
            function_meta.info = crate::ast::ast::Info::NoInfo;
            Exp::with_extra(
                ExpKind::FuncApp(
                    NameTransformer::predicate_low_name(&access.location.predicate_name),
                    arguments,
                ),
                function_meta,
                ExpExtra {
                    typ: Some(Type::Bool),
                    ..Default::default()
                },
            )
        }
        ExpKind::And(a, b) | ExpKind::Or(a, b) => {
            let left = predicate_low_body(a, names, fields, program)?;
            let right = predicate_low_body(b, names, fields, program)?;
            Exp::new(
                if matches!(expression.kind(), ExpKind::And(..)) {
                    ExpKind::And(left, right)
                } else {
                    ExpKind::Or(left, right)
                },
                meta,
            )
        }
        ExpKind::Implies(a, b) => {
            let condition = Exp::new(
                ExpKind::And(
                    sif_pure_expression(a, false, names, fields)?,
                    sif_pure_expression(a, true, names, fields)?,
                ),
                Metadata::default(),
            );
            Exp::new(
                ExpKind::Implies(condition, predicate_low_body(b, names, fields, program)?),
                meta,
            )
        }
        _ => Exp::new(ExpKind::TrueLit, Metadata::default()),
    };
    crate::ast::utility::simplifier::simplify(&transformed, false, &|e| {
        crate::ast::utility::expressions::is_known_well_defined(e, None)
    })
    .map_err(|e| format!("SIF predicate low simplification: {e:?}"))
}

/// Construct the source relational predicate helper, with original and primed predicate
/// preconditions and nested unfoldings. Call only for a relational predicate with a body.
pub fn predicate_low_function(
    predicate: &Predicate,
    names: &HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
    program: &Program,
    generator: &mut NameTransformer,
) -> Result<crate::ast::program::Function, String> {
    use crate::ast::{
        ast::Metadata,
        expression::PredicateAccess,
        program::{Function, FunctionData, LocalVarDecl},
        statement::PredicateAccessPredicate,
        r#type::Type,
    };
    let body = predicate
        .body
        .as_ref()
        .ok_or_else(|| "SIF predicate low function requires a body".to_owned())?;
    let prime_name = names
        .get(&predicate.name)
        .ok_or_else(|| "missing SIF primed predicate name".to_owned())?;
    let mut local_names = names.clone();
    let mut prime_params = Vec::new();
    for parameter in &predicate.formal_args {
        let name = generator.get_unused_name(&parameter.name);
        local_names.insert(parameter.name.clone(), name.clone());
        prime_params.push(LocalVarDecl::new(
            name,
            parameter.typ.clone(),
            parameter.meta.clone(),
        ));
    }
    let access = |params: &[LocalVarDecl], name: &str| {
        let args = params
            .iter()
            .map(|p| Exp::new(ExpKind::LocalVar(p.local_var()), p.meta.clone()))
            .collect();
        let loc = PredicateAccess::new(args, name.to_owned(), predicate.meta.clone());
        Exp::new(
            ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                loc,
                None,
                Metadata::default(),
            )),
            Metadata::default(),
        )
    };
    let first = access(&predicate.formal_args, &predicate.name);
    let second = access(&prime_params, prime_name);
    let translated = predicate_low_body(body, &local_names, fields, program)?;
    let translated = Exp::new(
        ExpKind::Unfolding(
            first.clone(),
            Exp::new(
                ExpKind::Unfolding(second.clone(), translated),
                Metadata::default(),
            ),
        ),
        Metadata::default(),
    );
    let mut args = predicate.formal_args.clone();
    args.extend(prime_params);
    Ok(Function::new(FunctionData {
        name: NameTransformer::predicate_low_name(&predicate.name),
        formal_args: args,
        typ: Type::Bool,
        pres: vec![first, second],
        posts: vec![],
        body: Some(translated),
        meta: predicate.meta.clone(),
    }))
}

/// Replace source low and lowEvent expressions by true, then simplify the unary predicate body.
pub fn predicate_unary_body(expression: &Exp, _program: &Program) -> Result<Exp, String> {
    use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
    use crate::ast::utility::rewriter::strategy::rewrite_expression_bottom_up;
    let rewritten = rewrite_expression_bottom_up(
        expression,
        &mut |node| {
            if let ExpKind::Extension(extension) = node.kind() {
                match extension.0.as_any().downcast_ref::<SifExpression>() {
                    Some(SifExpression {
                        kind: SifExpressionKind::Low { .. } | SifExpressionKind::LowEvent,
                        ..
                    }) => {
                        return Ok(Exp::new(
                            ExpKind::TrueLit,
                            crate::ast::ast::Metadata::default(),
                        ));
                    }
                    _ => return Err("unsupported SIF predicate extension".to_owned()),
                }
            }
            Ok(node.clone())
        },
        &|handle, _| Ok(handle.clone()),
    )
    .map_err(|e| format!("SIF unary predicate rewriting: {e:?}"))?;
    crate::ast::utility::simplifier::simplify(&rewritten, false, &|e| {
        crate::ast::utility::expressions::is_known_well_defined(e, None)
    })
    .map_err(|e| format!("SIF unary predicate simplification: {e:?}"))
}

/// Source assertion translation for a direct access to a relational predicate.
pub fn predicate_low_assertion(
    expression: &Exp,
    first: &Exp,
    second: &Exp,
    names: &HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
) -> Result<Exp, String> {
    use crate::ast::{ast::Metadata, expression::ExpExtra, r#type::Type};
    let ExpKind::PredicateAccessPredicate(access) = expression.kind() else {
        return Err("expected SIF predicate access assertion".into());
    };
    if expression.metadata().info.find(&|info| matches!(info, crate::ast::ast::Info::Extension(ext) if ext.as_any().is::<super::sif_ast_extensions::SifDynCheckInfo>())).is_some() {
        return Err("SIF dynamic predicate checks are unsupported".into());
    }
    let mut arguments = access.location.args.clone();
    arguments.extend(
        access
            .location
            .args
            .iter()
            .map(|a| sif_pure_expression(a, true, names, fields))
            .collect::<Result<Vec<_>, _>>()?,
    );
    let app = Exp::with_extra(
        ExpKind::FuncApp(
            NameTransformer::predicate_low_name(&access.location.predicate_name),
            arguments,
        ),
        expression.metadata().clone(),
        ExpExtra {
            typ: Some(Type::Bool),
            ..Default::default()
        },
    );
    let active = Exp::new(
        ExpKind::And(first.clone(), second.clone()),
        Metadata::default(),
    );
    let low = Exp::new(ExpKind::Implies(active, app), Metadata::default());
    let meta = sif_forward_meta(Node::Exp(expression.clone()), expression.metadata());
    let normal = sif_pure_expression(expression, false, names, fields)?;
    let prime = sif_pure_expression(expression, true, names, fields)?;
    let default = Exp::new(
        ExpKind::And(
            Exp::new(ExpKind::Implies(first.clone(), normal), meta.clone()),
            Exp::new(ExpKind::Implies(second.clone(), prime), meta.clone()),
        ),
        meta.clone(),
    );
    Ok(Exp::new(ExpKind::And(default, low), meta))
}

pub fn has_low_predicate(
    expression: &Exp,
    low_predicates: &HashSet<String>,
) -> Result<bool, String> {
    fn visit(node: &Node, names: &HashSet<String>) -> Result<bool, String> {
        if matches!(node, Node::PredicateAccess(access) if names.contains(&access.predicate_name)) {
            return Ok(true);
        }
        if matches!(node, Node::Exp(exp) if matches!(exp.kind(), ExpKind::PredicateAccess(access) if names.contains(&access.predicate_name)))
        {
            return Ok(true);
        }
        for child in subnodes(node).map_err(|e| format!("SIF predicate traversal: {e:?}"))? {
            if visit(&child, names)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    visit(&Node::Exp(expression.clone()), low_predicates)
}

/// Project the low-function contributions in an implication consequent.
pub fn predicate_low_only(
    expression: &Exp,
    low_predicates: &HashSet<String>,
    names: &HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
) -> Result<Exp, String> {
    use crate::ast::{ast::Metadata, expression::ExpExtra, r#type::Type};
    let transformed = match expression.kind() {
        ExpKind::PredicateAccessPredicate(access)
            if low_predicates.contains(&access.location.predicate_name) =>
        {
            let mut arguments = access.location.args.clone();
            arguments.extend(
                access
                    .location
                    .args
                    .iter()
                    .map(|a| sif_pure_expression(a, true, names, fields))
                    .collect::<Result<Vec<_>, _>>()?,
            );
            Exp::with_extra(
                ExpKind::FuncApp(
                    NameTransformer::predicate_low_name(&access.location.predicate_name),
                    arguments,
                ),
                expression.metadata().clone(),
                ExpExtra {
                    typ: Some(Type::Bool),
                    ..Default::default()
                },
            )
        }
        ExpKind::And(a, b) | ExpKind::Or(a, b) => {
            let left = predicate_low_only(a, low_predicates, names, fields)?;
            let right = predicate_low_only(b, low_predicates, names, fields)?;
            Exp::new(
                if matches!(expression.kind(), ExpKind::And(..)) {
                    ExpKind::And(left, right)
                } else {
                    ExpKind::Or(left, right)
                },
                expression.metadata().clone(),
            )
        }
        ExpKind::Implies(a, b) => {
            let condition = Exp::new(
                ExpKind::And(
                    sif_pure_expression(a, false, names, fields)?,
                    sif_pure_expression(a, true, names, fields)?,
                ),
                Metadata::default(),
            );
            Exp::new(
                ExpKind::Implies(
                    condition,
                    predicate_low_only(b, low_predicates, names, fields)?,
                ),
                expression.metadata().clone(),
            )
        }
        _ => Exp::new(ExpKind::TrueLit, Metadata::default()),
    };
    crate::ast::utility::simplifier::simplify(&transformed, false, &|e| {
        crate::ast::utility::expressions::is_known_well_defined(e, None)
    })
    .map_err(|e| format!("SIF low predicate projection: {e:?}"))
}

fn guard_loop_exhales(expression: &Exp, idle: &Exp) -> Result<Exp, String> {
    use crate::ast::ast::Metadata;
    rewrite_loop_preorder(expression, &|node| {
        if let ExpKind::InhaleExhaleExp(inhale, exhale) = node.kind() {
            let guard = Exp::new(ExpKind::Not(idle.clone()), Metadata::default());
            let guarded = Exp::new(ExpKind::Implies(guard, exhale.clone()), Metadata::default());
            Ok(Exp::new(
                ExpKind::InhaleExhaleExp(inhale.clone(), guarded),
                node.metadata().clone(),
            ))
        } else {
            Ok(node.clone())
        }
    })
}

fn rewrite_loop_preorder(
    expression: &Exp,
    rule: &dyn Fn(&Exp) -> Result<Exp, String>,
) -> Result<Exp, String> {
    use crate::ast::expression::{FieldAccess, PredicateAccess, Trigger};
    let rewritten = rule(expression)?;
    if !rewritten.same_node(expression) {
        return Ok(rewritten);
    }
    expression.map_expression_children(
        &mut |child| rewrite_loop_preorder(child, rule),
        &mut |extension| {
            let failure = std::cell::RefCell::new(None);
            let result = extension.0.map_expressions(&|child| {
                rewrite_loop_preorder(child, rule).map_err(|e| {
                    *failure.borrow_mut() = Some(e);
                    crate::verifier::verification_result::DiagnosticError::Unsupported(
                        "SIF loop expression rewrite",
                    )
                })
            });
            if let Some(error) = failure.into_inner() {
                return Err(error);
            }
            result.map_err(|_| "unsupported SIF loop extension".to_owned())
        },
        &mut |field| {
            let receiver = rewrite_loop_preorder(&field.receiver, rule)?;
            if receiver == field.receiver {
                Ok(field.clone())
            } else {
                Ok(FieldAccess::new(
                    receiver,
                    field.field.clone(),
                    field.meta.clone(),
                ))
            }
        },
        &mut |predicate| {
            let args = predicate
                .args
                .iter()
                .map(|e| rewrite_loop_preorder(e, rule))
                .collect::<Result<Vec<_>, _>>()?;
            if args == predicate.args {
                Ok(predicate.clone())
            } else {
                Ok(PredicateAccess::new(
                    args,
                    predicate.predicate_name.clone(),
                    predicate.meta.clone(),
                ))
            }
        },
        &mut |trigger| {
            let exps = trigger
                .exps
                .iter()
                .map(|e| rewrite_loop_preorder(e, rule))
                .collect::<Result<Vec<_>, _>>()?;
            if exps == trigger.exps {
                Ok(trigger.clone())
            } else {
                Ok(Trigger::new(exps, trigger.meta.clone()))
            }
        },
    )
}

fn sif_pure_expression(
    exp: &Exp,
    prime: bool,
    names: &HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
) -> Result<Exp, String> {
    use crate::ast::expression::LocalVar;
    let declaration = |d: &crate::ast::program::LocalVarDecl| {
        if prime {
            if let Some(name) = names.get(&d.name) {
                return crate::ast::program::LocalVarDecl::new(
                    name.clone(),
                    d.typ.clone(),
                    sif_forward_meta(Node::LocalDecl(d.clone()), &d.meta),
                );
            }
        }
        d.clone()
    };
    let meta = exp.metadata().clone();
    macro_rules! binary {
        ($ctor:ident, $a:expr, $b:expr) => {
            ExpKind::$ctor(
                sif_pure_expression($a, prime, names, fields)?,
                sif_pure_expression($b, prime, names, fields)?,
            )
        };
    }
    let kind = match exp.kind() {
        ExpKind::LocalVar(v) => {
            if !prime {
                return Ok(exp.clone());
            }
            let Some(name) = names.get(&v.name) else {
                return Ok(exp.clone());
            };
            let meta = sif_forward_meta(Node::LocalVar(v.clone()), &v.meta);
            ExpKind::LocalVar(LocalVar::new(name.clone(), v.typ.clone(), meta))
        }
        ExpKind::IntLit(_)
        | ExpKind::RefLit(_)
        | ExpKind::BackendValueLit(_, _)
        | ExpKind::LocalVarWithVersion(_, _)
        | ExpKind::TrueLit
        | ExpKind::FalseLit
        | ExpKind::NullLit
        | ExpKind::Result(_) => {
            return Ok(exp.clone());
        }
        ExpKind::FieldAccess(access) => {
            let receiver = sif_pure_expression(&access.receiver, prime, names, fields)?;
            let Some(primed_field) = fields.get(&access.field.name) else {
                return Err(format!("unmapped SIF field {}", access.field.name));
            };
            if !prime {
                return Ok(exp.clone());
            }
            let meta = sif_forward_meta(Node::FieldAccess(access.clone()), &access.meta);
            ExpKind::FieldAccess(crate::ast::expression::FieldAccess::new(
                receiver,
                primed_field.clone(),
                meta,
            ))
        }
        ExpKind::FieldAccessPredicate(access, permission) => {
            let view = Exp::new(ExpKind::FieldAccess(access.clone()), access.meta.clone());
            let translated = sif_pure_expression(&view, prime, names, fields)?;
            let ExpKind::FieldAccess(access) = translated.kind() else {
                return Err("invalid SIF field access".into());
            };
            let permission = permission
                .as_ref()
                .map(|p| sif_pure_expression(p, prime, names, fields))
                .transpose()?;
            ExpKind::FieldAccessPredicate(access.clone(), permission)
        }
        ExpKind::PredicateAccess(access) => {
            let arguments = access
                .args
                .iter()
                .map(|a| sif_pure_expression(a, prime, names, fields))
                .collect::<Result<Vec<_>, _>>()?;
            if !prime {
                return Ok(exp.clone());
            }
            let name = names
                .get(&access.predicate_name)
                .ok_or_else(|| format!("unmapped SIF predicate {}", access.predicate_name))?;
            ExpKind::PredicateAccess(crate::ast::expression::PredicateAccess::new(
                arguments,
                name.clone(),
                sif_forward_meta(Node::PredicateAccess(access.clone()), &access.meta),
            ))
        }
        ExpKind::PredicateAccessPredicate(access) => {
            let loc = Exp::new(
                ExpKind::PredicateAccess(access.location.clone()),
                access.location.meta.clone(),
            );
            let mapped = sif_pure_expression(&loc, prime, names, fields)?;
            let ExpKind::PredicateAccess(location) = mapped.kind() else {
                return Err("invalid SIF predicate access".into());
            };
            let permission = access
                .permission
                .as_ref()
                .map(|p| sif_pure_expression(p, prime, names, fields))
                .transpose()?;
            ExpKind::PredicateAccessPredicate(crate::ast::statement::PredicateAccessPredicate::new(
                location.clone(),
                permission,
                access.meta.clone(),
            ))
        }
        ExpKind::Unfolding(access, body) => binary!(Unfolding, access, body),
        ExpKind::CurrentPerm(resource) => {
            ExpKind::CurrentPerm(sif_pure_expression(resource, prime, names, fields)?)
        }
        ExpKind::FullPerm | ExpKind::NoPerm | ExpKind::WildcardPerm | ExpKind::EpsilonPerm => {
            return Ok(exp.clone());
        }
        ExpKind::FractionalPerm(a, b) => binary!(FractionalPerm, a, b),
        ExpKind::PermDiv(a, b) => binary!(PermDiv, a, b),
        ExpKind::PermPermDiv(a, b) => binary!(PermPermDiv, a, b),
        ExpKind::PermAdd(a, b) => binary!(PermAdd, a, b),
        ExpKind::PermSub(a, b) => binary!(PermSub, a, b),
        ExpKind::DebugPermMin(a, b) => binary!(DebugPermMin, a, b),
        ExpKind::PermMul(a, b) => binary!(PermMul, a, b),
        ExpKind::IntPermMul(a, b) => binary!(IntPermMul, a, b),
        ExpKind::PermLtCmp(a, b) => binary!(PermLtCmp, a, b),
        ExpKind::PermLeCmp(a, b) => binary!(PermLeCmp, a, b),
        ExpKind::PermGtCmp(a, b) => binary!(PermGtCmp, a, b),
        ExpKind::PermGeCmp(a, b) => binary!(PermGeCmp, a, b),
        ExpKind::PermMinus(a) => ExpKind::PermMinus(sif_pure_expression(a, prime, names, fields)?),
        ExpKind::FuncApp(name, arguments) => ExpKind::FuncApp(
            if prime {
                names.get(name).cloned().unwrap_or_else(|| name.clone())
            } else {
                name.clone()
            },
            arguments
                .iter()
                .map(|arg| sif_pure_expression(arg, prime, names, fields))
                .collect::<Result<_, _>>()?,
        ),
        ExpKind::DomainFuncApp(name, arguments, substitution) => ExpKind::DomainFuncApp(
            if prime {
                names.get(name).cloned().unwrap_or_else(|| name.clone())
            } else {
                name.clone()
            },
            arguments
                .iter()
                .map(|a| sif_pure_expression(a, prime, names, fields))
                .collect::<Result<Vec<_>, _>>()?,
            substitution.clone(),
        ),
        ExpKind::BackendFuncApp(name, arguments) => ExpKind::BackendFuncApp(
            name.clone(),
            arguments
                .iter()
                .map(|a| sif_pure_expression(a, prime, names, fields))
                .collect::<Result<Vec<_>, _>>()?,
        ),
        ExpKind::Add(a, b) => binary!(Add, a, b),
        ExpKind::Sub(a, b) => binary!(Sub, a, b),
        ExpKind::Mul(a, b) => binary!(Mul, a, b),
        ExpKind::Div(a, b) => binary!(Div, a, b),
        ExpKind::Mod(a, b) => binary!(Mod, a, b),
        ExpKind::LtCmp(a, b) => binary!(LtCmp, a, b),
        ExpKind::LeCmp(a, b) => binary!(LeCmp, a, b),
        ExpKind::GtCmp(a, b) => binary!(GtCmp, a, b),
        ExpKind::GeCmp(a, b) => binary!(GeCmp, a, b),
        ExpKind::EqCmp(a, b) => binary!(EqCmp, a, b),
        ExpKind::NeCmp(a, b) => binary!(NeCmp, a, b),
        ExpKind::Or(a, b) => binary!(Or, a, b),
        ExpKind::And(a, b) => binary!(And, a, b),
        ExpKind::Implies(a, b) => binary!(Implies, a, b),
        ExpKind::MagicWand(a, b) => binary!(MagicWand, a, b),
        ExpKind::Applying(a, b) => binary!(Applying, a, b),
        ExpKind::Asserting(a, b) => binary!(Asserting, a, b),
        ExpKind::InhaleExhaleExp(a, b) => binary!(InhaleExhaleExp, a, b),
        ExpKind::CondExp(condition, then_exp, else_exp) => ExpKind::CondExp(
            sif_pure_expression(condition, prime, names, fields)?,
            sif_pure_expression(then_exp, prime, names, fields)?,
            sif_pure_expression(else_exp, prime, names, fields)?,
        ),
        ExpKind::Old(inner) => ExpKind::Old(sif_pure_expression(inner, prime, names, fields)?),
        ExpKind::LabelledOld(inner, label) => ExpKind::LabelledOld(
            sif_pure_expression(inner, prime, names, fields)?,
            label.clone(),
        ),
        ExpKind::DebugLabelledOld(inner, label) => ExpKind::DebugLabelledOld(
            sif_pure_expression(inner, prime, names, fields)?,
            label.clone(),
        ),
        ExpKind::Let(var, value, body) => ExpKind::Let(
            declaration(var),
            sif_pure_expression(value, prime, names, fields)?,
            sif_pure_expression(body, prime, names, fields)?,
        ),
        ExpKind::Forall(vars, triggers, body) | ExpKind::Exists(vars, triggers, body) => {
            let vars = vars.iter().map(declaration).collect();
            let triggers = triggers
                .iter()
                .map(|t| {
                    Ok(crate::ast::expression::Trigger::new(
                        t.exps
                            .iter()
                            .map(|e| sif_pure_expression(e, prime, names, fields))
                            .collect::<Result<Vec<_>, _>>()?,
                        t.meta.clone(),
                    ))
                })
                .collect::<Result<Vec<_>, String>>()?;
            let body = sif_pure_expression(body, prime, names, fields)?;
            if matches!(exp.kind(), ExpKind::Forall(..)) {
                ExpKind::Forall(vars, triggers, body)
            } else {
                ExpKind::Exists(vars, triggers, body)
            }
        }
        ExpKind::ForPerm(vars, location, body) => {
            if !prime {
                sif_pure_expression(location, false, names, fields)?;
                sif_pure_expression(body, false, names, fields)?;
                return Ok(exp.clone());
            }
            let resource = match location.kind() {
                ExpKind::FieldAccess(access) => {
                    let field = fields.get(&access.field.name).unwrap_or(&access.field);
                    Exp::new(
                        ExpKind::FieldAccess(crate::ast::expression::FieldAccess::new(
                            access.receiver.clone(),
                            field.clone(),
                            access.meta.clone(),
                        )),
                        location.metadata().clone(),
                    )
                }
                ExpKind::PredicateAccess(access) => Exp::new(
                    ExpKind::PredicateAccess(crate::ast::expression::PredicateAccess::new(
                        access.args.clone(),
                        names
                            .get(&access.predicate_name)
                            .cloned()
                            .unwrap_or_else(|| access.predicate_name.clone()),
                        access.meta.clone(),
                    )),
                    location.metadata().clone(),
                ),
                _ => return Err("unsupported SIF forperm resource".into()),
            };
            return Ok(Exp::new(
                ExpKind::ForPerm(
                    vars.clone(),
                    resource,
                    sif_pure_expression(body, true, names, fields)?,
                ),
                sif_forward_meta(Node::Exp(exp.clone()), exp.metadata()),
            ));
        }
        ExpKind::Not(a) => ExpKind::Not(sif_pure_expression(a, prime, names, fields)?),
        ExpKind::Minus(a) => ExpKind::Minus(sif_pure_expression(a, prime, names, fields)?),
        ExpKind::EmptySeq(_)
        | ExpKind::EmptySet(_)
        | ExpKind::EmptyMultiset(_)
        | ExpKind::EmptyMap(_, _) => return Ok(exp.clone()),
        ExpKind::ExplicitSeq(es)
        | ExpKind::ExplicitSet(es)
        | ExpKind::ExplicitMultiset(es)
        | ExpKind::ExplicitMap(es) => {
            let children = es
                .iter()
                .map(|e| sif_pure_expression(e, prime, names, fields))
                .collect::<Result<Vec<_>, _>>()?;
            match exp.kind() {
                ExpKind::ExplicitSeq(_) => ExpKind::ExplicitSeq(children),
                ExpKind::ExplicitSet(_) => ExpKind::ExplicitSet(children),
                ExpKind::ExplicitMultiset(_) => ExpKind::ExplicitMultiset(children),
                ExpKind::ExplicitMap(_) => ExpKind::ExplicitMap(children),
                _ => unreachable!(),
            }
        }
        ExpKind::RangeSeq(a, b) => binary!(RangeSeq, a, b),
        ExpKind::SeqAppend(a, b) => binary!(SeqAppend, a, b),
        ExpKind::SeqIndex(a, b) => binary!(SeqIndex, a, b),
        ExpKind::SeqTake(a, b) => binary!(SeqTake, a, b),
        ExpKind::SeqDrop(a, b) => binary!(SeqDrop, a, b),
        ExpKind::SeqContains(a, b) => binary!(SeqContains, a, b),
        ExpKind::AnySetUnion(a, b) => binary!(AnySetUnion, a, b),
        ExpKind::AnySetIntersection(a, b) => binary!(AnySetIntersection, a, b),
        ExpKind::AnySetSubset(a, b) => binary!(AnySetSubset, a, b),
        ExpKind::AnySetMinus(a, b) => binary!(AnySetMinus, a, b),
        ExpKind::AnySetContains(a, b) => binary!(AnySetContains, a, b),
        ExpKind::Maplet(a, b) => binary!(Maplet, a, b),
        ExpKind::MapLookup(a, b) => binary!(MapLookup, a, b),
        ExpKind::MapContains(a, b) => binary!(MapContains, a, b),
        ExpKind::SeqUpdate(a, b, c) => ExpKind::SeqUpdate(
            sif_pure_expression(a, prime, names, fields)?,
            sif_pure_expression(b, prime, names, fields)?,
            sif_pure_expression(c, prime, names, fields)?,
        ),
        ExpKind::MapUpdate(a, b, c) => ExpKind::MapUpdate(
            sif_pure_expression(a, prime, names, fields)?,
            sif_pure_expression(b, prime, names, fields)?,
            sif_pure_expression(c, prime, names, fields)?,
        ),
        ExpKind::SeqLength(a) => ExpKind::SeqLength(sif_pure_expression(a, prime, names, fields)?),
        ExpKind::AnySetCardinality(a) => {
            ExpKind::AnySetCardinality(sif_pure_expression(a, prime, names, fields)?)
        }
        ExpKind::MapCardinality(a) => {
            ExpKind::MapCardinality(sif_pure_expression(a, prime, names, fields)?)
        }
        ExpKind::MapDomain(a) => ExpKind::MapDomain(sif_pure_expression(a, prime, names, fields)?),
        ExpKind::MapRange(a) => ExpKind::MapRange(sif_pure_expression(a, prime, names, fields)?),
        _ => return Err("SIF expression outside the supported pure product fragment".into()),
    };
    if !prime {
        return Ok(exp.clone());
    }
    let meta = if prime
        && matches!(exp.kind(), ExpKind::FuncApp(name, _) | ExpKind::DomainFuncApp(name, _, _) if names.contains_key(name))
    {
        sif_forward_meta(Node::Exp(exp.clone()), &meta)
    } else {
        meta
    };
    Ok(Exp::with_extra(kind, meta, exp.0.extra.clone()))
}

fn sif_assertion(
    exp: &Exp,
    first: &Exp,
    second: &Exp,
    names: &HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
    low_predicates: &HashSet<String>,
) -> Result<Exp, String> {
    sif_assertion_with_flags(exp, first, second, names, fields, low_predicates, None)
}

fn sif_assertion_with_flags(
    exp: &Exp,
    first: &Exp,
    second: &Exp,
    names: &HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
    low_predicates: &HashSet<String>,
    event_flags: Option<&(
        crate::ast::program::LocalVarDecl,
        crate::ast::program::LocalVarDecl,
    )>,
) -> Result<Exp, String> {
    use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
    use crate::ast::ast::Metadata;
    if exp.metadata().info.find(&|info| matches!(info, crate::ast::ast::Info::Extension(ext) if ext.as_any().is::<super::sif_ast_extensions::SifDynCheckInfo>())).is_some() {
        return Err("SIF dynamic checks are outside the supported product fragment".into());
    }
    let forwarded = || sif_forward_meta(Node::Exp(exp.clone()), exp.metadata());
    let make = |kind| Exp::new(kind, Metadata::default());
    match exp.kind() {
        ExpKind::And(left, right) => Ok(Exp::new(
            ExpKind::And(
                sif_assertion_with_flags(
                    left,
                    first,
                    second,
                    names,
                    fields,
                    low_predicates,
                    event_flags,
                )?,
                sif_assertion_with_flags(
                    right,
                    first,
                    second,
                    names,
                    fields,
                    low_predicates,
                    event_flags,
                )?,
            ),
            forwarded(),
        )),
        ExpKind::Forall(variables, triggers, body) if exp.is_pure() => {
            if variables.iter().any(|v| names.contains_key(&v.name)) {
                return Err("SIF quantified binder shadows a primed variable".into());
            }
            let mut all_triggers = triggers.clone();
            for trigger in triggers {
                let primed = trigger
                    .exps
                    .iter()
                    .map(|e| sif_pure_expression(e, true, names, fields))
                    .collect::<Result<Vec<_>, _>>()?;
                all_triggers.push(crate::ast::expression::Trigger::new(
                    primed,
                    Metadata::default(),
                ));
            }
            let quantified = Exp::new(
                ExpKind::Forall(
                    variables.clone(),
                    all_triggers,
                    sif_assertion_with_flags(
                        body,
                        first,
                        second,
                        names,
                        fields,
                        low_predicates,
                        event_flags,
                    )?,
                ),
                forwarded(),
            );
            crate::ast::utility::triggers::auto_trigger(&quantified)
                .map_err(|e| format!("SIF automatic trigger: {e:?}"))
        }
        ExpKind::Implies(left, right)
            if !is_directly_unary(exp, &SifConfig::default())
                .map_err(|e| format!("SIF expression traversal: {e:?}"))? =>
        {
            Ok(Exp::new(
                ExpKind::Implies(
                    sif_assertion_with_flags(
                        left,
                        first,
                        second,
                        names,
                        fields,
                        low_predicates,
                        event_flags,
                    )?,
                    sif_assertion_with_flags(
                        right,
                        first,
                        second,
                        names,
                        fields,
                        low_predicates,
                        event_flags,
                    )?,
                ),
                forwarded(),
            ))
        }
        ExpKind::Implies(left, right) if has_low_predicate(right, low_predicates)? => {
            let normal = sif_pure_expression(exp, false, names, fields)?;
            let prime = sif_pure_expression(exp, true, names, fields)?;
            let default = Exp::new(
                ExpKind::And(
                    Exp::new(ExpKind::Implies(first.clone(), normal), forwarded()),
                    Exp::new(ExpKind::Implies(second.clone(), prime), forwarded()),
                ),
                forwarded(),
            );
            let condition = sif_assertion_with_flags(
                left,
                first,
                second,
                names,
                fields,
                low_predicates,
                event_flags,
            )?;
            let low = predicate_low_only(right, low_predicates, names, fields)?;
            Ok(Exp::new(
                ExpKind::And(
                    default,
                    Exp::new(ExpKind::Implies(condition, low), Metadata::default()),
                ),
                exp.metadata().clone(),
            ))
        }
        ExpKind::PredicateAccessPredicate(access)
            if low_predicates.contains(&access.location.predicate_name) =>
        {
            predicate_low_assertion(exp, first, second, names, fields)
        }
        ExpKind::Old(inner) => Ok(Exp::new(
            ExpKind::Old(sif_assertion_with_flags(
                inner,
                first,
                second,
                names,
                fields,
                low_predicates,
                event_flags,
            )?),
            exp.metadata().clone(),
        )),
        ExpKind::Extension(extension) => {
            let Some(sif) = extension.0.as_any().downcast_ref::<SifExpression>() else {
                return Err("unsupported SIF assertion extension".into());
            };
            match &sif.kind {
                SifExpressionKind::Low {
                    exp: value,
                    comparator: None,
                    ..
                } => {
                    let normal = sif_pure_expression(value, false, names, fields)?;
                    let primed = sif_pure_expression(value, true, names, fields)?;
                    let equality = Exp::new(ExpKind::EqCmp(normal, primed), forwarded());
                    let both = make(ExpKind::And(first.clone(), second.clone()));
                    Ok(Exp::new(ExpKind::Implies(both, equality), forwarded()))
                }
                SifExpressionKind::LowEvent => {
                    let active = |p: &Exp, flag: &crate::ast::program::LocalVarDecl| {
                        Exp::new(
                            ExpKind::And(
                                p.clone(),
                                Exp::new(
                                    ExpKind::Not(Exp::new(
                                        ExpKind::LocalVar(flag.local_var()),
                                        Metadata::default(),
                                    )),
                                    Metadata::default(),
                                ),
                            ),
                            Metadata::default(),
                        )
                    };
                    let (left, right) = match event_flags {
                        Some((ret1, ret2)) => (active(first, ret1), active(second, ret2)),
                        None => (first.clone(), second.clone()),
                    };
                    Ok(Exp::new(ExpKind::EqCmp(left, right), forwarded()))
                }
                SifExpressionKind::Terminates { .. } => {
                    Ok(Exp::new(ExpKind::TrueLit, Metadata::default()))
                }
                _ => Err("SIF relational expression outside the supported product fragment".into()),
            }
        }
        _ => {
            if has_low_predicate(exp, low_predicates)? {
                return Err("SIF relational predicate under unsupported assertion form".into());
            }
            if !is_directly_unary(exp, &SifConfig::default())
                .map_err(|e| format!("SIF expression traversal: {e:?}"))?
            {
                use crate::ast::utility::rewriter::strategy::rewrite_expression_bottom_up;
                let normal = rewrite_expression_bottom_up(
                    exp,
                    &mut |node| {
                        let ExpKind::Extension(handle) = node.kind() else {
                            return Ok(node.clone());
                        };
                        let Some(sif) = handle.0.as_any().downcast_ref::<SifExpression>() else {
                            return Err("unsupported SIF expression extension".to_owned());
                        };
                        let (kind, meta) = match &sif.kind {
                            SifExpressionKind::Low {
                                exp: value,
                                comparator: None,
                                ..
                            } => {
                                let primed = sif_pure_expression(value, true, names, fields)?;
                                let equality = Exp::new(
                                    ExpKind::EqCmp(value.clone(), primed),
                                    sif_forward_meta(Node::Exp(node.clone()), node.metadata()),
                                );
                                let mut meta = Metadata::default();
                                meta.error_trafo =
                                    sif_forward_meta(Node::Exp(node.clone()), node.metadata())
                                        .error_trafo;
                                (
                                    ExpKind::Implies(
                                        make(ExpKind::And(first.clone(), second.clone())),
                                        equality,
                                    ),
                                    meta,
                                )
                            }
                            SifExpressionKind::LowEvent => (
                                ExpKind::And(first.clone(), second.clone()),
                                Metadata::default(),
                            ),
                            _ => return Err("unsupported SIF relational expression".into()),
                        };
                        Ok(Exp::new(kind, meta))
                    },
                    &|handle, _| Ok(handle.clone()),
                )
                .map_err(|e| format!("SIF expression rewriting: {e:?}"))?;
                let normal = sif_pure_expression(&normal, false, names, fields)?;
                let both = make(ExpKind::And(first.clone(), second.clone()));
                let normal = Exp::new(ExpKind::Implies(both, normal), forwarded());
                return Ok(Exp::new(
                    ExpKind::And(
                        Exp::new(ExpKind::Implies(first.clone(), normal), forwarded()),
                        Exp::new(
                            ExpKind::Implies(second.clone(), make(ExpKind::TrueLit)),
                            forwarded(),
                        ),
                    ),
                    forwarded(),
                ));
            }
            let normal = sif_pure_expression(exp, false, names, fields)?;
            let primed = sif_pure_expression(exp, true, names, fields)?;
            let left = Exp::new(ExpKind::Implies(first.clone(), normal), forwarded());
            let right = Exp::new(ExpKind::Implies(second.clone(), primed), forwarded());
            Ok(Exp::new(ExpKind::And(left, right), forwarded()))
        }
    }
}

fn termination_channel_checks(
    terminates: &Exp,
    first: &Exp,
    second: &Exp,
    names: &HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
    low_predicates: &HashSet<String>,
    event_flags: Option<&(
        crate::ast::program::LocalVarDecl,
        crate::ast::program::LocalVarDecl,
    )>,
) -> Result<Vec<Exp>, String> {
    use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
    use super::sif_error::SifTerminationReasonKind;
    use crate::ast::ast::{ErrorTrafo, Metadata};
    let ExpKind::Extension(extension) = terminates.kind() else {
        return Err("expected SIF termination expression".into());
    };
    let Some(SifExpression {
        kind: SifExpressionKind::Terminates { condition },
        ..
    }) = extension.0.as_any().downcast_ref::<SifExpression>()
    else {
        return Err("expected SIF termination expression".into());
    };
    let meta = |reason| {
        let trafo = std::sync::Arc::new(TerminationChannelTrafo {
            expression: terminates.clone(),
            offending_node: Node::Exp(terminates.clone()),
            reason,
        });
        let mut meta = terminates.metadata().clone();
        meta.error_trafo =
            ErrorTrafo::trafos(vec![trafo.clone()], vec![trafo], None).combine(&meta.error_trafo);
        meta
    };
    let event_meta = meta(SifTerminationReasonKind::ConditionNotLowEvent);
    let low_meta = meta(SifTerminationReasonKind::ConditionNotLow);
    let low_event = SifExpression {
        kind: SifExpressionKind::LowEvent,
        meta: event_meta.clone(),
    }
    .expression()
    .map_err(|e| format!("SIF lowEvent construction: {e:?}"))?;
    let condition_not = Exp::new(ExpKind::Not(condition.clone()), event_meta.clone());
    let condition_event = Exp::new(
        ExpKind::Implies(condition_not, low_event),
        event_meta.clone(),
    );
    let low = SifExpression {
        kind: SifExpressionKind::Low {
            exp: condition.clone(),
            comparator: None,
            type_variables: Default::default(),
        },
        meta: low_meta.clone(),
    }
    .expression()
    .map_err(|e| format!("SIF low construction: {e:?}"))?;
    let translate = |e: &Exp, meta: Metadata| -> Result<Exp, String> {
        let transformed =
            sif_assertion_with_flags(e, first, second, names, fields, low_predicates, event_flags)?;
        Ok(Exp::with_extra(
            transformed.kind().clone(),
            meta,
            transformed.0.extra.clone(),
        ))
    };
    Ok(vec![
        translate(&condition_event, event_meta)?,
        translate(&low, low_meta)?,
    ])
}

fn last_sif_termination(node: &Node, result: &mut Option<Exp>) -> Result<(), String> {
    if let Node::Exp(exp) = node {
        if matches!(exp.kind(), ExpKind::Extension(extension) if matches!(extension.0.as_any().downcast_ref::<super::sif_ast_extensions::SifExpression>(), Some(super::sif_ast_extensions::SifExpression { kind: super::sif_ast_extensions::SifExpressionKind::Terminates { .. }, .. })))
        {
            *result = Some(exp.clone());
        }
    }
    for child in subnodes(node).map_err(|e| format!("SIF termination traversal: {e:?}"))? {
        last_sif_termination(&child, result)?;
    }
    Ok(())
}

fn simplify_sif_conditions(expressions: Vec<Exp>) -> Result<Vec<Exp>, String> {
    let mut result = Vec::new();
    for expression in expressions {
        let simplified = rewrite_loop_preorder(&expression, &|e| {
            if e.is_pure() {
                crate::ast::utility::simplifier::simplify(e, false, &|v| {
                    crate::ast::utility::expressions::is_known_well_defined(v, None)
                })
                .map_err(|error| format!("SIF condition simplification: {error:?}"))
            } else {
                Ok(e.clone())
            }
        })?;
        if !matches!(simplified.kind(), ExpKind::TrueLit) {
            result.push(simplified);
        }
    }
    Ok(result)
}

fn sif_flatten_block(
    stmt: &crate::ast::statement::Stmt,
    declarations: &mut Vec<crate::ast::program::LocalVarDecl>,
    statements: &mut Vec<crate::ast::statement::Stmt>,
) -> Result<(), String> {
    use crate::ast::{program::Declaration, statement::StmtKind};
    match stmt.kind() {
        StmtKind::Seqn {
            statements: children,
            declarations: scoped,
        } => {
            for declaration in scoped {
                match declaration {
                    Declaration::Local(local) => declarations.push(local.clone()),
                    _ => return Err("SIF scoped declaration outside supported fragment".into()),
                }
            }
            for child in children {
                sif_flatten_block(child, declarations, statements)?;
            }
        }
        _ => statements.push(stmt.clone()),
    }
    Ok(())
}

fn contains_sif_return(node: &Node) -> Result<bool, String> {
    use super::sif_ast_extensions::{SifStatement, SifStatementKind};
    use crate::ast::statement::StmtKind;
    if matches!(node, Node::Stmt(stmt) if matches!(stmt.kind(), StmtKind::Extension(extension) if matches!(extension.0.as_any().downcast_ref::<SifStatement>(), Some(SifStatement { kind: SifStatementKind::Return { .. }, .. }))))
    {
        return Ok(true);
    }
    for child in subnodes(node).map_err(|e| format!("SIF control-flow traversal: {e:?}"))? {
        if contains_sif_return(&child)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn sif_assertion_block(
    stmt: &crate::ast::statement::Stmt,
    first: &Exp,
    second: &Exp,
    names: &mut HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
    low_predicates: &HashSet<String>,
    return_flags: Option<&(
        crate::ast::program::LocalVarDecl,
        crate::ast::program::LocalVarDecl,
    )>,
    generator: &mut NameTransformer,
) -> Result<crate::ast::statement::Stmt, String> {
    use crate::ast::{
        ast::Metadata,
        expression::LocalVar,
        program::{Declaration, LocalVarDecl},
        statement::{Stmt, StmtKind},
        r#type::Type,
    };
    if !matches!(stmt.kind(), StmtKind::Seqn { .. }) {
        return Err("SIF method and branch bodies must be blocks".into());
    }
    let raw_first = first;
    let raw_second = second;
    let active = |p: &Exp, flag: &LocalVarDecl| {
        Exp::new(
            ExpKind::And(
                p.clone(),
                Exp::new(
                    ExpKind::Not(Exp::new(
                        ExpKind::LocalVar(flag.local_var()),
                        Metadata::default(),
                    )),
                    Metadata::default(),
                ),
            ),
            Metadata::default(),
        )
    };
    let first_active = return_flags.map(|(a, _)| active(first, a));
    let second_active = return_flags.map(|(_, b)| active(second, b));
    let first = first_active.as_ref().unwrap_or(first);
    let second = second_active.as_ref().unwrap_or(second);
    let mut locals = Vec::new();
    let mut original = Vec::new();
    sif_flatten_block(stmt, &mut locals, &mut original)?;
    let mut declarations = Vec::new();
    for local in locals {
        if names.contains_key(&local.name) || !sif_supported_type(&local.typ) {
            return Err("SIF shadowed local or local type outside supported fragment".into());
        }
        let new_name = generator.get_unused_name(&local.name);
        names.insert(local.name.clone(), new_name.clone());
        declarations.push(Declaration::Local(local.clone()));
        declarations.push(Declaration::Local(LocalVarDecl::new(
            new_name,
            local.typ.clone(),
            Metadata::default(),
        )));
    }
    let skip = Stmt::new(
        StmtKind::Seqn {
            statements: vec![],
            declarations: vec![],
        },
        Metadata::default(),
    );
    let mut result = Vec::new();
    let mut normal = Vec::new();
    let mut primed = Vec::new();
    let flush = |normal: &mut Vec<Stmt>, primed: &mut Vec<Stmt>, result: &mut Vec<Stmt>| {
        if normal.is_empty() {
            return;
        }
        let first_body = Stmt::new(
            StmtKind::Seqn {
                statements: std::mem::take(normal),
                declarations: vec![],
            },
            Metadata::default(),
        );
        let second_body = Stmt::new(
            StmtKind::Seqn {
                statements: std::mem::take(primed),
                declarations: vec![],
            },
            Metadata::default(),
        );
        let first_if = Stmt::new(
            StmtKind::If {
                condition: first.clone(),
                then_branch: first_body,
                else_branch: skip.clone(),
            },
            Metadata::default(),
        );
        let second_if = Stmt::new(
            StmtKind::If {
                condition: second.clone(),
                then_branch: second_body,
                else_branch: skip.clone(),
            },
            Metadata::default(),
        );
        result.push(Stmt::new(
            StmtKind::Seqn {
                statements: vec![first_if, second_if, skip.clone()],
                declarations: vec![],
            },
            Metadata::default(),
        ));
    };
    for current in original {
        match current.kind() {
            StmtKind::LocalVarAssign { lhs, rhs } => {
                let Some(name) = names.get(&lhs.name) else {
                    return Err(format!("unmapped SIF assignment target {}", lhs.name));
                };
                let primed_lhs = LocalVar::new(
                    name.clone(),
                    lhs.typ.clone(),
                    sif_forward_meta(Node::LocalVar(lhs.clone()), &lhs.meta),
                );
                normal.push(Stmt::new(
                    StmtKind::LocalVarAssign {
                        lhs: lhs.clone(),
                        rhs: sif_pure_expression(rhs, false, names, fields)?,
                    },
                    current.metadata().clone(),
                ));
                primed.push(Stmt::new(
                    StmtKind::LocalVarAssign {
                        lhs: primed_lhs,
                        rhs: sif_pure_expression(rhs, true, names, fields)?,
                    },
                    current.metadata().clone(),
                ));
            }
            StmtKind::Inhale(exp) | StmtKind::Exhale(exp) => {
                if has_low_predicate(exp, low_predicates)?
                    || !is_directly_unary(exp, &SifConfig::default())
                        .map_err(|e| format!("SIF expression traversal: {e:?}"))?
                {
                    flush(&mut normal, &mut primed, &mut result);
                    let translated =
                        sif_assertion(exp, first, second, names, fields, low_predicates)?;
                    let kind = if matches!(current.kind(), StmtKind::Inhale(_)) {
                        StmtKind::Inhale(translated)
                    } else {
                        StmtKind::Exhale(translated)
                    };
                    result.push(Stmt::new(
                        kind,
                        sif_forward_meta(Node::Stmt(current.clone()), current.metadata()),
                    ));
                    continue;
                }
                let normal_exp = sif_pure_expression(exp, false, names, fields)?;
                let primed_exp = sif_pure_expression(exp, true, names, fields)?;
                let is_inhale = matches!(current.kind(), StmtKind::Inhale(_));
                normal.push(Stmt::new(
                    if is_inhale {
                        StmtKind::Inhale(normal_exp)
                    } else {
                        StmtKind::Exhale(normal_exp)
                    },
                    current.metadata().clone(),
                ));
                primed.push(Stmt::new(
                    if is_inhale {
                        StmtKind::Inhale(primed_exp)
                    } else {
                        StmtKind::Exhale(primed_exp)
                    },
                    current.metadata().clone(),
                ));
            }
            StmtKind::NewStmt {
                lhs,
                fields: allocated,
            } => {
                flush(&mut normal, &mut primed, &mut result);
                let Some(primed_name) = names.get(&lhs.name) else {
                    return Err(format!("unmapped SIF allocation target {}", lhs.name));
                };
                let mut all_fields = allocated.clone();
                for field in allocated {
                    all_fields.push(
                        fields
                            .get(&field.name)
                            .cloned()
                            .ok_or_else(|| format!("unmapped SIF field {}", field.name))?,
                    );
                }
                let temporary = LocalVarDecl::new(
                    generator.get_unused_name("tmp"),
                    Type::Ref,
                    Metadata::default(),
                );
                let value = Exp::new(
                    ExpKind::LocalVar(temporary.local_var()),
                    Metadata::default(),
                );
                let allocate = Stmt::new(
                    StmtKind::NewStmt {
                        lhs: temporary.local_var(),
                        fields: all_fields,
                    },
                    Metadata::default(),
                );
                let primed_lhs = LocalVar::new(
                    primed_name.clone(),
                    lhs.typ.clone(),
                    sif_forward_meta(Node::LocalVar(lhs.clone()), &lhs.meta),
                );
                let branch = |active: &Exp, target: LocalVar| {
                    let assign = Stmt::new(
                        StmtKind::LocalVarAssign {
                            lhs: target,
                            rhs: value.clone(),
                        },
                        Metadata::default(),
                    );
                    Stmt::new(
                        StmtKind::If {
                            condition: active.clone(),
                            then_branch: Stmt::new(
                                StmtKind::Seqn {
                                    statements: vec![assign],
                                    declarations: vec![],
                                },
                                Metadata::default(),
                            ),
                            else_branch: skip.clone(),
                        },
                        Metadata::default(),
                    )
                };
                result.push(Stmt::new(
                    StmtKind::Seqn {
                        statements: vec![
                            allocate,
                            branch(first, lhs.clone()),
                            branch(second, primed_lhs),
                            skip.clone(),
                        ],
                        declarations: vec![Declaration::Local(temporary)],
                    },
                    Metadata::default(),
                ));
            }
            StmtKind::FieldAssign { lhs, rhs } => {
                flush(&mut normal, &mut primed, &mut result);
                let access = Exp::new(ExpKind::FieldAccess(lhs.clone()), lhs.meta.clone());
                sif_pure_expression(&access, false, names, fields)?;
                sif_pure_expression(rhs, false, names, fields)?;
                let prime_access = sif_pure_expression(&access, true, names, fields)?;
                let ExpKind::FieldAccess(prime_lhs) = prime_access.kind() else {
                    return Err("invalid SIF primed field assignment".into());
                };
                let second_stmt = Stmt::new(
                    StmtKind::FieldAssign {
                        lhs: prime_lhs.clone(),
                        rhs: sif_pure_expression(rhs, true, names, fields)?,
                    },
                    current.metadata().clone(),
                );
                let branch = |active: &Exp, statement: Stmt| {
                    Stmt::new(
                        StmtKind::If {
                            condition: active.clone(),
                            then_branch: Stmt::new(
                                StmtKind::Seqn {
                                    statements: vec![statement],
                                    declarations: vec![],
                                },
                                Metadata::default(),
                            ),
                            else_branch: skip.clone(),
                        },
                        Metadata::default(),
                    )
                };
                result.push(Stmt::new(
                    StmtKind::Seqn {
                        statements: vec![
                            branch(first, current.clone()),
                            branch(second, second_stmt),
                            skip.clone(),
                        ],
                        declarations: vec![],
                    },
                    Metadata::default(),
                ));
            }
            StmtKind::MethodCall {
                method_name,
                args,
                targets,
            } => {
                flush(&mut normal, &mut primed, &mut result);
                let mut call_args = vec![first.clone(), second.clone()];
                let mut declarations = Vec::new();
                let mut first_arguments = Vec::new();
                let mut second_arguments = Vec::new();
                for argument in args {
                    let typ = argument
                        .typ()
                        .map_err(|e| format!("SIF argument type: {e:?}"))?;
                    if !sif_supported_type(&typ) {
                        return Err("SIF method argument type outside supported fragment".into());
                    }
                    let a = LocalVarDecl::new(
                        generator.get_unused_name("tmp1"),
                        typ.clone(),
                        Metadata::default(),
                    );
                    let b = LocalVarDecl::new(
                        generator.get_unused_name("tmp2"),
                        typ,
                        Metadata::default(),
                    );
                    call_args.push(Exp::new(
                        ExpKind::LocalVar(a.local_var()),
                        Metadata::default(),
                    ));
                    call_args.push(Exp::new(
                        ExpKind::LocalVar(b.local_var()),
                        Metadata::default(),
                    ));
                    first_arguments.push(Stmt::new(
                        StmtKind::LocalVarAssign {
                            lhs: a.local_var(),
                            rhs: sif_pure_expression(argument, false, names, fields)?,
                        },
                        Metadata::default(),
                    ));
                    second_arguments.push(Stmt::new(
                        StmtKind::LocalVarAssign {
                            lhs: b.local_var(),
                            rhs: sif_pure_expression(argument, true, names, fields)?,
                        },
                        Metadata::default(),
                    ));
                    declarations.extend([Declaration::Local(a), Declaration::Local(b)]);
                }
                let mut call_targets = Vec::new();
                let mut first_targets = Vec::new();
                let mut second_targets = Vec::new();
                for target in targets {
                    if !sif_supported_type(&target.typ) {
                        return Err("SIF method return type outside supported fragment".into());
                    }
                    let Some(primed_name) = names.get(&target.name) else {
                        return Err(format!("unmapped SIF call target {}", target.name));
                    };
                    let a = LocalVarDecl::new(
                        generator.get_unused_name("tmp1"),
                        target.typ.clone(),
                        Metadata::default(),
                    );
                    let b = LocalVarDecl::new(
                        generator.get_unused_name("tmp2"),
                        target.typ.clone(),
                        Metadata::default(),
                    );
                    call_targets.extend([a.local_var(), b.local_var()]);
                    first_targets.push(Stmt::new(
                        StmtKind::LocalVarAssign {
                            lhs: target.clone(),
                            rhs: Exp::new(ExpKind::LocalVar(a.local_var()), Metadata::default()),
                        },
                        Metadata::default(),
                    ));
                    let primed_target = LocalVar::new(
                        primed_name.clone(),
                        target.typ.clone(),
                        sif_forward_meta(Node::LocalVar(target.clone()), &target.meta),
                    );
                    second_targets.push(Stmt::new(
                        StmtKind::LocalVarAssign {
                            lhs: primed_target,
                            rhs: Exp::new(ExpKind::LocalVar(b.local_var()), Metadata::default()),
                        },
                        Metadata::default(),
                    ));
                    declarations.extend([Declaration::Local(a), Declaration::Local(b)]);
                }
                let conditional = |active: &Exp, statements: Vec<Stmt>| {
                    Stmt::new(
                        StmtKind::If {
                            condition: active.clone(),
                            then_branch: Stmt::new(
                                StmtKind::Seqn {
                                    statements,
                                    declarations: vec![],
                                },
                                Metadata::default(),
                            ),
                            else_branch: skip.clone(),
                        },
                        Metadata::default(),
                    )
                };
                let mut body = vec![
                    conditional(first, first_arguments),
                    conditional(second, second_arguments),
                    Stmt::new(
                        StmtKind::MethodCall {
                            method_name: method_name.clone(),
                            args: call_args,
                            targets: call_targets,
                        },
                        current.metadata().clone(),
                    ),
                ];
                if !targets.is_empty() {
                    body.extend([
                        conditional(first, first_targets),
                        conditional(second, second_targets),
                    ]);
                }
                let mut meta = Metadata::default();
                meta.info =
                    crate::ast::ast::Info::Simple(vec![format!("Method call: {method_name}\n  ")]);
                result.push(Stmt::new(
                    StmtKind::If {
                        condition: Exp::new(
                            ExpKind::Or(first.clone(), second.clone()),
                            Metadata::default(),
                        ),
                        then_branch: Stmt::new(
                            StmtKind::Seqn {
                                statements: body,
                                declarations,
                            },
                            Metadata::default(),
                        ),
                        else_branch: skip.clone(),
                    },
                    meta,
                ));
            }
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                flush(&mut normal, &mut primed, &mut result);
                let normal_cond = sif_pure_expression(condition, false, names, fields)?;
                let prime_cond = sif_pure_expression(condition, true, names, fields)?;
                let controls = ["p1", "p2", "p3", "p4"]
                    .into_iter()
                    .map(|name| {
                        LocalVarDecl::new(
                            generator.get_unused_name(name),
                            Type::Bool,
                            Metadata::default(),
                        )
                    })
                    .collect::<Vec<_>>();
                let refs = controls
                    .iter()
                    .map(|decl| Exp::new(ExpKind::LocalVar(decl.local_var()), Metadata::default()))
                    .collect::<Vec<_>>();
                let not_normal = Exp::new(ExpKind::Not(normal_cond.clone()), Metadata::default());
                let not_prime = Exp::new(ExpKind::Not(prime_cond.clone()), Metadata::default());
                let values = [
                    (first.clone(), normal_cond),
                    (second.clone(), prime_cond),
                    (first.clone(), not_normal),
                    (second.clone(), not_prime),
                ];
                let mut branches = controls
                    .iter()
                    .zip(values)
                    .map(|(decl, (active, test))| {
                        Stmt::new(
                            StmtKind::LocalVarAssign {
                                lhs: decl.local_var(),
                                rhs: Exp::new(ExpKind::And(active, test), Metadata::default()),
                            },
                            current.metadata().clone(),
                        )
                    })
                    .collect::<Vec<_>>();
                branches.push(skip.clone());
                branches.push(sif_assertion_block(
                    then_branch,
                    &refs[0],
                    &refs[1],
                    names,
                    fields,
                    low_predicates,
                    return_flags,
                    generator,
                )?);
                branches.push(sif_assertion_block(
                    else_branch,
                    &refs[2],
                    &refs[3],
                    names,
                    fields,
                    low_predicates,
                    return_flags,
                    generator,
                )?);
                result.push(Stmt::new(
                    StmtKind::Seqn {
                        statements: branches,
                        declarations: controls.into_iter().map(Declaration::Local).collect(),
                    },
                    Metadata::default(),
                ));
            }
            StmtKind::While {
                condition,
                invariants,
                body,
            } => {
                flush(&mut normal, &mut primed, &mut result);
                let reconstruct = contains_sif_return(&Node::Stmt(body.clone()))?;
                fn targets(
                    node: &Node,
                    result: &mut Vec<LocalVar>,
                    return_flags: Option<&(LocalVarDecl, LocalVarDecl)>,
                ) -> Result<(), String> {
                    if let Node::Stmt(stmt) = node {
                        let vars: Vec<LocalVar> = match stmt.kind() {
                            StmtKind::LocalVarAssign { lhs, .. }
                            | StmtKind::NewStmt { lhs, .. } => vec![lhs.clone()],
                            StmtKind::MethodCall { targets, .. } => targets.clone(),
                            StmtKind::Extension(extension)
                                if matches!(
                                    extension
                                        .0
                                        .as_any()
                                        .downcast_ref::<super::sif_ast_extensions::SifStatement>(),
                                    Some(super::sif_ast_extensions::SifStatement {
                                        kind: super::sif_ast_extensions::SifStatementKind::Return { .. },
                                        ..
                                    })
                                ) =>
                            {
                                vec![
                                    return_flags
                                        .ok_or_else(|| "missing SIF return flags".to_owned())?
                                        .0
                                        .local_var(),
                                ]
                            }
                            _ => vec![],
                        };
                        for variable in vars {
                            if !result.contains(&variable) {
                                result.push(variable);
                            }
                        }
                    }
                    for child in
                        subnodes(node).map_err(|e| format!("SIF loop target traversal: {e:?}"))?
                    {
                        targets(&child, result, return_flags)?;
                    }
                    Ok(())
                }
                fn has_inhale_exhale(node: &Node) -> Result<bool, String> {
                    if matches!(node, Node::Exp(e) if matches!(e.kind(), ExpKind::InhaleExhaleExp(..)))
                    {
                        return Ok(true);
                    }
                    for child in subnodes(node)
                        .map_err(|e| format!("SIF loop invariant traversal: {e:?}"))?
                    {
                        if has_inhale_exhale(&child)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                let mut has_idle = false;
                let mut loop_termination = None;
                for invariant in invariants {
                    last_sif_termination(&Node::Exp(invariant.clone()), &mut loop_termination)?;
                    has_idle |= has_inhale_exhale(&Node::Exp(invariant.clone()))?;
                }
                let fresh = |generator: &mut NameTransformer, name: &str, typ: Type| {
                    let decl = LocalVarDecl::new(
                        generator.get_unused_name(name),
                        typ,
                        Metadata::default(),
                    );
                    let exp = Exp::new(ExpKind::LocalVar(decl.local_var()), Metadata::default());
                    (decl, exp)
                };
                let assign = |target: &LocalVarDecl, value: Exp| {
                    Stmt::new(
                        StmtKind::LocalVarAssign {
                            lhs: target.local_var(),
                            rhs: value,
                        },
                        Metadata::default(),
                    )
                };
                let not = |e: Exp| Exp::new(ExpKind::Not(e), Metadata::default());
                let and = |a: Exp, b: Exp| Exp::new(ExpKind::And(a, b), Metadata::default());
                let implies =
                    |a: Exp, b: Exp| Exp::new(ExpKind::Implies(a, b), Metadata::default());
                let (bypass1, bypass1_exp) = fresh(generator, "bypass1", Type::Bool);
                let (bypass2, bypass2_exp) = fresh(generator, "bypass2", Type::Bool);
                let mut declarations = vec![
                    Declaration::Local(bypass1.clone()),
                    Declaration::Local(bypass2.clone()),
                ];
                let mut statements = vec![
                    assign(&bypass1, not(first.clone())),
                    assign(&bypass2, not(second.clone())),
                ];
                let mut modified = Vec::new();
                targets(&Node::Stmt(current.clone()), &mut modified, return_flags)?;
                let mut first_snapshots = Vec::new();
                let mut second_snapshots = Vec::new();
                let mut first_equalities = Vec::new();
                let mut second_equalities = Vec::new();
                for target in &modified {
                    if !names.contains_key(&target.name) {
                        continue;
                    }
                    let (tmp1, tmp1_exp) = fresh(generator, "tmp1", target.typ.clone());
                    let (tmp2, tmp2_exp) = fresh(generator, "tmp2", target.typ.clone());
                    declarations.extend([
                        Declaration::Local(tmp1.clone()),
                        Declaration::Local(tmp2.clone()),
                    ]);
                    let original = Exp::new(ExpKind::LocalVar(target.clone()), target.meta.clone());
                    let normal = sif_pure_expression(&original, false, names, fields)?;
                    let prime = sif_pure_expression(&original, true, names, fields)?;
                    first_snapshots.push(assign(&tmp1, normal.clone()));
                    second_snapshots.push(assign(&tmp2, prime.clone()));
                    let eq1 = Exp::new(ExpKind::EqCmp(tmp1_exp, normal), Metadata::default());
                    let eq2 = Exp::new(ExpKind::EqCmp(tmp2_exp, prime), Metadata::default());
                    if !first_equalities.contains(&eq1) {
                        first_equalities.push(eq1);
                    }
                    if !second_equalities.contains(&eq2) {
                        second_equalities.push(eq2);
                    }
                }
                let conditional = |condition: Exp, items: Vec<Stmt>| {
                    Stmt::new(
                        StmtKind::If {
                            condition,
                            then_branch: Stmt::new(
                                StmtKind::Seqn {
                                    statements: items,
                                    declarations: vec![],
                                },
                                Metadata::default(),
                            ),
                            else_branch: skip.clone(),
                        },
                        Metadata::default(),
                    )
                };
                if !modified.is_empty() {
                    statements.push(conditional(bypass1_exp.clone(), first_snapshots));
                    statements.push(conditional(bypass2_exp.clone(), second_snapshots));
                }
                let old_return_flags = if reconstruct {
                    let Some((ret1, ret2)) = return_flags else {
                        return Err("missing SIF return flags".into());
                    };
                    let (old1, old1_exp) =
                        fresh(generator, &format!("old{}", ret1.name), Type::Bool);
                    let (old2, old2_exp) =
                        fresh(generator, &format!("old{}", ret2.name), Type::Bool);
                    declarations.extend([
                        Declaration::Local(old1.clone()),
                        Declaration::Local(old2.clone()),
                    ]);
                    statements.push(assign(
                        &old1,
                        Exp::new(ExpKind::LocalVar(ret1.local_var()), Metadata::default()),
                    ));
                    statements.push(assign(
                        &old2,
                        Exp::new(ExpKind::LocalVar(ret2.local_var()), Metadata::default()),
                    ));
                    Some((old1_exp, old2_exp))
                } else {
                    None
                };
                let normal_condition = sif_pure_expression(condition, false, names, fields)?;
                let prime_condition = sif_pure_expression(condition, true, names, fields)?;
                let loop_condition = Exp::new(
                    ExpKind::Or(
                        and(
                            and(first.clone(), not(bypass1_exp.clone())),
                            normal_condition.clone(),
                        ),
                        and(
                            and(second.clone(), not(bypass2_exp.clone())),
                            prime_condition.clone(),
                        ),
                    ),
                    Metadata::default(),
                );
                let (inner1, inner1_exp) = fresh(generator, "p1", Type::Bool);
                let (inner2, inner2_exp) = fresh(generator, "p2", Type::Bool);
                declarations.extend([
                    Declaration::Local(inner1.clone()),
                    Declaration::Local(inner2.clone()),
                ]);
                let mut body_preamble = vec![
                    assign(&inner1, and(first.clone(), normal_condition.clone())),
                    assign(&inner2, and(second.clone(), prime_condition.clone())),
                ];
                let idle = if has_idle {
                    let (idle1, idle1_exp) = fresh(generator, "idle1", Type::Bool);
                    let (idle2, idle2_exp) = fresh(generator, "idle2", Type::Bool);
                    names.insert(idle1.name.clone(), idle2.name.clone());
                    declarations.extend([
                        Declaration::Local(idle1.clone()),
                        Declaration::Local(idle2.clone()),
                    ]);
                    statements.push(assign(
                        &idle1,
                        Exp::new(ExpKind::FalseLit, Metadata::default()),
                    ));
                    statements.push(assign(
                        &idle2,
                        Exp::new(ExpKind::FalseLit, Metadata::default()),
                    ));
                    body_preamble.push(assign(
                        &idle1,
                        and(first.clone(), not(normal_condition.clone())),
                    ));
                    body_preamble.push(assign(
                        &idle2,
                        and(second.clone(), not(prime_condition.clone())),
                    ));
                    Some((idle1_exp, idle2_exp))
                } else {
                    None
                };
                let mut new_invariants = invariants
                    .iter()
                    .map(|invariant| {
                        if let Some((idle1, _)) = &idle {
                            guard_loop_exhales(invariant, idle1)
                        } else {
                            Ok(invariant.clone())
                        }
                    })
                    .collect::<Result<Vec<_>, String>>()?;
                if let Some(terminates) = loop_termination {
                    use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
                    use super::sif_error::SifTerminationReasonKind;
                    use crate::ast::ast::ErrorTrafo;
                    for check in termination_channel_checks(
                        &terminates,
                        raw_first,
                        raw_second,
                        names,
                        fields,
                        low_predicates,
                        return_flags,
                    )? {
                        statements.push(Stmt::new(
                            StmtKind::Assert(check.clone()),
                            check.metadata().clone(),
                        ));
                    }
                    let ExpKind::Extension(extension) = terminates.kind() else {
                        return Err("invalid SIF termination expression".into());
                    };
                    let Some(SifExpression {
                        kind:
                            SifExpressionKind::Terminates {
                                condition: termination_condition,
                            },
                        ..
                    }) = extension.0.as_any().downcast_ref::<SifExpression>()
                    else {
                        return Err("invalid SIF termination expression".into());
                    };
                    let (cond1, cond1_exp) = fresh(generator, "cond", Type::Bool);
                    let (cond2, _cond2_exp) = fresh(generator, "cond", Type::Bool);
                    names.insert(cond1.name.clone(), cond2.name.clone());
                    declarations.extend([
                        Declaration::Local(cond1.clone()),
                        Declaration::Local(cond2.clone()),
                    ]);
                    statements.push(conditional(
                        raw_first.clone(),
                        vec![assign(
                            &cond1,
                            sif_pure_expression(termination_condition, false, names, fields)?,
                        )],
                    ));
                    statements.push(conditional(
                        raw_second.clone(),
                        vec![assign(
                            &cond2,
                            sif_pure_expression(termination_condition, true, names, fields)?,
                        )],
                    ));
                    let trafo = std::sync::Arc::new(TerminationChannelTrafo {
                        expression: terminates.clone(),
                        offending_node: Node::Exp(terminates.clone()),
                        reason: SifTerminationReasonKind::ConditionNotTight,
                    });
                    let mut meta = terminates.metadata().clone();
                    meta.error_trafo =
                        ErrorTrafo::trafos(vec![trafo], vec![], None).combine(&meta.error_trafo);
                    new_invariants.push(Exp::new(
                        ExpKind::Implies(not(cond1_exp), condition.clone()),
                        meta,
                    ));
                }
                let invariant1 = and(raw_first.clone(), not(bypass1_exp.clone()));
                let invariant2 = and(raw_second.clone(), not(bypass2_exp.clone()));
                let mut translated_invariants = Vec::new();
                for original_invariant in &new_invariants {
                    let translated = sif_assertion_with_flags(
                        original_invariant,
                        &invariant1,
                        &invariant2,
                        names,
                        fields,
                        low_predicates,
                        return_flags,
                    )?;
                    let simplified = rewrite_loop_preorder(&translated, &|e| {
                        if e.is_pure() {
                            crate::ast::utility::simplifier::simplify(e, false, &|v| {
                                crate::ast::utility::expressions::is_known_well_defined(v, None)
                            })
                            .map_err(|error| {
                                format!("SIF loop invariant simplification: {error:?}")
                            })
                        } else {
                            Ok(e.clone())
                        }
                    })?;
                    if !matches!(simplified.kind(), ExpKind::TrueLit) {
                        translated_invariants.push(simplified);
                    }
                }
                translated_invariants.extend(
                    first_equalities
                        .into_iter()
                        .map(|eq| implies(bypass1_exp.clone(), eq)),
                );
                translated_invariants.extend(
                    second_equalities
                        .into_iter()
                        .map(|eq| implies(bypass2_exp.clone(), eq)),
                );
                let product_body = sif_assertion_block(
                    body,
                    &inner1_exp,
                    &inner2_exp,
                    names,
                    fields,
                    low_predicates,
                    return_flags,
                    generator,
                )?;
                body_preamble.push(product_body);
                let body = Stmt::new(
                    StmtKind::Seqn {
                        statements: body_preamble.clone(),
                        declarations: vec![],
                    },
                    Metadata::default(),
                );
                statements.push(Stmt::new(
                    StmtKind::While {
                        condition: loop_condition,
                        invariants: translated_invariants,
                        body,
                    },
                    Metadata::default(),
                ));
                if let Some((old1, old2)) = old_return_flags {
                    let Some((ret1, ret2)) = return_flags else {
                        return Err("missing SIF return flags".into());
                    };
                    let var = |decl: &LocalVarDecl| {
                        Exp::new(ExpKind::LocalVar(decl.local_var()), Metadata::default())
                    };
                    let ret1_exp = var(ret1);
                    let ret2_exp = var(ret2);
                    let reconstruction_condition = Exp::new(
                        ExpKind::Or(
                            and(not(bypass1_exp.clone()), ret1_exp.clone()),
                            and(not(bypass2_exp.clone()), ret2_exp.clone()),
                        ),
                        Metadata::default(),
                    );
                    let inhale = |e: Exp| Stmt::new(StmtKind::Inhale(e), Metadata::default());
                    let mut reconstructed = vec![
                        assign(ret1, old1),
                        assign(ret2, old2),
                        inhale(implies(
                            and(raw_first.clone(), not(ret1_exp.clone())),
                            normal_condition.clone(),
                        )),
                        // Source uses activeExecNoContNormal for the second reconstruction inhale.
                        inhale(implies(
                            and(raw_second.clone(), not(ret1_exp.clone())),
                            prime_condition.clone(),
                        )),
                    ];
                    reconstructed.extend(body_preamble);
                    reconstructed.push(inhale(Exp::new(
                        ExpKind::Or(not(inner1_exp.clone()), not(not(ret1_exp))),
                        Metadata::default(),
                    )));
                    reconstructed.push(inhale(Exp::new(
                        ExpKind::Or(not(inner2_exp.clone()), not(not(ret2_exp))),
                        Metadata::default(),
                    )));
                    let mut meta = Metadata::default();
                    meta.info =
                        crate::ast::ast::Info::Simple(vec!["Loop Reconstruction.\n  ".into()]);
                    statements.push(Stmt::new(
                        StmtKind::If {
                            condition: reconstruction_condition,
                            then_branch: Stmt::new(
                                StmtKind::Seqn {
                                    statements: reconstructed,
                                    declarations: vec![],
                                },
                                Metadata::default(),
                            ),
                            else_branch: skip.clone(),
                        },
                        meta,
                    ));
                }
                result.push(Stmt::new(
                    StmtKind::Seqn {
                        statements,
                        declarations,
                    },
                    Metadata::default(),
                ));
            }
            StmtKind::Assert(exp) => {
                flush(&mut normal, &mut primed, &mut result);
                result.push(Stmt::new(
                    StmtKind::Assert(sif_assertion(
                        exp,
                        first,
                        second,
                        names,
                        fields,
                        low_predicates,
                    )?),
                    sif_forward_meta(Node::Stmt(current.clone()), current.metadata()),
                ));
            }
            StmtKind::Fold(access) | StmtKind::Unfold(access) => {
                flush(&mut normal, &mut primed, &mut result);
                let source_access = Exp::new(
                    ExpKind::PredicateAccessPredicate(access.clone()),
                    access.meta.clone(),
                );
                let translated = sif_pure_expression(&source_access, true, names, fields)?;
                let ExpKind::PredicateAccessPredicate(primed_access) = translated.kind() else {
                    return Err("invalid SIF folded predicate".into());
                };
                let explicit = crate::ast::statement::PredicateAccessPredicate::new(
                    primed_access.location.clone(),
                    Some(primed_access.permission_or_full()),
                    Metadata::default(),
                );
                let prime_stmt = if matches!(current.kind(), StmtKind::Fold(_)) {
                    StmtKind::Fold(explicit)
                } else {
                    StmtKind::Unfold(explicit)
                };
                let branch = |condition: &Exp, statement: Stmt| {
                    Stmt::new(
                        StmtKind::If {
                            condition: condition.clone(),
                            then_branch: Stmt::new(
                                StmtKind::Seqn {
                                    statements: vec![statement],
                                    declarations: vec![],
                                },
                                Metadata::default(),
                            ),
                            else_branch: skip.clone(),
                        },
                        Metadata::default(),
                    )
                };
                let first_branch = branch(first, current.clone());
                let second_branch =
                    branch(second, Stmt::new(prime_stmt, current.metadata().clone()));
                let low_check = if low_predicates.contains(&access.location.predicate_name) {
                    use crate::ast::{ast::ErrorTrafo, expression::ExpExtra};
                    let is_fold = matches!(current.kind(), StmtKind::Fold(_));
                    let mut arguments = access.location.args.clone();
                    arguments.extend(
                        access
                            .location
                            .args
                            .iter()
                            .map(|a| sif_pure_expression(a, true, names, fields))
                            .collect::<Result<Vec<_>, _>>()?,
                    );
                    let transformation = ErrorTrafo::trafos(
                        vec![std::sync::Arc::new(PredicateLowCheckTrafo {
                            statement: current.clone(),
                        })],
                        vec![],
                        None,
                    )
                    .combine(&current.metadata().error_trafo);
                    let mut error_meta = current.metadata().clone();
                    error_meta.error_trafo = transformation;
                    let app = Exp::with_extra(
                        ExpKind::FuncApp(
                            NameTransformer::predicate_low_name(&access.location.predicate_name),
                            arguments,
                        ),
                        if is_fold {
                            error_meta.clone()
                        } else {
                            Metadata::default()
                        },
                        ExpExtra {
                            typ: Some(Type::Bool),
                            ..Default::default()
                        },
                    );
                    let active = Exp::new(
                        ExpKind::And(first.clone(), second.clone()),
                        Metadata::default(),
                    );
                    let condition = if is_fold {
                        app
                    } else {
                        let permission = |location: crate::ast::expression::PredicateAccess| {
                            let location =
                                Exp::new(ExpKind::PredicateAccess(location), Metadata::default());
                            Exp::new(
                                ExpKind::PermGeCmp(
                                    Exp::new(ExpKind::CurrentPerm(location), Metadata::default()),
                                    Exp::new(ExpKind::FullPerm, Metadata::default()),
                                ),
                                Metadata::default(),
                            )
                        };
                        let owned = Exp::new(
                            ExpKind::And(
                                permission(access.location.clone()),
                                permission(primed_access.location.clone()),
                            ),
                            Metadata::default(),
                        );
                        Exp::new(ExpKind::Implies(owned, app), Metadata::default())
                    };
                    Stmt::new(
                        StmtKind::Assert(Exp::new(
                            ExpKind::Implies(active, condition),
                            Metadata::default(),
                        )),
                        error_meta,
                    )
                } else {
                    skip.clone()
                };
                let statements = if matches!(current.kind(), StmtKind::Fold(_)) {
                    vec![first_branch, second_branch, low_check]
                } else {
                    vec![low_check, first_branch, second_branch]
                };
                result.push(Stmt::new(
                    StmtKind::Seqn {
                        statements,
                        declarations: vec![],
                    },
                    Metadata::default(),
                ));
            }
            StmtKind::Extension(extension) => {
                use super::sif_ast_extensions::{SifStatement, SifStatementKind};
                use crate::plugin::standard::refute::refute_ast_extension::Refute;
                if let Some(SifStatement {
                    kind: SifStatementKind::Return { exp, result_var },
                    ..
                }) = extension.0.as_any().downcast_ref::<SifStatement>()
                {
                    let Some((ret1, ret2)) = return_flags else {
                        return Err("missing SIF return flags".into());
                    };
                    let mut first_return = Vec::new();
                    let mut second_return = Vec::new();
                    if let Some(target) = result_var {
                        let value = exp
                            .as_ref()
                            .ok_or_else(|| "SIF return target has no value".to_owned())?;
                        let primed_name = names
                            .get(&target.name)
                            .ok_or_else(|| format!("unmapped SIF return target {}", target.name))?;
                        let prime_target = LocalVar::new(
                            primed_name.clone(),
                            target.typ.clone(),
                            sif_forward_meta(Node::LocalVar(target.clone()), &target.meta),
                        );
                        first_return.push(Stmt::new(
                            StmtKind::LocalVarAssign {
                                lhs: target.clone(),
                                rhs: sif_pure_expression(value, false, names, fields)?,
                            },
                            current.metadata().clone(),
                        ));
                        second_return.push(Stmt::new(
                            StmtKind::LocalVarAssign {
                                lhs: prime_target,
                                rhs: sif_pure_expression(value, true, names, fields)?,
                            },
                            current.metadata().clone(),
                        ));
                    }
                    let set_true = |decl: &LocalVarDecl| {
                        Stmt::new(
                            StmtKind::LocalVarAssign {
                                lhs: decl.local_var(),
                                rhs: Exp::new(ExpKind::TrueLit, Metadata::default()),
                            },
                            Metadata::default(),
                        )
                    };
                    first_return.push(set_true(ret1));
                    second_return.push(set_true(ret2));
                    normal.push(Stmt::new(
                        StmtKind::Seqn {
                            statements: first_return,
                            declarations: vec![],
                        },
                        Metadata::default(),
                    ));
                    primed.push(Stmt::new(
                        StmtKind::Seqn {
                            statements: second_return,
                            declarations: vec![],
                        },
                        Metadata::default(),
                    ));
                    flush(&mut normal, &mut primed, &mut result);
                } else if let Some(refute) = extension.0.as_any().downcast_ref::<Refute>() {
                    flush(&mut normal, &mut primed, &mut result);
                    result.push(
                        Refute::new(
                            sif_assertion(
                                &refute.exp,
                                first,
                                second,
                                names,
                                fields,
                                low_predicates,
                            )?,
                            sif_forward_meta(Node::Stmt(current.clone()), current.metadata()),
                        )
                        .statement(),
                    );
                } else if let Some(SifStatement {
                    kind: SifStatementKind::Declassify(exp),
                    ..
                }) = extension.0.as_any().downcast_ref::<SifStatement>()
                {
                    flush(&mut normal, &mut primed, &mut result);
                    let meta = current.metadata().clone();
                    let both = Exp::new(
                        ExpKind::And(first.clone(), second.clone()),
                        Metadata::default(),
                    );
                    let equality = Exp::new(
                        ExpKind::EqCmp(
                            sif_pure_expression(exp, false, names, fields)?,
                            sif_pure_expression(exp, true, names, fields)?,
                        ),
                        Metadata::default(),
                    );
                    result.push(Stmt::new(
                        StmtKind::Inhale(Exp::new(
                            ExpKind::Implies(both, equality),
                            Metadata::default(),
                        )),
                        meta,
                    ));
                } else {
                    return Err(
                        "SIF statement extension outside the supported product fragment".into(),
                    );
                }
            }
            _ => return Err("SIF statement outside the supported pure product fragment".into()),
        }
    }
    flush(&mut normal, &mut primed, &mut result);
    Ok(Stmt::new(
        StmtKind::Seqn {
            statements: result,
            declarations,
        },
        Metadata::default(),
    ))
}

impl super::sif_plugin::SifTransformer for NativeSifTransformer {
    fn transform(
        &mut self,
        input: Program,
        enable_timing: bool,
    ) -> Result<Program, crate::plugin::silver_plugin::PluginHookError> {
        use crate::ast::{
            ast::Metadata,
            expression::ExpKind,
            program::{LocalVarDecl, Method, MethodData},
            statement::{Stmt, StmtKind},
            r#type::Type,
        };
        use crate::plugin::silver_plugin::PluginHookError;
        if enable_timing || !input.extensions.is_empty() {
            return Err(PluginHookError(
                "SIF program outside the supported pure method fragment".into(),
            ));
        }
        for domain in &input.domains {
            for axiom in &domain.axioms {
                if !is_directly_unary(axiom.exp(), &SifConfig::default())
                    .map_err(|e| PluginHookError(format!("SIF domain traversal: {e:?}")))?
                {
                    return Err(PluginHookError(
                        "relational assertions are not allowed in domains".into(),
                    ));
                }
            }
        }
        let relational = source_relational_predicates(&input, &SifConfig::default())
            .map_err(|e| PluginHookError(format!("SIF relational predicate analysis: {e:?}")))?;
        for domain in &input.domains {
            for axiom in &domain.axioms {
                if has_low_predicate(axiom.exp(), &relational).map_err(PluginHookError)? {
                    return Err(PluginHookError(
                        "relational assertions are not allowed in domains".into(),
                    ));
                }
            }
        }
        let low_predicates: HashSet<_> = input
            .predicates
            .iter()
            .filter(|p| p.body.is_some() && relational.contains(&p.name))
            .map(|p| p.name.clone())
            .collect();
        let occupied_globals: HashSet<_> = input
            .fields
            .iter()
            .map(|field| field.name.as_str())
            .chain(input.methods.iter().map(|method| method.name.as_str()))
            .chain(input.domains.iter().map(|domain| domain.name.as_str()))
            .chain(input.domains.iter().flat_map(|domain| {
                domain
                    .functions
                    .iter()
                    .map(|function| function.name.as_str())
            }))
            .chain(
                input
                    .predicates
                    .iter()
                    .map(|predicate| predicate.name.as_str()),
            )
            .chain(
                input
                    .functions
                    .iter()
                    .map(|function| function.name.as_str()),
            )
            .collect();
        for field in &input.fields {
            if occupied_globals.contains(NameTransformer::primed_field_name(&field.name).as_str()) {
                return Err(PluginHookError(
                    "SIF primed field conflicts with an existing global declaration".into(),
                ));
            }
        }
        let mut fields = HashMap::new();
        let mut product_fields = input.fields.clone();
        for field in &input.fields {
            let prime =
                field.copy_with(|data| data.name = NameTransformer::primed_field_name(&field.name));
            fields.insert(field.name.clone(), prime.clone());
            product_fields.push(prime);
        }
        // A function is unchanged by the source transformer when its preconditions are
        // heap independent. Reject expression families whose translation is not yet available.
        for function in &input.functions {
            if !sif_supported_type(&function.typ)
                || function
                    .formal_args
                    .iter()
                    .any(|arg| !sif_supported_type(&arg.typ))
            {
                return Err(PluginHookError(
                    "SIF function type outside supported fragment".into(),
                ));
            }
            for expression in function
                .pres
                .iter()
                .chain(&function.posts)
                .chain(function.body.iter())
            {
                if has_low_predicate(expression, &relational).map_err(PluginHookError)? {
                    return Err(PluginHookError(
                        "relational assertions are not allowed in functions".into(),
                    ));
                }
                sif_pure_expression(expression, false, &HashMap::new(), &fields)
                    .map_err(PluginHookError)?;
            }
        }
        fn seed_declarations(node: &Node, names: &mut Vec<String>) -> Result<(), PluginHookError> {
            if let Node::LocalDecl(decl) = node {
                names.push(decl.name.clone());
            }
            for child in
                subnodes(node).map_err(|e| PluginHookError(format!("SIF name traversal: {e:?}")))?
            {
                seed_declarations(&child, names)?;
            }
            Ok(())
        }
        let mut all_declarations = Vec::new();
        seed_declarations(&Node::Program(input.clone()), &mut all_declarations)?;
        let mut generator = NameTransformer::default();
        generator.mark_used(all_declarations);
        generator.mark_used(input.fields.iter().map(|field| field.name.clone()));
        generator.mark_used(input.domains.iter().flat_map(|domain| {
            std::iter::once(domain.name.clone())
                .chain(domain.functions.iter().map(|f| f.name.clone()))
        }));
        generator.mark_used(
            input
                .predicates
                .iter()
                .map(|predicate| predicate.name.clone()),
        );
        generator.mark_used(input.methods.iter().flat_map(|m| {
            std::iter::once(m.name.clone())
                .chain(m.formal_args.iter().map(|a| a.name.clone()))
                .chain(m.formal_returns.iter().map(|a| a.name.clone()))
        }));
        fn collect_local_names(stmt: &Stmt, names: &mut Vec<String>) {
            match stmt.kind() {
                StmtKind::Seqn {
                    statements,
                    declarations,
                } => {
                    for declaration in declarations {
                        if let crate::ast::program::Declaration::Local(local) = declaration {
                            names.push(local.name.clone());
                        }
                    }
                    for child in statements {
                        collect_local_names(child, names);
                    }
                }
                StmtKind::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    collect_local_names(then_branch, names);
                    collect_local_names(else_branch, names);
                }
                _ => {}
            }
        }
        for method in &input.methods {
            if let Some(body) = &method.body {
                let mut names = Vec::new();
                collect_local_names(body, &mut names);
                generator.mark_used(names);
            }
        }
        generator.mark_used(input.functions.iter().flat_map(|f| {
            std::iter::once(f.name.clone()).chain(f.formal_args.iter().map(|arg| arg.name.clone()))
        }));
        let mut function_names = HashMap::new();
        for function in &input.functions {
            let mut dependent = false;
            for pre in &function.pres {
                dependent |= crate::ast::utility::expressions::is_heap_dependent(pre, &input)
                    .map_err(|e| PluginHookError(format!("SIF heap dependency: {e:?}")))?;
            }
            if dependent {
                function_names.insert(
                    function.name.clone(),
                    generator.get_unused_name(&function.name),
                );
            }
        }
        for predicate in &input.predicates {
            function_names.insert(
                predicate.name.clone(),
                generator.get_unused_name(&predicate.name),
            );
        }
        let mut functions = Vec::new();
        for function in &input.functions {
            let Some(name) = function_names.get(&function.name) else {
                functions.push(function.clone());
                continue;
            };
            let map = |expressions: &[Exp], prime| {
                expressions
                    .iter()
                    .map(|e| sif_pure_expression(e, prime, &function_names, &fields))
                    .collect::<Result<Vec<_>, _>>()
            };
            let first_pres = map(&function.pres, false).map_err(PluginHookError)?;
            let first_posts = map(&function.posts, false).map_err(PluginHookError)?;
            let first_body = function
                .body
                .as_ref()
                .map(|e| sif_pure_expression(e, false, &function_names, &fields))
                .transpose()
                .map_err(PluginHookError)?;
            let first = function.copy_with(|f| {
                f.pres = first_pres;
                f.posts = first_posts;
                f.body = first_body;
            });
            let pres = map(&function.pres, true).map_err(PluginHookError)?;
            let posts = map(&function.posts, true).map_err(PluginHookError)?;
            let body = function
                .body
                .as_ref()
                .map(|e| sif_pure_expression(e, true, &function_names, &fields))
                .transpose()
                .map_err(PluginHookError)?;
            let second = function.copy_with(|f| {
                f.name = name.clone();
                f.pres = pres;
                f.posts = posts;
                f.body = body;
            });
            functions.extend([first, second]);
        }
        let mut predicates = Vec::new();
        for predicate in &input.predicates {
            let name = function_names
                .get(&predicate.name)
                .ok_or_else(|| PluginHookError("missing SIF predicate name".into()))?;
            let unary = predicate
                .body
                .as_ref()
                .map(|e| predicate_unary_body(e, &input))
                .transpose()
                .map_err(PluginHookError)?;
            let normal = unary
                .as_ref()
                .map(|e| sif_pure_expression(e, false, &function_names, &fields))
                .transpose()
                .map_err(PluginHookError)?;
            let prime = unary
                .as_ref()
                .map(|e| sif_pure_expression(e, true, &function_names, &fields))
                .transpose()
                .map_err(PluginHookError)?;
            predicates.push(predicate.copy_with(|p| p.body = normal));
            predicates.push(predicate.copy_with(|p| {
                p.name = name.clone();
                p.body = prime;
            }));
            if predicate.body.is_some() {
                if low_predicates.contains(&predicate.name) {
                    functions.push(
                        predicate_low_function(
                            predicate,
                            &function_names,
                            &fields,
                            &input,
                            &mut generator,
                        )
                        .map_err(PluginHookError)?,
                    );
                } else {
                    for parameter in &predicate.formal_args {
                        let _ = generator.get_unused_name(&parameter.name);
                    }
                }
            }
        }
        let mut methods = Vec::new();
        for method in &input.methods {
            if method
                .formal_args
                .iter()
                .chain(&method.formal_returns)
                .any(|a| !sif_supported_type(&a.typ))
            {
                return Err(PluginHookError(
                    "SIF method result or type outside supported fragment".into(),
                ));
            }
            let first = LocalVarDecl::new(
                generator.get_unused_name("p1"),
                Type::Bool,
                Metadata::default(),
            );
            let second = LocalVarDecl::new(
                generator.get_unused_name("p2"),
                Type::Bool,
                Metadata::default(),
            );
            let _ = generator.get_unused_name("t1");
            let _ = generator.get_unused_name("t2");
            let mut names = function_names.clone();
            let mut args = vec![first.clone(), second.clone()];
            for arg in &method.formal_args {
                let name = generator.get_unused_name(&arg.name);
                names.insert(arg.name.clone(), name.clone());
                args.push(arg.clone());
                args.push(LocalVarDecl::new(name, arg.typ.clone(), arg.meta.clone()));
            }
            let _ = generator.get_unused_name("t1");
            let _ = generator.get_unused_name("t2");
            let mut returns = Vec::new();
            for ret in &method.formal_returns {
                if names.contains_key(&ret.name) {
                    return Err(PluginHookError("SIF duplicate formal name".into()));
                }
                let name = generator.get_unused_name(&ret.name);
                names.insert(ret.name.clone(), name.clone());
                returns.push(ret.clone());
                returns.push(LocalVarDecl::new(name, ret.typ.clone(), ret.meta.clone()));
            }
            let first_exp = Exp::new(ExpKind::LocalVar(first.local_var()), Metadata::default());
            let second_exp = Exp::new(ExpKind::LocalVar(second.local_var()), Metadata::default());
            let mut pres: Vec<Exp> = method
                .pres
                .iter()
                .map(|e| {
                    sif_assertion(e, &first_exp, &second_exp, &names, &fields, &low_predicates)
                })
                .collect::<Result<_, _>>()
                .map_err(PluginHookError)?;
            let mut posts: Vec<Exp> = method
                .posts
                .iter()
                .map(|e| {
                    sif_assertion(e, &first_exp, &second_exp, &names, &fields, &low_predicates)
                })
                .collect::<Result<_, _>>()
                .map_err(PluginHookError)?;
            let mut terminates = None;
            for pre in &method.pres {
                last_sif_termination(&Node::Exp(pre.clone()), &mut terminates)
                    .map_err(PluginHookError)?;
            }
            if let Some(terminates) = terminates {
                use super::sif_ast_extensions::{SifExpression, SifExpressionKind};
                use super::sif_error::SifTerminationReasonKind;
                use crate::ast::ast::ErrorTrafo;
                pres.extend(
                    termination_channel_checks(
                        &terminates,
                        &first_exp,
                        &second_exp,
                        &names,
                        &fields,
                        &low_predicates,
                        None,
                    )
                    .map_err(PluginHookError)?,
                );
                pres = simplify_sif_conditions(pres).map_err(PluginHookError)?;
                let ExpKind::Extension(extension) = terminates.kind() else {
                    return Err(PluginHookError("invalid SIF termination expression".into()));
                };
                let Some(SifExpression {
                    kind: SifExpressionKind::Terminates { condition },
                    ..
                }) = extension.0.as_any().downcast_ref::<SifExpression>()
                else {
                    return Err(PluginHookError("invalid SIF termination expression".into()));
                };
                let trafo = std::sync::Arc::new(TerminationChannelTrafo {
                    expression: terminates.clone(),
                    offending_node: Node::Exp(condition.clone()),
                    reason: SifTerminationReasonKind::ConditionNotTight,
                });
                let mut meta = condition.metadata().clone();
                meta.error_trafo =
                    ErrorTrafo::trafos(vec![trafo], vec![], None).combine(&meta.error_trafo);
                let old = Exp::new(ExpKind::Old(condition.clone()), meta);
                posts.push(
                    sif_assertion(
                        &old,
                        &first_exp,
                        &second_exp,
                        &names,
                        &fields,
                        &low_predicates,
                    )
                    .map_err(PluginHookError)?,
                );
            }
            let body = method
                .body
                .as_ref()
                .map(|body| {
                    let flags = if contains_sif_return(&Node::Stmt(body.clone()))? {
                        let ret1 = LocalVarDecl::new(
                            generator.get_unused_name("ret1"),
                            Type::Bool,
                            Metadata::default(),
                        );
                        let ret2 = LocalVarDecl::new(
                            generator.get_unused_name("ret2"),
                            Type::Bool,
                            Metadata::default(),
                        );
                        names.insert(ret1.name.clone(), ret2.name.clone());
                        Some((ret1, ret2))
                    } else {
                        None
                    };
                    let transformed = sif_assertion_block(
                        body,
                        &first_exp,
                        &second_exp,
                        &mut names,
                        &fields,
                        &low_predicates,
                        flags.as_ref(),
                        &mut generator,
                    )?;
                    let mut statements = vec![Stmt::new(
                        StmtKind::Inhale(first_exp.clone()),
                        Metadata::default(),
                    )];
                    let mut declarations = Vec::new();
                    if let Some((ret1, ret2)) = flags {
                        for ret in [ret1, ret2] {
                            statements.push(Stmt::new(
                                StmtKind::LocalVarAssign {
                                    lhs: ret.local_var(),
                                    rhs: Exp::new(ExpKind::FalseLit, Metadata::default()),
                                },
                                Metadata::default(),
                            ));
                            declarations.push(crate::ast::program::Declaration::Local(ret));
                        }
                    }
                    statements.push(transformed);
                    Ok::<_, String>(Stmt::new(
                        StmtKind::Seqn {
                            statements,
                            declarations,
                        },
                        Metadata::default(),
                    ))
                })
                .transpose()
                .map_err(PluginHookError)?;
            methods.push(Method::new(MethodData {
                name: method.name.clone(),
                formal_args: args,
                formal_returns: returns,
                pres,
                posts,
                body,
                meta: method.meta.clone(),
            }));
        }
        Ok(input.copy_with(|p| {
            p.domains = input.domains.iter().map(|d| d.copy_with(|_| {})).collect();
            p.methods = methods;
            p.fields = product_fields;
            p.functions = functions;
            p.predicates = predicates;
        }))
    }
}
