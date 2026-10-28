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
//! implemented, including heap-dependent function and unary predicate duplication. Relational
//! predicates, loops and other relational forms remain explicitly unsupported.

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
    fn false_inhale_is_preserved_unguarded() {
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
            &mut NameTransformer::default(),
        )
        .unwrap();
        assert!(
            matches!(product.kind(), StmtKind::Seqn { statements, .. } if statements.len() == 1 && statements[0].same_node(&original))
        );
    }
}

/// Concrete source product construction for a pure method fragment. Every other
/// source product is rejected until its corresponding transformer is implemented.
#[derive(Default)]
pub struct NativeSifTransformer;

fn sif_supported_type(typ: &crate::ast::r#type::Type) -> bool {
    use crate::ast::r#type::Type;
    match typ {
        Type::Int | Type::Bool | Type::Ref => true,
        Type::Seq(inner) | Type::Set(inner) | Type::Multiset(inner) => sif_supported_type(inner),
        Type::Map(pair) => sif_supported_type(&pair.0) && sif_supported_type(&pair.1),
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
    let meta =
        if prime && matches!(exp.kind(), ExpKind::FuncApp(name, _) if names.contains_key(name)) {
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
                sif_assertion(left, first, second, names, fields)?,
                sif_assertion(right, first, second, names, fields)?,
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
                    sif_assertion(body, first, second, names, fields)?,
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
                    sif_assertion(left, first, second, names, fields)?,
                    sif_assertion(right, first, second, names, fields)?,
                ),
                forwarded(),
            ))
        }
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
                SifExpressionKind::LowEvent => Ok(Exp::new(
                    ExpKind::EqCmp(first.clone(), second.clone()),
                    forwarded(),
                )),
                _ => Err("SIF relational expression outside the supported product fragment".into()),
            }
        }
        _ => {
            let normal = sif_pure_expression(exp, false, names, fields)?;
            let primed = sif_pure_expression(exp, true, names, fields)?;
            let left = Exp::new(ExpKind::Implies(first.clone(), normal), forwarded());
            let right = Exp::new(ExpKind::Implies(second.clone(), primed), forwarded());
            Ok(Exp::new(ExpKind::And(left, right), forwarded()))
        }
    }
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

fn sif_assertion_block(
    stmt: &crate::ast::statement::Stmt,
    first: &Exp,
    second: &Exp,
    names: &mut HashMap<String, String>,
    fields: &HashMap<String, crate::ast::program::Field>,
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
            StmtKind::Inhale(exp) if matches!(exp.kind(), ExpKind::FalseLit) => {
                flush(&mut normal, &mut primed, &mut result);
                result.push(current.clone());
            }
            StmtKind::Inhale(exp) | StmtKind::Exhale(exp) => {
                if !is_directly_unary(exp, &SifConfig::default())
                    .map_err(|e| format!("SIF expression traversal: {e:?}"))?
                {
                    flush(&mut normal, &mut primed, &mut result);
                    let translated = sif_assertion(exp, first, second, names, fields)?;
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
                    generator,
                )?);
                branches.push(sif_assertion_block(
                    else_branch,
                    &refs[2],
                    &refs[3],
                    names,
                    fields,
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
            StmtKind::Assert(exp) => {
                flush(&mut normal, &mut primed, &mut result);
                result.push(Stmt::new(
                    StmtKind::Assert(sif_assertion(exp, first, second, names, fields)?),
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
                let statements = if matches!(current.kind(), StmtKind::Fold(_)) {
                    vec![first_branch, second_branch, skip.clone()]
                } else {
                    vec![skip.clone(), first_branch, second_branch]
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
                flush(&mut normal, &mut primed, &mut result);
                if let Some(refute) = extension.0.as_any().downcast_ref::<Refute>() {
                    result.push(
                        Refute::new(
                            sif_assertion(&refute.exp, first, second, names, fields)?,
                            sif_forward_meta(Node::Stmt(current.clone()), current.metadata()),
                        )
                        .statement(),
                    );
                } else if let Some(SifStatement {
                    kind: SifStatementKind::Declassify(exp),
                    ..
                }) = extension.0.as_any().downcast_ref::<SifStatement>()
                {
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
        if enable_timing || !input.domains.is_empty() || !input.extensions.is_empty() {
            return Err(PluginHookError(
                "SIF program outside the supported pure method fragment".into(),
            ));
        }
        if !source_relational_predicates(&input, &SifConfig::default())
            .map_err(|e| PluginHookError(format!("SIF relational predicate analysis: {e:?}")))?
            .is_empty()
        {
            return Err(PluginHookError(
                "SIF relational predicates are outside the supported product fragment".into(),
            ));
        }
        let occupied_globals: HashSet<_> = input
            .fields
            .iter()
            .map(|field| field.name.as_str())
            .chain(input.methods.iter().map(|method| method.name.as_str()))
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
            let normal = predicate
                .body
                .as_ref()
                .map(|e| sif_pure_expression(e, false, &function_names, &fields))
                .transpose()
                .map_err(PluginHookError)?;
            let prime = predicate
                .body
                .as_ref()
                .map(|e| sif_pure_expression(e, true, &function_names, &fields))
                .transpose()
                .map_err(PluginHookError)?;
            predicates.push(predicate.copy_with(|p| p.body = normal));
            predicates.push(predicate.copy_with(|p| {
                p.name = name.clone();
                p.body = prime;
            }));
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
            let pres = method
                .pres
                .iter()
                .map(|e| sif_assertion(e, &first_exp, &second_exp, &names, &fields))
                .collect::<Result<_, _>>()
                .map_err(PluginHookError)?;
            let posts = method
                .posts
                .iter()
                .map(|e| sif_assertion(e, &first_exp, &second_exp, &names, &fields))
                .collect::<Result<_, _>>()
                .map_err(PluginHookError)?;
            let body = method
                .body
                .as_ref()
                .map(|body| {
                    let transformed = sif_assertion_block(
                        body,
                        &first_exp,
                        &second_exp,
                        &mut names,
                        &fields,
                        &mut generator,
                    )?;
                    Ok::<_, String>(Stmt::new(
                        StmtKind::Seqn {
                            statements: vec![
                                Stmt::new(StmtKind::Inhale(first_exp.clone()), Metadata::default()),
                                transformed,
                            ],
                            declarations: vec![],
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
            p.methods = methods;
            p.fields = product_fields;
            p.functions = functions;
            p.predicates = predicates;
        }))
    }
}
