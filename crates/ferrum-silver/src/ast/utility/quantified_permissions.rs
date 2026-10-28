//! Quantified permission assertions and dependency-aware resource discovery.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/QuantifiedPermissions.scala
//! Status: partial; assertion extraction, resource discovery and common desugaring are implemented.
//! Extension trigger reconstruction remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::nodes::{Node, ReferencedMemberError, TraversalError, referenced_members, subnodes};
use crate::ast::{
    expression::{Exp, ExpKind},
    program::{Field, Member, Predicate, Program},
};
use std::collections::VecDeque;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuantifiedPermissionError {
    Traversal(TraversalError),
    Reference(ReferencedMemberError),
    MissingPredicate(String),
    Wand(super::expressions::MagicWandError),
    Projection(super::expressions::UnsupportedExtensionProjection),
    Replacement(super::rewriter::strategy::ExpressionReplacementError),
    Trigger(super::triggers::TriggerGenerationError),
    DesugarUnsupported(&'static str),
}
impl From<TraversalError> for QuantifiedPermissionError {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
impl From<ReferencedMemberError> for QuantifiedPermissionError {
    fn from(e: ReferencedMemberError) -> Self {
        Self::Reference(e)
    }
}
impl From<super::expressions::MagicWandError> for QuantifiedPermissionError {
    fn from(e: super::expressions::MagicWandError) -> Self {
        Self::Wand(e)
    }
}

/// Return forall and its implication; synthesize true and implication with forall metadata when absent.
pub fn source_quantified_permission_assertion(forall: &Exp) -> Option<(Exp, Exp)> {
    let ExpKind::Forall(_, _, body) = forall.kind() else {
        return None;
    };
    let implication = if matches!(body.kind(), ExpKind::Implies(..)) {
        body.clone()
    } else {
        let yes = Exp::new(ExpKind::TrueLit, forall.metadata().clone());
        Exp::new(
            ExpKind::Implies(yes, body.clone()),
            forall.metadata().clone(),
        )
    };
    Some((forall.clone(), implication))
}
pub fn quantified_permission_assertion(forall: &Exp) -> Option<(Exp, Exp, Exp)> {
    let (forall, implication) = source_quantified_permission_assertion(forall)?;
    let ExpKind::Implies(condition, resource) = implication.kind() else {
        unreachable!()
    };
    matches!(
        resource.kind(),
        ExpKind::FieldAccessPredicate(..)
            | ExpKind::PredicateAccessPredicate(..)
            | ExpKind::MagicWand(..)
    )
    .then(|| (forall, condition.clone(), resource.clone()))
}
fn visit(
    node: &Node,
    f: &mut impl FnMut(&Node) -> Result<(), QuantifiedPermissionError>,
) -> Result<(), QuantifiedPermissionError> {
    f(node)?;
    for child in subnodes(node)? {
        visit(&child, f)?;
    }
    Ok(())
}
fn dependencies(
    root: &Member,
    program: &Program,
    mut collect: impl FnMut(&Node) -> Result<(), QuantifiedPermissionError>,
) -> Result<(), QuantifiedPermissionError> {
    let mut visited = Vec::<Member>::new();
    let mut queue = VecDeque::from([root.clone()]);
    queue.extend(referenced_members(&Node::Member(root.clone()), program)?);
    while let Some(current) = queue.pop_front() {
        let relevant: Vec<Node> = match &current {
            Member::Method(m) if current != *root => m
                .pres
                .iter()
                .chain(&m.posts)
                .cloned()
                .map(Node::Exp)
                .collect(),
            Member::Function(f) if current != *root => f
                .pres
                .iter()
                .chain(&f.posts)
                .cloned()
                .map(Node::Exp)
                .collect(),
            _ => vec![Node::Member(current.clone())],
        };
        visited.push(current);
        for node in relevant {
            collect(&node)?;
            for member in referenced_members(&node, program)? {
                if !visited.contains(&member) {
                    queue.push_back(member);
                }
            }
        }
    }
    Ok(())
}
pub fn quantified_fields(
    root: &Member,
    program: &Program,
) -> Result<Vec<Field>, QuantifiedPermissionError> {
    let mut collected = Vec::new();
    dependencies(root, program, |node| {
        visit(node, &mut |node| {
            if let Node::Exp(e) = node {
                if let Some((_, _, a)) = quantified_permission_assertion(e) {
                    if let ExpKind::FieldAccessPredicate(loc, _) = a.kind() {
                        if !collected.contains(&loc.field) {
                            collected.push(loc.field.clone());
                        }
                        return Ok(());
                    }
                }
                if let ExpKind::Forall(_, triggers, _) | ExpKind::Exists(_, triggers, _) = e.kind()
                {
                    for t in triggers {
                        for e in &t.exps {
                            if let ExpKind::FieldAccess(loc) = e.kind() {
                                if !collected.contains(&loc.field) {
                                    collected.push(loc.field.clone());
                                }
                            }
                        }
                    }
                }
            }
            Ok(())
        })
    })?;
    Ok(collected)
}
pub fn quantified_predicates(
    root: &Member,
    program: &Program,
) -> Result<Vec<Predicate>, QuantifiedPermissionError> {
    let mut collected = Vec::new();
    let mut add = |name: &str| -> Result<(), QuantifiedPermissionError> {
        let pred = program
            .find_predicate_optionally(name)
            .ok_or_else(|| QuantifiedPermissionError::MissingPredicate(name.into()))?;
        if !collected.contains(pred) {
            collected.push(pred.clone());
        }
        Ok(())
    };
    dependencies(root, program, |node| {
        visit(node, &mut |node| {
            if let Node::Exp(e) = node {
                if let Some((_, _, a)) = quantified_permission_assertion(e) {
                    if let ExpKind::PredicateAccessPredicate(p) = a.kind() {
                        add(&p.location.predicate_name)?;
                        return Ok(());
                    }
                }
                if let ExpKind::Forall(_, triggers, _) | ExpKind::Exists(_, triggers, _) = e.kind()
                {
                    for t in triggers {
                        for e in &t.exps {
                            if let ExpKind::PredicateAccess(p) = e.kind() {
                                add(&p.predicate_name)?;
                            }
                        }
                    }
                }
            }
            Ok(())
        })
    })?;
    Ok(collected)
}
pub fn quantified_magic_wands(
    root: &Node,
    program: &Program,
) -> Result<Vec<Exp>, QuantifiedPermissionError> {
    let mut result = Vec::new();
    let mut add = |wand: &Exp| -> Result<(), QuantifiedPermissionError> {
        let structure = wand.magic_wand_structure(program, false)?;
        if !result.contains(&structure) {
            result.push(structure);
        }
        Ok(())
    };
    visit(root, &mut |node| {
        if let Node::Exp(e) = node {
            if let Some((_, _, a)) = quantified_permission_assertion(e) {
                if matches!(a.kind(), ExpKind::MagicWand(..)) {
                    add(&a)?;
                    return Ok(());
                }
            }
            if let ExpKind::Forall(_, triggers, _) | ExpKind::Exists(_, triggers, _) = e.kind() {
                for t in triggers {
                    for e in &t.exps {
                        if matches!(e.kind(), ExpKind::MagicWand(..)) {
                            add(e)?;
                        }
                    }
                }
            }
        }
        Ok(())
    })?;
    Ok(result)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Resource {
    Field(Field),
    Predicate(Predicate),
    MagicWand(Exp),
}
pub fn resource_triggers(
    root: &Member,
    program: &Program,
) -> Result<Vec<Resource>, QuantifiedPermissionError> {
    let mut result = Vec::new();
    dependencies(root, program, |node| {
        visit(node, &mut |node| {
            if let Node::Exp(e) = node {
                if let ExpKind::Forall(_, triggers, _) | ExpKind::Exists(_, triggers, _) = e.kind()
                {
                    for t in triggers {
                        for term in &t.exps {
                            let resource = match term.kind() {
                                ExpKind::FieldAccess(f) => Some(Resource::Field(f.field.clone())),
                                ExpKind::PredicateAccess(p) => Some(Resource::Predicate(
                                    program
                                        .find_predicate_optionally(&p.predicate_name)
                                        .ok_or_else(|| {
                                            QuantifiedPermissionError::MissingPredicate(
                                                p.predicate_name.clone(),
                                            )
                                        })?
                                        .clone(),
                                )),
                                ExpKind::MagicWand(..) => Some(Resource::MagicWand(term.clone())),
                                _ => None,
                            };
                            if let Some(resource) = resource {
                                if !result.contains(&resource) {
                                    result.push(resource);
                                }
                            }
                        }
                    }
                }
            }
            Ok(())
        })
    })?;
    Ok(result)
}

fn position_info(node: &Exp) -> crate::ast::ast::Metadata {
    crate::ast::ast::Metadata {
        position: node.metadata().position.clone(),
        info: node.metadata().info.clone(),
        ..Default::default()
    }
}
fn conjunction(left: &Exp, right: &Exp) -> Exp {
    Exp::new(
        ExpKind::And(left.clone(), right.clone()),
        crate::ast::ast::Metadata {
            position: left.metadata().position.clone(),
            info: crate::ast::ast::Info::pair(
                left.metadata().info.clone(),
                right.metadata().info.clone(),
            ),
            ..Default::default()
        },
    )
}
pub fn do_desugar_source_quantified_permission_syntax(
    source: &Exp,
) -> Result<Vec<Exp>, QuantifiedPermissionError> {
    let ExpKind::Forall(vars, triggers, _) = source.kind() else {
        return Err(QuantifiedPermissionError::DesugarUnsupported(
            "expected Forall",
        ));
    };
    let (_, implication) = source_quantified_permission_assertion(source).expect("forall");
    let ExpKind::Implies(cond, rhs) = implication.kind() else {
        unreachable!()
    };
    if rhs.is_pure() {
        return Ok(vec![source.clone()]);
    }
    let make = |condition: Exp, body: Exp| {
        Exp::new(
            ExpKind::Forall(
                vars.clone(),
                triggers.clone(),
                Exp::new(ExpKind::Implies(condition, body), position_info(rhs)),
            ),
            position_info(source),
        )
    };
    match rhs.kind() {
        ExpKind::And(a, b) => {
            let mut first =
                do_desugar_source_quantified_permission_syntax(&make(cond.clone(), a.clone()))?;
            first.extend(do_desugar_source_quantified_permission_syntax(&make(
                cond.clone(),
                b.clone(),
            ))?);
            Ok(first)
        }
        ExpKind::Implies(a, b) => {
            do_desugar_source_quantified_permission_syntax(&make(conjunction(cond, a), b.clone()))
        }
        ExpKind::CondExp(b, a, c) => {
            let neg = Exp::new(ExpKind::Not(b.clone()), position_info(b));
            let mut first = do_desugar_source_quantified_permission_syntax(&make(
                conjunction(cond, b),
                a.clone(),
            ))?;
            first.extend(do_desugar_source_quantified_permission_syntax(&make(
                conjunction(cond, &neg),
                c.clone(),
            ))?);
            Ok(first)
        }
        ExpKind::Forall(nested_vars, nested_triggers, _) => {
            let generated;
            let nested_triggers = if nested_triggers.is_empty() {
                generated = super::triggers::auto_trigger(rhs)
                    .map_err(QuantifiedPermissionError::Trigger)?;
                let ExpKind::Forall(_, generated_triggers, _) = generated.kind() else {
                    unreachable!()
                };
                generated_triggers
            } else {
                nested_triggers
            };
            let (_, nested_implication) =
                source_quantified_permission_assertion(rhs).expect("forall");
            let ExpKind::Implies(nested_cond, nested_rhs) = nested_implication.kind() else {
                unreachable!()
            };
            let mut all_vars = vars.clone();
            all_vars.extend(nested_vars.iter().cloned());
            let mut all_triggers = Vec::new();
            for outer in triggers {
                for inner in nested_triggers {
                    let mut exps = outer.exps.clone();
                    exps.extend(inner.exps.iter().cloned());
                    all_triggers.push(crate::ast::expression::Trigger::new(
                        exps,
                        crate::ast::ast::Metadata {
                            position: outer.meta.position.clone(),
                            info: crate::ast::ast::Info::pair(
                                outer.meta.info.clone(),
                                inner.meta.info.clone(),
                            ),
                            error_trafo: outer.meta.error_trafo.combine(&inner.meta.error_trafo),
                        },
                    ));
                }
            }
            let new_body = Exp::new(
                ExpKind::Implies(conjunction(cond, nested_cond), nested_rhs.clone()),
                rhs.metadata().clone(),
            );
            let meta = crate::ast::ast::Metadata {
                position: source.metadata().position.clone(),
                info: crate::ast::ast::Info::pair(
                    source.metadata().info.clone(),
                    rhs.metadata().info.clone(),
                ),
                error_trafo: source
                    .metadata()
                    .error_trafo
                    .combine(&rhs.metadata().error_trafo),
            };
            do_desugar_source_quantified_permission_syntax(&Exp::new(
                ExpKind::Forall(all_vars, all_triggers, new_body),
                meta,
            ))
        }
        ExpKind::Let(var, value, body) => {
            use super::rewriter::strategy::replace_expressions;
            let forall = Exp::new(
                ExpKind::Forall(vars.clone(), triggers.clone(), body.clone()),
                position_info(source),
            );
            let local = var.local_var();
            let local_exp = Exp::new(ExpKind::LocalVar(local.clone()), local.meta.clone());
            let replacements = [(local_exp, value.clone())];
            let mut result = Vec::new();
            for inner in do_desugar_source_quantified_permission_syntax(&forall)? {
                let ExpKind::Forall(inner_vars, inner_triggers, inner_body) = inner.kind() else {
                    return Err(QuantifiedPermissionError::DesugarUnsupported(
                        "let desugaring did not yield forall",
                    ));
                };
                let (_, implication) =
                    source_quantified_permission_assertion(&inner).expect("forall");
                let ExpKind::Implies(inner_cond, inner_rhs) = implication.kind() else {
                    unreachable!()
                };
                if !inner_rhs.is_pure() {
                    let mut new_triggers = Vec::new();
                    for trigger in inner_triggers {
                        let exps = trigger
                            .exps
                            .iter()
                            .map(|e| {
                                replace_expressions(e, &replacements)
                                    .map_err(QuantifiedPermissionError::Replacement)
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        new_triggers.push(if exps == trigger.exps {
                            trigger.clone()
                        } else {
                            crate::ast::expression::Trigger::new(exps, trigger.meta.clone())
                        });
                    }
                    let inner_rhs = replace_expressions(inner_rhs, &replacements)
                        .map_err(QuantifiedPermissionError::Replacement)?;
                    let wrapped = Exp::new(
                        ExpKind::Let(var.clone(), value.clone(), inner_cond.clone()),
                        rhs.metadata().clone(),
                    );
                    let condition =
                        Exp::new(ExpKind::And(cond.clone(), wrapped), rhs.metadata().clone());
                    let result_body = Exp::new(
                        ExpKind::Implies(condition, inner_rhs),
                        inner.metadata().clone(),
                    );
                    result.push(Exp::new(
                        ExpKind::Forall(inner_vars.clone(), new_triggers, result_body),
                        inner.metadata().clone(),
                    ));
                } else {
                    let ExpKind::Implies(inner_cond, inner_body) = inner_body.kind() else {
                        return Err(QuantifiedPermissionError::DesugarUnsupported(
                            "pure let desugaring lacks implication",
                        ));
                    };
                    let implication = Exp::new(
                        ExpKind::Implies(inner_cond.clone(), inner_body.clone()),
                        position_info(rhs),
                    );
                    let wrapped = Exp::new(
                        ExpKind::Let(var.clone(), value.clone(), implication),
                        rhs.metadata().clone(),
                    );
                    let result_body = Exp::new(
                        ExpKind::Implies(cond.clone(), wrapped),
                        rhs.metadata().clone(),
                    );
                    result.push(Exp::new(
                        ExpKind::Forall(inner_vars.clone(), inner_triggers.clone(), result_body),
                        position_info(&inner),
                    ));
                }
            }
            Ok(result)
        }
        _ => Ok(vec![source.clone()]),
    }
}
pub fn desugar_source_quantified_permission_syntax(
    source: &Exp,
) -> Result<Vec<Exp>, QuantifiedPermissionError> {
    let inhale =
        super::expressions::when_inhaling(source).map_err(QuantifiedPermissionError::Projection)?;
    if inhale == *source {
        return do_desugar_source_quantified_permission_syntax(source);
    }
    let exhale =
        super::expressions::when_exhaling(source).map_err(QuantifiedPermissionError::Projection)?;
    let mut result = Vec::new();
    for e in do_desugar_source_quantified_permission_syntax(&inhale)? {
        let yes = Exp::new(ExpKind::TrueLit, position_info(source));
        result.push(Exp::new(
            ExpKind::InhaleExhaleExp(e, yes),
            position_info(source),
        ));
    }
    for e in do_desugar_source_quantified_permission_syntax(&exhale)? {
        let yes = Exp::new(ExpKind::TrueLit, position_info(source));
        result.push(Exp::new(
            ExpKind::InhaleExhaleExp(yes, e),
            position_info(source),
        ));
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        expression::{FieldAccess, LocalVar, Trigger},
        program::Method,
        r#type::Type,
    };
    #[test]
    fn quantified_field_match_takes_precedence_over_its_trigger_case() {
        let meta = Metadata::default();
        let field = |name: &str| {
            Field::new(crate::ast::program::FieldData {
                name: name.into(),
                typ: Type::Int,
                meta: meta.clone(),
            })
        };
        let receiver = Exp::new(
            ExpKind::LocalVar(LocalVar::new("r".into(), Type::Ref, meta.clone())),
            meta.clone(),
        );
        let a = FieldAccess::new(receiver.clone(), field("a"), meta.clone());
        let b = FieldAccess::new(receiver, field("b"), meta.clone());
        let body = Exp::new(ExpKind::FieldAccessPredicate(a, None), meta.clone());
        let trigger = Trigger::new(
            vec![Exp::new(ExpKind::FieldAccess(b), meta.clone())],
            meta.clone(),
        );
        let quantifier = Exp::new(ExpKind::Forall(vec![], vec![trigger], body), meta.clone());
        let method = Member::Method(Method::new(crate::ast::program::MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![quantifier],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        }));
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], meta);
        let fields = quantified_fields(&method, &program).unwrap();
        assert_eq!(
            fields.iter().map(|f| f.name.as_str()).collect::<Vec<_>>(),
            vec!["a"]
        );
    }
}

#[cfg(test)]
mod let_desugar_tests {
    use super::*;
    use crate::ast::{ast::Metadata, expression::LocalVar, program::LocalVarDecl, r#type::Type};
    #[test]
    fn unhandled_impure_extension_preserves_original_forall() {
        use crate::plugin::sif::sif_ast_extensions::{SifExpression, SifExpressionKind};
        let meta = Metadata::default();
        let extension = SifExpression {
            kind: SifExpressionKind::LowExit,
            meta: meta.clone(),
        }
        .expression()
        .unwrap();
        assert!(!extension.is_pure());
        let body = Exp::new(
            ExpKind::Implies(Exp::new(ExpKind::TrueLit, meta.clone()), extension),
            meta.clone(),
        );
        let original = Exp::new(ExpKind::Forall(vec![], vec![], body), meta);
        let result = do_desugar_source_quantified_permission_syntax(&original).unwrap();
        assert_eq!(result.len(), 1);
        assert!(result[0].same_node(&original));
    }
    #[test]
    fn let_binding_expands_in_impure_resource_but_remains_in_condition() {
        let m = Metadata::default();
        let var = LocalVarDecl::new("x".into(), Type::Int, m.clone());
        let x = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Int, m.clone())),
            m.clone(),
        );
        let value = Exp::new(ExpKind::IntLit(7.into()), m.clone());
        let assertion = Exp::new(ExpKind::EqCmp(x.clone(), x), m.clone());
        let wand = Exp::new(
            ExpKind::MagicWand(assertion, Exp::new(ExpKind::TrueLit, m.clone())),
            m.clone(),
        );
        let bound = Exp::new(ExpKind::Let(var, value, wand), m.clone());
        let source = Exp::new(
            ExpKind::Forall(
                vec![],
                vec![],
                Exp::new(
                    ExpKind::Implies(Exp::new(ExpKind::TrueLit, m.clone()), bound),
                    m.clone(),
                ),
            ),
            m,
        );
        let result = do_desugar_source_quantified_permission_syntax(&source).unwrap();
        let ExpKind::Forall(_, _, body) = result[0].kind() else {
            panic!("forall")
        };
        let ExpKind::Implies(condition, resource) = body.kind() else {
            panic!("implication")
        };
        assert!(
            matches!(condition.kind(), ExpKind::And(_, e) if matches!(e.kind(), ExpKind::Let(..)))
        );
        assert!(
            matches!(resource.kind(), ExpKind::MagicWand(e, _) if matches!(e.kind(), ExpKind::EqCmp(a, b) if matches!(a.kind(), ExpKind::IntLit(_)) && matches!(b.kind(), ExpKind::IntLit(_))))
        );
    }
}
