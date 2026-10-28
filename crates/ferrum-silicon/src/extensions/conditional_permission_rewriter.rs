//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/extensions/ConditionalPermissionRewriter.scala
//!
//! Purpose:
//! Rewrite conditional accessibility into conditional permissions when well-defined.
//!
//! Planned Rust structure:
//! Port ConditionalPermissionRewriter, Condition, ternaryRewriter, contextual rewriter,
//! conditionalize and makeCondExp.
//!
//! Behavior to preserve:
//! First split impure ternaries into implication conjunctions when condition lacks permission
//! introspection; then rewrite functions separately from predicates/methods, honoring function
//! wildcard option. Do not push through permission introspection, wildcard where forbidden, or
//! unsafe let-bound expressions; skip triggers and access children. For unsafe field receivers use
//! conditional null; unsafe predicate arguments and wands retain implication. Preserve metadata
//! and seen-node guard.
//!
//! Integration:
//! ferrum_silver::ast::utility::{expressions,rewriter}, Silicon verifier preprocessing/config.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for contextual rewrites, metadata and AST identity.
//!
//! Open decisions:
//! Agree on proof-obligation and expression identity semantics with Silver rewriter and verifier.
//!
//! Status: partial; program ternary and contextual permission rewriting are implemented.
//! Extension reconstruction and full upstream edge-case validation remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2020 ETH Zurich.

use ferrum_silver::ast::ast::Metadata;
use ferrum_silver::ast::expression::{Exp, ExpKind, FieldAccess, Trigger};
use ferrum_silver::ast::program::{Member, Program};
use ferrum_silver::ast::statement::PredicateAccessPredicate;
use ferrum_silver::ast::utility::{
    expressions,
    nodes::{self, Node, NodeReplacementError},
    statements::StatementReplacementError,
    viper_strategy,
};

#[derive(Clone, Debug)]
pub struct ConditionalPermissionError(pub String);
impl From<NodeReplacementError> for ConditionalPermissionError {
    fn from(e: NodeReplacementError) -> Self {
        Self(format!("{e:?}"))
    }
}
impl From<StatementReplacementError> for ConditionalPermissionError {
    fn from(e: StatementReplacementError) -> Self {
        Self(format!("{e:?}"))
    }
}
fn failure(e: impl std::fmt::Debug) -> ConditionalPermissionError {
    ConditionalPermissionError(format!("{e:?}"))
}
fn make(kind: ExpKind, meta: &Metadata) -> Exp {
    Exp::new(kind, meta.clone())
}
fn direct(old: &Exp, new: Exp) -> Result<Exp, ConditionalPermissionError> {
    match viper_strategy::preserve_metadata(&Node::Exp(old.clone()), &Node::Exp(new), true)
        .map_err(failure)?
    {
        Node::Exp(e) => Ok(e),
        _ => Err(ConditionalPermissionError(
            "expression metadata replacement".into(),
        )),
    }
}
fn no_introspection(e: &Exp) -> Result<bool, ConditionalPermissionError> {
    expressions::contains_permission_introspection(e)
        .map(|b| !b)
        .map_err(failure)
}
fn no_obligations(e: &Exp, p: &Program) -> Result<bool, ConditionalPermissionError> {
    expressions::proof_obligations(e, p)
        .map(|x| x.is_empty())
        .map_err(failure)
}
fn contains_wildcard(e: &Exp) -> Result<bool, ConditionalPermissionError> {
    fn walk(n: &Node) -> Result<bool, ConditionalPermissionError> {
        if matches!(n, Node::Exp(e) if matches!(e.kind(), ExpKind::WildcardPerm)) {
            return Ok(true);
        }
        for child in nodes::subnodes(n).map_err(failure)? {
            if walk(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    walk(&Node::Exp(e.clone()))
}
#[derive(Clone, Default)]
struct Condition(Option<Exp>);
impl Condition {
    fn add(&self, e: &Exp) -> Self {
        Self(Some(match &self.0 {
            None => e.clone(),
            Some(c) => make(ExpKind::And(c.clone(), e.clone()), e.metadata()),
        }))
    }
    fn expression(&self) -> Exp {
        self.0
            .clone()
            .unwrap_or_else(|| Exp::new(ExpKind::TrueLit, Metadata::default()))
    }
}
fn conditionalize(
    acc: &Exp,
    cond: &Condition,
    function: bool,
    program: &Program,
) -> Result<Exp, ConditionalPermissionError> {
    let condition = cond.expression();
    let default = Exp::new(
        if function {
            ExpKind::WildcardPerm
        } else {
            ExpKind::FullPerm
        },
        Metadata::default(),
    );
    let conditional = |value: Exp, otherwise: Exp| {
        make(
            ExpKind::CondExp(condition.clone(), value.clone(), otherwise),
            value.metadata(),
        )
    };
    let result = match acc.kind() {
        ExpKind::FieldAccessPredicate(location, permission) => {
            let receiver = if no_obligations(&location.receiver, program)? {
                location.receiver.clone()
            } else {
                conditional(
                    location.receiver.clone(),
                    Exp::new(ExpKind::NullLit, Metadata::default()),
                )
            };
            let location = if receiver == location.receiver {
                location.clone()
            } else {
                FieldAccess::new(receiver, location.field.clone(), location.meta.clone())
            };
            let permission = conditional(
                permission.clone().unwrap_or(default),
                Exp::new(ExpKind::NoPerm, Metadata::default()),
            );
            make(
                ExpKind::FieldAccessPredicate(location, Some(permission)),
                acc.metadata(),
            )
        }
        ExpKind::PredicateAccessPredicate(predicate) => {
            let mut safe = true;
            for arg in &predicate.location.args {
                if !no_obligations(arg, program)? {
                    safe = false;
                    break;
                }
            }
            if safe {
                let permission = conditional(
                    predicate.permission.clone().unwrap_or(default),
                    Exp::new(ExpKind::NoPerm, Metadata::default()),
                );
                make(
                    ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                        predicate.location.clone(),
                        Some(permission),
                        predicate.meta.clone(),
                    )),
                    acc.metadata(),
                )
            } else {
                make(ExpKind::Implies(condition, acc.clone()), acc.metadata())
            }
        }
        ExpKind::MagicWand(..) => make(ExpKind::Implies(condition, acc.clone()), acc.metadata()),
        _ => {
            return Err(ConditionalPermissionError(
                "expected access predicate".into(),
            ));
        }
    };
    Ok(result)
}
fn is_access(e: &Exp) -> bool {
    matches!(
        e.kind(),
        ExpKind::FieldAccessPredicate(..)
            | ExpKind::PredicateAccessPredicate(..)
            | ExpKind::MagicWand(..)
    )
}
fn conditional_rewrite(
    e: &Exp,
    condition: &Condition,
    allow_wildcards: bool,
    program: &Program,
    seen: &std::cell::RefCell<Vec<Exp>>,
) -> Result<Exp, ConditionalPermissionError> {
    if let ExpKind::Implies(cond, rhs) = e.kind() {
        if is_access(rhs) {
            let safe = (allow_wildcards
                || !contains_wildcard(&rhs.permission_or_full().expect("access permission"))?)
                && no_introspection(cond)?;
            let result = if safe {
                direct(
                    e,
                    conditionalize(rhs, &condition.add(cond), allow_wildcards, program)?,
                )
            } else {
                direct(
                    e,
                    make(
                        ExpKind::Implies(
                            make(
                                ExpKind::And(condition.expression(), cond.clone()),
                                &Metadata::default(),
                            ),
                            rhs.clone(),
                        ),
                        e.metadata(),
                    ),
                )
            }?;
            seen.borrow_mut().push(result.clone());
            return Ok(result);
        }
        if let ExpKind::Let(_, bound, _) = rhs.kind() {
            if !rhs.is_pure() {
                if no_obligations(bound, program)? && no_introspection(cond)? {
                    let replacement = direct(e, rhs.clone())?;
                    return recurse_children(
                        &replacement,
                        &condition.add(cond),
                        allow_wildcards,
                        program,
                        seen,
                    );
                }
                let result = direct(
                    e,
                    make(
                        ExpKind::Implies(
                            make(
                                ExpKind::And(condition.expression(), cond.clone()),
                                &Metadata::default(),
                            ),
                            rhs.clone(),
                        ),
                        e.metadata(),
                    ),
                )?;
                seen.borrow_mut().push(result.clone());
                return Ok(result);
            }
        }
        if !rhs.is_pure() {
            if no_introspection(cond)? {
                let replacement = direct(e, rhs.clone())?;
                return recurse_children(
                    &replacement,
                    &condition.add(cond),
                    allow_wildcards,
                    program,
                    seen,
                );
            }
            let result = direct(
                e,
                make(
                    ExpKind::Implies(
                        make(
                            ExpKind::And(condition.expression(), cond.clone()),
                            &Metadata::default(),
                        ),
                        rhs.clone(),
                    ),
                    e.metadata(),
                ),
            )?;
            return recurse_children(&result, condition, allow_wildcards, program, seen);
        }
    }
    if is_access(e) && condition.0.is_some() {
        let result = if allow_wildcards
            || !contains_wildcard(&e.permission_or_full().expect("access permission"))?
        {
            direct(e, conditionalize(e, condition, allow_wildcards, program)?)?
        } else {
            direct(
                e,
                make(
                    ExpKind::Implies(condition.expression(), e.clone()),
                    e.metadata(),
                ),
            )?
        };
        seen.borrow_mut().push(result.clone());
        return Ok(result);
    }
    if let ExpKind::Let(_, bound, _) = e.kind() {
        if !no_obligations(bound, program)? {
            let result = direct(
                e,
                make(
                    ExpKind::Implies(condition.expression(), e.clone()),
                    e.metadata(),
                ),
            )?;
            seen.borrow_mut().push(result.clone());
            return Ok(result);
        }
    }
    if condition.0.is_some() && e.is_pure() {
        let c = condition.expression();
        return direct(
            e,
            make(ExpKind::Implies(c.clone(), e.clone()), c.metadata()),
        );
    }
    recurse_children(e, condition, allow_wildcards, program, seen)
}
fn recurse_children(
    e: &Exp,
    condition: &Condition,
    allow_wildcards: bool,
    program: &Program,
    seen: &std::cell::RefCell<Vec<Exp>>,
) -> Result<Exp, ConditionalPermissionError> {
    if seen.borrow().contains(e) || e.is_pure() || is_access(e) {
        return Ok(e.clone());
    }
    match e.kind() {
        ExpKind::Forall(vars, triggers, body) => Ok(make(
            ExpKind::Forall(
                vars.clone(),
                triggers.clone(),
                conditional_rewrite(body, condition, allow_wildcards, program, seen)?,
            ),
            e.metadata(),
        )),
        ExpKind::Exists(vars, triggers, body) => Ok(make(
            ExpKind::Exists(
                vars.clone(),
                triggers.clone(),
                conditional_rewrite(body, condition, allow_wildcards, program, seen)?,
            ),
            e.metadata(),
        )),
        ExpKind::Let(var, bound, body) => Ok(make(
            ExpKind::Let(
                var.clone(),
                bound.clone(),
                conditional_rewrite(body, condition, allow_wildcards, program, seen)?,
            ),
            e.metadata(),
        )),
        _ => e.map_expression_children(
            &mut |child| conditional_rewrite(child, condition, allow_wildcards, program, seen),
            &mut |_| {
                Err(ConditionalPermissionError(
                    "extension expression reconstruction".into(),
                ))
            },
            &mut |field| Ok(field.clone()),
            &mut |pred| Ok(pred.clone()),
            &mut |trigger: &Trigger| Ok(trigger.clone()),
        ),
    }
}

/// Two-pass source preprocessing. Unsupported expression or statement extension
/// products fail instead of bypassing conditional permission rewriting.
pub fn rewrite(
    program: &Program,
    allow_ternary_wildcards_in_functions: bool,
) -> Result<Program, ConditionalPermissionError> {
    use ferrum_silver::verifier::verification_result::DiagnosticError;
    let preprocessed = nodes::map_node_tree(&Node::Program(program.clone()), &|node| {
        if let Node::Exp(e) = node {
            if let ExpKind::CondExp(cond, yes, no) = e.kind() {
                if (!yes.is_pure() || !no.is_pure())
                    && expressions::contains_permission_introspection(cond).map_err(|_| {
                        DiagnosticError::Unsupported("ternary permission introspection")
                    })? == false
                {
                    let negated = make(ExpKind::Not(cond.clone()), cond.metadata());
                    let rewritten = make(
                        ExpKind::And(
                            make(ExpKind::Implies(cond.clone(), yes.clone()), e.metadata()),
                            make(ExpKind::Implies(negated, no.clone()), e.metadata()),
                        ),
                        e.metadata(),
                    );
                    return viper_strategy::preserve_metadata(node, &Node::Exp(rewritten), true)
                        .map_err(|_| DiagnosticError::Unsupported("ternary metadata"));
                }
            }
        }
        Ok(node.clone())
    })
    .map_err(failure)?;
    let Node::Program(preprocessed) = preprocessed else {
        return Err(ConditionalPermissionError("expected program".into()));
    };
    let mut contents = preprocessed.clone();
    let function_seen = std::cell::RefCell::new(Vec::new());
    let nonfunction_seen = std::cell::RefCell::new(Vec::new());
    let mut functions = Vec::new();
    for function in &preprocessed.functions {
        let mapped =
            nodes::map_expression_roots(&Node::Member(Member::Function(function.clone())), &|e| {
                conditional_rewrite(
                    e,
                    &Condition::default(),
                    allow_ternary_wildcards_in_functions,
                    program,
                    &function_seen,
                )
            })?;
        let Node::Member(Member::Function(function)) = mapped else {
            return Err(ConditionalPermissionError("expected function".into()));
        };
        functions.push(function);
    }
    let mut predicates = Vec::new();
    for predicate in &preprocessed.predicates {
        let mapped = nodes::map_expression_roots(
            &Node::Member(Member::Predicate(predicate.clone())),
            &|e| conditional_rewrite(e, &Condition::default(), false, program, &nonfunction_seen),
        )?;
        let Node::Member(Member::Predicate(predicate)) = mapped else {
            return Err(ConditionalPermissionError("expected predicate".into()));
        };
        predicates.push(predicate);
    }
    let mut methods = Vec::new();
    for method in &preprocessed.methods {
        let mapped =
            nodes::map_expression_roots(&Node::Member(Member::Method(method.clone())), &|e| {
                conditional_rewrite(e, &Condition::default(), false, program, &nonfunction_seen)
            })?;
        let Node::Member(Member::Method(method)) = mapped else {
            return Err(ConditionalPermissionError("expected method".into()));
        };
        methods.push(method);
    }
    contents = contents.copy_with(|p| {
        p.functions = functions;
        p.predicates = predicates;
        p.methods = methods;
    });
    Ok(contents)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ferrum_silver::ast::expression::LocalVar;
    use ferrum_silver::ast::program::{Field, FieldData, Method, MethodData};
    use ferrum_silver::ast::r#type::Type;

    #[test]
    fn replacement_is_recurred_into_without_rewriting_its_root_again() {
        let meta = Metadata::default();
        let receiver = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Ref, meta.clone())),
            meta.clone(),
        );
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let access = Exp::new(
            ExpKind::FieldAccessPredicate(FieldAccess::new(receiver, field, meta.clone()), None),
            meta.clone(),
        );
        let outer = Exp::new(
            ExpKind::LocalVar(LocalVar::new("a".into(), Type::Bool, meta.clone())),
            meta.clone(),
        );
        let inner = Exp::new(
            ExpKind::LocalVar(LocalVar::new("b".into(), Type::Bool, meta.clone())),
            meta.clone(),
        );
        let nested = Exp::new(ExpKind::Implies(inner, access), meta.clone());
        let source = Exp::new(ExpKind::Implies(outer, nested), meta.clone());
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], meta);
        let result = conditional_rewrite(
            &source,
            &Condition::default(),
            false,
            &program,
            &std::cell::RefCell::new(vec![]),
        )
        .unwrap();
        assert!(
            matches!(result.kind(), ExpKind::Implies(_, right) if matches!(right.kind(), ExpKind::FieldAccessPredicate(_, Some(_))))
        );
    }

    #[test]
    fn seen_replacement_with_introspection_skips_its_children() {
        let meta = Metadata::default();
        let receiver = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Ref, meta.clone())),
            meta.clone(),
        );
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let location = FieldAccess::new(receiver, field, meta.clone());
        let access = Exp::new(
            ExpKind::FieldAccessPredicate(location.clone(), None),
            meta.clone(),
        );
        let rhs = Exp::new(ExpKind::And(access.clone(), access), meta.clone());
        let field_exp = Exp::new(ExpKind::FieldAccess(location), meta.clone());
        let condition = Exp::new(
            ExpKind::PermGtCmp(
                Exp::new(ExpKind::CurrentPerm(field_exp), meta.clone()),
                Exp::new(ExpKind::NoPerm, meta.clone()),
            ),
            meta.clone(),
        );
        let original = Exp::new(
            ExpKind::Implies(condition.clone(), rhs.clone()),
            meta.clone(),
        );
        let true_condition = Exp::new(ExpKind::TrueLit, Metadata::default());
        let combined = Exp::new(ExpKind::And(true_condition, condition), Metadata::default());
        let replacement = Exp::new(ExpKind::Implies(combined, rhs.clone()), meta.clone());
        let seen = std::cell::RefCell::new(vec![replacement.clone()]);
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], meta);
        let result =
            conditional_rewrite(&original, &Condition::default(), false, &program, &seen).unwrap();
        assert_eq!(result, replacement);
        assert!(matches!(result.kind(), ExpKind::Implies(_, body) if *body == rhs));
    }

    #[test]
    fn rewrites_guarded_field_permission() {
        let m = Metadata::default();
        let receiver = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Ref, m.clone())),
            m.clone(),
        );
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: m.clone(),
        });
        let access = Exp::new(
            ExpKind::FieldAccessPredicate(FieldAccess::new(receiver, field, m.clone()), None),
            m.clone(),
        );
        let condition = Exp::new(
            ExpKind::LocalVar(LocalVar::new("b".into(), Type::Bool, m.clone())),
            m.clone(),
        );
        let assertion = Exp::new(ExpKind::Implies(condition.clone(), access), m.clone());
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![assertion],
            posts: vec![],
            body: None,
            meta: m.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], m);
        let output = rewrite(&program, false).unwrap();
        assert!(
            matches!(output.methods[0].pres[0].kind(), ExpKind::FieldAccessPredicate(_, Some(p)) if matches!(p.kind(), ExpKind::CondExp(c, yes, no) if *c == condition && matches!(yes.kind(), ExpKind::FullPerm) && matches!(no.kind(), ExpKind::NoPerm)))
        );
    }
}
