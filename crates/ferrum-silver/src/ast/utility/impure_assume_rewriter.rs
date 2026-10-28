//! Synthetic helpers and inhale splitting for impure-assume rewriting.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/ImpureAssumeRewriter.scala
//! Status: partial; whole-program inverse, contextual permission and inhale-splitting
//! stages are implemented. Unsupported inverse/traversal cases propagate errors;
//! full upstream compatibility and plugin-specific reconstruction remain under review.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    ast::Metadata,
    expression::{Exp, ExpExtra, ExpKind, LocalVar, Trigger},
    program::{AnyLocalVarDecl, DomainAxiom, DomainFunc, LocalVarDecl},
    statement::{Stmt, StmtKind},
    r#type::Type,
};
use std::collections::HashMap;
pub const DOMAIN_NAME: &str = "__ns__impure_assume_rewriter";
pub fn split(exp: &Exp) -> Vec<Exp> {
    if let ExpKind::And(a, b) = exp.kind() {
        let mut out = split(a);
        out.extend(split(b));
        out
    } else {
        vec![exp.clone()]
    }
}
pub fn rewrite_inhale(inhale: &Stmt) -> Result<Stmt, &'static str> {
    let StmtKind::Inhale(exp) = inhale.kind() else {
        return Err("expected inhale statement");
    };
    let statements = split(exp)
        .into_iter()
        .map(|e| Stmt::new(StmtKind::Inhale(e.clone()), e.metadata().clone()))
        .collect();
    Ok(Stmt::new(
        StmtKind::Seqn {
            statements,
            declarations: vec![],
        },
        inhale.metadata().clone(),
    ))
}
fn variable(name: String, typ: Type) -> Exp {
    Exp::new(
        ExpKind::LocalVar(LocalVar::new(name, typ, Metadata::default())),
        Metadata::default(),
    )
}
/// Construct the source helper and defining quantified axiom. Argument declarations
/// are prepended in each loop, while references in the conditional sum are appended.
pub fn generate_func(num_of_conds: i32) -> (DomainFunc, DomainAxiom) {
    let name = format!("__iar__assume_helper_{num_of_conds}");
    let mut condition_decls = Vec::new();
    let mut perm_decls = vec![LocalVarDecl::new(
        "p_0".into(),
        Type::Perm,
        Metadata::default(),
    )];
    let mut conditions = Vec::new();
    let mut permissions = Vec::new();
    for i in 0..num_of_conds {
        let n = format!("c_{}", i + 1);
        condition_decls.insert(
            0,
            LocalVarDecl::new(n.clone(), Type::Bool, Metadata::default()),
        );
        conditions.push(variable(n, Type::Bool));
    }
    for i in 0..num_of_conds {
        let n = format!("p_{}", i + 1);
        perm_decls.insert(
            0,
            LocalVarDecl::new(n.clone(), Type::Perm, Metadata::default()),
        );
        permissions.push(variable(n, Type::Perm));
    }
    let args: Vec<_> = condition_decls.into_iter().chain(perm_decls).collect();
    let mut body = variable("p_0".into(), Type::Perm);
    for (condition, permission) in conditions.into_iter().zip(permissions) {
        let zero = Exp::new(ExpKind::NoPerm, Metadata::default());
        let conditional = Exp::new(
            ExpKind::CondExp(condition, permission, zero),
            Metadata::default(),
        );
        body = Exp::new(ExpKind::PermAdd(body, conditional), Metadata::default());
    }
    let function = DomainFunc::new(crate::ast::program::DomainFuncData {
        name: name.clone(),
        formal_args: args.iter().cloned().map(AnyLocalVarDecl::Named).collect(),
        typ: Type::Perm,
        unique: false,
        interpretation: None,
        domain_name: DOMAIN_NAME.into(),
        meta: Metadata::default(),
    });
    let app = || {
        Exp::with_extra(
            ExpKind::DomainFuncApp(
                name.clone(),
                args.iter()
                    .map(|v| Exp::new(ExpKind::LocalVar(v.local_var()), v.meta.clone()))
                    .collect(),
                HashMap::new(),
            ),
            Metadata::default(),
            ExpExtra {
                typ: Some(Type::Perm),
                domain_name: Some(DOMAIN_NAME.into()),
                interpretation: None,
            },
        )
    };
    let trigger = Trigger::new(vec![app()], Metadata::default());
    let equality = Exp::new(ExpKind::EqCmp(app(), body), Metadata::default());
    let axiom = Exp::new(
        ExpKind::Forall(args, vec![trigger], equality),
        Metadata::default(),
    );
    (
        function,
        DomainAxiom::new(crate::ast::program::DomainAxiomKind::Named {
            name: format!("{name}_axiom"),
            exp: axiom,
            domain_name: DOMAIN_NAME.into(),
            meta: Metadata::default(),
        }),
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssumeRewriteError {
    Traversal(String),
    Inverse(String),
    Replacement(String),
    Simplification(String),
    MissingPredicate(String),
    InvalidResource,
    InvalidRewrite(&'static str),
}

#[derive(Clone, PartialEq, Eq)]
enum Resource {
    Field(crate::ast::program::Field),
    Predicate(crate::ast::program::Predicate),
}
#[derive(Clone)]
struct Frame {
    condition: Exp,
    variables: Vec<Exp>,
    permission: Exp,
}
struct AssumeRewriter {
    frames: std::cell::RefCell<Vec<(Resource, Vec<Frame>)>>,
    functions: std::cell::RefCell<Vec<DomainFunc>>,
    axioms: std::cell::RefCell<Vec<DomainAxiom>>,
}
impl AssumeRewriter {
    fn new() -> Self {
        Self {
            frames: Default::default(),
            functions: Default::default(),
            axioms: Default::default(),
        }
    }
    fn add_frame(&self, resource: Resource, frame: Frame) -> Vec<Frame> {
        let mut all = self.frames.borrow_mut();
        if let Some((_, frames)) = all.iter_mut().find(|(key, _)| *key == resource) {
            let old = frames.clone();
            frames.push(frame);
            old
        } else {
            all.push((resource, vec![frame]));
            Vec::new()
        }
    }
    fn permission_comparison(
        &self,
        frames: &[Frame],
        args: &[Exp],
        permission: Exp,
        location: Exp,
        metadata: Metadata,
    ) -> Result<Exp, AssumeRewriteError> {
        use super::{
            expressions::is_known_well_defined, rewriter::strategy::replace_expressions,
            simplifier::simplify,
        };
        let current = Exp::new(ExpKind::CurrentPerm(location), metadata);
        if frames.is_empty() {
            return Ok(Exp::new(
                ExpKind::PermGeCmp(current, permission),
                Metadata::default(),
            ));
        }
        let mut conditions = Vec::new();
        for frame in frames {
            if frame.variables.len() != args.len() {
                return Err(AssumeRewriteError::InvalidResource);
            }
            let replacements: Vec<_> = frame
                .variables
                .iter()
                .cloned()
                .zip(args.iter().cloned())
                .collect();
            let condition = replace_expressions(&frame.condition, &replacements)
                .map_err(|e| AssumeRewriteError::Replacement(format!("{e:?}")))?;
            conditions.push(
                simplify(&condition, false, &|e| is_known_well_defined(e, None))
                    .map_err(|e| AssumeRewriteError::Simplification(format!("{e:?}")))?,
            );
        }
        let index = frames.len() - 1;
        if self.functions.borrow().len() <= index {
            let n = self.functions.borrow().len() + 1;
            let (function, axiom) = generate_func(n as i32);
            self.functions.borrow_mut().push(function);
            self.axioms.borrow_mut().push(axiom);
        }
        let function = self.functions.borrow()[index].clone();
        let arguments = conditions
            .into_iter()
            .chain(frames.iter().map(|f| f.permission.clone()))
            .chain(std::iter::once(permission))
            .collect();
        let app = Exp::with_extra(
            ExpKind::DomainFuncApp(function.name.clone(), arguments, HashMap::new()),
            Metadata::default(),
            ExpExtra {
                typ: Some(Type::Perm),
                domain_name: Some(DOMAIN_NAME.into()),
                interpretation: None,
            },
        );
        Ok(Exp::new(
            ExpKind::PermGeCmp(current, app),
            Metadata::default(),
        ))
    }
    fn walk(
        &self,
        expression: &Exp,
        program: &crate::ast::program::Program,
        condition: &Exp,
        inside_wand: bool,
        parent_unfolding: bool,
    ) -> Result<Exp, AssumeRewriteError> {
        use crate::ast::expression::{FieldAccess, PredicateAccess};
        let mut current = expression.clone();
        let mut context = condition.clone();
        match expression.kind() {
            ExpKind::Implies(left, _) => {
                context = Exp::new(
                    ExpKind::And(condition.clone(), left.clone()),
                    Metadata::default(),
                )
            }
            ExpKind::FieldAccessPredicate(loc, _) => {
                let dummy = variable("__iar__dummy".into(), Type::Ref);
                let eq = Exp::new(
                    ExpKind::EqCmp(loc.receiver.clone(), dummy.clone()),
                    Metadata::default(),
                );
                let frame = Frame {
                    condition: Exp::new(ExpKind::And(condition.clone(), eq), Metadata::default()),
                    variables: vec![dummy],
                    permission: expression
                        .permission_or_full()
                        .ok_or(AssumeRewriteError::InvalidResource)?,
                };
                let old = self.add_frame(Resource::Field(loc.field.clone()), frame.clone());
                if !inside_wand {
                    let location = Exp::new(ExpKind::FieldAccess(loc.clone()), loc.meta.clone());
                    current = self.permission_comparison(
                        &old,
                        std::slice::from_ref(&loc.receiver),
                        frame.permission,
                        location,
                        expression.metadata().clone(),
                    )?;
                }
            }
            ExpKind::PredicateAccessPredicate(access) => {
                let predicate = program
                    .find_predicate_optionally(&access.location.predicate_name)
                    .ok_or_else(|| {
                        AssumeRewriteError::MissingPredicate(access.location.predicate_name.clone())
                    })?;
                if predicate.formal_args.len() < access.location.args.len() {
                    return Err(AssumeRewriteError::InvalidResource);
                }
                let vars: Vec<_> = access
                    .location
                    .args
                    .iter()
                    .enumerate()
                    .map(|(i, _)| {
                        variable(
                            format!("__iar__dummy{i}"),
                            predicate.formal_args[i].typ.clone(),
                        )
                    })
                    .collect();
                let equalities: Vec<_> = access
                    .location
                    .args
                    .iter()
                    .cloned()
                    .zip(vars.iter().cloned())
                    .map(|(a, b)| Exp::new(ExpKind::EqCmp(a, b), Metadata::default()))
                    .collect();
                let cond = equalities
                    .into_iter()
                    .reduce(|a, b| Exp::new(ExpKind::And(a, b), Metadata::default()))
                    .unwrap_or_else(|| Exp::new(ExpKind::TrueLit, Metadata::default()));
                let frame = Frame {
                    condition: Exp::new(ExpKind::And(condition.clone(), cond), Metadata::default()),
                    variables: vars,
                    permission: access.permission_or_full(),
                };
                let old = self.add_frame(Resource::Predicate(predicate.clone()), frame.clone());
                if !inside_wand && !parent_unfolding {
                    let location = Exp::new(
                        ExpKind::PredicateAccess(access.location.clone()),
                        access.location.meta.clone(),
                    );
                    current = self.permission_comparison(
                        &old,
                        &access.location.args,
                        frame.permission,
                        location,
                        expression.metadata().clone(),
                    )?;
                }
            }
            _ => {}
        }
        let wand = inside_wand || matches!(current.kind(), ExpKind::MagicWand(..));
        let unfolding = matches!(current.kind(), ExpKind::Unfolding(..));
        current.map_expression_children_by_identity(
            &mut |e| self.walk(e, program, &context, wand, unfolding),
            &mut |ext| {
                ext.0
                    .map_expressions(&|e| {
                        self.walk(e, program, &context, wand, unfolding)
                            .map_err(|_| {
                                crate::verifier::verification_result::DiagnosticError::Unsupported(
                                    "assume extension expression",
                                )
                            })
                    })
                    .map_err(|e| AssumeRewriteError::Traversal(format!("{e:?}")))
            },
            &mut |f| {
                let r = self.walk(&f.receiver, program, &context, wand, false)?;
                Ok(if r.same_node(&f.receiver) {
                    f.clone()
                } else {
                    FieldAccess::new(r, f.field.clone(), f.meta.clone())
                })
            },
            &mut |p| {
                let args = p
                    .args
                    .iter()
                    .map(|e| self.walk(e, program, &context, wand, false))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(if args.iter().zip(&p.args).all(|(a, b)| a.same_node(b)) {
                    p.clone()
                } else {
                    PredicateAccess::new(args, p.predicate_name.clone(), p.meta.clone())
                })
            },
            &mut |t| {
                let exps = t
                    .exps
                    .iter()
                    .map(|e| self.walk(e, program, &context, wand, false))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(if exps.iter().zip(&t.exps).all(|(a, b)| a.same_node(b)) {
                    t.clone()
                } else {
                    Trigger::new(exps, t.meta.clone())
                })
            },
        )
    }
}

fn rewrite_qps(
    exp: &Exp,
    program: &crate::ast::program::Program,
    domains: &mut Vec<crate::ast::program::Domain>,
) -> Result<Exp, AssumeRewriteError> {
    use super::{
        expressions::sub_expressions, inverse_functions::get_fresh_inverse,
        rewriter::strategy::replace_expressions,
    };
    if matches!(exp.kind(), ExpKind::Forall(..)) {
        let (inverse, axioms, forall) = get_fresh_inverse(exp, program)
            .map_err(|e| AssumeRewriteError::Inverse(format!("{e:?}")))?;
        if let (Some((_, domain)), Some(axioms)) = (inverse, axioms) {
            domains.push(domain);
            let mut iter = axioms.into_iter();
            let mut result = iter
                .next()
                .ok_or(AssumeRewriteError::InvalidRewrite("empty inverse axioms"))?;
            for next in iter {
                result = Exp::new(ExpKind::And(result, next), Metadata::default());
            }
            return Ok(Exp::new(ExpKind::And(result, forall), Metadata::default()));
        }
        return Ok(forall);
    }
    let children =
        sub_expressions(exp).map_err(|e| AssumeRewriteError::Traversal(format!("{e:?}")))?;
    let mut replacements = Vec::new();
    for child in children {
        replacements.push((child.clone(), rewrite_qps(&child, program, domains)?));
    }
    replace_expressions(exp, &replacements)
        .map_err(|e| AssumeRewriteError::Replacement(format!("{e:?}")))
}

/// Apply the three source assume stages, propagating unsupported inverse or traversal paths.
pub fn rewrite_assumes(
    program: &crate::ast::program::Program,
) -> Result<crate::ast::program::Program, AssumeRewriteError> {
    use super::nodes::{Node, map_node_tree};
    use crate::verifier::verification_result::DiagnosticError;
    fn contains_assume(node: &Node) -> Result<bool, AssumeRewriteError> {
        if matches!(node, Node::Stmt(stmt) if matches!(stmt.kind(), StmtKind::Assume(_))) {
            return Ok(true);
        }
        for child in super::nodes::subnodes(node)
            .map_err(|e| AssumeRewriteError::Traversal(format!("{e:?}")))?
        {
            if contains_assume(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    if !contains_assume(&Node::Program(program.clone()))? {
        return Ok(program.clone());
    }
    let domains = std::cell::RefCell::new(Vec::new());
    let failure = std::cell::RefCell::new(None);
    let first = map_node_tree(&Node::Program(program.clone()), &|node| {
        if let Node::Stmt(stmt) = node {
            if let StmtKind::Assume(exp) = stmt.kind() {
                return match rewrite_qps(exp, program, &mut domains.borrow_mut()) {
                    Ok(value) => Ok(Node::Stmt(Stmt::new(
                        StmtKind::Assume(value),
                        stmt.metadata().clone(),
                    ))),
                    Err(error) => {
                        *failure.borrow_mut() = Some(error);
                        Err(DiagnosticError::Unsupported("assume quantified rewrite"))
                    }
                };
            }
        }
        Ok(node.clone())
    });
    if let Some(error) = failure.into_inner() {
        return Err(error);
    }
    let Node::Program(first) =
        first.map_err(|e| AssumeRewriteError::Traversal(format!("{e:?}")))?
    else {
        return Err(AssumeRewriteError::InvalidRewrite("program"));
    };
    let rewriter = AssumeRewriter::new();
    let failure = std::cell::RefCell::new(None);
    let second = map_node_tree(&Node::Program(first.clone()), &|node| {
        if let Node::Stmt(stmt) = node {
            if let StmtKind::Assume(exp) = stmt.kind() {
                rewriter.frames.borrow_mut().clear();
                let truth = Exp::new(ExpKind::TrueLit, Metadata::default());
                let result = rewriter
                    .walk(exp, &first, &truth, false, false)
                    .and_then(|exp| {
                        let meta = Metadata {
                            position: stmt.metadata().position.clone(),
                            ..Metadata::default()
                        };
                        rewrite_inhale(&Stmt::new(StmtKind::Inhale(exp), meta))
                            .map_err(AssumeRewriteError::InvalidRewrite)
                    });
                return match result {
                    Ok(value) => Ok(Node::Stmt(value)),
                    Err(error) => {
                        *failure.borrow_mut() = Some(error);
                        Err(DiagnosticError::Unsupported("assume rewrite"))
                    }
                };
            }
        }
        Ok(node.clone())
    });
    if let Some(error) = failure.into_inner() {
        return Err(error);
    }
    let Node::Program(second) =
        second.map_err(|e| AssumeRewriteError::Traversal(format!("{e:?}")))?
    else {
        return Err(AssumeRewriteError::InvalidRewrite("program"));
    };
    let inverse_domains = domains.into_inner();
    let functions = rewriter.functions.into_inner();
    let axioms = rewriter.axioms.into_inner();
    if inverse_domains.is_empty() && functions.is_empty() {
        return Ok(second);
    }
    let meta = Metadata {
        info: crate::ast::ast::Info::Synthesized,
        ..Metadata::default()
    };
    let helper = crate::ast::program::Domain::new(crate::ast::program::DomainData {
        name: DOMAIN_NAME.into(),
        functions,
        axioms,
        type_vars: vec![],
        interpretations: None,
        meta,
    });
    Ok(second.copy_with(|p| {
        p.domains.extend(inverse_domains);
        p.domains.push(helper);
    }))
}

#[cfg(test)]
mod rewrite_tests {
    use super::*;
    use crate::ast::{
        expression::FieldAccess,
        program::{Field, FieldData, Method, MethodData, Program},
    };
    #[test]
    fn whole_program_splits_pure_assume_and_aggregates_aliased_permissions() {
        let meta = Metadata::default();
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let receiver = variable("r".into(), Type::Ref);
        let access = || {
            Exp::new(
                ExpKind::FieldAccessPredicate(
                    FieldAccess::new(receiver.clone(), field.clone(), meta.clone()),
                    None,
                ),
                meta.clone(),
            )
        };
        let assertion = Exp::new(ExpKind::And(access(), access()), meta.clone());
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![
                    Stmt::new(StmtKind::Assume(assertion), meta.clone()),
                    Stmt::new(
                        StmtKind::Assume(Exp::new(ExpKind::TrueLit, meta.clone())),
                        meta.clone(),
                    ),
                ],
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
        let program = Program::new(
            vec![],
            vec![field],
            vec![],
            vec![],
            vec![method],
            vec![],
            meta,
        );
        let result = rewrite_assumes(&program).unwrap();
        let helper = result
            .find_domain_optionally(DOMAIN_NAME)
            .expect("helper domain");
        assert_eq!(helper.functions.len(), 1);
        assert_eq!(helper.axioms.len(), 1);
        let StmtKind::Seqn { statements, .. } = result.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!("body")
        };
        let StmtKind::Seqn {
            statements: rewritten,
            ..
        } = statements[0].kind()
        else {
            panic!("split assume")
        };
        assert_eq!(rewritten.len(), 2);
        let StmtKind::Inhale(second) = rewritten[1].kind() else {
            panic!("inhale")
        };
        let ExpKind::PermGeCmp(_, amount) = second.kind() else {
            panic!("permission comparison")
        };
        assert!(
            matches!(amount.kind(), ExpKind::DomainFuncApp(name, _, _) if name == "__iar__assume_helper_1")
        );
        let StmtKind::Seqn {
            statements: pure, ..
        } = statements[1].kind()
        else {
            panic!("pure assume")
        };
        assert!(matches!(pure[0].kind(), StmtKind::Inhale(_)));
    }
}
