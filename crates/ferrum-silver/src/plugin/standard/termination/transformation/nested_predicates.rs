//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/NestedPredicates.scala
//!
//! Purpose:
//! Generate nested predicate-instance relationships for termination measures.
//!
//! Planned Rust structure:
//! Port NestedPredicates containsPredicateInstances, addNestedPredicateInformation, unfold/body
//! transformation, predicate assignments and unique local generation.
//!
//! Behavior to preserve:
//! When unfolding, assign caller instance, unfold, then inspect instantiated predicate body once
//! and inhale nested relations for predicate accesses; field accesses contribute nothing. Respect
//! conditional/implication branches and sequential binary traversal. Missing nestedPredicates
//! function reports consistency error and produces empty statement; preserve generated-name and
//! local-variable bookkeeping.
//!
//! Integration:
//! predicateinstance::predicate_instance_ast_extension, program_manager and function/method
//! checks; ast rewriter and verifier consistency errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for exact node metadata, naming and mutable state.
//!
//! Open decisions:
//! Reconcile hash-derived local names, domain substitutions and ownership with predicateinstance
//! and AST.
//!
//! Status: partial; per-unfold nested-relation instrumentation is implemented with injected Scala
//! hash/rendering callbacks and a bottom-up program pass. Lifecycle wiring remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::ast::{Info, Metadata};
use crate::ast::expression::{Exp, ExpExtra, ExpKind, LocalVar, PredicateAccess};
use crate::ast::program::{Declaration, LocalVarDecl, Program};
use crate::ast::statement::{PredicateAccessPredicate, Stmt, StmtKind};
use crate::ast::r#type::TypeSubstitution;
use crate::plugin::standard::predicateinstance::predicate_instance_ast_extension::{
    PredicateInstance, predicate_instance_type,
};
use crate::verifier::verification_result::{FrontendError, FrontendErrorKind};
use std::collections::HashSet;

#[derive(Debug)]
pub enum NestedPredicateError {
    MissingPredicate(String),
    MissingDomain(String),
    InvalidSubstitution,
    UnsupportedExpression(&'static str),
    Callback(String),
}

/// Hash and argument rendering are injected so callers can preserve Scala's
/// sequence-hash and argument rendering rather than silently changing names.
pub struct NestedPredicates<'a> {
    pub program: &'a Program,
    pub errors: Vec<FrontendError>,
    used_names: HashSet<String>,
    hash_args: &'a dyn Fn(&[Exp]) -> Result<i32, String>,
    render_args: &'a dyn Fn(&[Exp]) -> Result<String, String>,
}
impl<'a> NestedPredicates<'a> {
    pub fn new(
        program: &'a Program,
        hash_args: &'a dyn Fn(&[Exp]) -> Result<i32, String>,
        render_args: &'a dyn Fn(&[Exp]) -> Result<String, String>,
    ) -> Self {
        Self {
            program,
            errors: vec![],
            used_names: HashSet::new(),
            hash_args,
            render_args,
        }
    }
    pub fn contains_predicate_instances(
        spec: &crate::plugin::standard::termination::termination_ast_extension::DecreasesSpecification,
    ) -> Result<bool, NestedPredicateError> {
        use crate::plugin::standard::termination::termination_ast_extension::DecreasesKind;
        if let Some(clause) = &spec.tuple {
            if let DecreasesKind::Tuple { tuple, .. } = &clause.kind {
                for expression in tuple {
                    let typ = expression.typ().map_err(|_| {
                        NestedPredicateError::UnsupportedExpression("decreases expression type")
                    })?;
                    if typ.is_subtype(&predicate_instance_type()) {
                        return Ok(true);
                    }
                }
            }
        }
        Ok(false)
    }
    pub fn replace_used_names(&mut self, names: HashSet<String>) {
        self.used_names = names;
    }
    pub fn take_used_names(&mut self) -> HashSet<String> {
        std::mem::take(&mut self.used_names)
    }
    /// Bottom-up source Unfold rewrite; extension reconstruction remains fallible.
    fn rewrite_node(
        &mut self,
        input: &crate::ast::utility::nodes::Node,
    ) -> Result<crate::ast::utility::nodes::Node, NestedPredicateError> {
        use crate::ast::utility::{
            nodes::{Node, map_node_tree_bottom_up},
            viper_strategy,
        };
        use crate::verifier::verification_result::DiagnosticError;
        let current = std::cell::RefCell::new(self);
        let error = std::cell::RefCell::new(None);
        let result = map_node_tree_bottom_up(
            input,
            &|node| {
                if let Node::Stmt(statement) = node {
                    if let StmtKind::Unfold(access) = statement.kind() {
                        let replacement = match current.borrow_mut().unfold_nested(access) {
                            Ok(stmt) => stmt,
                            Err(err) => {
                                *error.borrow_mut() = Some(err);
                                return Err(DiagnosticError::Unsupported(
                                    "nested-predicate generation",
                                ));
                            }
                        };
                        return viper_strategy::preserve_metadata(
                            node,
                            &Node::Stmt(replacement),
                            true,
                        )
                        .map_err(|_| DiagnosticError::Unsupported("nested-predicate metadata"));
                    }
                }
                Ok(node.clone())
            },
            false,
        );
        if let Some(err) = error.into_inner() {
            return Err(err);
        }
        result
            .map_err(|_| NestedPredicateError::UnsupportedExpression("nested-predicate traversal"))
    }
    pub fn add_nested_predicate_information(
        &mut self,
        input: &Program,
    ) -> Result<Program, NestedPredicateError> {
        match self.rewrite_node(&crate::ast::utility::nodes::Node::Program(input.clone()))? {
            crate::ast::utility::nodes::Node::Program(program) => Ok(program),
            _ => Err(NestedPredicateError::UnsupportedExpression(
                "nested-predicate program",
            )),
        }
    }
    pub fn add_nested_to_statement(&mut self, input: &Stmt) -> Result<Stmt, NestedPredicateError> {
        match self.rewrite_node(&crate::ast::utility::nodes::Node::Stmt(input.clone()))? {
            crate::ast::utility::nodes::Node::Stmt(stmt) => Ok(stmt),
            _ => Err(NestedPredicateError::UnsupportedExpression(
                "nested-predicate statement",
            )),
        }
    }
    fn unique_var(
        &mut self,
        access: &PredicateAccess,
    ) -> Result<LocalVarDecl, NestedPredicateError> {
        let hash = (self.hash_args)(&access.args).map_err(NestedPredicateError::Callback)?;
        let prefix = format!(
            "{}_{}",
            access.predicate_name,
            hash.to_string().replace('-', "_")
        );
        let mut name = prefix.clone();
        let mut index = 0i32;
        while self.used_names.contains(&name) {
            name = format!("{prefix}{index}");
            index = index.wrapping_add(1);
        }
        self.used_names.insert(name.clone());
        let info = Info::Simple(vec![format!(
            "{}_{}",
            access.predicate_name,
            (self.render_args)(&access.args).map_err(NestedPredicateError::Callback)?
        )]);
        Ok(LocalVarDecl::new(
            name,
            predicate_instance_type(),
            Metadata {
                info,
                ..Default::default()
            },
        ))
    }
    fn assignment(&self, var: LocalVar, access: &PredicateAccess) -> Stmt {
        let instance = PredicateInstance {
            predicate: access.predicate_name.clone(),
            args: access.args.clone(),
            meta: access.meta.clone(),
        }
        .expression();
        Stmt::new(
            StmtKind::LocalVarAssign {
                lhs: var,
                rhs: instance,
            },
            Metadata {
                position: access.meta.position.clone(),
                ..Default::default()
            },
        )
    }
    /// Source reports the missing relation and produces an empty statement.
    pub fn unfold_nested(
        &mut self,
        access: &PredicateAccessPredicate,
    ) -> Result<Stmt, NestedPredicateError> {
        if self
            .program
            .find_domain_function_optionally("nestedPredicates")
            .is_none()
        {
            self.errors.push(FrontendError::new(
                FrontendErrorKind::ConsistencyError(
                    "nestedPredicates function is needed but not declared.".into(),
                ),
                access.meta.position.clone(),
            ));
            return Ok(crate::ast::utility::statements::empty_stmt());
        }
        let caller = self.unique_var(&access.location)?;
        let assignment = self.assignment(caller.local_var(), &access.location);
        let unfold = Stmt::new(StmtKind::Unfold(access.clone()), Metadata::default());
        let predicate = self
            .program
            .find_predicate_optionally(&access.location.predicate_name)
            .ok_or_else(|| {
                NestedPredicateError::MissingPredicate(access.location.predicate_name.clone())
            })?;
        let body = if let Some(body) = &predicate.body {
            let replacements: Vec<_> = predicate
                .formal_args
                .iter()
                .zip(&access.location.args)
                .map(|(v, arg)| {
                    (
                        Exp::new(ExpKind::LocalVar(v.local_var()), v.meta.clone()),
                        arg.clone(),
                    )
                })
                .collect();
            let crate::ast::utility::nodes::Node::Exp(body) =
                crate::ast::utility::nodes::replace_expressions(
                    &crate::ast::utility::nodes::Node::Exp(body.clone()),
                    &replacements,
                )
                .map_err(|_| NestedPredicateError::InvalidSubstitution)?
            else {
                return Err(NestedPredicateError::InvalidSubstitution);
            };
            self.transform_body(&body, &caller)?
        } else {
            crate::ast::utility::statements::empty_stmt()
        };
        Ok(sequence(
            vec![assignment, unfold, body],
            vec![Declaration::Local(caller)],
            Metadata::default(),
        ))
    }
    fn transform_body(
        &mut self,
        body: &Exp,
        caller: &LocalVarDecl,
    ) -> Result<Stmt, NestedPredicateError> {
        use ExpKind::*;
        match body.kind() {
            FieldAccessPredicate(..) => Ok(crate::ast::utility::statements::empty_stmt()),
            MagicWand(..) => Err(NestedPredicateError::UnsupportedExpression(
                "magic wand in predicate body",
            )),
            PredicateAccessPredicate(callee) => {
                let var = self.unique_var(&callee.location)?;
                let assignment = self.assignment(var.local_var(), &callee.location);
                let nested = self
                    .program
                    .find_domain_function_optionally("nestedPredicates")
                    .ok_or(NestedPredicateError::UnsupportedExpression(
                        "missing nestedPredicates",
                    ))?;
                let domain = self
                    .program
                    .find_domain_optionally(&nested.domain_name)
                    .ok_or_else(|| {
                        NestedPredicateError::MissingDomain(nested.domain_name.clone())
                    })?;
                let types: TypeSubstitution = domain
                    .type_vars
                    .iter()
                    .cloned()
                    .zip(nested.formal_args.iter().map(|a| a.typ().clone()))
                    .collect();
                let meta = Metadata {
                    position: callee.meta.position.clone(),
                    ..Default::default()
                };
                let lhs = Exp::new(LocalVar(var.local_var()), var.meta.clone());
                let rhs = Exp::new(LocalVar(caller.local_var()), caller.meta.clone());
                let app = Exp::with_extra(
                    DomainFuncApp(nested.name.clone(), vec![lhs, rhs], types),
                    meta.clone(),
                    ExpExtra {
                        typ: Some(nested.typ.clone()),
                        domain_name: Some(nested.domain_name.clone()),
                        interpretation: None,
                    },
                );
                Ok(sequence(
                    vec![assignment, Stmt::new(StmtKind::Inhale(app), meta.clone())],
                    vec![Declaration::Local(var)],
                    meta,
                ))
            }
            CondExp(cond, yes, no) => {
                let yes = self.transform_body(yes, caller)?;
                let no = self.transform_body(no, caller)?;
                let meta = Metadata {
                    position: body.metadata().position.clone(),
                    ..Default::default()
                };
                Ok(Stmt::new(
                    StmtKind::If {
                        condition: cond.clone(),
                        then_branch: sequence(vec![yes], vec![], meta.clone()),
                        else_branch: sequence(vec![no], vec![], meta.clone()),
                    },
                    meta,
                ))
            }
            Implies(cond, consequent) => {
                let yes = self.transform_body(consequent, caller)?;
                let meta = Metadata {
                    position: body.metadata().position.clone(),
                    ..Default::default()
                };
                Ok(Stmt::new(
                    StmtKind::If {
                        condition: cond.clone(),
                        then_branch: sequence(vec![yes], vec![], meta.clone()),
                        else_branch: crate::ast::utility::statements::empty_stmt(),
                    },
                    meta,
                ))
            }
            Add(a, b)
            | Sub(a, b)
            | Mul(a, b)
            | Div(a, b)
            | Mod(a, b)
            | LtCmp(a, b)
            | LeCmp(a, b)
            | GtCmp(a, b)
            | GeCmp(a, b)
            | EqCmp(a, b)
            | NeCmp(a, b)
            | Or(a, b)
            | And(a, b)
            | FractionalPerm(a, b)
            | PermDiv(a, b)
            | PermPermDiv(a, b)
            | PermAdd(a, b)
            | PermSub(a, b)
            | PermMul(a, b)
            | IntPermMul(a, b)
            | DebugPermMin(a, b)
            | PermLtCmp(a, b)
            | PermLeCmp(a, b)
            | PermGtCmp(a, b)
            | PermGeCmp(a, b)
            | AnySetUnion(a, b)
            | AnySetIntersection(a, b)
            | AnySetSubset(a, b)
            | AnySetMinus(a, b)
            | AnySetContains(a, b) => {
                let left = self.transform_body(a, caller)?;
                let right = self.transform_body(b, caller)?;
                Ok(sequence(
                    vec![left, right],
                    vec![],
                    Metadata {
                        position: body.metadata().position.clone(),
                        ..Default::default()
                    },
                ))
            }
            Minus(inner) | Not(inner) | PermMinus(inner) => self.transform_body(inner, caller),
            _ => Ok(crate::ast::utility::statements::empty_stmt()),
        }
    }
}
fn sequence(statements: Vec<Stmt>, declarations: Vec<Declaration>, meta: Metadata) -> Stmt {
    Stmt::new(
        StmtKind::Seqn {
            statements,
            declarations,
        },
        meta,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::program::{
        AnyLocalVarDecl, Domain, DomainData, DomainFunc, DomainFuncData, Predicate, PredicateData,
    };
    use crate::ast::r#type::Type;

    #[test]
    fn unfold_generates_nested_assumption_after_substituting_arguments() {
        let meta = Metadata::default();
        let arg = LocalVarDecl::new("x".into(), Type::Int, meta.clone());
        let var = Exp::new(ExpKind::LocalVar(arg.local_var()), meta.clone());
        let q = PredicateAccess::new(vec![var], "q".into(), meta.clone());
        let body = Exp::new(
            ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(q, None, meta.clone())),
            meta.clone(),
        );
        let pred = Predicate::new(PredicateData {
            name: "p".into(),
            formal_args: vec![arg],
            body: Some(body),
            meta: meta.clone(),
        });
        let instance = predicate_instance_type();
        let formal = || {
            AnyLocalVarDecl::Named(LocalVarDecl::new(
                "a".into(),
                instance.clone(),
                meta.clone(),
            ))
        };
        let nested = DomainFunc::new(DomainFuncData {
            name: "nestedPredicates".into(),
            formal_args: vec![formal(), formal()],
            typ: Type::Bool,
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![nested],
            axioms: vec![],
            type_vars: vec![],
            interpretations: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![domain],
            vec![],
            vec![],
            vec![pred],
            vec![],
            vec![],
            meta.clone(),
        );
        let actual = Exp::new(ExpKind::IntLit(7.into()), meta.clone());
        let access = PredicateAccessPredicate::new(
            PredicateAccess::new(vec![actual.clone()], "p".into(), meta.clone()),
            None,
            meta,
        );
        let mut generator = NestedPredicates::new(&program, &|_| Ok(5), &|_| Ok("7".into()));
        let result = generator.unfold_nested(&access).unwrap();
        let StmtKind::Seqn { statements, .. } = result.kind() else {
            panic!()
        };
        assert!(matches!(statements[1].kind(), StmtKind::Unfold(_)));
        let StmtKind::Seqn {
            statements: nested, ..
        } = statements[2].kind()
        else {
            panic!()
        };
        assert!(
            matches!(nested[0].kind(), StmtKind::LocalVarAssign { rhs, .. } if matches!(rhs.kind(), ExpKind::Extension(ext) if ext.0.as_any().downcast_ref::<PredicateInstance>().is_some_and(|p| p.args == vec![actual.clone()])))
        );
        assert!(
            matches!(nested[1].kind(), StmtKind::Inhale(exp) if matches!(exp.kind(), ExpKind::DomainFuncApp(name, _, _) if name == "nestedPredicates"))
        );
    }
}
