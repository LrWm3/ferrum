//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/FunctionCheck.scala
//!
//! Purpose:
//! Generate proof methods for function termination and recursive-call decreases.
//!
//! Planned Rust structure:
//! Port FunctionCheck generateProofMethods, removeConcretePermissionAmounts, transformExp
//! override, FContext and SCC call graph.
//!
//! Behavior to preserve:
//! Only functions with tuple specifications generate proofs; independently process body, posts and
//! pres in that order, omit empty proofs and preserve result/inhale-exhale locals. Check arguments
//! first; recursive calls check condition and lexicographic decrease using old caller tuple, other
//! calls check callee termination condition. Optional legacy permission mode rewrites concrete
//! positive amounts to wildcard and merges quantified-permission implications. Map assertion
//! failures to FunctionTerminationError; add nested predicate info when needed.
//!
//! Integration:
//! trafo, call_graph, decreases_check, exp_transformer, nested_predicates and
//! termination_ast_extension; ast simplifier and quantified permissions.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, exact permission handling, metadata and contexts.
//!
//! Open decisions:
//! Reconcile proof method names, permission option and error transforms with termination_plugin
//! and verifier.
//!
//! Status: partial; proof-method orchestration and legacy permission removal are implemented.
//! A concrete SCC-based call-check engine uses the statement simplifier; nested instrumentation
//! requires explicit Scala-compatible services. Termination lifecycle integration remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::ast::Metadata;
use crate::ast::expression::{Exp, ExpKind};
use crate::ast::statement::{PredicateAccessPredicate, Stmt, StmtKind};
use crate::ast::utility::{
    expressions,
    nodes::{Node, map_node_tree},
    quantified_permissions, simplifier,
};
use crate::verifier::verification_result::DiagnosticError;

fn default_exp(kind: ExpKind) -> Exp {
    Exp::new(kind, Metadata::default())
}
fn wildcard() -> Exp {
    default_exp(ExpKind::WildcardPerm)
}
fn permission_condition(permission: &Exp) -> Result<Exp, DiagnosticError> {
    let Node::Exp(amount) = map_node_tree(&Node::Exp(permission.clone()), &|node| match node {
        Node::Exp(e) if matches!(e.kind(), ExpKind::WildcardPerm) => {
            Ok(Node::Exp(default_exp(ExpKind::FullPerm)))
        }
        _ => Ok(node.clone()),
    })?
    else {
        return Err(DiagnosticError::InvalidNode("permission amount"));
    };
    let comparison = default_exp(ExpKind::PermLtCmp(default_exp(ExpKind::NoPerm), amount));
    simplifier::simplify(&comparison, false, &|e| {
        expressions::is_known_well_defined(e, None)
    })
    .map_err(|_| DiagnosticError::Unsupported("permission condition simplification"))
}
fn rewrite_access(
    original: &Exp,
    wildcard_access: Exp,
    amount: Option<&Exp>,
) -> Result<Exp, DiagnosticError> {
    let Some(amount) = amount else {
        return Ok(wildcard_access);
    };
    let condition = permission_condition(amount)?;
    Ok(match condition.kind() {
        ExpKind::TrueLit => wildcard_access,
        ExpKind::FalseLit => default_exp(ExpKind::TrueLit),
        _ => Exp::new(
            ExpKind::Implies(condition, wildcard_access),
            original.metadata().clone(),
        ),
    })
}
/// Source's legacy function-proof permission rewrite. Unknown product kinds
/// return an error; this is not safe for arbitrary methods with introspection.
pub fn remove_concrete_permission_amounts(root: &Node) -> Result<Node, DiagnosticError> {
    map_node_tree(root, &|node| {
        match node {
            Node::PredicateAccessPredicate(access)
                if !access
                    .permission
                    .as_ref()
                    .is_some_and(|p| matches!(p.kind(), ExpKind::WildcardPerm)) =>
            {
                let original = Exp::new(
                    ExpKind::PredicateAccessPredicate(access.clone()),
                    access.meta.clone(),
                );
                let wildcard_access = Exp::new(
                    ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                        access.location.clone(),
                        Some(wildcard()),
                        access.meta.clone(),
                    )),
                    access.meta.clone(),
                );
                return Ok(Node::Exp(rewrite_access(
                    &original,
                    wildcard_access,
                    access.permission.as_ref(),
                )?));
            }
            Node::Stmt(statement) => {
                if let StmtKind::Unfold(access) = statement.kind() {
                    let access = PredicateAccessPredicate::new(
                        access.location.clone(),
                        Some(wildcard()),
                        access.meta.clone(),
                    );
                    return Ok(Node::Stmt(Stmt::new(
                        StmtKind::Unfold(access),
                        statement.metadata().clone(),
                    )));
                }
            }
            Node::Exp(exp) => match exp.kind() {
                ExpKind::Unfolding(access, body) => {
                    if let ExpKind::PredicateAccessPredicate(p) = access.kind() {
                        let wildcard_access = Exp::new(
                            ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                                p.location.clone(),
                                Some(wildcard()),
                                p.meta.clone(),
                            )),
                            access.metadata().clone(),
                        );
                        return Ok(Node::Exp(Exp::new(
                            ExpKind::Unfolding(wildcard_access, body.clone()),
                            exp.metadata().clone(),
                        )));
                    }
                }
                ExpKind::PredicateAccessPredicate(access)
                    if !access
                        .permission
                        .as_ref()
                        .is_some_and(|p| matches!(p.kind(), ExpKind::WildcardPerm)) =>
                {
                    let wildcard_access = Exp::new(
                        ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                            access.location.clone(),
                            Some(wildcard()),
                            access.meta.clone(),
                        )),
                        exp.metadata().clone(),
                    );
                    return Ok(Node::Exp(rewrite_access(
                        exp,
                        wildcard_access,
                        access.permission.as_ref(),
                    )?));
                }
                ExpKind::FieldAccessPredicate(location, amount)
                    if !amount
                        .as_ref()
                        .is_some_and(|p| matches!(p.kind(), ExpKind::WildcardPerm)) =>
                {
                    let wildcard_access = Exp::new(
                        ExpKind::FieldAccessPredicate(location.clone(), Some(wildcard())),
                        exp.metadata().clone(),
                    );
                    return Ok(Node::Exp(rewrite_access(
                        exp,
                        wildcard_access,
                        amount.as_ref(),
                    )?));
                }
                ExpKind::Forall(vars, triggers, _) => {
                    if let Some((_, implication)) =
                        quantified_permissions::source_quantified_permission_assertion(exp)
                    {
                        let ExpKind::Implies(lhs, rhs) = implication.kind() else {
                            return Err(DiagnosticError::InvalidNode(
                                "quantified permission implication",
                            ));
                        };
                        let Node::Exp(rhs) =
                            remove_concrete_permission_amounts(&Node::Exp(rhs.clone()))?
                        else {
                            return Err(DiagnosticError::InvalidNode("quantified permission body"));
                        };
                        let complete = if let ExpKind::Implies(next_lhs, next_rhs) = rhs.kind() {
                            let condition = Exp::new(
                                ExpKind::And(lhs.clone(), next_lhs.clone()),
                                lhs.metadata().clone(),
                            );
                            Exp::new(
                                ExpKind::Implies(condition, next_rhs.clone()),
                                rhs.metadata().clone(),
                            )
                        } else {
                            Exp::new(
                                ExpKind::Implies(lhs.clone(), rhs.clone()),
                                rhs.metadata().clone(),
                            )
                        };
                        return Ok(Node::Exp(Exp::new(
                            ExpKind::Forall(vars.clone(), triggers.clone(), complete),
                            exp.metadata().clone(),
                        )));
                    }
                }
                _ => {}
            },
            _ => {}
        }
        Ok(node.clone())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::expression::{FieldAccess, LocalVar};
    use crate::ast::program::{Field, FieldData, LocalVarDecl};
    use crate::ast::r#type::Type;

    #[test]
    fn predicate_access_without_amount_becomes_wildcard() {
        let meta = Metadata::default();
        let location =
            crate::ast::expression::PredicateAccess::new(vec![], "p".into(), meta.clone());
        let access = PredicateAccessPredicate::new(location, None, meta.clone());
        let expression = Exp::new(ExpKind::PredicateAccessPredicate(access), meta);
        let result = remove_concrete_permission_amounts(&Node::Exp(expression)).unwrap();
        assert!(
            matches!(result, Node::Exp(e) if matches!(e.kind(), ExpKind::PredicateAccessPredicate(p) if p.permission.as_ref().is_some_and(|v| matches!(v.kind(), ExpKind::WildcardPerm))))
        );
    }

    #[test]
    fn quantified_permission_merges_positive_amount_guard() {
        let meta = Metadata::default();
        let x = LocalVarDecl::new("x".into(), Type::Ref, meta.clone());
        let receiver = Exp::new(ExpKind::LocalVar(x.local_var()), meta.clone());
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let permission = Exp::new(
            ExpKind::LocalVar(LocalVar::new("p".into(), Type::Perm, meta.clone())),
            meta.clone(),
        );
        let access = Exp::new(
            ExpKind::FieldAccessPredicate(
                FieldAccess::new(receiver, field, meta.clone()),
                Some(permission),
            ),
            meta.clone(),
        );
        let condition = Exp::new(
            ExpKind::LocalVar(LocalVar::new("b".into(), Type::Bool, meta.clone())),
            meta.clone(),
        );
        let body = Exp::new(ExpKind::Implies(condition, access), meta.clone());
        let forall = Exp::new(ExpKind::Forall(vec![x], vec![], body), meta);
        let Node::Exp(result) = remove_concrete_permission_amounts(&Node::Exp(forall)).unwrap()
        else {
            panic!()
        };
        assert!(
            matches!(result.kind(), ExpKind::Forall(_, _, body) if matches!(body.kind(), ExpKind::Implies(lhs, rhs) if matches!(lhs.kind(), ExpKind::And(_, _)) && matches!(rhs.kind(), ExpKind::FieldAccessPredicate(_, Some(amount)) if matches!(amount.kind(), ExpKind::WildcardPerm))))
        );
    }
}

/// Concrete collaborators must check function calls, simplify generated statements,
/// and add nested-predicate information; none is replaced by an identity fallback.
pub trait FunctionProofEngine {
    type Error;
    fn transform(
        &mut self,
        manager: &mut super::program_manager::ProgramManager,
        function: &crate::ast::program::Function,
        condition_in_ex: &crate::ast::program::LocalVarDecl,
        expression: &Exp,
        inhale: bool,
    ) -> Result<Stmt, Self::Error>;
    fn simplify(&mut self, statement: Stmt) -> Result<Stmt, Self::Error>;
    fn add_nested(&mut self, statement: Stmt) -> Result<Stmt, Self::Error>;
}
#[derive(Debug)]
pub enum FunctionProofError<E> {
    Engine(E),
    InvalidSpecification(&'static str),
    PredicateType,
    Rewrite(DiagnosticError),
}
#[derive(Default)]
pub struct FunctionProofGenerator {
    result_name: Option<String>,
    condition_name: Option<String>,
}
impl FunctionProofGenerator {
    /// Build source body/post/pre proof methods in order. The engine must provide
    /// the function-context call checks; the API never supplies a no-op substitute.
    pub fn generate<E: FunctionProofEngine>(
        &mut self,
        manager: &mut super::program_manager::ProgramManager,
        engine: &mut E,
        function: &crate::ast::program::Function,
        respect_permissions: bool,
    ) -> Result<Vec<crate::ast::program::Method>, FunctionProofError<E::Error>> {
        use crate::ast::ast::PreviousNode;
        use crate::ast::program::{Declaration, LocalVarDecl, Method, MethodData};
        use crate::ast::r#type::Type;
        use crate::plugin::standard::termination::termination_ast_extension::DecreasesSpecification;
        use std::sync::Arc;
        let spec = DecreasesSpecification::from_info(&function.meta.info)
            .map_err(FunctionProofError::InvalidSpecification)?;
        if spec.tuple.is_none() {
            return Ok(vec![]);
        }
        let nested =
            super::nested_predicates::NestedPredicates::contains_predicate_instances(&spec)
                .map_err(|_| FunctionProofError::PredicateType)?;
        let mut proofs = Vec::new();
        let mut make_condition = |manager: &mut super::program_manager::ProgramManager| {
            let name = self
                .condition_name
                .get_or_insert_with(|| manager.unique_name("$condInEx"))
                .clone();
            LocalVarDecl::new(name, Type::Bool, Metadata::default())
        };
        if let Some(body) = &function.body {
            let name = manager.unique_name(&format!("{}_termination_proof", function.name));
            let condition = make_condition(manager);
            let check = engine
                .transform(manager, function, &condition, body, false)
                .map_err(FunctionProofError::Engine)?;
            let mut check = engine.simplify(check).map_err(FunctionProofError::Engine)?;
            if nested {
                check = engine
                    .add_nested(check)
                    .map_err(FunctionProofError::Engine)?;
            }
            if check != crate::ast::utility::statements::empty_stmt() {
                proofs.push(Method::new(MethodData {
                    name,
                    formal_args: function.formal_args.clone(),
                    formal_returns: vec![],
                    pres: function.pres.clone(),
                    posts: vec![],
                    body: Some(Stmt::new(
                        StmtKind::Seqn {
                            statements: vec![check],
                            declarations: vec![],
                        },
                        Metadata::default(),
                    )),
                    meta: Metadata {
                        info: function.meta.info.clone(),
                        ..Default::default()
                    },
                }));
            }
        }
        if !function.posts.is_empty() {
            let name = manager.unique_name(&format!("{}_posts_termination_proof", function.name));
            let condition = make_condition(manager);
            let result_name = self
                .result_name
                .get_or_insert_with(|| manager.unique_name("$result"))
                .clone();
            let result_node = function.result();
            let result_meta = Metadata {
                position: result_node.metadata().position.clone(),
                info: result_node.metadata().info.clone(),
                error_trafo: crate::ast::ast::ErrorTrafo::trafos(
                    vec![],
                    vec![],
                    Some(Arc::new(PreviousNode(Node::Exp(result_node)))),
                ),
            };
            let result = LocalVarDecl::new(result_name, function.typ.clone(), result_meta);
            let result_exp = Exp::new(ExpKind::LocalVar(result.local_var()), result.meta.clone());
            let mut posts = Vec::new();
            for post in &function.posts {
                let Node::Exp(post) = crate::ast::utility::nodes::map_node_tree_bottom_up(
                    &Node::Exp(post.clone()),
                    &|node| {
                        if matches!(node, Node::Exp(e) if matches!(e.kind(), ExpKind::Result(_))) {
                            crate::ast::utility::viper_strategy::preserve_metadata(
                                node,
                                &Node::Exp(result_exp.clone()),
                                true,
                            )
                            .map_err(|_| {
                                DiagnosticError::Unsupported("result replacement metadata")
                            })
                        } else {
                            Ok(node.clone())
                        }
                    },
                    false,
                )
                .map_err(FunctionProofError::Rewrite)?
                else {
                    return Err(FunctionProofError::Rewrite(DiagnosticError::InvalidNode(
                        "postcondition",
                    )));
                };
                posts.push(post);
            }
            let mut posts = posts.into_iter();
            let mut post = posts.next().expect("nonempty posts");
            for next in posts {
                let meta = Metadata {
                    position: post.metadata().position.clone(),
                    ..Default::default()
                };
                post = Exp::new(ExpKind::And(post, next), meta);
            }
            let check = engine
                .transform(manager, function, &condition, &post, false)
                .map_err(FunctionProofError::Engine)?;
            let mut check = engine.simplify(check).map_err(FunctionProofError::Engine)?;
            if nested {
                check = engine
                    .add_nested(check)
                    .map_err(FunctionProofError::Engine)?;
            }
            if check != crate::ast::utility::statements::empty_stmt() {
                proofs.push(Method::new(MethodData {
                    name,
                    formal_args: function.formal_args.clone(),
                    formal_returns: vec![],
                    pres: function.pres.clone(),
                    posts: vec![],
                    body: Some(Stmt::new(
                        StmtKind::Seqn {
                            statements: vec![check],
                            declarations: vec![
                                Declaration::Local(result),
                                Declaration::Local(condition),
                            ],
                        },
                        Metadata::default(),
                    )),
                    meta: Metadata {
                        info: function.meta.info.clone(),
                        ..Default::default()
                    },
                }));
            }
        }
        if !function.pres.is_empty() {
            let name = manager.unique_name(&format!("{}_pres_termination_proof", function.name));
            let condition = make_condition(manager);
            let mut pres = function.pres.iter().cloned();
            let mut pre = pres.next().expect("nonempty pres");
            for next in pres {
                let meta = Metadata {
                    position: pre.metadata().position.clone(),
                    ..Default::default()
                };
                pre = Exp::new(ExpKind::And(pre, next), meta);
            }
            let check = engine
                .transform(manager, function, &condition, &pre, true)
                .map_err(FunctionProofError::Engine)?;
            let check = engine.simplify(check).map_err(FunctionProofError::Engine)?;
            if check != crate::ast::utility::statements::empty_stmt() {
                proofs.push(Method::new(MethodData {
                    name,
                    formal_args: function.formal_args.clone(),
                    formal_returns: vec![],
                    pres: vec![],
                    posts: vec![],
                    body: Some(Stmt::new(
                        StmtKind::Seqn {
                            statements: vec![check],
                            declarations: vec![Declaration::Local(condition)],
                        },
                        Metadata::default(),
                    )),
                    meta: Metadata {
                        info: function.meta.info.clone(),
                        ..Default::default()
                    },
                }));
            }
        }
        if !respect_permissions {
            for proof in &mut proofs {
                let Node::Member(crate::ast::program::Member::Method(rewritten)) =
                    remove_concrete_permission_amounts(&Node::Member(
                        crate::ast::program::Member::Method(proof.clone()),
                    ))
                    .map_err(FunctionProofError::Rewrite)?
                else {
                    return Err(FunctionProofError::Rewrite(DiagnosticError::InvalidNode(
                        "proof method",
                    )));
                };
                *proof = rewritten;
            }
        }
        Ok(proofs)
    }
}

#[cfg(test)]
mod proof_tests {
    use super::*;
    use crate::ast::program::{Function, FunctionData, Program};
    use crate::ast::r#type::Type;
    use crate::plugin::standard::termination::termination_ast_extension::{
        DecreasesClause, DecreasesKind, DecreasesSpecification,
    };

    #[derive(Default)]
    struct Engine {
        calls: Vec<bool>,
    }
    impl FunctionProofEngine for Engine {
        type Error = ();
        fn transform(
            &mut self,
            _: &mut super::super::program_manager::ProgramManager,
            _: &Function,
            _: &crate::ast::program::LocalVarDecl,
            expression: &Exp,
            inhale: bool,
        ) -> Result<Stmt, ()> {
            self.calls.push(inhale);
            Ok(Stmt::new(
                StmtKind::Assert(expression.clone()),
                Metadata::default(),
            ))
        }
        fn simplify(&mut self, statement: Stmt) -> Result<Stmt, ()> {
            Ok(statement)
        }
        fn add_nested(&mut self, statement: Stmt) -> Result<Stmt, ()> {
            Ok(statement)
        }
    }
    #[test]
    fn constructs_body_post_and_pre_proofs_in_source_order() {
        let meta = Metadata::default();
        let yes = default_exp(ExpKind::TrueLit);
        let function = Function::new(FunctionData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            pres: vec![yes.clone()],
            posts: vec![default_exp(ExpKind::Result(Type::Bool))],
            body: Some(yes),
            meta: meta.clone(),
        });
        let spec = DecreasesSpecification {
            tuple: Some(DecreasesClause::new(
                DecreasesKind::Tuple {
                    tuple: vec![],
                    condition: None,
                },
                meta.clone(),
            )),
            ..Default::default()
        };
        let function = spec.append_to_function(&function);
        let program = Program::new(
            vec![],
            vec![],
            vec![function.clone()],
            vec![],
            vec![],
            vec![],
            meta,
        );
        let mut manager =
            super::super::program_manager::ProgramManager::new(program, Vec::<String>::new());
        let mut engine = Engine::default();
        let proofs = FunctionProofGenerator::default()
            .generate(&mut manager, &mut engine, &function, true)
            .unwrap();
        assert_eq!(
            proofs.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(),
            vec![
                "f_termination_proof",
                "f_posts_termination_proof",
                "f_pres_termination_proof"
            ]
        );
        assert_eq!(engine.calls, vec![false, false, true]);
        let StmtKind::Seqn {
            statements,
            declarations,
        } = proofs[1].body.as_ref().unwrap().kind()
        else {
            panic!()
        };
        assert_eq!(declarations.len(), 2);
        assert!(
            matches!(statements[0].kind(), StmtKind::Assert(e) if matches!(e.kind(), ExpKind::LocalVar(v) if v.name == "$result"))
        );
    }
}

#[derive(Clone, Debug)]
struct FunctionCallErrorTrafo {
    call: Exp,
}
impl crate::ast::ast::ErrorTransformation for FunctionCallErrorTrafo {
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
        DiagnosticError,
    > {
        use crate::verifier::verification_error::{
            RenderedVerificationError, VerificationErrorKind,
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
        let error = crate::plugin::standard::termination::termination_errors::TerminationError::new(crate::plugin::standard::termination::termination_errors::TerminationErrorKind::Function, Node::Exp(self.call.clone()), original.error().reason.clone(), original.error().cached, original.renderer())?;
        Ok(Some(std::sync::Arc::new(error)))
    }
}
struct FunctionCalls {
    caller: crate::ast::program::Function,
    recursive: Vec<String>,
}
impl super::exp_transformer::FunctionCallHandler for FunctionCalls {
    fn transform_call(
        &self,
        transformer: &mut super::exp_transformer::ExpTransformer,
        call: &Exp,
        context: &super::exp_transformer::ExpressionContext,
    ) -> Result<Stmt, super::exp_transformer::ExpressionTransformError> {
        use super::exp_transformer::ExpressionTransformError as Error;
        use super::{
            decreases_check::{create_condition_check, create_tuple_check},
            error_trafo_factory::ReasonTrafoFactory,
        };
        use crate::ast::ast::ErrorTrafo;
        use crate::plugin::standard::termination::termination_ast_extension::{
            DecreasesKind, DecreasesSpecification,
        };
        use std::sync::Arc;
        let ExpKind::FuncApp(name, args) = call.kind() else {
            return Err(Error("expected function application".into()));
        };
        let mut statements = Vec::new();
        for arg in args {
            statements.push(transformer.transform_exp(arg, context, false)?);
        }
        let caller_spec = DecreasesSpecification::from_info(&self.caller.meta.info)
            .map_err(|e| Error(e.into()))?;
        let Some(tuple) = caller_spec.tuple else {
            return Ok(Stmt::new(
                StmtKind::Seqn {
                    statements,
                    declarations: vec![],
                },
                Metadata::default(),
            ));
        };
        let DecreasesKind::Tuple {
            tuple: caller_values,
            condition: caller_condition,
        } = &tuple.kind
        else {
            return Err(Error("invalid caller tuple".into()));
        };
        let program = transformer.manager.program.clone();
        let callee = program
            .find_function_optionally(name)
            .ok_or_else(|| Error(format!("missing function {name}")))?;
        let spec =
            DecreasesSpecification::from_info(&callee.meta.info).map_err(|e| Error(e.into()))?;
        let substitutions: Vec<_> = callee
            .formal_args
            .iter()
            .zip(args)
            .map(|(formal, actual)| {
                (
                    Exp::new(ExpKind::LocalVar(formal.local_var()), formal.meta.clone()),
                    actual.clone(),
                )
            })
            .collect();
        let substitute = |expression: &Exp| -> Result<Exp, Error> {
            match crate::ast::utility::nodes::replace_expressions(
                &Node::Exp(expression.clone()),
                &substitutions,
            )
            .map_err(|e| Error(format!("call substitution: {e:?}")))?
            {
                Node::Exp(e) => Ok(e),
                _ => Err(Error("call substitution returned a non-expression".into())),
            }
        };
        let old = |e: &Exp| Exp::new(ExpKind::Old(e.clone()), Metadata::default());
        let old_condition = caller_condition.as_ref().map(old);
        let old_values: Vec<_> = caller_values.iter().map(old).collect();
        let factory = ReasonTrafoFactory {
            offending_node: Node::Exp(tuple.clone().expression()),
        };
        let error = ErrorTrafo::trafos(
            vec![Arc::new(FunctionCallErrorTrafo { call: call.clone() })],
            vec![],
            None,
        );
        if self.recursive.contains(name) {
            if let Some(callee_tuple) = spec.tuple {
                let DecreasesKind::Tuple {
                    tuple: values,
                    condition,
                } = &callee_tuple.kind
                else {
                    return Err(Error("invalid callee tuple".into()));
                };
                let reason = ErrorTrafo::trafos(
                    vec![],
                    vec![factory.generate_tuple_condition_false(Some(Node::Exp(
                        callee_tuple.clone().expression(),
                    )))],
                    None,
                );
                statements.push(create_condition_check(
                    old_condition.clone(),
                    condition.as_ref().map(substitute).transpose()?,
                    error.clone(),
                    reason,
                ));
                let values = values
                    .iter()
                    .map(substitute)
                    .collect::<Result<Vec<_>, _>>()?;
                let mut missing = Vec::new();
                let check = create_tuple_check(
                    old_condition,
                    &old_values,
                    &values,
                    program.find_domain_function_optionally("decreasing"),
                    program.find_domain_function_optionally("bounded"),
                    error,
                    &factory,
                    |message| missing.push(message.to_owned()),
                )
                .map_err(|e| Error(format!("decreases check: {e:?}")))?;
                if !missing.is_empty() {
                    return Err(Error(missing.join("; ")));
                }
                statements.push(check);
            } else {
                let reason = ErrorTrafo::trafos(
                    vec![],
                    vec![factory.generate_tuple_condition_false(Some(Node::Member(
                        crate::ast::program::Member::Function(callee.clone()),
                    )))],
                    None,
                );
                statements.push(create_condition_check(
                    old_condition,
                    Some(default_exp(ExpKind::FalseLit)),
                    error,
                    reason,
                ));
            }
        } else {
            let reason = ErrorTrafo::trafos(
                vec![],
                vec![
                    factory.generate_termination_condition_false(Some(Node::Member(
                        crate::ast::program::Member::Function(callee.clone()),
                    ))),
                ],
                None,
            );
            statements.push(create_condition_check(
                old_condition,
                Some(substitute(&spec.termination_condition())?),
                error,
                reason,
            ));
        }
        Ok(Stmt::new(
            StmtKind::Seqn {
                statements,
                declarations: vec![],
            },
            Metadata::default(),
        ))
    }
}

/// Collect source call-graph edges from function preconditions, postconditions and bodies.
pub fn function_call_graph(
    program: &crate::ast::program::Program,
) -> Result<super::call_graph::DirectedGraph<String>, DiagnosticError> {
    fn visit(
        node: &Node,
        caller: &str,
        program: &crate::ast::program::Program,
        graph: &mut super::call_graph::DirectedGraph<String>,
    ) -> Result<(), DiagnosticError> {
        if let Node::Exp(exp) = node {
            if let ExpKind::FuncApp(name, _) = exp.kind() {
                if program.find_function_optionally(name).is_none() {
                    return Err(DiagnosticError::InvalidNode("function call graph target"));
                }
                graph.add_edge(caller.to_owned(), name.clone());
            }
        }
        for child in crate::ast::utility::nodes::subnodes(node)
            .map_err(|_| DiagnosticError::Unsupported("function call graph traversal"))?
        {
            visit(&child, caller, program, graph)?;
        }
        Ok(())
    }
    let mut graph = super::call_graph::DirectedGraph::new();
    for function in &program.functions {
        graph.add_vertex(function.name.clone());
    }
    for function in &program.functions {
        for exp in function
            .pres
            .iter()
            .chain(&function.posts)
            .chain(function.body.iter())
        {
            visit(&Node::Exp(exp.clone()), &function.name, program, &mut graph)?;
        }
    }
    Ok(graph)
}

/// Concrete call-aware proof engine. Nested instrumentation is supplied only
/// when its Scala-compatible hash and rendering services are available.
pub struct ConcreteFunctionProofEngine {
    components: Vec<Vec<String>>,
    pub nested: Option<
        Box<dyn FnMut(Stmt) -> Result<Stmt, super::exp_transformer::ExpressionTransformError>>,
    >,
}
impl ConcreteFunctionProofEngine {
    pub fn new(program: &crate::ast::program::Program) -> Result<Self, DiagnosticError> {
        let graph = function_call_graph(program)?;
        Ok(Self {
            components: super::call_graph::mutually_recursive_vertices(&graph),
            nested: None,
        })
    }
    pub fn configure_nested_services(
        &mut self,
        program: crate::ast::program::Program,
        hash: impl Fn(&[Exp]) -> Result<i32, String> + 'static,
        render: impl Fn(&[Exp]) -> Result<String, String> + 'static,
    ) {
        let mut used = std::collections::HashSet::new();
        self.nested = Some(Box::new(move |statement| {
            let mut nested =
                super::nested_predicates::NestedPredicates::new(&program, &hash, &render);
            nested.replace_used_names(std::mem::take(&mut used));
            let result = nested.add_nested_to_statement(&statement);
            used = nested.take_used_names();
            if !nested.errors.is_empty() {
                return Err(super::exp_transformer::ExpressionTransformError(format!(
                    "nested-predicate diagnostics: {:?}",
                    nested.errors
                )));
            }
            result.map_err(|e| {
                super::exp_transformer::ExpressionTransformError(format!(
                    "nested-predicate generation: {e:?}"
                ))
            })
        }));
    }
}
impl FunctionProofEngine for ConcreteFunctionProofEngine {
    type Error = super::exp_transformer::ExpressionTransformError;
    fn transform(
        &mut self,
        manager: &mut super::program_manager::ProgramManager,
        function: &crate::ast::program::Function,
        condition_in_ex: &crate::ast::program::LocalVarDecl,
        expression: &Exp,
        inhale: bool,
    ) -> Result<Stmt, Self::Error> {
        let recursive = self
            .components
            .iter()
            .find(|component| component.contains(&function.name))
            .cloned()
            .ok_or_else(|| {
                super::exp_transformer::ExpressionTransformError(
                    "function absent from call graph".into(),
                )
            })?;
        let handler = std::sync::Arc::new(FunctionCalls {
            caller: function.clone(),
            recursive,
        });
        let mut transformer = super::exp_transformer::ExpTransformer {
            manager: manager.clone(),
            call_handler: Some(handler),
        };
        let result = transformer.transform_exp(
            expression,
            &super::exp_transformer::ExpressionContext {
                condition_in_ex: Some(condition_in_ex.clone()),
            },
            inhale,
        );
        *manager = transformer.manager;
        result
    }
    fn simplify(&mut self, statement: Stmt) -> Result<Stmt, Self::Error> {
        simplifier::simplify_statement(&statement, false, &|e| {
            expressions::is_known_well_defined(e, None)
        })
        .map_err(|e| {
            super::exp_transformer::ExpressionTransformError(format!(
                "statement simplification: {e:?}"
            ))
        })
    }
    fn add_nested(&mut self, statement: Stmt) -> Result<Stmt, Self::Error> {
        match &mut self.nested {
            Some(instrument) => instrument(statement),
            None => Err(super::exp_transformer::ExpressionTransformError(
                "nested predicate hash/rendering services are not configured".into(),
            )),
        }
    }
}

#[cfg(test)]
mod concrete_engine_tests {
    use super::*;
    use crate::ast::expression::ExpExtra;
    use crate::ast::program::{Function, FunctionData, Program};
    use crate::ast::r#type::Type;
    use crate::plugin::standard::termination::termination_ast_extension::{
        DecreasesClause, DecreasesKind, DecreasesSpecification,
    };

    #[test]
    fn recursive_call_generates_decrease_check() {
        use crate::ast::program::{
            AnyLocalVarDecl, Domain, DomainData, DomainFunc, DomainFuncData, LocalVarDecl,
        };
        use crate::ast::r#type::TypeVar;
        let meta = Metadata::default();
        let variable = LocalVarDecl::new("n".into(), Type::Int, meta.clone());
        let n = Exp::new(ExpKind::LocalVar(variable.local_var()), meta.clone());
        let next = Exp::new(
            ExpKind::Sub(n.clone(), Exp::new(ExpKind::IntLit(1.into()), meta.clone())),
            meta.clone(),
        );
        let call = Exp::with_extra(
            ExpKind::FuncApp("f".into(), vec![next]),
            meta.clone(),
            ExpExtra {
                typ: Some(Type::Bool),
                ..Default::default()
            },
        );
        let function = Function::new(FunctionData {
            name: "f".into(),
            formal_args: vec![variable],
            typ: Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(call),
            meta: meta.clone(),
        });
        let spec = DecreasesSpecification {
            tuple: Some(DecreasesClause::new(
                DecreasesKind::Tuple {
                    tuple: vec![n],
                    condition: None,
                },
                meta.clone(),
            )),
            ..Default::default()
        };
        let function = spec.append_to_function(&function);
        let t = TypeVar::new("T");
        let formal = || {
            AnyLocalVarDecl::Named(LocalVarDecl::new(
                "x".into(),
                Type::Var(t.clone()),
                meta.clone(),
            ))
        };
        let domain_func = |name: &str, args| {
            DomainFunc::new(DomainFuncData {
                name: name.into(),
                formal_args: args,
                typ: Type::Bool,
                unique: false,
                interpretation: None,
                domain_name: "Order".into(),
                meta: meta.clone(),
            })
        };
        let domain = Domain::new(DomainData {
            name: "Order".into(),
            functions: vec![
                domain_func("decreasing", vec![formal(), formal()]),
                domain_func("bounded", vec![formal()]),
            ],
            axioms: vec![],
            type_vars: vec![t],
            interpretations: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![domain],
            vec![],
            vec![function.clone()],
            vec![],
            vec![],
            vec![],
            meta,
        );
        let mut manager = super::super::program_manager::ProgramManager::new(
            program.clone(),
            Vec::<String>::new(),
        );
        let mut engine = ConcreteFunctionProofEngine::new(&program).unwrap();
        let proofs = FunctionProofGenerator::default()
            .generate(&mut manager, &mut engine, &function, true)
            .unwrap();
        assert_eq!(proofs.len(), 1);
        fn has_decreasing(node: &Node) -> bool {
            if matches!(node, Node::Exp(e) if matches!(e.kind(), ExpKind::DomainFuncApp(name, _, _) if name == "decreasing"))
            {
                return true;
            }
            crate::ast::utility::nodes::subnodes(node)
                .unwrap()
                .iter()
                .any(has_decreasing)
        }
        assert!(has_decreasing(&Node::Stmt(
            proofs[0].body.as_ref().unwrap().clone()
        )));
    }

    #[test]
    fn nonrecursive_call_without_termination_spec_produces_failing_check() {
        let meta = Metadata::default();
        let callee = Function::new(FunctionData {
            name: "g".into(),
            formal_args: vec![],
            typ: Type::Bool,
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let call = Exp::with_extra(
            ExpKind::FuncApp("g".into(), vec![]),
            meta.clone(),
            ExpExtra {
                typ: Some(Type::Bool),
                ..Default::default()
            },
        );
        let caller = Function::new(FunctionData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(call),
            meta: meta.clone(),
        });
        let spec = DecreasesSpecification {
            tuple: Some(DecreasesClause::new(
                DecreasesKind::Tuple {
                    tuple: vec![],
                    condition: None,
                },
                meta.clone(),
            )),
            ..Default::default()
        };
        let caller = spec.append_to_function(&caller);
        let program = Program::new(
            vec![],
            vec![],
            vec![caller.clone(), callee],
            vec![],
            vec![],
            vec![],
            meta,
        );
        let mut manager = super::super::program_manager::ProgramManager::new(
            program.clone(),
            Vec::<String>::new(),
        );
        let mut engine = ConcreteFunctionProofEngine::new(&program).unwrap();
        let proofs = FunctionProofGenerator::default()
            .generate(&mut manager, &mut engine, &caller, true)
            .unwrap();
        assert_eq!(proofs.len(), 1);
        fn has_false_assertion(stmt: &Stmt) -> bool {
            match stmt.kind() {
                StmtKind::Assert(e) => matches!(e.kind(), ExpKind::FalseLit),
                StmtKind::Seqn { statements, .. } => statements.iter().any(has_false_assertion),
                _ => false,
            }
        }
        assert!(has_false_assertion(proofs[0].body.as_ref().unwrap()));
    }
}
