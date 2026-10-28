//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/transformation/MethodCheck.scala
//!
//! Purpose:
//! Insert termination obligations around method calls and loops.
//!
//! Planned Rust structure:
//! Port MethodCheck transformMethod, bottom-up methodStrategy, methodTransformer, loop
//! marker/counter, MContext and SCC graph.
//!
//! Behavior to preserve:
//! Skip expression traversal. For recursive calls check callee tuple condition and decrease
//! against old caller tuple; nonrecursive calls check callee termination condition, then execute
//! call. For loops check method termination condition, save tuple and condition before body, then
//! check next iteration condition and decrease; mark transformed loops to prevent repeat
//! processing. Add nested predicate information when required and preserve error mapping.
//!
//! Integration:
//! trafo, call_graph, decreases_check, nested_predicates, termination_ast_extension and errors;
//! ast rewriter and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordered checks, context, AST metadata and branch state.
//!
//! Open decisions:
//! Agree on loop marker identity, generated locals and error transformations with AST and
//! verifier.
//!
//! Status: partial; method-call and loop termination checks are implemented. Nested predicate
//! services, extension statement reconstruction and plugin lifecycle integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::decreases_check::{create_condition_check, create_tuple_check};
use super::error_trafo_factory::ReasonTrafoFactory;
use super::program_manager::ProgramManager;
use crate::ast::ast::{
    ErrorTrafo, ErrorTransformation, ExtensionInfo, Info, Metadata, PreviousNode,
};
use crate::ast::expression::{Exp, ExpKind, LocalVar};
use crate::ast::program::{Declaration, LocalVarDecl, Member, Method, Program};
use crate::ast::statement::{Stmt, StmtKind};
use crate::ast::r#type::Type;
use crate::ast::utility::nodes::{self, Node};
use crate::plugin::standard::termination::termination_ast_extension::{
    DecreasesKind, DecreasesSpecification,
};
use crate::plugin::standard::termination::termination_errors::{
    TerminationError, TerminationErrorKind,
};
use crate::verifier::verification_result::{DiagnosticError, VerificationDiagnostic};
use std::{any::Any, sync::Arc};

#[derive(Debug)]
pub struct MethodCheckError(pub String);
#[derive(Debug)]
struct Transformed;
impl ExtensionInfo for Transformed {
    fn as_any(&self) -> &dyn Any {
        self
    }
}
#[derive(Debug)]
struct MethodErrorTrafo {
    kind: TerminationErrorKind,
    offending: Node,
}
impl ErrorTransformation for MethodErrorTrafo {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn transform_error(
        &self,
        diagnostic: &Arc<dyn VerificationDiagnostic>,
    ) -> Result<Option<Arc<dyn VerificationDiagnostic>>, DiagnosticError> {
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
        Ok(Some(Arc::new(TerminationError::new(
            self.kind,
            self.offending.clone(),
            original.error().reason.clone(),
            original.error().cached,
            original.renderer(),
        )?)))
    }
}
fn error_trafo(kind: TerminationErrorKind, offending: Node) -> ErrorTrafo {
    ErrorTrafo::trafos(
        vec![Arc::new(MethodErrorTrafo { kind, offending })],
        vec![],
        None,
    )
}
fn reason_trafo(reason: Arc<dyn ErrorTransformation>) -> ErrorTrafo {
    ErrorTrafo::trafos(vec![], vec![reason], None)
}
fn exp(kind: ExpKind, meta: Metadata) -> Exp {
    Exp::new(kind, meta)
}
fn seq(statements: Vec<Stmt>, declarations: Vec<LocalVarDecl>, meta: Metadata) -> Stmt {
    Stmt::new(
        StmtKind::Seqn {
            statements,
            declarations: declarations.into_iter().map(Declaration::Local).collect(),
        },
        meta,
    )
}
fn old(e: &Exp) -> Exp {
    exp(ExpKind::Old(e.clone()), Metadata::default())
}
fn substitute(e: &Exp, substitutions: &[(Exp, Exp)]) -> Result<Exp, MethodCheckError> {
    match nodes::replace_expressions(&Node::Exp(e.clone()), substitutions)
        .map_err(|e| MethodCheckError(format!("method substitution: {e:?}")))?
    {
        Node::Exp(e) => Ok(e),
        _ => Err(MethodCheckError("expected substituted expression".into())),
    }
}
fn preserve(old: &Stmt, new: Stmt) -> Result<Stmt, MethodCheckError> {
    match crate::ast::utility::viper_strategy::preserve_metadata(
        &Node::Stmt(old.clone()),
        &Node::Stmt(new),
        true,
    )
    .map_err(|e| MethodCheckError(format!("method metadata: {e:?}")))?
    {
        Node::Stmt(stmt) => Ok(stmt),
        _ => Err(MethodCheckError("expected statement".into())),
    }
}
fn tuple(
    clause: &crate::plugin::standard::termination::termination_ast_extension::DecreasesClause,
) -> Result<(&[Exp], Option<&Exp>), MethodCheckError> {
    match &clause.kind {
        DecreasesKind::Tuple { tuple, condition } => Ok((tuple, condition.as_ref())),
        _ => Err(MethodCheckError("invalid decreases tuple".into())),
    }
}

pub struct MethodCheck {
    pub program: Program,
    components: Vec<Vec<String>>,
    while_counter: i32,
    pub nested: Option<Box<dyn FnMut(Stmt) -> Result<Stmt, MethodCheckError> + Send>>,
}
impl MethodCheck {
    pub fn new(program: Program) -> Result<Self, MethodCheckError> {
        let graph = method_call_graph(&program)?;
        Ok(Self {
            program,
            components: super::call_graph::mutually_recursive_vertices(&graph),
            while_counter: 1,
            nested: None,
        })
    }
    pub fn transform_method(
        &mut self,
        manager: &mut ProgramManager,
        method: &Method,
    ) -> Result<Method, MethodCheckError> {
        let Some(body) = &method.body else {
            return Ok(method.clone());
        };
        let spec = DecreasesSpecification::from_info(&method.meta.info)
            .map_err(|e| MethodCheckError(e.into()))?;
        let mut nested_required =
            super::nested_predicates::NestedPredicates::contains_predicate_instances(&spec)
                .map_err(|e| MethodCheckError(format!("predicate instances: {e:?}")))?;
        let recursive = self
            .components
            .iter()
            .find(|component| component.contains(&method.name))
            .cloned()
            .ok_or_else(|| MethodCheckError("method absent from call graph".into()))?;
        let mut body = self.rewrite_stmt(manager, body, &spec, &recursive, &mut nested_required)?;
        if nested_required {
            body = match &mut self.nested {
                Some(callback) => callback(body)?,
                None => {
                    return Err(MethodCheckError(
                        "nested predicate services are not configured".into(),
                    ));
                }
            };
        }
        Ok(method.copy_with(|data| data.body = Some(seq(vec![body], vec![], Metadata::default()))))
    }
    fn rewrite_stmt(
        &mut self,
        manager: &mut ProgramManager,
        original: &Stmt,
        spec: &DecreasesSpecification,
        recursive: &[String],
        nested_required: &mut bool,
    ) -> Result<Stmt, MethodCheckError> {
        let rebuilt = match original.kind() {
            StmtKind::Seqn {
                statements,
                declarations,
            } => {
                let values = statements
                    .iter()
                    .map(|s| self.rewrite_stmt(manager, s, spec, recursive, nested_required))
                    .collect::<Result<Vec<_>, _>>()?;
                if values == *statements {
                    original.clone()
                } else {
                    Stmt::new(
                        StmtKind::Seqn {
                            statements: values,
                            declarations: declarations.clone(),
                        },
                        original.metadata().clone(),
                    )
                }
            }
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let then_branch =
                    self.rewrite_stmt(manager, then_branch, spec, recursive, nested_required)?;
                let else_branch =
                    self.rewrite_stmt(manager, else_branch, spec, recursive, nested_required)?;
                if matches!(original.kind(), StmtKind::If { then_branch: a, else_branch: b, .. } if *a == then_branch && *b == else_branch)
                {
                    original.clone()
                } else {
                    Stmt::new(
                        StmtKind::If {
                            condition: condition.clone(),
                            then_branch,
                            else_branch,
                        },
                        original.metadata().clone(),
                    )
                }
            }
            StmtKind::While {
                condition,
                invariants,
                body,
            } => {
                let body = self.rewrite_stmt(manager, body, spec, recursive, nested_required)?;
                if matches!(original.kind(), StmtKind::While { body: old, .. } if *old == body) {
                    original.clone()
                } else {
                    Stmt::new(
                        StmtKind::While {
                            condition: condition.clone(),
                            invariants: invariants.clone(),
                            body,
                        },
                        original.metadata().clone(),
                    )
                }
            }
            StmtKind::Package { wand, proof_script } => {
                let proof_script =
                    self.rewrite_stmt(manager, proof_script, spec, recursive, nested_required)?;
                if matches!(original.kind(), StmtKind::Package { proof_script: old, .. } if *old == proof_script)
                {
                    original.clone()
                } else {
                    Stmt::new(
                        StmtKind::Package {
                            wand: wand.clone(),
                            proof_script,
                        },
                        original.metadata().clone(),
                    )
                }
            }
            StmtKind::Extension(_) => {
                return Err(MethodCheckError(
                    "unsupported method statement extension".into(),
                ));
            }
            _ => original.clone(),
        };
        match rebuilt.kind() {
            StmtKind::MethodCall {
                method_name, args, ..
            } => {
                let Some(caller_tuple) = &spec.tuple else {
                    return Ok(rebuilt);
                };
                let callee = self
                    .program
                    .find_method_optionally(method_name)
                    .ok_or_else(|| MethodCheckError(format!("missing method {method_name}")))?;
                let callee_spec = DecreasesSpecification::from_info(&callee.meta.info)
                    .map_err(|e| MethodCheckError(e.into()))?;
                let (caller_values, caller_condition) = tuple(caller_tuple)?;
                let replacements: Vec<_> = callee
                    .formal_args
                    .iter()
                    .zip(args)
                    .map(|(v, arg)| {
                        (
                            exp(ExpKind::LocalVar(v.local_var()), v.meta.clone()),
                            arg.clone(),
                        )
                    })
                    .collect();
                let old_condition = caller_condition.map(old);
                let old_values: Vec<_> = caller_values.iter().map(old).collect();
                let error = error_trafo(TerminationErrorKind::Method, Node::Stmt(rebuilt.clone()));
                let factory = ReasonTrafoFactory {
                    offending_node: Node::Exp(caller_tuple.clone().expression()),
                };
                let mut checks = Vec::new();
                if recursive.contains(method_name) {
                    if let Some(callee_tuple) = &callee_spec.tuple {
                        let (values, condition) = tuple(callee_tuple)?;
                        let reason = reason_trafo(factory.generate_tuple_condition_false(Some(
                            Node::Exp(callee_tuple.clone().expression()),
                        )));
                        checks.push(create_condition_check(
                            old_condition.clone(),
                            condition
                                .map(|e| substitute(e, &replacements))
                                .transpose()?,
                            error.clone(),
                            reason,
                        ));
                        let values = values
                            .iter()
                            .map(|e| substitute(e, &replacements))
                            .collect::<Result<Vec<_>, _>>()?;
                        checks.push(self.tuple_check(
                            old_condition,
                            &old_values,
                            &values,
                            error,
                            &factory,
                        )?);
                    } else {
                        let reason = reason_trafo(factory.generate_tuple_condition_false(Some(
                            Node::Member(Member::Method(callee.clone())),
                        )));
                        checks.push(create_condition_check(
                            old_condition,
                            Some(exp(ExpKind::FalseLit, Metadata::default())),
                            error,
                            reason,
                        ));
                    }
                } else {
                    let reason = reason_trafo(factory.generate_termination_condition_false(Some(
                        Node::Member(Member::Method(callee.clone())),
                    )));
                    checks.push(create_condition_check(
                        old_condition,
                        Some(substitute(
                            &callee_spec.termination_condition(),
                            &replacements,
                        )?),
                        error,
                        reason,
                    ));
                }
                checks.push(rebuilt.clone());
                let meta = Metadata {
                    position: rebuilt.metadata().position.clone(),
                    error_trafo: ErrorTrafo::trafos(
                        vec![],
                        vec![],
                        Some(Arc::new(PreviousNode(Node::Stmt(rebuilt.clone())))),
                    ),
                    ..Default::default()
                };
                preserve(&rebuilt, seq(checks, vec![], meta))
            }
            StmtKind::While {
                condition,
                invariants,
                body,
            } => self.rewrite_while(
                manager,
                &rebuilt,
                condition,
                invariants,
                body,
                spec,
                nested_required,
            ),
            _ => Ok(rebuilt),
        }
    }
    fn tuple_check(
        &self,
        condition: Option<Exp>,
        bigger: &[Exp],
        smaller: &[Exp],
        error: ErrorTrafo,
        factory: &ReasonTrafoFactory,
    ) -> Result<Stmt, MethodCheckError> {
        let mut missing = Vec::new();
        let result = create_tuple_check(
            condition,
            bigger,
            smaller,
            self.program.find_domain_function_optionally("decreasing"),
            self.program.find_domain_function_optionally("bounded"),
            error,
            factory,
            |message| missing.push(message.to_owned()),
        )
        .map_err(|e| MethodCheckError(format!("tuple check: {e:?}")))?;
        if missing.is_empty() {
            Ok(result)
        } else {
            Err(MethodCheckError(missing.join("; ")))
        }
    }
    fn rewrite_while(
        &mut self,
        manager: &mut ProgramManager,
        original: &Stmt,
        condition: &Exp,
        invariants: &[Exp],
        body: &Stmt,
        method_spec: &DecreasesSpecification,
        nested_required: &mut bool,
    ) -> Result<Stmt, MethodCheckError> {
        let spec = DecreasesSpecification::from_info(&original.metadata().info)
            .map_err(|e| MethodCheckError(e.into()))?;
        *nested_required |=
            super::nested_predicates::NestedPredicates::contains_predicate_instances(&spec)
                .map_err(|e| MethodCheckError(format!("predicate instances: {e:?}")))?;
        if !original
            .metadata()
            .info
            .all_extensions::<Transformed>()
            .is_empty()
        {
            return Ok(original.clone());
        }
        let number = self.while_counter;
        self.while_counter = self.while_counter.wrapping_add(1);
        let mut before = Vec::new();
        if let Some(method_tuple) = &method_spec.tuple {
            let error = error_trafo(TerminationErrorKind::Method, Node::Stmt(original.clone()));
            let factory = ReasonTrafoFactory {
                offending_node: Node::Exp(method_tuple.clone().expression()),
            };
            let reason = reason_trafo(
                factory.generate_termination_condition_false(Some(Node::Stmt(original.clone()))),
            );
            let required = exp(
                ExpKind::And(old(&method_tuple.effective_condition()), condition.clone()),
                Metadata::default(),
            );
            before.push(create_condition_check(
                Some(required),
                Some(spec.termination_condition()),
                error,
                reason,
            ));
        }
        let body = if let Some(loop_tuple) = &spec.tuple {
            let (values, tuple_condition) = tuple(loop_tuple)?;
            // The source allocates the condition variable first, but emits tuple
            // assignments before the condition assignment.
            let (old_condition, condition_assignment) = if let Some(value) = tuple_condition {
                let name = manager.unique_name(&format!("old_W{number}_C"));
                let variable = LocalVar::new(name.clone(), Type::Bool, value.metadata().clone());
                let assignment = Stmt::new(
                    StmtKind::LocalVarAssign {
                        lhs: variable.clone(),
                        rhs: value.clone(),
                    },
                    value.metadata().clone(),
                );
                let declaration = LocalVarDecl::new(name, Type::Bool, Metadata::default());
                (
                    exp(ExpKind::LocalVar(variable), value.metadata().clone()),
                    Some((assignment, declaration)),
                )
            } else {
                (exp(ExpKind::TrueLit, Metadata::default()), None)
            };
            let mut assignments = Vec::new();
            let mut declarations = Vec::new();
            let mut old_values = Vec::new();
            for (i, value) in values.iter().enumerate() {
                let typ = value
                    .typ()
                    .map_err(|e| MethodCheckError(format!("loop tuple type: {e:?}")))?;
                let name = manager.unique_name(&format!("old_W{number}_T{i}"));
                let variable = LocalVar::new(name.clone(), typ.clone(), value.metadata().clone());
                assignments.push(Stmt::new(
                    StmtKind::LocalVarAssign {
                        lhs: variable.clone(),
                        rhs: value.clone(),
                    },
                    value.metadata().clone(),
                ));
                declarations.push(LocalVarDecl::new(name, typ, Metadata::default()));
                old_values.push(exp(ExpKind::LocalVar(variable), value.metadata().clone()));
            }
            if let Some((assignment, declaration)) = condition_assignment {
                assignments.push(assignment);
                declarations.push(declaration);
            }
            let required = exp(
                ExpKind::And(old_condition, condition.clone()),
                Metadata::default(),
            );
            let error = error_trafo(
                TerminationErrorKind::Loop,
                Node::Exp(loop_tuple.clone().expression()),
            );
            let factory = ReasonTrafoFactory {
                offending_node: Node::Exp(loop_tuple.clone().expression()),
            };
            let reason =
                reason_trafo(factory.generate_tuple_condition_false(Some(Node::Exp(
                    loop_tuple.clone().expression(),
                ))));
            let condition_check = create_condition_check(
                Some(required.clone()),
                tuple_condition.cloned(),
                error.clone(),
                reason,
            );
            let tuple_check =
                self.tuple_check(Some(required), &old_values, values, error, &factory)?;
            assignments.push(body.clone());
            assignments.push(condition_check);
            assignments.push(tuple_check);
            seq(assignments, declarations, Metadata::default())
        } else {
            body.clone()
        };
        let mut meta = original.metadata().clone();
        meta.info = Info::pair(Info::Extension(Arc::new(Transformed)), meta.info);
        let new_loop = Stmt::new(
            StmtKind::While {
                condition: condition.clone(),
                invariants: invariants.to_vec(),
                body,
            },
            meta,
        );
        before.push(new_loop);
        preserve(original, seq(before, vec![], Metadata::default()))
    }
}

pub fn method_call_graph(
    program: &Program,
) -> Result<super::call_graph::DirectedGraph<String>, MethodCheckError> {
    fn visit(
        node: &Node,
        caller: &str,
        program: &Program,
        graph: &mut super::call_graph::DirectedGraph<String>,
    ) -> Result<(), MethodCheckError> {
        if let Node::Stmt(statement) = node {
            if let StmtKind::MethodCall { method_name, .. } = statement.kind() {
                if program.find_method_optionally(method_name).is_none() {
                    return Err(MethodCheckError(format!("missing method {method_name}")));
                }
                graph.add_edge(caller.to_owned(), method_name.clone());
            }
        }
        for child in nodes::subnodes(node)
            .map_err(|e| MethodCheckError(format!("method call graph: {e:?}")))?
        {
            visit(&child, caller, program, graph)?;
        }
        Ok(())
    }
    let mut graph = super::call_graph::DirectedGraph::new();
    for method in &program.methods {
        graph.add_vertex(method.name.clone());
    }
    for method in &program.methods {
        if let Some(body) = &method.body {
            visit(&Node::Stmt(body.clone()), &method.name, program, &mut graph)?;
        }
    }
    Ok(graph)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::program::{
        AnyLocalVarDecl, Domain, DomainData, DomainFunc, DomainFuncData, MethodData,
    };
    use crate::ast::r#type::TypeVar;
    use crate::plugin::standard::termination::termination_ast_extension::DecreasesClause;

    fn spec(meta: &Metadata, values: Vec<Exp>) -> DecreasesSpecification {
        DecreasesSpecification {
            tuple: Some(DecreasesClause::new(
                DecreasesKind::Tuple {
                    tuple: values,
                    condition: None,
                },
                meta.clone(),
            )),
            ..Default::default()
        }
    }
    #[test]
    fn nonrecursive_call_checks_callee_termination_before_call() {
        let meta = Metadata::default();
        let call = Stmt::new(
            StmtKind::MethodCall {
                method_name: "g".into(),
                args: vec![],
                targets: vec![],
            },
            meta.clone(),
        );
        let make = |name: &str, body| {
            Method::new(MethodData {
                name: name.into(),
                formal_args: vec![],
                formal_returns: vec![],
                pres: vec![],
                posts: vec![],
                body,
                meta: meta.clone(),
            })
        };
        let caller = spec(&meta, vec![]).append_to_method(&make("f", Some(call)));
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![caller.clone(), make("g", None)],
            vec![],
            meta,
        );
        let mut checker = MethodCheck::new(program.clone()).unwrap();
        let mut manager = ProgramManager::new(program, Vec::<String>::new());
        let result = checker.transform_method(&mut manager, &caller).unwrap();
        let StmtKind::Seqn { statements, .. } = result.body.as_ref().unwrap().kind() else {
            panic!()
        };
        let StmtKind::Seqn { statements, .. } = statements[0].kind() else {
            panic!()
        };
        assert!(
            matches!(statements[0].kind(), StmtKind::Assert(e) if matches!(e.kind(), ExpKind::FalseLit))
        );
        assert!(
            matches!(statements[1].kind(), StmtKind::MethodCall { method_name, .. } if method_name == "g")
        );
    }
    #[test]
    fn loop_snapshots_measure_before_body_and_checks_after() {
        let meta = Metadata::default();
        let value = exp(ExpKind::IntLit(3.into()), meta.clone());
        let condition = exp(ExpKind::TrueLit, meta.clone());
        let loop_stmt = Stmt::new(
            StmtKind::While {
                condition,
                invariants: vec![],
                body: crate::ast::utility::statements::empty_stmt(),
            },
            meta.clone(),
        );
        let loop_stmt = spec(&meta, vec![value])
            .append_to_while(&loop_stmt)
            .unwrap();
        let method = Method::new(MethodData {
            name: "f".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(loop_stmt),
            meta: meta.clone(),
        });
        let t = TypeVar::new("T");
        let formal = || {
            AnyLocalVarDecl::Named(LocalVarDecl::new(
                "x".into(),
                Type::Var(t.clone()),
                meta.clone(),
            ))
        };
        let fun = |name: &str, args| {
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
                fun("decreasing", vec![formal(), formal()]),
                fun("bounded", vec![formal()]),
            ],
            axioms: vec![],
            type_vars: vec![t],
            interpretations: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![domain],
            vec![],
            vec![],
            vec![],
            vec![method.clone()],
            vec![],
            meta,
        );
        let mut checker = MethodCheck::new(program.clone()).unwrap();
        let mut manager = ProgramManager::new(program, Vec::<String>::new());
        let result = checker.transform_method(&mut manager, &method).unwrap();
        let StmtKind::Seqn { statements, .. } = result.body.as_ref().unwrap().kind() else {
            panic!()
        };
        let StmtKind::Seqn { statements, .. } = statements[0].kind() else {
            panic!()
        };
        let StmtKind::While { body, .. } = statements[0].kind() else {
            panic!()
        };
        let StmtKind::Seqn {
            statements,
            declarations,
        } = body.kind()
        else {
            panic!()
        };
        assert_eq!(declarations.len(), 1);
        assert!(
            matches!(statements[0].kind(), StmtKind::LocalVarAssign { lhs, .. } if lhs.name == "old_W1_T0")
        );
        assert!(matches!(
            statements.last().unwrap().kind(),
            StmtKind::Assert(_)
        ));
    }
}
