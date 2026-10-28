//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/predicateinstance/PredicateInstancePlugin.scala
//!
//! Purpose:
//! Lower predicate instance expressions into generated functions guarded by predicate permission.
//!
//! Planned Rust structure:
//! Port PredicateInstancePlugin predicateInstance parser, beforeParse/beforeVerify, generated
//! function cache and entity/program error mapping.
//!
//! Behavior to preserve:
//! Register # expression at start. Bottom-up rewrite creates one PI_<predicate> function per used
//! predicate in insertion order with wildcard predicate-access precondition and PredicateInstance
//! domain result, appending them to functions. Report missing domain as consistency error; map
//! PreconditionInAppFalse through ErrTrafo to PredicateInstanceNoAccess.
//!
//! Integration:
//! parser::fast_parser and translator; predicate_instance AST/PAST/errors, ast::utility::rewriter
//! and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, diagnostics and AST identity.
//!
//! Open decisions:
//! Agree on generated names, domain resolution and error transformation with ast and verifier.
//!
//! Status: partial; bottom-up instance lowering and ordered function generation implemented.
//! Parser feature, program lowering and fallible result mapping are connected. Some node and
//! reason back-transformations and generic extension traversal remain explicitly unsupported.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::predicate_instance_ast_extension::PredicateInstance;
use crate::ast::ast::{ErrorTrafo, ErrorTransformation, Metadata};
use crate::ast::expression::{Exp, ExpExtra, ExpKind, ExtensionExpHandle, PredicateAccess};
use crate::ast::program::{Function, FunctionData, Program};
use crate::ast::statement::PredicateAccessPredicate;
use crate::ast::r#type::{DomainType, Type};
use crate::ast::utility::nodes::{
    Node, NodeReplacementError, map_expression_roots_with_extensions,
};
use crate::ast::utility::rewriter::strategy::{
    ExpressionRewriteError, rewrite_expression_bottom_up,
};
use crate::ast::utility::statements::StatementReplacementError;
use std::{any::Any, cell::RefCell, sync::Arc};

/// Source partial error transformation for generated applications. The general
/// diagnostic back-transformation pipeline must invoke it before verification results are used.
#[derive(Debug)]
pub struct PredicateInstanceErrorTrafo;
impl ErrorTransformation for PredicateInstanceErrorTrafo {
    fn as_any(&self) -> &dyn Any {
        self
    }
    fn transform_error(
        &self,
        diagnostic: &Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>,
    ) -> Result<
        Option<Arc<dyn crate::verifier::verification_result::VerificationDiagnostic>>,
        crate::verifier::verification_result::DiagnosticError,
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
        let VerificationErrorKind::PreconditionInAppFalse(expression) = &original.error().kind
        else {
            return Ok(None);
        };
        Ok(Some(
            super::predicate_instance_errors::PredicateInstanceNoAccess {
                offending_node: Node::Exp(expression.clone()),
                scope: Default::default(),
                reason: original.error().reason.clone(),
                cached: original.error().cached,
                failure_contexts: Vec::new(),
                renderer: original.renderer(),
            }
            .into_diagnostic()?,
        ))
    }
}
#[derive(Debug)]
pub enum PredicateInstanceLoweringError {
    MissingDomain,
    MissingPredicate(String),
    UnsupportedExtension,
    Reconstruction,
}
impl From<NodeReplacementError> for PredicateInstanceLoweringError {
    fn from(_: NodeReplacementError) -> Self {
        Self::Reconstruction
    }
}
impl From<StatementReplacementError> for PredicateInstanceLoweringError {
    fn from(_: StatementReplacementError) -> Self {
        Self::Reconstruction
    }
}
/// Construct the source bottom-up lowering and generated predicate-instance
/// functions. This is not a verifier hook yet: executing the error transformation
/// attached to the generated applications is required before verification.
pub fn lower_predicate_instances(
    program: &Program,
) -> Result<Program, PredicateInstanceLoweringError> {
    use PredicateInstanceLoweringError as Error;
    let created: RefCell<Vec<(String, Function)>> = RefCell::new(Vec::new());
    let mapper = |root: &Exp| -> Result<Exp, Error> {
        let extension = |handle: &ExtensionExpHandle,
                         recur: &mut dyn FnMut(
            &Exp,
        )
            -> Result<Exp, ExpressionRewriteError<Error>>| {
            if let Some(instance) = handle.0.as_any().downcast_ref::<PredicateInstance>() {
                let args = instance
                    .args
                    .iter()
                    .map(recur)
                    .collect::<Result<Vec<_>, _>>()?;
                if args == instance.args {
                    return Ok(handle.clone());
                }
                return Ok(ExtensionExpHandle(Arc::new(PredicateInstance {
                    predicate: instance.predicate.clone(),
                    args,
                    meta: instance.meta.clone(),
                })));
            }
            // Other extension expressions provide their own typed child reconstruction.
            // Keep the actual recursive failure rather than replacing it with a success.
            let failure = RefCell::new(None);
            let recur = RefCell::new(recur);
            let result = handle
                .0
                .map_expressions(&|child| match (recur.borrow_mut())(child) {
                    Ok(value) => Ok(value),
                    Err(error) => {
                        *failure.borrow_mut() = Some(error);
                        Err(
                            crate::verifier::verification_result::DiagnosticError::Unsupported(
                                "predicate instance child rewrite",
                            ),
                        )
                    }
                });
            if let Some(error) = failure.into_inner() {
                return Err(error);
            }
            result.map_err(|_| ExpressionRewriteError::Callback(Error::UnsupportedExtension))
        };
        let mut rule = |expression: &Exp| -> Result<Exp, Error> {
            let ExpKind::Extension(extension) = expression.kind() else {
                return Ok(expression.clone());
            };
            let Some(instance) = extension.0.as_any().downcast_ref::<PredicateInstance>() else {
                return Ok(expression.clone());
            };
            let domain = program
                .domains
                .iter()
                .find(|d| d.name == "PredicateInstance")
                .ok_or(Error::MissingDomain)?;
            let existing = created
                .borrow()
                .iter()
                .find(|(name, _)| name == &instance.predicate)
                .map(|(_, function)| function.clone());
            let function = if let Some(function) = existing {
                function
            } else {
                let predicate = program
                    .predicates
                    .iter()
                    .find(|p| p.name == instance.predicate)
                    .ok_or_else(|| Error::MissingPredicate(instance.predicate.clone()))?;
                let args = predicate
                    .formal_args
                    .iter()
                    .map(|arg| Exp::new(ExpKind::LocalVar(arg.local_var()), arg.meta.clone()))
                    .collect();
                let access =
                    PredicateAccess::new(args, predicate.name.clone(), instance.meta.clone());
                let permission = Exp::new(ExpKind::WildcardPerm, Metadata::default());
                let pre = Exp::new(
                    ExpKind::PredicateAccessPredicate(PredicateAccessPredicate::new(
                        access,
                        Some(permission),
                        instance.meta.clone(),
                    )),
                    instance.meta.clone(),
                );
                let typ = Type::Domain(DomainType::new(
                    domain.name.clone(),
                    Default::default(),
                    domain.type_vars.clone(),
                ));
                let function = Function::new(FunctionData {
                    name: format!("PI_{}", instance.predicate),
                    formal_args: predicate.formal_args.clone(),
                    typ,
                    pres: vec![pre],
                    posts: vec![],
                    body: None,
                    meta: Metadata {
                        position: domain.meta.position.clone(),
                        info: domain.meta.info.clone(),
                        ..Metadata::default()
                    },
                });
                created
                    .borrow_mut()
                    .push((instance.predicate.clone(), function.clone()));
                function
            };
            let mut meta = instance.meta.clone();
            meta.error_trafo =
                ErrorTrafo::trafos(vec![Arc::new(PredicateInstanceErrorTrafo)], vec![], None);
            let replacement = Exp::with_extra(
                ExpKind::FuncApp(function.name.clone(), instance.args.clone()),
                meta,
                ExpExtra {
                    typ: Some(function.typ.clone()),
                    ..Default::default()
                },
            );
            let Node::Exp(replacement) = crate::ast::utility::viper_strategy::preserve_metadata(
                &Node::Exp(expression.clone()),
                &Node::Exp(replacement),
                true,
            )
            .map_err(|_| Error::Reconstruction)?
            else {
                return Err(Error::Reconstruction);
            };
            Ok(replacement)
        };
        rewrite_expression_bottom_up(root, &mut rule, &extension).map_err(|e| match e {
            ExpressionRewriteError::Callback(e) => e,
            _ => Error::Reconstruction,
        })
    };
    fn rewrite_statement(
        handle: &crate::ast::statement::ExtensionStmtHandle,
        map: &dyn Fn(&Exp) -> Result<Exp, Error>,
    ) -> Result<crate::ast::statement::ExtensionStmtHandle, Error> {
        use crate::verifier::verification_result::DiagnosticError;
        let failure = std::cell::RefCell::new(None);
        let with_expressions = handle.0.map_expressions(&|exp| {
            map(exp).map_err(|e| {
                *failure.borrow_mut() = Some(e);
                DiagnosticError::Unsupported("predicate instance expression rewrite")
            })
        });
        if let Some(error) = failure.borrow_mut().take() {
            return Err(error);
        }
        let with_expressions = with_expressions.map_err(|_| Error::UnsupportedExtension)?;
        let with_statements =
            with_expressions
                .0
                .map_statements(&|stmt| match map_expression_roots_with_extensions(
                    &Node::Stmt(stmt.clone()),
                    map,
                    &rewrite_statement,
                ) {
                    Ok(Node::Stmt(mapped)) => Ok(mapped),
                    Ok(_) => Err(DiagnosticError::InvalidNode("statement")),
                    Err(e) => {
                        *failure.borrow_mut() = Some(e);
                        Err(DiagnosticError::Unsupported(
                            "predicate instance statement rewrite",
                        ))
                    }
                });
        if let Some(error) = failure.into_inner() {
            return Err(error);
        }
        let mapped = with_statements
            .map_err(|_| Error::UnsupportedExtension)?
            .unwrap_or(with_expressions);
        Ok(if mapped == *handle {
            handle.clone()
        } else {
            mapped
        })
    }
    let Node::Program(rewritten) = map_expression_roots_with_extensions(
        &Node::Program(program.clone()),
        &mapper,
        &rewrite_statement,
    )?
    else {
        return Err(Error::Reconstruction);
    };
    let functions = created
        .into_inner()
        .into_iter()
        .map(|(_, f)| f)
        .collect::<Vec<_>>();
    Ok(rewritten.copy_with(|p| p.functions.extend(functions)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::program::{Domain, DomainData, Predicate, PredicateData};
    #[test]
    fn lowers_instances_inside_refute_statements() {
        use crate::parser::fast_parser::{ParserFeature, parse_program_with_features};
        use crate::parser::resolver::{NameAnalyser, check_program_core};
        use crate::parser::translator::translate_program_core;
        let program = parse_program_with_features(
            "domain PredicateInstance {} predicate p() method m() { refute #p() == #p(); }",
            "test.vpr",
            &[ParserFeature::Refute, ParserFeature::PredicateInstance],
        )
        .unwrap();
        crate::parser::parse_ast::init_properties(program.node()).unwrap();
        assert!(NameAnalyser::default().run(program.node()).unwrap());
        check_program_core(&program, &mut |_, _| {}).unwrap();
        let program =
            lower_predicate_instances(&translate_program_core(&program).unwrap()).unwrap();
        assert_eq!(program.functions.len(), 1);
        let crate::ast::statement::StmtKind::Seqn { statements, .. } =
            program.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!("body")
        };
        let crate::ast::statement::StmtKind::Extension(extension) = statements[0].kind() else {
            panic!("refute")
        };
        let refute = extension
            .0
            .as_any()
            .downcast_ref::<crate::plugin::standard::refute::refute_ast_extension::Refute>()
            .unwrap();
        assert!(
            matches!(refute.exp.kind(), ExpKind::EqCmp(left, _) if matches!(left.kind(), ExpKind::FuncApp(..)))
        );
    }
    #[test]
    fn generated_application_precondition_maps_to_original_instance_error() {
        use crate::ast::program::{Domain, DomainData, Predicate, PredicateData};
        use crate::verifier::verification_error::{
            ErrorNodeRenderer, ErrorReason, RenderedVerificationError, VerificationError,
            VerificationErrorKind,
        };
        use crate::verifier::verification_result::{DiagnosticError, VerificationDiagnostic};
        #[derive(Debug)]
        struct Renderer;
        impl ErrorNodeRenderer for Renderer {
            fn render_node(&self, _: &Node) -> Result<String, DiagnosticError> {
                Ok("p()".into())
            }
        }
        let meta = Metadata::default();
        let domain = Domain::new(DomainData {
            name: "PredicateInstance".into(),
            functions: vec![],
            axioms: vec![],
            type_vars: vec![],
            interpretations: None,
            meta: meta.clone(),
        });
        let pred = Predicate::new(PredicateData {
            name: "p".into(),
            formal_args: vec![],
            body: None,
            meta: meta.clone(),
        });
        let instance = PredicateInstance {
            predicate: "p".into(),
            args: vec![],
            meta: meta.clone(),
        }
        .expression();
        let f = Function::new(FunctionData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(instance),
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![domain],
            vec![],
            vec![f],
            vec![pred],
            vec![],
            vec![],
            meta.clone(),
        );
        let lowered = lower_predicate_instances(&program).unwrap();
        let call = lowered.functions[0].body.as_ref().unwrap().clone();
        let reason = ErrorReason::AssertionFalse(Exp::new(ExpKind::FalseLit, meta));
        let original = RenderedVerificationError::new(
            VerificationError::new(VerificationErrorKind::PreconditionInAppFalse(call), reason),
            Arc::new(Renderer),
        )
        .unwrap();
        let mapped = original.transformed_error().unwrap();
        assert_eq!(
            mapped.full_id(),
            "predicateinstance.no.access:assertion.false"
        );
        assert!(
            matches!(mapped.offending_node().unwrap(), Node::Exp(e) if matches!(e.kind(), ExpKind::Extension(h) if h.0.as_any().is::<PredicateInstance>()))
        );
    }
    #[test]
    fn generates_one_function_for_repeated_instances() {
        let meta = Metadata::default();
        let domain = Domain::new(DomainData {
            name: "PredicateInstance".into(),
            functions: vec![],
            axioms: vec![],
            type_vars: vec![],
            interpretations: None,
            meta: meta.clone(),
        });
        let predicate = Predicate::new(PredicateData {
            name: "p".into(),
            formal_args: vec![],
            body: None,
            meta: meta.clone(),
        });
        let instance = || {
            PredicateInstance {
                predicate: "p".into(),
                args: vec![],
                meta: meta.clone(),
            }
            .expression()
        };
        let body = Exp::new(ExpKind::EqCmp(instance(), instance()), meta.clone());
        let input_function = Function::new(FunctionData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![domain],
            vec![],
            vec![input_function],
            vec![predicate],
            vec![],
            vec![],
            meta,
        );
        let output = lower_predicate_instances(&program).unwrap();
        assert_eq!(output.functions.len(), 2);
        assert_eq!(output.functions[1].name, "PI_p");
        assert_eq!(output.functions[1].pres.len(), 1);
        assert!(
            matches!(output.functions[0].body.as_ref().unwrap().kind(), ExpKind::EqCmp(left, right) if matches!(left.kind(), ExpKind::FuncApp(..)) && matches!(right.kind(), ExpKind::FuncApp(..)))
        );
    }
}

/// Registers predicate-instance syntax, lowering and fallible result mapping.
pub struct PredicateInstancePlugin;
impl crate::plugin::silver_plugin::SilverPlugin for PredicateInstancePlugin {
    fn parser_features(&self) -> Vec<crate::parser::fast_parser::ParserFeature> {
        vec![crate::parser::fast_parser::ParserFeature::PredicateInstance]
    }
    fn before_verify(
        &mut self,
        program: Program,
    ) -> Result<Program, crate::plugin::silver_plugin::PluginHookError> {
        lower_predicate_instances(&program).map_err(|e| {
            crate::plugin::silver_plugin::PluginHookError(format!(
                "predicate instance lowering: {e:?}"
            ))
        })
    }
    fn map_entity_verification_result(
        &mut self,
        _: &crate::reporter::package::Entity,
        result: crate::verifier::verification_result::VerificationResult,
    ) -> Result<
        crate::verifier::verification_result::VerificationResult,
        crate::plugin::silver_plugin::PluginHookError,
    > {
        map_predicate_instance_result(result)
    }
    fn map_verification_result(
        &mut self,
        _: &Program,
        result: crate::verifier::verification_result::VerificationResult,
    ) -> Result<
        crate::verifier::verification_result::VerificationResult,
        crate::plugin::silver_plugin::PluginHookError,
    > {
        map_predicate_instance_result(result)
    }
}
fn map_predicate_instance_result(
    result: crate::verifier::verification_result::VerificationResult,
) -> Result<
    crate::verifier::verification_result::VerificationResult,
    crate::plugin::silver_plugin::PluginHookError,
> {
    use crate::verifier::verification_error::{RenderedVerificationError, VerificationErrorKind};
    use crate::verifier::verification_result::{AbstractError, VerificationResult};
    let VerificationResult::Failure(errors) = result else {
        return Ok(result);
    };
    let mut output = Vec::with_capacity(errors.len());
    for error in errors {
        if let AbstractError::Verification(diagnostic) = &error {
            if let Some(typed) = diagnostic
                .as_any()
                .downcast_ref::<RenderedVerificationError>()
            {
                if matches!(
                    typed.error().kind,
                    VerificationErrorKind::PreconditionInAppFalse(_)
                ) {
                    output.push(AbstractError::Verification(
                        diagnostic.transformed_error().map_err(|e| {
                            crate::plugin::silver_plugin::PluginHookError(format!(
                                "predicate instance error transformation: {e:?}"
                            ))
                        })?,
                    ));
                    continue;
                }
            } else if diagnostic
                .full_id()
                .starts_with("application.precondition:")
            {
                return Err(crate::plugin::silver_plugin::PluginHookError(
                    "cannot inspect function precondition diagnostic".into(),
                ));
            }
        }
        output.push(error);
    }
    Ok(VerificationResult::Failure(output))
}
