//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/refute/RefutePlugin.scala
//!
//! Purpose:
//! Implement refutation by lowering refute to nondeterministically reached assertions and
//! interpreting results.
//!
//! Planned Rust structure:
//! Port RefutePlugin parser, beforeParse/beforeVerify and entity/program result mappings,
//! mapVerificationResultsForNode and NodeWithRefuteInfo.
//!
//! Behavior to preserve:
//! Register keyword and end-statement parser; per method replace each Refute by a fresh local
//! nondeterministic branch containing Assert tagged RefuteInfo then synthesized inhale false.
//! Remove matching AssertFailed errors, preserve others, and add RefuteFailed for contained tagged
//! assertions without errors, matching source refute plus position. Use same mapping for entity
//! and overall results.
//!
//! Integration:
//! plugin::standard::refute::{refute_ast_extension,refute_past_extension,refute_errors}; parser,
//! ast::utility::rewriter, verifier results and reporter entities; smoke runs before refute.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for node identity, error transformations and ordered traversal.
//!
//! Open decisions:
//! Agree on tag identity, traversal and per-entity versus overall result mapping with reporter and
//! smoke.
//!
//! Status: partial; refute lowering, core method-body traversal and result mapping are
//! implemented as fallible plugin hooks. Parser registration and general extension traversal
//! remain pending; do not use lowering without its result mapping.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use super::refute_ast_extension::{Refute, RefuteInfo};
use crate::ast::ast::{Info, Metadata};
use crate::ast::expression::{Exp, ExpKind};
use crate::ast::program::{Declaration, LocalVarDecl};
use crate::ast::statement::{Stmt, StmtKind};
use crate::ast::r#type::Type;
use std::sync::Arc;

/// Construct the source plugin's nondeterministic branch for one refute statement.
/// `number` is the one-based encounter index within its method. Result mapping must
/// be installed before this lowering is used for verification.
pub fn lower_refute(refute: &Refute, number: usize) -> Stmt {
    let position = refute.meta.position.clone();
    let plain = || Metadata {
        position: position.clone(),
        ..Metadata::default()
    };
    let local = LocalVarDecl::new(
        format!("__plugin_refute_nondet{number}"),
        Type::Bool,
        plain(),
    );
    let mut assert_meta = plain();
    assert_meta.info = Info::Extension(Arc::new(RefuteInfo {
        refute: refute.clone(),
    }));
    let assertion = Stmt::new(StmtKind::Assert(refute.exp.clone()), assert_meta);
    let mut inhale_meta = plain();
    inhale_meta.info = Info::Synthesized;
    let inhale = Stmt::new(
        StmtKind::Inhale(Exp::new(ExpKind::FalseLit, plain())),
        inhale_meta,
    );
    let branch = Stmt::new(
        StmtKind::Seqn {
            statements: vec![assertion, inhale],
            declarations: vec![],
        },
        plain(),
    );
    let empty = Stmt::new(
        StmtKind::Seqn {
            statements: vec![],
            declarations: vec![],
        },
        plain(),
    );
    let condition = Exp::new(ExpKind::LocalVar(local.local_var()), plain());
    let conditional = Stmt::new(
        StmtKind::If {
            condition,
            then_branch: branch,
            else_branch: empty,
        },
        plain(),
    );
    Stmt::new(
        StmtKind::Seqn {
            statements: vec![conditional],
            declarations: vec![Declaration::Local(local)],
        },
        plain(),
    )
}

/// Rewrite refutes in a method body in source traversal order. Extension statements
/// other than Refute need their own reconstruction adapter before they can be traversed.
pub fn lower_method_body(body: &Stmt) -> Result<Stmt, &'static str> {
    fn visit(stmt: &Stmt, count: &mut usize) -> Result<Stmt, &'static str> {
        use crate::ast::utility::nodes::Node;
        let kind = match stmt.kind() {
            StmtKind::Extension(extension) => {
                let Some(refute) = extension.0.as_any().downcast_ref::<Refute>() else {
                    return Err("unsupported extension statement traversal");
                };
                *count += 1;
                let replacement = lower_refute(refute, *count);
                let Node::Stmt(replacement) =
                    crate::ast::utility::viper_strategy::preserve_metadata(
                        &Node::Stmt(stmt.clone()),
                        &Node::Stmt(replacement),
                        true,
                    )
                    .map_err(|_| "refute rewrite metadata")?
                else {
                    return Err("refute rewrite metadata");
                };
                return Ok(replacement);
            }
            StmtKind::Seqn {
                statements,
                declarations,
            } => StmtKind::Seqn {
                statements: statements
                    .iter()
                    .map(|s| visit(s, count))
                    .collect::<Result<_, _>>()?,
                declarations: declarations.clone(),
            },
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => StmtKind::If {
                condition: condition.clone(),
                then_branch: visit(then_branch, count)?,
                else_branch: visit(else_branch, count)?,
            },
            StmtKind::While {
                condition,
                invariants,
                body,
            } => StmtKind::While {
                condition: condition.clone(),
                invariants: invariants.clone(),
                body: visit(body, count)?,
            },
            StmtKind::Package { wand, proof_script } => StmtKind::Package {
                wand: wand.clone(),
                proof_script: visit(proof_script, count)?,
            },
            _ => return Ok(stmt.clone()),
        };
        if &kind == stmt.kind() {
            Ok(stmt.clone())
        } else {
            Ok(Stmt::new(kind, stmt.metadata().clone()))
        }
    }
    visit(body, &mut 0)
}

/// Map verification errors against tagged assertions in an already-lowered node.
/// Unsupported diagnostic or traversal adapters are reported instead of treating an
/// uninspectable assertion failure as a successful refutation.
pub fn map_refute_results(
    root: &crate::ast::utility::nodes::Node,
    input: crate::verifier::verification_result::VerificationResult,
    renderer: Arc<dyn crate::verifier::verification_error::ErrorNodeRenderer>,
) -> Result<crate::verifier::verification_result::VerificationResult, &'static str> {
    use super::refute_errors::{RefutationTrue, RefuteFailed};
    use crate::ast::utility::nodes::{Node, subnodes};
    use crate::verifier::verification_error::{RenderedVerificationError, VerificationErrorKind};
    use crate::verifier::verification_result::{AbstractError, VerificationResult};
    fn tag(stmt: &Stmt) -> Result<Option<Refute>, &'static str> {
        let tags = stmt.metadata().info.all_extensions::<RefuteInfo>();
        if tags.len() > 1 {
            return Err("multiple refute metadata entries");
        }
        Ok(tags.first().map(|tag| tag.refute.clone()))
    }
    fn collect(node: &Node, result: &mut Vec<Refute>) -> Result<(), &'static str> {
        if let Node::Stmt(stmt) = node {
            if let Some(refute) = tag(stmt)? {
                result.push(refute);
            }
        }
        for child in subnodes(node).map_err(|_| "refute node traversal")? {
            collect(&child, result)?;
        }
        Ok(())
    }
    fn same_refute(a: &Refute, b: &Refute) -> bool {
        a.exp == b.exp && a.meta.position == b.meta.position
    }
    let mut failed = Vec::new();
    let mut other = Vec::new();
    if let VerificationResult::Failure(errors) = input {
        for error in errors {
            if let AbstractError::Verification(diagnostic) = &error {
                if let Some(typed) = diagnostic
                    .as_any()
                    .downcast_ref::<RenderedVerificationError>()
                {
                    if let VerificationErrorKind::AssertFailed(stmt) = &typed.error().kind {
                        if let Some(refute) = tag(stmt)? {
                            failed.push(refute);
                            continue;
                        }
                    }
                } else if diagnostic.full_id().starts_with("assert.failed:") {
                    return Err("cannot inspect assertion failure diagnostic");
                }
            }
            other.push(error);
        }
    }
    let mut contained = Vec::new();
    collect(root, &mut contained)?;
    for refute in contained {
        if !failed.iter().any(|f| same_refute(f, &refute)) {
            other.push(AbstractError::Verification(Arc::new(RefuteFailed {
                reason: crate::verifier::verification_error::ErrorReason::Extension(
                    crate::verifier::verification_error::ExtensionErrorReasonHandle(Arc::new(
                        RefutationTrue {
                            offending_node: crate::ast::utility::nodes::Node::Exp(
                                refute.exp.clone(),
                            ),
                        },
                    )),
                ),
                offending_stmt: refute.clone().statement(),
                offending_node: refute,
                cached: false,
                failure_contexts: Vec::new(),
                renderer: renderer.clone(),
            })));
        }
    }
    Ok(if other.is_empty() {
        VerificationResult::Success
    } else {
        VerificationResult::Failure(other)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::utility::nodes::Node;
    use crate::verifier::verification_error::ErrorNodeRenderer;
    use crate::verifier::verification_result::{DiagnosticError, VerificationResult};
    #[derive(Debug)]
    struct Renderer;
    impl ErrorNodeRenderer for Renderer {
        fn render_node(&self, _: &Node) -> Result<String, DiagnosticError> {
            Ok("false".into())
        }
    }
    #[test]
    fn refute_result_requires_a_matching_assert_failure() {
        let original = Refute::new(
            Exp::new(ExpKind::FalseLit, Metadata::default()),
            Metadata::default(),
        );
        let lowered = lower_method_body(&original.clone().statement()).unwrap();
        let result = map_refute_results(
            &Node::Stmt(lowered),
            VerificationResult::Success,
            Arc::new(Renderer),
        )
        .unwrap();
        let VerificationResult::Failure(errors) = result else {
            panic!("refutation must fail")
        };
        assert_eq!(errors[0].full_id(), "refute.failed:refutation.true");
        let lowered = lower_method_body(&original.clone().statement()).unwrap();
        let StmtKind::Seqn { statements, .. } = lowered.kind() else {
            panic!("sequence")
        };
        let StmtKind::If { then_branch, .. } = statements[0].kind() else {
            panic!("if")
        };
        let StmtKind::Seqn { statements, .. } = then_branch.kind() else {
            panic!("branch")
        };
        let error = crate::verifier::verification_error::VerificationError::new(
            crate::verifier::verification_error::VerificationErrorKind::AssertFailed(
                statements[0].clone(),
            ),
            crate::verifier::verification_error::ErrorReason::AssertionFalse(original.exp.clone()),
        );
        let error = crate::verifier::verification_error::RenderedVerificationError::new(
            error,
            Arc::new(Renderer),
        )
        .unwrap();
        let result = map_refute_results(
            &Node::Stmt(lowered),
            VerificationResult::Failure(vec![
                crate::verifier::verification_result::AbstractError::Verification(Arc::new(error)),
            ]),
            Arc::new(Renderer),
        )
        .unwrap();
        assert!(matches!(result, VerificationResult::Success));
    }
}

/// Runtime refute hooks. Parser registration is supplied separately until the
/// native parser extension registry is connected.
#[derive(Debug)]
pub struct RefutePlugin {
    pub renderer: Arc<dyn crate::verifier::verification_error::ErrorNodeRenderer>,
}
impl crate::plugin::silver_plugin::SilverPlugin for RefutePlugin {
    fn parser_features(&self) -> Vec<crate::parser::fast_parser::ParserFeature> {
        vec![crate::parser::fast_parser::ParserFeature::Refute]
    }
    fn before_verify(
        &mut self,
        program: crate::ast::program::Program,
    ) -> Result<crate::ast::program::Program, crate::plugin::silver_plugin::PluginHookError> {
        let mut methods = Vec::with_capacity(program.methods.len());
        for method in &program.methods {
            let body = method
                .body
                .as_ref()
                .map(lower_method_body)
                .transpose()
                .map_err(|e| crate::plugin::silver_plugin::PluginHookError(e.into()))?;
            methods.push(method.copy_with(|m| m.body = body));
        }
        Ok(program.copy_with(|p| p.methods = methods))
    }
    fn map_entity_verification_result(
        &mut self,
        entity: &crate::reporter::package::Entity,
        input: crate::verifier::verification_result::VerificationResult,
    ) -> Result<
        crate::verifier::verification_result::VerificationResult,
        crate::plugin::silver_plugin::PluginHookError,
    > {
        map_refute_results(
            &crate::ast::utility::nodes::Node::Member((**entity).clone()),
            input,
            self.renderer.clone(),
        )
        .map_err(|e| crate::plugin::silver_plugin::PluginHookError(e.into()))
    }
    fn map_verification_result(
        &mut self,
        program: &crate::ast::program::Program,
        input: crate::verifier::verification_result::VerificationResult,
    ) -> Result<
        crate::verifier::verification_result::VerificationResult,
        crate::plugin::silver_plugin::PluginHookError,
    > {
        map_refute_results(
            &crate::ast::utility::nodes::Node::Program(program.clone()),
            input,
            self.renderer.clone(),
        )
        .map_err(|e| crate::plugin::silver_plugin::PluginHookError(e.into()))
    }
}
