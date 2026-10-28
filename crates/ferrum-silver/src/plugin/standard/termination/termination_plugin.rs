//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/termination/TerminationPlugin.scala
//!
//! Purpose:
//! Parse decreases specifications, import well-founded orders and generate termination
//! obligations.
//!
//! Planned Rust structure:
//! Port TerminationPlugin grammar/registration, beforeResolve predicate-instance rewriting,
//! beforeTranslate domain import and warning logic, beforeVerify extraction/Trafo, result mapping,
//! PAstProvider and constants.
//!
//! Behavior to preserve:
//! Register tuple, wildcard and star syntax in pre/post/invariant hooks. Rewrite predicate
//! accesses only in decreases tuples with unfolding/applying/current-permission recursion
//! boundaries. Unless disabled, warn on unexpectedly constrained types and import missing
//! type-specific well-founded-order resources, retaining domains only. Before verification check
//! unsafe recursive function postconditions lacking decreases, extract clauses into metadata with
//! duplicate and forbidden tuple diagnostics, then generate checks with permission option.
//! Disabled mode still extracts clauses but skips imports, checks and error mapping. Map
//! transformed AssertFailed at entity and overall result boundaries.
//!
//! Integration:
//! parser::fast_parser/resolver, frontend::viper_p_ast_provider, predicateinstance, termination
//! transformation, ast::utility functions/rewriter, reporter and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for plugin order, source positions, native resource loading and
//! mutable contexts.
//!
//! Open decisions:
//! Agree on import ordering and provider lifecycle, parser extension registration and persistent
//! decreasesClauses state with frontend and parser.
//!
//! Status: partial; decreases extraction/validation and verification-result mapping are implemented.
//! Parsing, imports, recursive-postcondition validation and concrete lifecycle transformer remain
//! pending; active verification requires an explicit validator/transformer.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::termination_ast_extension::{DecreasesClause, DecreasesKind, DecreasesSpecification};
use crate::ast::expression::{Exp, ExpKind};
use crate::ast::program::Program;
use crate::ast::statement::{Stmt, StmtKind};
use crate::ast::utility::nodes::{self, Node};
use crate::plugin::silver_plugin::{PluginErrors, PluginHookError, SilverPlugin};
use crate::verifier::verification_result::{
    AbstractError, FrontendError, FrontendErrorKind, VerificationResult,
};

pub const WELL_FOUNDED_ORDER_DOMAIN_NAME: &str = "WellFoundedOrder";
/// Must validate recursive postconditions and resource availability before
/// applying actual function and method termination transformations.
pub trait TerminationTransformer: Send {
    fn validate_and_transform(
        &mut self,
        program: Program,
        respect_function_permissions: bool,
    ) -> Result<Program, PluginHookError>;
}
pub struct TerminationPlugin {
    pub disabled: bool,
    pub respect_function_permissions: bool,
    pub transformer: Option<Box<dyn TerminationTransformer>>,
    errors: PluginErrors,
}
impl TerminationPlugin {
    pub fn new(
        disabled: bool,
        respect_function_permissions: bool,
        transformer: Option<Box<dyn TerminationTransformer>>,
    ) -> Self {
        Self {
            disabled,
            respect_function_permissions,
            transformer,
            errors: PluginErrors::default(),
        }
    }
    fn issue(&mut self, text: &str, exp: &Exp) {
        let error = AbstractError::Frontend(FrontendError::new(
            FrontendErrorKind::ConsistencyError(text.into()),
            exp.metadata().position.clone(),
        ));
        let _ = self.errors.report(error);
    }
    fn check_tuple_exp(&mut self, exp: &Exp) -> Result<(), PluginHookError> {
        self.check_tuple_node(&Node::Exp(exp.clone()))
    }
    fn check_tuple_node(&mut self, node: &Node) -> Result<(), PluginHookError> {
        let children = if let Node::Exp(exp) = node {
            match exp.kind() {
                ExpKind::MagicWand(..) => self.issue(
                    "Magic wand expressions are not allowed as termination measure.",
                    exp,
                ),
                ExpKind::InhaleExhaleExp(..) => self.issue(
                    "Inhale Exhale expressions are not allowed as termination measure.",
                    exp,
                ),
                _ => {}
            }
            match exp.kind() {
                ExpKind::CondExp(_, yes, no) => vec![Node::Exp(yes.clone()), Node::Exp(no.clone())],
                ExpKind::Applying(_, body) | ExpKind::Unfolding(_, body) => {
                    vec![Node::Exp(body.clone())]
                }
                ExpKind::CurrentPerm(_) => vec![],
                _ => nodes::subnodes(node)
                    .map_err(|e| PluginHookError(format!("termination tuple traversal: {e:?}")))?,
            }
        } else {
            nodes::subnodes(node)
                .map_err(|e| PluginHookError(format!("termination tuple traversal: {e:?}")))?
        };
        for child in children {
            self.check_tuple_node(&child)?;
        }
        Ok(())
    }
    fn extract_expressions(
        &mut self,
        expressions: &[Exp],
    ) -> Result<(Vec<Exp>, Option<DecreasesSpecification>), PluginHookError> {
        let mut ordinary = Vec::new();
        let mut tuples = Vec::new();
        let mut wildcards = Vec::new();
        let mut stars = Vec::new();
        for expression in expressions {
            let clause = match expression.kind() {
                ExpKind::Extension(e) => e.0.as_any().downcast_ref::<DecreasesClause>(),
                _ => None,
            };
            if let Some(clause) = clause {
                match &clause.kind {
                    DecreasesKind::Tuple { tuple, .. } => {
                        for value in tuple {
                            self.check_tuple_exp(value)?;
                        }
                        tuples.push((clause.clone(), expression.clone()));
                    }
                    DecreasesKind::Wildcard { .. } => {
                        wildcards.push((clause.clone(), expression.clone()))
                    }
                    DecreasesKind::Star => stars.push((clause.clone(), expression.clone())),
                }
            } else {
                ordinary.push(expression.clone());
            }
        }
        if tuples.len() > 1 {
            self.issue("Multiple decreases tuple.", &tuples[0].1);
        }
        if wildcards.len() > 1 {
            self.issue("Multiple decreases wildcard.", &wildcards[0].1);
        }
        if stars.len() > 1 {
            self.issue("Multiple decreases star.", &stars[0].1);
        }
        if tuples.is_empty() && wildcards.is_empty() && stars.is_empty() {
            return Ok((ordinary, None));
        }
        Ok((
            ordinary,
            Some(DecreasesSpecification {
                tuple: tuples.into_iter().next().map(|x| x.0),
                wildcard: wildcards.into_iter().next().map(|x| x.0),
                star: stars.into_iter().next().map(|x| x.0),
            }),
        ))
    }
    fn extract_statement(&mut self, statement: &Stmt) -> Result<Stmt, PluginHookError> {
        Ok(match statement.kind() {
            StmtKind::Seqn {
                statements,
                declarations,
            } => Stmt::new(
                StmtKind::Seqn {
                    statements: statements
                        .iter()
                        .map(|s| self.extract_statement(s))
                        .collect::<Result<_, _>>()?,
                    declarations: declarations.clone(),
                },
                statement.metadata().clone(),
            ),
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => Stmt::new(
                StmtKind::If {
                    condition: condition.clone(),
                    then_branch: self.extract_statement(then_branch)?,
                    else_branch: self.extract_statement(else_branch)?,
                },
                statement.metadata().clone(),
            ),
            StmtKind::While {
                condition,
                invariants,
                body,
            } => {
                let (invariants, spec) = self.extract_expressions(invariants)?;
                let result = Stmt::new(
                    StmtKind::While {
                        condition: condition.clone(),
                        invariants,
                        body: self.extract_statement(body)?,
                    },
                    statement.metadata().clone(),
                );
                if let Some(spec) = spec {
                    spec.append_to_while(&result)
                        .map_err(|e| PluginHookError(e.into()))?
                } else {
                    result
                }
            }
            StmtKind::Package { wand, proof_script } => Stmt::new(
                StmtKind::Package {
                    wand: wand.clone(),
                    proof_script: self.extract_statement(proof_script)?,
                },
                statement.metadata().clone(),
            ),
            StmtKind::Extension(_) => {
                return Err(PluginHookError(
                    "termination extraction for statement extension is unsupported".into(),
                ));
            }
            _ => statement.clone(),
        })
    }
    pub fn extract_decreases(&mut self, input: &Program) -> Result<Program, PluginHookError> {
        let mut functions = Vec::new();
        for function in &input.functions {
            let (pres, pre_spec) = self.extract_expressions(&function.pres)?;
            let (posts, post_spec) = self.extract_expressions(&function.posts)?;
            let mut f = function.copy_with(|v| {
                v.pres = pres;
                v.posts = posts;
            });
            if let Some(spec) = pre_spec {
                f = spec.append_to_function(&f);
            }
            if let Some(spec) = post_spec {
                f = spec.append_to_function(&f);
            }
            functions.push(f);
        }
        let mut methods = Vec::new();
        for method in &input.methods {
            let (pres, pre_spec) = self.extract_expressions(&method.pres)?;
            let (posts, post_spec) = self.extract_expressions(&method.posts)?;
            let body = method
                .body
                .as_ref()
                .map(|s| self.extract_statement(s))
                .transpose()?;
            let mut m = method.copy_with(|v| {
                v.pres = pres;
                v.posts = posts;
                v.body = body;
            });
            if let Some(spec) = pre_spec {
                m = spec.append_to_method(&m);
            }
            if let Some(spec) = post_spec {
                m = spec.append_to_method(&m);
            }
            methods.push(m);
        }
        Ok(input.copy_with(|p| {
            p.functions = functions;
            p.methods = methods;
        }))
    }
    fn map_result(&self, input: VerificationResult) -> Result<VerificationResult, PluginHookError> {
        use crate::verifier::verification_error::{
            RenderedVerificationError, VerificationErrorKind,
        };
        if self.disabled {
            return Ok(input);
        }
        let VerificationResult::Failure(errors) = input else {
            return Ok(input);
        };
        let mut mapped = Vec::new();
        for error in errors {
            let transform = matches!(&error, AbstractError::Verification(e) if e.as_any().downcast_ref::<RenderedVerificationError>().is_some_and(|v| matches!(&v.error().kind, VerificationErrorKind::AssertFailed(stmt) if matches!(stmt.kind(), StmtKind::Assert(_)))));
            mapped.push(if transform {
                error.transformed_error().map_err(|e| {
                    PluginHookError(format!("termination error transformation: {e:?}"))
                })?
            } else {
                error
            });
        }
        Ok(VerificationResult::Failure(mapped))
    }
}
impl SilverPlugin for TerminationPlugin {
    fn errors(&self) -> &[AbstractError] {
        self.errors.errors()
    }
    fn before_verify(&mut self, input: Program) -> Result<Program, PluginHookError> {
        let extracted = self.extract_decreases(&input)?;
        if self.disabled || !self.errors.errors().is_empty() {
            return Ok(extracted);
        }
        let transformer = self.transformer.as_mut().ok_or_else(|| {
            PluginHookError("termination validator and transformer are not configured".into())
        })?;
        transformer.validate_and_transform(extracted, self.respect_function_permissions)
    }
    fn map_entity_verification_result(
        &mut self,
        _: &crate::reporter::package::Entity,
        input: VerificationResult,
    ) -> Result<VerificationResult, PluginHookError> {
        self.map_result(input)
    }
    fn map_verification_result(
        &mut self,
        _: &Program,
        input: VerificationResult,
    ) -> Result<VerificationResult, PluginHookError> {
        self.map_result(input)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ast::Metadata;
    use crate::ast::program::{Function, FunctionData};
    use crate::ast::r#type::Type;

    #[test]
    fn disabled_plugin_extracts_clauses_and_reports_duplicates() {
        let meta = Metadata::default();
        let clause = DecreasesClause::new(
            DecreasesKind::Tuple {
                tuple: vec![],
                condition: None,
            },
            meta.clone(),
        )
        .expression();
        let function = Function::new(FunctionData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            pres: vec![clause.clone(), clause],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![function], vec![], vec![], vec![], meta);
        let mut plugin = TerminationPlugin::new(true, false, None);
        let output = plugin.before_verify(program).unwrap();
        assert!(output.functions[0].pres.is_empty());
        assert!(
            DecreasesSpecification::from_info(&output.functions[0].meta.info)
                .unwrap()
                .tuple
                .is_some()
        );
        assert_eq!(plugin.errors().len(), 1);
    }
    #[test]
    fn active_plugin_rejects_missing_transformer() {
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let mut plugin = TerminationPlugin::new(false, false, None);
        assert!(plugin.before_verify(program).is_err());
    }
}
