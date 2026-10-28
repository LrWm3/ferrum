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
//! Status: partial; decreases syntax, extraction, native order imports, recursive-postcondition
//! validation, concrete proof generation and verification-result mapping are implemented.
//! Predicate-access rewriting in tuple clauses is implemented; import-domain warnings and some
//! proof shapes remain pending and unsupported proof shapes return explicit errors.

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

fn rewrite_predicate_instances(
    input: &crate::parser::parse_ast::PProgramHandle,
) -> Result<(), PluginHookError> {
    use super::termination_past_extension::{PDecreasesClause, PDecreasesKind};
    use crate::parser::parse_ast::{
        PDeclarationClass, PExpressionKind, PMemberKind, PNodeHandle, PNodeKind, subnodes,
    };
    use crate::plugin::standard::predicateinstance::predicate_instance_past_extension::{
        PPredicateInstance, marker_symbol,
    };
    let mut predicates = std::collections::HashSet::new();
    for member in input.all_members() {
        if let PNodeKind::Member(member) = &member.node().read().expect("poisoned parse node").kind
        {
            if let PMemberKind::Predicate { idndef, .. } = &member.kind {
                if let PNodeKind::IdnDef(id) = &idndef.read().expect("poisoned parse node").kind {
                    predicates.insert(id.name.clone());
                }
            }
        }
    }
    fn walk(
        node: &PNodeHandle,
        predicates: &std::collections::HashSet<String>,
        in_tuple: bool,
    ) -> Result<(), PluginHookError> {
        let (kind, pos) = {
            let node = node.read().expect("poisoned parse node");
            (node.kind.clone(), node.pos.clone())
        };
        if let PNodeKind::Expression(expression) = kind {
            if !in_tuple {
                if let PExpressionKind::Extension(extension) = &expression.kind {
                    if let Some(PDecreasesClause {
                        kind: PDecreasesKind::Tuple { .. },
                        ..
                    }) = extension.as_any().downcast_ref::<PDecreasesClause>()
                    {
                        for child in subnodes(node).map_err(|e| {
                            PluginHookError(format!("termination tuple traversal: {e:?}"))
                        })? {
                            walk(&child, predicates, true)?;
                        }
                        return Ok(());
                    }
                }
            } else {
                let call = match &expression.kind {
                    PExpressionKind::Call {
                        idnref,
                        call_args,
                        type_annotated: None,
                        ..
                    } => Some((idnref.clone(), call_args.clone(), pos.clone())),
                    PExpressionKind::AccPred { amount, .. } => {
                        let call = amount
                            .inner()
                            .first()
                            .node()
                            .read()
                            .expect("poisoned parse node");
                        if let PNodeKind::Expression(e) = &call.kind {
                            if let PExpressionKind::Call {
                                idnref,
                                call_args,
                                type_annotated: None,
                                ..
                            } = &e.kind
                            {
                                Some((idnref.clone(), call_args.clone(), call.pos.clone()))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some((idnref, args, call_pos)) = call {
                    let matched = matches!(&idnref.read().expect("poisoned parse node").kind, PNodeKind::IdnRef(id) if predicates.contains(&id.name));
                    if matched {
                        if let PNodeKind::IdnRef(id) =
                            &mut idnref.write().expect("poisoned parse node").kind
                        {
                            id.declaration_class = PDeclarationClass::Predicate;
                        }
                        let replacement = PPredicateInstance {
                            marker: marker_symbol((
                                crate::ast::position::Position::NoPosition,
                                crate::ast::position::Position::NoPosition,
                            )),
                            idnuse: idnref,
                            args,
                            pos: call_pos.clone(),
                        }
                        .expression();
                        let replacement_kind = replacement
                            .node()
                            .read()
                            .expect("poisoned parse node")
                            .kind
                            .clone();
                        let mut current = node.write().expect("poisoned parse node");
                        current.kind = replacement_kind;
                        current.pos = call_pos;
                        drop(current);
                        for child in subnodes(node).map_err(|e| {
                            PluginHookError(format!("termination predicate traversal: {e:?}"))
                        })? {
                            walk(&child, predicates, true)?;
                        }
                        return Ok(());
                    }
                }
                match expression.kind {
                    PExpressionKind::Unfolding { exp, .. }
                    | PExpressionKind::Applying { exp, .. } => {
                        return walk(exp.node(), predicates, true);
                    }
                    PExpressionKind::CurrentPerm { .. } => return Ok(()),
                    _ => {}
                }
            }
        }
        for child in subnodes(node)
            .map_err(|e| PluginHookError(format!("termination clause traversal: {e:?}")))?
        {
            walk(&child, predicates, in_tuple)?;
        }
        Ok(())
    }
    walk(input.node(), &predicates, false)
}
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
            StmtKind::Extension(extension) => {
                use crate::verifier::verification_result::DiagnosticError;
                use std::cell::RefCell;
                let transformer = RefCell::new(self);
                let failure = RefCell::new(None);
                let mapped = extension.0.map_statements(&|child| {
                    transformer
                        .borrow_mut()
                        .extract_statement(child)
                        .map_err(|error| {
                            *failure.borrow_mut() = Some(error);
                            DiagnosticError::Unsupported("termination statement extraction")
                        })
                });
                if let Some(error) = failure.into_inner() {
                    return Err(error);
                }
                match mapped.map_err(|e| {
                    PluginHookError(format!("termination extension traversal: {e:?}"))
                })? {
                    Some(mapped) if mapped == *extension => statement.clone(),
                    Some(mapped) => {
                        Stmt::new(StmtKind::Extension(mapped), statement.metadata().clone())
                    }
                    None => statement.clone(),
                }
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
    fn parser_features(&self) -> Vec<crate::parser::fast_parser::ParserFeature> {
        vec![crate::parser::fast_parser::ParserFeature::Termination]
    }
    fn before_resolve(
        &mut self,
        input: crate::parser::parse_ast::PProgramHandle,
    ) -> crate::parser::parse_ast::PProgramHandle {
        if let Err(error) = rewrite_predicate_instances(&input) {
            let position = input
                .node()
                .read()
                .expect("poisoned parse node")
                .pos
                .0
                .clone();
            let _ = self
                .errors
                .report(AbstractError::Frontend(FrontendError::new(
                    FrontendErrorKind::TypecheckerError(error.0),
                    position,
                )));
        }
        input
    }
    fn additional_standard_imports(
        &self,
        input: &crate::parser::parse_ast::PProgramHandle,
    ) -> Result<Vec<String>, PluginHookError> {
        use super::termination_past_extension::{PDecreasesClause, PDecreasesKind};
        use crate::parser::parse_ast::{
            PExpressionKind, PMemberKind, PNodeHandle, PNodeKind, PTypeKind, subnodes,
        };
        if self.disabled {
            return Ok(Vec::new());
        }
        let mut present = std::collections::HashSet::new();
        for member in input.all_members() {
            if let PNodeKind::Member(member) =
                &member.node().read().expect("poisoned parse node").kind
            {
                if let PMemberKind::Domain { idndef, .. } = &member.kind {
                    if let PNodeKind::IdnDef(id) = &idndef.read().expect("poisoned parse node").kind
                    {
                        present.insert(id.name.clone());
                    }
                }
            }
        }
        fn walk(
            node: &PNodeHandle,
            present: &std::collections::HashSet<String>,
            imports: &mut Vec<String>,
        ) -> Result<(), PluginHookError> {
            let kind = node.read().expect("poisoned parse node").kind.clone();
            if let PNodeKind::Expression(expression) = kind {
                if let PExpressionKind::Extension(extension) = expression.kind {
                    if let Some(PDecreasesClause {
                        kind: PDecreasesKind::Tuple { tuple, .. },
                        ..
                    }) = extension.as_any().downcast_ref::<PDecreasesClause>()
                    {
                        for exp in tuple.to_seq() {
                            let expression =
                                match &exp.node().read().expect("poisoned parse node").kind {
                                    PNodeKind::Expression(e) => e.clone(),
                                    _ => {
                                        return Err(PluginHookError(
                                            "termination tuple is not an expression".into(),
                                        ));
                                    }
                                };
                            if matches!(&expression.kind, PExpressionKind::Extension(e) if e.as_any().is::<crate::plugin::standard::predicateinstance::predicate_instance_past_extension::PPredicateInstance>())
                            {
                                if !present.contains("PredicateInstancesWellFoundedOrder")
                                    && !imports
                                        .iter()
                                        .any(|v| v == "decreases/predicate_instance.vpr")
                                {
                                    imports.push("decreases/predicate_instance.vpr".into());
                                }
                                continue;
                            }
                            let (domain, resource) = match expression.typ.kind() {
                                PTypeKind::Primitive { name } => match name.value() {
                                    crate::parser::parse_ast_keyword::PKw::Int => {
                                        ("IntWellFoundedOrder", "decreases/int.vpr")
                                    }
                                    crate::parser::parse_ast_keyword::PKw::Ref => {
                                        ("RefWellFoundedOrder", "decreases/ref.vpr")
                                    }
                                    crate::parser::parse_ast_keyword::PKw::Bool => {
                                        ("BoolWellFoundedOrder", "decreases/bool.vpr")
                                    }
                                    crate::parser::parse_ast_keyword::PKw::Perm
                                    | crate::parser::parse_ast_keyword::PKw::Rational
                                        if !present.contains("RationalWellFoundedOrder") =>
                                    {
                                        ("PermWellFoundedOrder", "decreases/perm.vpr")
                                    }
                                    crate::parser::parse_ast_keyword::PKw::Perm
                                    | crate::parser::parse_ast_keyword::PKw::Rational => continue,
                                    _ => ("WellFoundedOrder", "decreases/declaration.vpr"),
                                },
                                PTypeKind::Seq { .. } => {
                                    ("SeqWellFoundedOrder", "decreases/seq.vpr")
                                }
                                PTypeKind::Set { .. } => {
                                    ("SetWellFoundedOrder", "decreases/set.vpr")
                                }
                                PTypeKind::Multiset { .. } => {
                                    ("MultiSetWellFoundedOrder", "decreases/multiset.vpr")
                                }
                                _ => ("WellFoundedOrder", "decreases/declaration.vpr"),
                            };
                            if !present.contains(domain) && !imports.iter().any(|v| v == resource) {
                                imports.push(resource.into());
                            }
                        }
                    }
                }
            }
            for child in subnodes(node)
                .map_err(|e| PluginHookError(format!("termination import traversal: {e:?}")))?
            {
                walk(&child, present, imports)?;
            }
            Ok(())
        }
        let mut imports = Vec::new();
        walk(input.node(), &present, &mut imports)?;
        Ok(imports)
    }
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

/// Native termination checker for already extracted, typed Silver programs.
/// Resource imports and decreases parser registration still occur earlier in the frontend.
#[derive(Default)]
pub struct NativeTerminationTransformer;
impl TerminationTransformer for NativeTerminationTransformer {
    fn validate_and_transform(
        &mut self,
        program: Program,
        respect: bool,
    ) -> Result<Program, PluginHookError> {
        use super::transformation::{
            call_graph::{DirectedGraph, mutually_recursive_vertices},
            function_check::{ConcreteFunctionProofEngine, FunctionProofGenerator},
            method_check::MethodCheck,
            program_manager::ProgramManager,
            trafo::{TerminationChecks, Trafo},
        };
        use crate::ast::utility::consistency::transitive_scoped_names;
        use std::sync::{Arc, Mutex};
        fn calls(node: &Node, out: &mut Vec<String>) -> Result<(), PluginHookError> {
            if let Node::Exp(exp) = node {
                if let ExpKind::FuncApp(name, _) = exp.kind() {
                    out.push(name.clone());
                }
            }
            for child in nodes::subnodes(node)
                .map_err(|e| PluginHookError(format!("termination call traversal: {e:?}")))?
            {
                calls(&child, out)?;
            }
            Ok(())
        }
        let mut graph = DirectedGraph::new();
        for f in &program.functions {
            graph.add_vertex(f.name.clone());
        }
        for f in &program.functions {
            if let Some(body) = &f.body {
                let mut names = Vec::new();
                calls(&Node::Exp(body.clone()), &mut names)?;
                for name in names {
                    if program.find_function_optionally(&name).is_none() {
                        return Err(PluginHookError(format!("unknown function {name}")));
                    }
                    graph.add_edge(f.name.clone(), name);
                }
            }
        }
        let components = mutually_recursive_vertices(&graph);
        for function in &program.functions {
            let spec = DecreasesSpecification::from_info(&function.meta.info)
                .map_err(|e| PluginHookError(e.into()))?;
            if spec.tuple.is_some() || spec.wildcard.is_some() || spec.star.is_some() {
                continue;
            }
            let component = components
                .iter()
                .find(|c| c.contains(&function.name))
                .ok_or_else(|| PluginHookError("function missing from termination graph".into()))?;
            for post in &function.posts {
                let mut names = Vec::new();
                calls(&Node::Exp(post.clone()), &mut names)?;
                if names.iter().any(|name| {
                    name == &function.name || component.len() > 1 && component.contains(name)
                }) {
                    return Err(PluginHookError(format!(
                        "Function {} has a recursive call in its postcondition and must be proven well-founded.",
                        function.name
                    )));
                }
            }
        }
        fn instrument(
            program: &Program,
            names: &Mutex<std::collections::HashSet<String>>,
            statement: Stmt,
        ) -> Result<Stmt, String> {
            let hash = |args: &[Exp]| {
                crate::ast::utility::expressions::scala_expression_sequence_hash(args)
                    .map_err(|e| format!("predicate argument hash: {e:?}"))
            };
            let render = |args: &[Exp]| {
                args.iter()
                    .map(crate::ast::pretty::pretty_printer::expression_to_string)
                    .collect::<Result<Vec<_>, _>>()
                    .map(|v| v.join(","))
                    .map_err(|e| format!("predicate argument rendering: {e:?}"))
            };
            let mut guard = names
                .lock()
                .map_err(|_| "poisoned nested-predicate names".to_string())?;
            let mut nested = super::transformation::nested_predicates::NestedPredicates::new(
                program, &hash, &render,
            );
            nested.replace_used_names(std::mem::take(&mut *guard));
            let result = nested.add_nested_to_statement(&statement);
            *guard = nested.take_used_names();
            if !nested.errors.is_empty() {
                return Err(format!("nested predicate diagnostics: {:?}", nested.errors));
            }
            result.map_err(|e| format!("nested predicate instrumentation: {e:?}"))
        }
        struct Checks {
            function: FunctionProofGenerator,
            engine: ConcreteFunctionProofEngine,
            methods: MethodCheck,
        }
        impl TerminationChecks for Checks {
            type Error = PluginHookError;
            fn generate_proof_methods(
                &mut self,
                manager: &mut ProgramManager,
                function: &crate::ast::program::Function,
                respect: bool,
            ) -> Result<Vec<crate::ast::program::Method>, Self::Error> {
                self.function
                    .generate(manager, &mut self.engine, function, respect)
                    .map_err(|e| PluginHookError(format!("function termination: {e:?}")))
            }
            fn transform_method(
                &mut self,
                manager: &mut ProgramManager,
                method: &crate::ast::program::Method,
            ) -> Result<crate::ast::program::Method, Self::Error> {
                self.methods
                    .transform_method(manager, method)
                    .map_err(|e| PluginHookError(format!("method termination: {e:?}")))
            }
        }
        let names = transitive_scoped_names(&program)
            .map_err(|e| PluginHookError(format!("termination scoped names: {e:?}")))?;
        let manager = ProgramManager::new(program.clone(), names);
        let mut engine = ConcreteFunctionProofEngine::new(&program)
            .map_err(|e| PluginHookError(format!("function termination graph: {e:?}")))?;
        let mut methods = MethodCheck::new(program.clone())
            .map_err(|e| PluginHookError(format!("method termination graph: {e:?}")))?;
        let shared_names = Arc::new(Mutex::new(std::collections::HashSet::new()));
        let function_program = program.clone();
        let function_names = shared_names.clone();
        engine.nested = Some(Box::new(move |stmt| {
            instrument(&function_program, &function_names, stmt)
                .map_err(super::transformation::exp_transformer::ExpressionTransformError)
        }));
        let method_program = program.clone();
        methods.nested = Some(Box::new(move |stmt| {
            instrument(&method_program, &shared_names, stmt)
                .map_err(super::transformation::method_check::MethodCheckError)
        }));
        let checks = Checks {
            function: FunctionProofGenerator::default(),
            engine,
            methods,
        };
        Trafo::new(manager, checks, respect).get_transformed_program()
    }
}
