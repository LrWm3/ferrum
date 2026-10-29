//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/debugger/DebugTypechecker.scala
//!
//! Purpose:
//! Resolve debugger versioned variables against captured types.
//!
//! Planned Rust structure:
//! Port DebugResolver and DebugTypeChecker checkInternal and acceptAndCheckTypedEntityWithVersion.
//!
//! Behavior to preserve:
//! Look up full versioned name in debugVariableTypes, set type or append positioned diagnostic;
//! delegate other expressions to ordinary TypeChecker.
//!
//! Integration:
//! debugger::{debug_parser,silicon_debugger}, ferrum_silver::parser::{resolver,fast_message}.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for type and error ownership.
//!
//! Open decisions:
//! Agree on captured version naming and scope with debugger and parser.
//!
//! Status: partial; source debug tokens, typed nodes and translation/check callbacks exist.
//! General parser/resolver override registration and debugger-session integration remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright notice: the pinned upstream file does not carry an individual notice.

use super::debug_parser::versioned_name;
use ferrum_silver::{
    ast::position::Position,
    parser::parse_ast::{PExpHandle, PExpressionKind, PNodeKind, PTypeHandle},
};
use std::collections::HashMap;
#[derive(Clone, Debug)]
pub struct DebugTypeMessage {
    pub expression: PExpHandle,
    pub message: String,
    pub position: Position,
}
#[derive(Default)]
pub struct DebugTypeChecker {
    pub debug_variable_types: HashMap<String, PTypeHandle>,
    pub messages: Vec<DebugTypeMessage>,
}
impl DebugTypeChecker {
    /// Resolve every versioned variable before Silver's recursive typechecker runs.
    /// A debug-old label has the same parse-node shape as a versioned variable,
    /// but names a heap and must not be looked up as a variable.
    pub fn check_tree(
        &mut self,
        expression: &PExpHandle,
    ) -> Result<(), ferrum_silver::parser::parse_ast::ChildrenNotPorted> {
        use ferrum_silver::parser::parse_ast::{PNodeHandle, subnodes};
        fn walk(
            checker: &mut DebugTypeChecker,
            node: &PNodeHandle,
        ) -> Result<(), ferrum_silver::parser::parse_ast::ChildrenNotPorted> {
            let kind = node.read().expect("poisoned parse node").kind.clone();
            if let PNodeKind::Expression(e) = &kind {
                match &e.kind {
                    PExpressionKind::VersionedIdnUse { .. } => {
                        let expression = PExpHandle::from_node(node.clone()).expect("expression");
                        let name = versioned_name(&expression).expect("versioned identifier");
                        checker.accept_versioned(&[expression], || {
                            format!("Could not resolve the type of {name}")
                        });
                        return Ok(());
                    }
                    PExpressionKind::DebugLabelledOldExp { exp, .. } => {
                        return walk(checker, exp.node());
                    }
                    _ => {}
                }
            }
            for child in subnodes(node)? {
                walk(checker, &child)?;
            }
            Ok(())
        }
        walk(self, expression.node())
    }
    pub fn check_internal<E>(
        &mut self,
        expression: &PExpHandle,
        fallback: &mut impl FnMut(&PExpHandle) -> Result<(), E>,
    ) -> Result<(), E> {
        let is_versioned = matches!(&expression.node().read().expect("poisoned parse node").kind, PNodeKind::Expression(e) if matches!(&e.kind, PExpressionKind::VersionedIdnUse { .. }));
        if is_versioned {
            let name = versioned_name(expression).expect("matched versioned expression");
            self.accept_versioned(std::slice::from_ref(expression), || {
                format!("Could not resolve the type of {name}")
            });
            Ok(())
        } else {
            fallback(expression)
        }
    }
    pub fn accept_versioned(&mut self, expressions: &[PExpHandle], message: impl Fn() -> String) {
        for expression in expressions {
            let name = versioned_name(expression).expect("versioned identifier required");
            if let Some(typ) = self.debug_variable_types.get(&name) {
                if let PNodeKind::Expression(e) =
                    &mut expression.node().write().expect("poisoned parse node").kind
                {
                    e.typ = typ.clone();
                }
            } else {
                self.messages.push(DebugTypeMessage {
                    expression: expression.clone(),
                    message: message(),
                    position: expression
                        .node()
                        .read()
                        .expect("poisoned parse node")
                        .error_position(),
                });
            }
        }
    }
}

/// A retained source program and the resolver scope chosen from a failed
/// assertion's SourcePNodeInfo, matching Silicon's nearest-PScope walk.
pub struct DebugSourceScope {
    source: ferrum_silver::parser::parse_ast::PProgramHandle,
    names: ferrum_silver::parser::resolver::NameAnalyser,
    scope: Option<ferrum_silver::parser::parse_ast::PNodeHandle>,
}
impl DebugSourceScope {
    pub fn new(
        program: &ferrum_silver::ast::program::Program,
        failed: Option<&ferrum_silver::ast::expression::Exp>,
    ) -> Result<Self, DebugTranslateError> {
        use ferrum_silver::{
            ast::ast::Info,
            parser::{parse_ast, resolver::NameAnalyser},
        };
        let source = program
            .source_program()
            .ok_or(DebugTranslateError::MissingSourceProgram)?
            .clone();
        let mut names = NameAnalyser::default();
        names
            .collect_scopes(source.node())
            .map_err(DebugTranslateError::Name)?;
        let scope = failed.and_then(|exp| {
            let all = exp
                .metadata()
                .info
                .all_matching(&|info| matches!(info, Info::SourcePNode(_)));
            if all.len() != 1 {
                return None;
            }
            let Info::SourcePNode(node) = all[0] else {
                unreachable!()
            };
            if parse_ast::scope_id(node).is_some() {
                Some(node.clone())
            } else {
                parse_ast::get_enclosing_scope(node)
            }
        });
        Ok(Self {
            source,
            names,
            scope,
        })
    }
    pub fn has_scope(&self) -> bool {
        self.scope.is_some()
    }
    pub fn translate_boolean(
        &mut self,
        input: &str,
        program: &ferrum_silver::ast::program::Program,
        types: &HashMap<String, PTypeHandle>,
    ) -> Result<ferrum_silver::ast::expression::Exp, DebugTranslateError> {
        let _retain_source_tree = &self.source;
        translate_debug_boolean_in_scope(
            input,
            program,
            &mut self.names,
            self.scope.as_ref(),
            types,
        )
    }
}

/// Failures of parsing, scoped name resolution, checking or translation of a
/// debugger command. Missing source scope is a port gap, not an empty scope.
#[derive(Debug)]
pub enum DebugTranslateError {
    MissingSourceProgram,
    InvalidDebugVariableName(String),
    Parse(ferrum_silver::parser::fast_parser::SyntaxError),
    Name(ferrum_silver::parser::resolver::NameAnalysisError),
    NameMessages(Vec<ferrum_silver::parser::fast_message::FastMessage>),
    Children(ferrum_silver::parser::parse_ast::ChildrenNotPorted),
    DebugTypes(Vec<DebugTypeMessage>),
    Type(ferrum_silver::parser::resolver::TypeCheckError),
    Translation(ferrum_silver::parser::translator::TranslationError),
}

/// Parse a debugger command against the retained source scope and captured
/// versioned variable types, require Bool and translate using program fields.
/// The caller retains the parsed program and resolver used for the original run.
pub fn translate_debug_boolean(
    input: &str,
    program: &ferrum_silver::ast::program::Program,
    names: &mut ferrum_silver::parser::resolver::NameAnalyser,
    scope: &ferrum_silver::parser::parse_ast::PNodeHandle,
    debug_variable_types: &HashMap<String, PTypeHandle>,
) -> Result<ferrum_silver::ast::expression::Exp, DebugTranslateError> {
    translate_debug_boolean_in_scope(input, program, names, Some(scope), debug_variable_types)
}

fn translate_debug_boolean_in_scope(
    input: &str,
    program: &ferrum_silver::ast::program::Program,
    names: &mut ferrum_silver::parser::resolver::NameAnalyser,
    scope: Option<&ferrum_silver::parser::parse_ast::PNodeHandle>,
    debug_variable_types: &HashMap<String, PTypeHandle>,
) -> Result<ferrum_silver::ast::expression::Exp, DebugTranslateError> {
    use ferrum_silver::parser::{fast_parser, resolver, translator};
    let expression = fast_parser::parse_expression_with_features(
        input,
        "userInput",
        &[fast_parser::ParserFeature::Debugger],
    )
    .map_err(DebugTranslateError::Parse)?
    .expression;
    let resolved = if let Some(scope) = scope {
        names.run_in_scope(expression.node(), scope)
    } else {
        names.run(expression.node())
    }
    .map_err(DebugTranslateError::Name)?;
    if !resolved {
        return Err(DebugTranslateError::NameMessages(std::mem::take(
            &mut names.messages,
        )));
    }
    let mut normalized = HashMap::new();
    for (name, typ) in debug_variable_types {
        let name = crate::utils::ast::simplify_variable_name(name)
            .map_err(|_| DebugTranslateError::InvalidDebugVariableName(name.clone()))?;
        normalized.insert(name.to_string(), typ.clone());
    }
    let mut checker = DebugTypeChecker {
        debug_variable_types: normalized,
        messages: Vec::new(),
    };
    checker
        .check_tree(&expression)
        .map_err(DebugTranslateError::Children)?;
    if !checker.messages.is_empty() {
        return Err(DebugTranslateError::DebugTypes(checker.messages));
    }
    let bool_type = fast_parser::parse_type("Bool", "userInput")
        .map_err(DebugTranslateError::Parse)?
        .typ;
    resolver::check_top_expression(&expression, Some(&bool_type), |_, _| {})
        .map_err(DebugTranslateError::Type)?;
    translator::translate_expression_in_program(&expression, program)
        .map_err(DebugTranslateError::Translation)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ferrum_silver::parser::{fast_parser, resolver, translator};

    #[test]
    fn nested_debug_variables_typecheck_and_translate() {
        let parsed = fast_parser::parse_expression_with_features(
            "x@1 && old[debug@heap](x@1)",
            "debug.vpr",
            &[fast_parser::ParserFeature::Debugger],
        )
        .unwrap()
        .expression;
        let mut checker = DebugTypeChecker::default();
        checker.debug_variable_types.insert(
            "x@1".into(),
            fast_parser::parse_type("Bool", "debug.vpr").unwrap().typ,
        );
        checker.check_tree(&parsed).unwrap();
        assert!(checker.messages.is_empty());
        resolver::check_top_expression(&parsed, None, |_, _| {}).unwrap();
        let translated = translator::translate_expression(&parsed).unwrap();
        let rendered = format!("{:?}", translated);
        assert!(rendered.contains("LocalVarWithVersion"));
        assert!(rendered.contains("DebugLabelledOld"));

        let missing = fast_parser::parse_expression_with_features(
            "x@2",
            "debug.vpr",
            &[fast_parser::ParserFeature::Debugger],
        )
        .unwrap()
        .expression;
        checker.check_tree(&missing).unwrap();
        assert_eq!(checker.messages.len(), 1);
        assert!(resolver::check_top_expression(&missing, None, |_, _| {}).is_err());
    }
}

#[cfg(test)]
mod adapter_tests {
    use super::*;
    use ferrum_silver::parser::{fast_parser, resolver, translator};
    #[test]
    fn scoped_boolean_adapter_accepts_variables_and_rejects_non_boolean() {
        let parsed =
            fast_parser::parse_program("method m(x: Int) { assert x > 0 }", "scope.vpr").unwrap();
        let scope = parsed.all_members()[0].node().clone();
        let mut names = resolver::NameAnalyser::default();
        assert!(names.run(parsed.node()).unwrap());
        names.collect_scopes(parsed.node()).unwrap();
        resolver::check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = translator::translate_program_core(&parsed).unwrap();
        let mut types = HashMap::new();
        types.insert(
            "x@1@worker".into(),
            fast_parser::parse_type("Int", "userInput").unwrap().typ,
        );
        for input in ["x > 1", "x@1 > 1", "old[debug@heap](x@1 > 1)"] {
            translate_debug_boolean(input, &program, &mut names, &scope, &types).unwrap();
        }
        assert!(matches!(
            translate_debug_boolean("x", &program, &mut names, &scope, &types),
            Err(DebugTranslateError::Type(_))
        ));
        assert!(matches!(
            translate_debug_boolean("x@2 > 0", &program, &mut names, &scope, &types),
            Err(DebugTranslateError::DebugTypes(_))
        ));
    }
}

#[cfg(test)]
mod captured_scope_tests {
    use super::*;
    use ferrum_silver::{
        ast::statement::StmtKind,
        parser::{fast_parser, parse_ast, resolver, translator},
    };

    #[test]
    fn retained_source_selects_scope_and_translates_member_expressions() {
        let source = "field f: Int\nfunction ok(x: Int): Bool { x > 0 }\nmethod m(r: Ref, x: Int) requires acc(r.f) { assert r.f > 0 && ok(x) }";
        let parsed = fast_parser::parse_program(source, "scope.vpr").unwrap();
        parse_ast::init_properties(parsed.node()).unwrap();
        let mut names = resolver::NameAnalyser::default();
        assert!(names.run(parsed.node()).unwrap());
        resolver::check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let ordinary = translator::translate_program_core(&parsed).unwrap();
        assert!(ordinary.source_program().is_none());
        let program = translator::translate_program_core_preserving_source(&parsed).unwrap();
        let copied = program.copy_with(|_| {});
        drop(parsed);
        let body = copied.methods[0].body.as_ref().unwrap();
        let StmtKind::Seqn { statements, .. } = body.kind() else {
            panic!("expected body")
        };
        let StmtKind::Assert(failed) = statements[0].kind() else {
            panic!("expected assertion")
        };
        let mut context = DebugSourceScope::new(&copied, Some(failed)).unwrap();
        assert!(context.has_scope());
        let translated = context
            .translate_boolean("r.f > 0 && ok(x)", &copied, &HashMap::new())
            .unwrap();
        let rendered = format!("{translated:?}");
        assert!(rendered.contains("FieldAccess"));
        assert!(rendered.contains("FuncApp"));
    }
}
