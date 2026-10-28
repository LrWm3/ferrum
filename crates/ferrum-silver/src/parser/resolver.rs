//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/Resolver.scala
//!
//! Purpose:
//! Resolve names and typecheck parse AST before translation.
//!
//! Planned Rust structure:
//! Port Resolver, NameAnalyser, DeclarationMap and TypeChecker with scope collection/merge,
//! declaration and body checks, statement and expression dispatch, unification/grounding and
//! extension hooks.
//!
//! Behavior to preserve:
//! Run typechecking even after name errors, recording internal typechecker exceptions. Check
//! domain/function/method signatures before extensions and bodies; preserve visibility, backward
//! references, override/uniqueness and opaque traversal. Resolve overloaded operators by ordered
//! substitutions and ground first candidate, warning on unconstrained variables. Retain
//! permission/wand restrictions, assignment and quantifier context, and configurable function
//! permission warning.
//!
//! Integration:
//! parser::parse_ast and parse_ast_keyword, fast_message, macro_expander and translator;
//! frontend::sil_frontend.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Resolve stable scope identity, mutable references, substitution ordering and error context
//! with parse_ast and translator.
//!
//! Status: partial; declaration-map insertion, uniqueness and scope merge implemented.
//! Core name traversal and operator inference are partial; full typechecking is pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use super::parse_ast::{PNodeHandle, PNodeKind};
use std::collections::HashMap;

/// Visibility and uniqueness markers are supplied by the concrete parse-node adapter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclarationVisibility {
    Local,
    Member,
    Global,
    Other,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclarationUniqueness {
    Global,
    Member,
    Scope,
    None,
}
#[derive(Clone, Debug)]
pub struct Declaration {
    pub name: String,
    pub node: PNodeHandle,
    pub visibility: DeclarationVisibility,
    pub uniqueness: DeclarationUniqueness,
    pub backward: bool,
    pub overrides: bool,
}
#[derive(Default)]
pub struct DeclarationMap {
    pub decls: HashMap<String, Vec<Declaration>>,
    unique: HashMap<String, (bool, Declaration)>,
    refs: HashMap<String, Vec<PNodeHandle>>,
    pub is_member: bool,
    pub is_global: bool,
}
impl DeclarationMap {
    pub fn new(is_member: bool, is_global: bool) -> Self {
        Self {
            is_member,
            is_global,
            ..Self::default()
        }
    }
    /// Returns the earlier conflicting declaration, retaining the source's precedence
    /// between global, member and local uniqueness.
    pub fn check_unique(
        &mut self,
        declaration: &Declaration,
        can_unique: bool,
    ) -> Option<Declaration> {
        let old = self.unique.get(&declaration.name).cloned();
        let global = old
            .as_ref()
            .is_some_and(|(active, d)| *active && d.uniqueness == DeclarationUniqueness::Global);
        let member = global
            || old.as_ref().is_some_and(|(active, d)| {
                *active && d.uniqueness == DeclarationUniqueness::Member
            });
        let scope = member
            || old
                .as_ref()
                .is_some_and(|(active, d)| *active && d.uniqueness == DeclarationUniqueness::Scope);
        let install = match declaration.uniqueness {
            DeclarationUniqueness::Global if can_unique => true,
            DeclarationUniqueness::Member if !global && can_unique => true,
            DeclarationUniqueness::Scope if !member && can_unique => true,
            _ if scope => false,
            _ => {
                self.unique
                    .insert(declaration.name.clone(), (can_unique, declaration.clone()));
                return None;
            }
        };
        if install {
            self.unique
                .insert(declaration.name.clone(), (can_unique, declaration.clone()));
        }
        old.map(|(_, declaration)| declaration)
    }
    pub fn new_decl(&mut self, declaration: Declaration) {
        if declaration.backward {
            if let Some(refs) = self.refs.get(&declaration.name) {
                for reference in refs {
                    with_reference(reference, |r| r.new_decl(&declaration.node));
                }
            }
        }
        let decls = self.decls.entry(declaration.name.clone()).or_default();
        if declaration.overrides {
            decls.clear();
        }
        decls.push(declaration);
    }
    pub fn new_ref(&mut self, reference: PNodeHandle) {
        let name = match &reference.read().expect("poisoned parse node").kind {
            PNodeKind::IdnRef(reference) => reference.name.clone(),
            _ => panic!("expected identifier reference"),
        };
        if let Some(decls) = self.decls.get(&name) {
            with_reference(&reference, |r| {
                for declaration in decls {
                    r.new_decl(&declaration.node);
                }
            });
        }
        self.refs.entry(name).or_default().push(reference);
    }
    /// Merge a completed child scope. The callback identifies overriding declarations
    /// already present on a reference, including candidates contributed by earlier scopes.
    pub fn merge(
        &mut self,
        child: DeclarationMap,
        is_override: impl Fn(&PNodeHandle) -> bool,
    ) -> Vec<(Declaration, Declaration)> {
        for (name, refs) in &child.refs {
            if let Some(decls) = self.decls.get(name) {
                for reference in refs {
                    let skip = match &reference.read().expect("poisoned parse node").kind {
                        PNodeKind::IdnRef(r) => r.declarations.iter().any(&is_override),
                        _ => panic!("expected identifier reference"),
                    };
                    if !skip {
                        with_reference(reference, |r| {
                            r.prepend_decls(decls.iter().map(|d| d.node.clone()).collect())
                        });
                    }
                }
            }
        }
        for declarations in child.decls.into_values() {
            for d in declarations {
                if d.visibility != DeclarationVisibility::Local
                    && !(d.visibility == DeclarationVisibility::Member && child.is_member)
                    && !(d.visibility == DeclarationVisibility::Global && child.is_global)
                {
                    self.new_decl(d);
                }
            }
        }
        for (name, refs) in child.refs {
            self.refs.entry(name).or_default().extend(refs);
        }
        let mut clashes = Vec::new();
        for (in_scope, declaration) in child.unique.into_values() {
            let can_unique = (declaration.uniqueness == DeclarationUniqueness::Global
                && !child.is_global)
                || (declaration.uniqueness == DeclarationUniqueness::Member && !child.is_member);
            if let Some(old) = self.check_unique(&declaration, in_scope && can_unique) {
                clashes.push((declaration, old));
            }
        }
        clashes
    }
    pub fn clear(&mut self) {
        self.decls.clear();
        self.unique.clear();
        self.refs.clear();
    }
    pub fn keys(&self) -> impl Iterator<Item = &String> {
        self.decls.keys()
    }
}
fn with_reference(node: &PNodeHandle, f: impl FnOnce(&mut super::parse_ast::PIdnRef)) {
    let mut node = node.write().expect("poisoned parse node");
    match &mut node.kind {
        PNodeKind::IdnRef(reference) => f(reference),
        _ => panic!("expected identifier reference"),
    }
}

use super::fast_message::{FastMessage, UnexpectedPosition, message_for_node};
use super::parse_ast::{
    ChildrenNotPorted, PDeclarationKind, PExpressionKind, PMemberKind, PStatementKind, subnodes,
};

#[derive(Debug)]
pub enum NameAnalysisError {
    Children(ChildrenNotPorted),
    Position(UnexpectedPosition),
    Unsupported(&'static str),
}
impl From<ChildrenNotPorted> for NameAnalysisError {
    fn from(value: ChildrenNotPorted) -> Self {
        Self::Children(value)
    }
}
impl From<UnexpectedPosition> for NameAnalysisError {
    fn from(value: UnexpectedPosition) -> Self {
        Self::Position(value)
    }
}
/// Name resolution for the currently represented core node families. Unsupported extension,
/// domain and macro scopes fail explicitly; successful resolution is not typechecking.
pub struct NameAnalyser {
    pub messages: Vec<FastMessage>,
    pub global: DeclarationMap,
}
impl Default for NameAnalyser {
    fn default() -> Self {
        Self {
            messages: Vec::new(),
            global: DeclarationMap::new(false, true),
        }
    }
}
impl NameAnalyser {
    pub fn reset(&mut self) {
        self.global.clear();
    }
    pub fn run(&mut self, root: &PNodeHandle) -> Result<bool, NameAnalysisError> {
        let mut global = std::mem::replace(&mut self.global, DeclarationMap::new(false, true));
        let result = visit_names(root, &mut global, &mut self.messages);
        self.global = global;
        result?;
        Ok(self.messages.iter().all(|message| !message.error))
    }
    pub fn global_definitions(&self, name: &str) -> Vec<PNodeHandle> {
        self.global
            .decls
            .get(name)
            .into_iter()
            .flatten()
            .map(|d| d.node.clone())
            .collect()
    }
}
fn definition_name(node: &PNodeHandle) -> String {
    match &node.read().expect("poisoned parse node").kind {
        PNodeKind::IdnDef(name) => name.name.clone(),
        _ => panic!("expected identifier definition"),
    }
}
fn add_named_declaration(
    map: &mut DeclarationMap,
    node: &PNodeHandle,
    idndef: &PNodeHandle,
    visibility: DeclarationVisibility,
    uniqueness: DeclarationUniqueness,
    backward: bool,
    messages: &mut Vec<FastMessage>,
) -> Result<(), NameAnalysisError> {
    let declaration = Declaration {
        name: definition_name(idndef),
        node: node.clone(),
        visibility,
        uniqueness,
        backward,
        overrides: false,
    };
    map.new_decl(declaration.clone());
    if let Some(old) = map.check_unique(&declaration, true) {
        report_duplicate(&declaration, &old, idndef, messages)?;
    }
    Ok(())
}
fn report_duplicate(
    declaration: &Declaration,
    old: &Declaration,
    idndef: &PNodeHandle,
    messages: &mut Vec<FastMessage>,
) -> Result<(), NameAnalysisError> {
    let original_idndef = declaration_identifier(&old.node)
        .ok_or(NameAnalysisError::Unsupported("declaration identifier"))?;
    let here = idndef.read().expect("poisoned parse node").pos.0.clone();
    let there = original_idndef
        .read()
        .expect("poisoned parse node")
        .pos
        .0
        .clone();
    messages.extend(message_for_node(
        idndef,
        format!(
            "duplicate identifier `{}` at {here} and at {there}",
            declaration.name
        ),
        true,
        true,
    )?);
    Ok(())
}
fn declaration_identifier(node: &PNodeHandle) -> Option<PNodeHandle> {
    match &node.read().expect("poisoned parse node").kind {
        PNodeKind::Declaration(d) => Some(d.idndef.clone()),
        PNodeKind::Member(member) => match &member.kind {
            PMemberKind::Domain { idndef, .. }
            | PMemberKind::Function { idndef, .. }
            | PMemberKind::Predicate { idndef, .. }
            | PMemberKind::Method { idndef, .. }
            | PMemberKind::Define { idndef, .. } => Some(idndef.clone()),
            _ => None,
        },
        PNodeKind::Statement(statement) => match &statement.kind {
            PStatementKind::Label { idndef, .. } => Some(idndef.clone()),
            _ => None,
        },
        _ => None,
    }
}
fn visit_names(
    node: &PNodeHandle,
    current: &mut DeclarationMap,
    messages: &mut Vec<FastMessage>,
) -> Result<(), NameAnalysisError> {
    let kind = node.read().expect("poisoned parse node").kind.clone();
    let mut scope = None;
    match &kind {
        PNodeKind::Declaration(declaration) => {
            let (visibility, uniqueness, backward) = match declaration.kind {
                PDeclarationKind::FormalArg | PDeclarationKind::FormalReturn => (
                    DeclarationVisibility::Member,
                    DeclarationUniqueness::Member,
                    false,
                ),
                PDeclarationKind::LogicalVar | PDeclarationKind::LocalVar => (
                    DeclarationVisibility::Local,
                    DeclarationUniqueness::Scope,
                    false,
                ),
                PDeclarationKind::Field { .. } => (
                    DeclarationVisibility::Global,
                    DeclarationUniqueness::Global,
                    true,
                ),
            };
            add_named_declaration(
                current,
                node,
                &declaration.idndef,
                visibility,
                uniqueness,
                backward,
                messages,
            )?;
        }
        PNodeKind::Member(member) => {
            match &member.kind {
                PMemberKind::Function { idndef, .. }
                | PMemberKind::Predicate { idndef, .. }
                | PMemberKind::Method { idndef, .. } => add_named_declaration(
                    current,
                    node,
                    idndef,
                    DeclarationVisibility::Global,
                    DeclarationUniqueness::Global,
                    true,
                    messages,
                )?,
                PMemberKind::Fields { .. } | PMemberKind::Import { .. } => {}
                PMemberKind::Domain { .. }
                | PMemberKind::Define { .. }
                | PMemberKind::Extension(_) => {
                    return Err(NameAnalysisError::Unsupported(
                        "domain or macro name analysis",
                    ));
                }
            }
            scope = Some(DeclarationMap::new(true, false));
        }
        PNodeKind::Statement(statement) => match &statement.kind {
            PStatementKind::Label { idndef, .. } => add_named_declaration(
                current,
                node,
                idndef,
                DeclarationVisibility::Member,
                DeclarationUniqueness::None,
                true,
                messages,
            )?,
            PStatementKind::Seqn { .. } => scope = Some(DeclarationMap::new(false, false)),
            PStatementKind::Extension(_)
            | PStatementKind::MacroSeqn { .. }
            | PStatementKind::Quasihavocall { .. } => {
                return Err(NameAnalysisError::Unsupported(
                    "statement extension or macro scope",
                ));
            }
            _ => {}
        },
        PNodeKind::Expression(expression) => match &expression.kind {
            PExpressionKind::Forall(_)
            | PExpressionKind::Exists(_)
            | PExpressionKind::ForPerm { .. } => scope = Some(DeclarationMap::new(false, false)),
            PExpressionKind::Let { .. } | PExpressionKind::Extension(_) => {
                return Err(NameAnalysisError::Unsupported(
                    "let or extension name analysis",
                ));
            }
            _ => {}
        },
        PNodeKind::IdnRef(_) => current.new_ref(node.clone()),
        PNodeKind::DomainMember(_)
        | PNodeKind::TypeVarDecl { .. }
        | PNodeKind::DefineParam { .. }
        | PNodeKind::LetNestedScope { .. }
        | PNodeKind::Extension(_) => {
            return Err(NameAnalysisError::Unsupported(
                "domain, macro or extension name analysis",
            ));
        }
        _ => {}
    }
    let children = subnodes(node)?;
    if let Some(mut child) = scope {
        for child_node in children {
            visit_names(&child_node, &mut child, messages)?;
        }
        for (declaration, old) in current.merge(child, |_| false) {
            let idndef = declaration_identifier(&declaration.node)
                .ok_or(NameAnalysisError::Unsupported("declaration identifier"))?;
            report_duplicate(&declaration, &old, &idndef, messages)?;
        }
    } else {
        for child_node in children {
            visit_names(&child_node, current, messages)?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::fast_parser::parse_program;
    fn collect(node: &PNodeHandle, out: &mut Vec<PNodeHandle>) {
        out.push(node.clone());
        for child in subnodes(node).unwrap() {
            collect(&child, out);
        }
    }
    #[test]
    fn resolves_outer_formal_and_local_identifiers_in_source_order() {
        let program = parse_program(
            "method m(x: Int) { var y: Int := x; assert y > 0; }",
            "test.vpr",
        )
        .unwrap();
        let mut names = NameAnalyser::default();
        assert!(names.run(program.node()).unwrap());
        let mut nodes = Vec::new();
        collect(program.node(), &mut nodes);
        let refs: Vec<_> = nodes
            .into_iter()
            .filter_map(|n| {
                let snapshot = n.read().unwrap().kind.clone();
                match snapshot {
                    PNodeKind::IdnRef(r) if r.name == "x" || r.name == "y" => {
                        Some((r.name, r.declarations.len()))
                    }
                    _ => None,
                }
            })
            .collect();
        assert_eq!(refs, vec![("x".into(), 1), ("y".into(), 1)]);
    }
    #[test]
    fn duplicate_formals_are_reported() {
        let program = parse_program("method m(x: Int, x: Int)", "test.vpr").unwrap();
        let mut names = NameAnalyser::default();
        assert!(!names.run(program.node()).unwrap());
        assert_eq!(names.messages.len(), 1);
        assert!(names.messages[0].label.contains("duplicate identifier `x`"));
    }
}

/// One operator argument's actual type, signature type and possible substitutions.
#[derive(Clone)]
pub struct UnificationArgument {
    pub actual: super::parse_ast::PTypeHandle,
    pub expected: super::parse_ast::PTypeHandle,
    pub substitutions: Vec<super::parse_ast::PTypeSubstitution>,
    pub expression: PNodeHandle,
}
#[derive(Clone, Debug)]
pub enum UnificationError {
    EmptyCandidates,
    Mismatch {
        actual: super::parse_ast::PTypeHandle,
        expected: super::parse_ast::PTypeHandle,
        expression: PNodeHandle,
    },
}
/// Compose all argument alternatives before applying constraints, retaining candidate order.
pub fn unify_sequence_with_substitutions(
    signatures: &[super::parse_ast::PTypeSubstitution],
    arguments: &[UnificationArgument],
) -> Result<Vec<super::parse_ast::PTypeSubstitution>, UnificationError> {
    use super::parse_ast::{PTypeSubstitution, PTypeSubstitutionInternal};
    let mut candidates: Vec<_> = signatures
        .iter()
        .cloned()
        .map(|base| {
            PTypeSubstitutionInternal::new(base, PTypeSubstitution::new(HashMap::new(), true))
        })
        .collect();
    if candidates.is_empty() {
        return Err(UnificationError::EmptyCandidates);
    }
    for argument in arguments {
        let mut next = Vec::new();
        let mut first_error = None;
        for candidate in &candidates {
            for substitution in &argument.substitutions {
                match candidate.compose(substitution) {
                    Ok(merged) => next.push(merged),
                    Err(error) => {
                        if first_error.is_none() {
                            first_error = Some(error);
                        }
                    }
                }
            }
        }
        if next.is_empty() {
            return match first_error {
                Some((actual, expected)) => Err(UnificationError::Mismatch {
                    actual,
                    expected,
                    expression: argument.expression.clone(),
                }),
                None => Err(UnificationError::EmptyCandidates),
            };
        }
        candidates = next;
    }
    for argument in arguments {
        let mut next = Vec::new();
        let mut first_error = None;
        for candidate in &candidates {
            match candidate.add(&argument.actual, &argument.expected) {
                Ok(merged) => next.push(merged),
                Err(error) => {
                    if first_error.is_none() {
                        first_error = Some(error);
                    }
                }
            }
        }
        if next.is_empty() {
            return match first_error {
                Some((actual, expected)) => Err(UnificationError::Mismatch {
                    actual,
                    expected,
                    expression: argument.expression.clone(),
                }),
                None => Err(UnificationError::EmptyCandidates),
            };
        }
        candidates = next;
    }
    Ok(candidates
        .into_iter()
        .map(|candidate| candidate.collapse())
        .collect())
}

#[cfg(test)]
mod unification_tests {
    use super::*;
    use crate::ast::position::Position;
    use crate::parser::parse_ast::{PNode, PTypeSubstitution, p_type_var, type_from_signature};
    use crate::parser::parse_ast_keyword::SignatureType;
    #[test]
    fn filters_operator_candidates_without_reordering_them() {
        let int = type_from_signature(&SignatureType::Int);
        let boolean = type_from_signature(&SignatureType::Bool);
        let signature =
            |typ| PTypeSubstitution::new([("#T0".to_string(), typ)].into_iter().collect(), false);
        let node = PNode::new(
            PNodeKind::IdnDef(super::super::parse_ast::PIdnDef { name: "x".into() }),
            (Position::NoPosition, Position::NoPosition),
        );
        let arg = UnificationArgument {
            actual: int.clone(),
            expected: p_type_var("#T0"),
            substitutions: vec![PTypeSubstitution::default()],
            expression: node,
        };
        let result =
            unify_sequence_with_substitutions(&[signature(boolean), signature(int)], &[arg])
                .unwrap();
        assert_eq!(result.len(), 1);
    }
}

use super::parse_ast::{
    PExpHandle, PTypeHandle, PTypeSubstitution, fresh_type_renaming, is_subtype, p_type_var,
    substitution_from_signature,
};

#[derive(Clone, Debug)]
pub enum TypeCheckError {
    Unsupported(&'static str),
    Undeclared(String),
    AmbiguousIdentifier(String),
    Incompatible {
        expression: PNodeHandle,
        actual: PTypeHandle,
        expected: PTypeHandle,
    },
    Unification(UnificationError),
}
/// Infer supported literals, identifiers and unary/binary operator applications.
/// This does not claim to check a whole program; calls, statements, scopes, permissions,
/// quantifiers and remaining source restrictions still require the full TypeChecker.
pub fn check_expression(
    input: &PExpHandle,
    expected: Option<&PTypeHandle>,
) -> Result<PTypeHandle, TypeCheckError> {
    let expression = match &input.node().read().expect("poisoned parse node").kind {
        PNodeKind::Expression(expression) => expression.clone(),
        _ => return Err(TypeCheckError::Unsupported("not an expression")),
    };
    let (typ, substitutions) = match expression.kind {
        PExpressionKind::IntLit(_)
        | PExpressionKind::BoolLit(_)
        | PExpressionKind::NullLit(_)
        | PExpressionKind::NoPerm(_)
        | PExpressionKind::FullPerm(_)
        | PExpressionKind::Wildcard(_)
        | PExpressionKind::Epsilon(_) => (expression.typ, vec![PTypeSubstitution::default()]),
        PExpressionKind::IdnUse { idnref } => {
            let name = match &idnref.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(reference) => reference.name.clone(),
                _ => return Err(TypeCheckError::Unsupported("identifier reference")),
            };
            let candidates = super::parse_ast::PIdnRef::decls(&idnref, |_| true);
            if candidates.is_empty() {
                return Err(TypeCheckError::Undeclared(name));
            }
            if candidates.len() != 1 {
                return Err(TypeCheckError::AmbiguousIdentifier(name));
            }
            let typ = match &candidates[0].read().expect("poisoned parse node").kind {
                PNodeKind::Declaration(declaration) => declaration.typ.clone(),
                _ => return Err(TypeCheckError::Unsupported("identifier declaration")),
            };
            (typ, vec![PTypeSubstitution::default()])
        }
        PExpressionKind::UnExp { op, exp } => {
            let signatures = op
                .value()
                .signatures()
                .ok_or(TypeCheckError::Unsupported("unary operator"))?
                .iter()
                .map(substitution_from_signature)
                .collect();
            check_operator(input, signatures, vec![exp], expected, false)?
        }
        PExpressionKind::BinExp { left, op, right } => {
            let signatures = op
                .value()
                .signatures()
                .ok_or(TypeCheckError::Unsupported("binary operator"))?;
            let require_pure = op.value().require_pure_args();
            check_operator(input, signatures, vec![left, right], expected, require_pure)?
        }
        _ => return Err(TypeCheckError::Unsupported("expression typechecking")),
    };
    if let Some(expected) = expected {
        if typ.is_ground() && !is_subtype(&typ, expected) {
            return Err(TypeCheckError::Incompatible {
                expression: input.node().clone(),
                actual: typ,
                expected: expected.clone(),
            });
        }
    }
    let mut node = input.node().write().expect("poisoned parse node");
    let PNodeKind::Expression(expression) = &mut node.kind else {
        unreachable!()
    };
    expression.typ = typ.clone();
    expression.type_substitutions = Some(substitutions);
    Ok(typ)
}
fn check_operator(
    input: &PExpHandle,
    signatures: Vec<PTypeSubstitution>,
    arguments: Vec<PExpHandle>,
    expected: Option<&PTypeHandle>,
    require_pure: bool,
) -> Result<(PTypeHandle, Vec<PTypeSubstitution>), TypeCheckError> {
    let mut argument_types = Vec::new();
    for argument in &arguments {
        let typ = check_expression(argument, None)?;
        if require_pure && !typ.is_pure() {
            return Err(TypeCheckError::Unsupported("impure equality argument"));
        }
        argument_types.push(typ);
    }
    let mut names: std::collections::HashSet<String> = ["#R".into()].into_iter().collect();
    for index in 0..arguments.len() {
        names.insert(format!("#T{index}"));
    }
    for signature in &signatures {
        for (key, typ) in signature.iter() {
            names.insert(key.clone());
            names.extend(typ.free_type_variables());
        }
    }
    let renaming = fresh_type_renaming(&names.into_iter().collect::<Vec<_>>(), None);
    let replacement = renaming.as_substitution();
    let refreshed = signatures
        .iter()
        .map(|signature| {
            PTypeSubstitution::new(
                signature
                    .iter()
                    .map(|(key, value)| {
                        (
                            renaming.rename(key).to_owned(),
                            value.substitute(&replacement),
                        )
                    })
                    .collect(),
                false,
            )
        })
        .collect::<Vec<_>>();
    let result_type = p_type_var(renaming.rename("#R"));
    let mut constraints = Vec::new();
    for (index, (expression, actual)) in arguments.iter().zip(argument_types).enumerate() {
        constraints.push(UnificationArgument {
            actual,
            expected: p_type_var(renaming.rename(&format!("#T{index}"))),
            substitutions: expression
                .type_subs_distinct()
                .ok_or(TypeCheckError::Unsupported("binder substitution state"))?,
            expression: expression.node().clone(),
        });
    }
    if let Some(expected) = expected {
        constraints.push(UnificationArgument {
            actual: expected.clone(),
            expected: result_type.clone(),
            substitutions: vec![PTypeSubstitution::default()],
            expression: input.node().clone(),
        });
    }
    let substitutions = unify_sequence_with_substitutions(&refreshed, &constraints)
        .map_err(TypeCheckError::Unification)?;
    let types = substitutions
        .iter()
        .map(|s| result_type.substitute(s))
        .collect::<Vec<_>>();
    let typ = if types.iter().all(|t| t.structurally_equals(&types[0])) {
        types[0].clone()
    } else {
        result_type
    };
    Ok((typ, substitutions))
}

#[cfg(test)]
mod expression_tests {
    use super::*;
    use crate::parser::fast_parser::parse_expression;
    use crate::parser::parse_ast::type_from_signature;
    use crate::parser::parse_ast_keyword::SignatureType;
    #[test]
    fn infers_arithmetic_and_narrows_division_using_context() {
        let add = parse_expression("1 + 2 * 3", "test.vpr")
            .unwrap()
            .expression;
        let typ = check_expression(&add, None).unwrap();
        assert!(typ.structurally_equals(&type_from_signature(&SignatureType::Int)));
        let div = parse_expression("1 / 2", "test.vpr").unwrap().expression;
        let typ = check_expression(&div, Some(&type_from_signature(&SignatureType::Int))).unwrap();
        assert!(typ.structurally_equals(&type_from_signature(&SignatureType::Int)));
        assert!(
            check_expression(
                &parse_expression("1 + true", "test.vpr").unwrap().expression,
                None
            )
            .is_err()
        );
    }
}
