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

use super::parse_ast::{PMember, PNodeHandle, PNodeKind};
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
#[derive(Clone, Default)]
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
    scopes: HashMap<usize, (PNodeHandle, DeclarationMap)>,
}
impl Default for NameAnalyser {
    fn default() -> Self {
        Self {
            messages: Vec::new(),
            global: DeclarationMap::new(false, true),
            scopes: HashMap::new(),
        }
    }
}
impl NameAnalyser {
    pub fn reset(&mut self) {
        self.global.clear();
        self.scopes.clear();
    }
    pub fn run(&mut self, root: &PNodeHandle) -> Result<bool, NameAnalysisError> {
        let mut global = std::mem::replace(&mut self.global, DeclarationMap::new(false, true));
        let result = visit_names(
            root,
            &mut global,
            &mut self.messages,
            &mut self.scopes,
            true,
        );
        self.global = global;
        result?;
        Ok(self.messages.iter().all(|message| !message.error))
    }
    /// Rebuild scope declarations without altering existing resolved references.
    pub fn collect_scopes(&mut self, root: &PNodeHandle) -> Result<(), NameAnalysisError> {
        self.reset();
        self.messages.clear();
        let mut global = DeclarationMap::new(false, true);
        let result = visit_names(
            root,
            &mut global,
            &mut self.messages,
            &mut self.scopes,
            false,
        );
        self.global = global;
        result
    }
    /// Resolve a new expression using the map retained for a parsed source scope.
    pub fn run_in_scope(
        &mut self,
        root: &PNodeHandle,
        scope: &PNodeHandle,
    ) -> Result<bool, NameAnalysisError> {
        let key = std::sync::Arc::as_ptr(scope) as usize;
        let (retained_scope, mut declarations) = self
            .scopes
            .remove(&key)
            .ok_or(NameAnalysisError::Unsupported("unknown debugger scope"))?;
        let result = visit_names(
            root,
            &mut declarations,
            &mut self.messages,
            &mut self.scopes,
            true,
        );
        self.scopes.insert(key, (retained_scope, declarations));
        result?;
        // Resolve names absent from the current scope against enclosing scopes,
        // nearest first, then global siblings. Do not mutate the original parse tree.
        let mut outer = Vec::new();
        let mut cursor = super::parse_ast::get_enclosing_scope(scope);
        while let Some(parent) = cursor {
            if let Some((_, map)) = self.scopes.get(&(std::sync::Arc::as_ptr(&parent) as usize)) {
                outer.push(map);
            }
            cursor = super::parse_ast::get_enclosing_scope(&parent);
        }
        outer.push(&self.global);
        fn resolve_outer(
            node: &PNodeHandle,
            maps: &[&DeclarationMap],
        ) -> Result<(), NameAnalysisError> {
            let name = match &node.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(reference) if reference.declarations.is_empty() => {
                    Some(reference.name.clone())
                }
                _ => None,
            };
            if let Some(name) = name {
                for map in maps {
                    if let Some(declarations) = map.decls.get(&name) {
                        with_reference(node, |reference| {
                            for declaration in declarations {
                                reference.new_decl(&declaration.node);
                            }
                        });
                        break;
                    }
                }
            }
            for child in subnodes(node)? {
                resolve_outer(&child, maps)?;
            }
            Ok(())
        }
        resolve_outer(root, &outer)?;
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

/// Resolve value identifiers independently when declaration errors already exist,
/// so unrelated missing or ambiguous values are not hidden by those errors.
pub fn value_identifier_messages(
    root: &PNodeHandle,
) -> Result<Vec<FastMessage>, NameAnalysisError> {
    fn visit(node: &PNodeHandle, messages: &mut Vec<FastMessage>) -> Result<(), NameAnalysisError> {
        let kind = node.read().expect("poisoned parse node").kind.clone();
        if matches!(
            &kind,
            PNodeKind::Member(PMember {
                kind: PMemberKind::Define { .. },
                ..
            })
        ) {
            return Ok(());
        }
        // Assignment targets use a context-specific declaration filter and
        // diagnostics in the statement checker. Treat only the RHS as an
        // ordinary value expression here.
        if let PNodeKind::Statement(super::parse_ast::PStatement {
            kind: PStatementKind::Assign { rhs, .. },
        }) = &kind
        {
            return visit(rhs.node(), messages);
        }
        if let PNodeKind::Expression(super::parse_ast::PExpression {
            kind: PExpressionKind::IdnUse { idnref },
            ..
        }) = &kind
        {
            let candidates = super::parse_ast::PIdnRef::decls(idnref, |_| true);
            let name = match &idnref.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(reference) => reference.name.clone(),
                _ => return Err(NameAnalysisError::Unsupported("identifier reference")),
            };
            if candidates.is_empty() || candidates.len() > 1 {
                let label = if candidates.is_empty() {
                    format!("undeclared identifier `{name}`")
                } else {
                    format!("ambiguous identifier `{name}`")
                };
                messages.extend(message_for_node(idnref, label, true, true)?);
            }
        }
        for child in subnodes(node)? {
            visit(&child, messages)?;
        }
        Ok(())
    }
    let mut messages = Vec::new();
    visit(root, &mut messages)?;
    Ok(messages)
}
fn definition_name(node: &PNodeHandle) -> String {
    match &node.read().expect("poisoned parse node").kind {
        PNodeKind::IdnDef(name) => name.name.clone(),
        _ => panic!("expected identifier definition"),
    }
}
fn let_binding(node: &PNodeHandle) -> Option<(PNodeHandle, super::parse_ast::PExpHandle)> {
    let parent = super::parse_ast::get_ancestor(node, |node| {
        matches!(
            &node.read().expect("poisoned parse node").kind,
            PNodeKind::Expression(super::parse_ast::PExpression {
                kind: PExpressionKind::Let { .. },
                ..
            })
        )
    })?;
    let snapshot = parent.read().expect("poisoned parse node").kind.clone();
    match snapshot {
        PNodeKind::Expression(super::parse_ast::PExpression {
            kind: PExpressionKind::Let { variable, exp, .. },
            ..
        }) => Some((variable, exp.inner().clone())),
        _ => None,
    }
}
fn adt_signature(
    owner: &PNodeHandle,
) -> Result<(String, Vec<String>, super::parse_ast::PTypeHandle), TypeCheckError> {
    use super::parse_ast::{PDeclarationClass, PDomainTypeKind, PIdnRef, PNode, PTypeKind};
    use super::parse_ast_keyword::{PDelimited, PGrouped, PReserved, PSym};
    let adt = match &owner.read().expect("poisoned parse node").kind {
        PNodeKind::Member(PMember {
            kind: PMemberKind::Extension(ext),
            ..
        }) => ext
            .as_any()
            .downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdt>()
            .cloned()
            .ok_or(TypeCheckError::Unsupported("ADT owner"))?,
        _ => return Err(TypeCheckError::Unsupported("ADT owner")),
    };
    let name = definition_name(&adt.idndef);
    let names = adt
        .type_vars
        .iter()
        .map(|node| {
            declaration_identifier(node)
                .map(|id| definition_name(&id))
                .ok_or(TypeCheckError::Unsupported("ADT type variable"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let no_pos = (
        crate::ast::position::Position::NoPosition,
        crate::ast::position::Position::NoPosition,
    );
    let mut reference = PIdnRef::with_class(name.clone(), PDeclarationClass::TypeDeclaration);
    reference.new_decl(owner);
    let domain = PNode::new(PNodeKind::IdnRef(reference), no_pos.clone());
    let args = if adt.type_vars_present {
        let mut vars = names
            .iter()
            .map(|name| super::parse_ast::p_type_var(name.clone()));
        let first = vars.next();
        let rest = vars
            .map(|v| (PReserved::new(PSym::Comma, no_pos.clone()), v))
            .collect();
        let list = PDelimited::new(first, rest, None, no_pos.clone());
        Some(PGrouped::new(
            PReserved::new(PSym::LBracket, no_pos.clone()),
            list,
            PReserved::new(PSym::RBracket, no_pos.clone()),
            no_pos.clone(),
        ))
    } else {
        None
    };
    let typ = super::parse_ast::PTypeHandle::new(
        PTypeKind::Domain {
            domain,
            args,
            kind: PDomainTypeKind::Adt,
        },
        no_pos,
    );
    Ok((name, names, typ))
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
            PMemberKind::Extension(extension) => extension
                .as_any()
                .downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdt>()
                .map(|adt| adt.idndef.clone()),
            _ => None,
        },
        PNodeKind::Extension(extension) => extension
            .as_any()
            .downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>()
            .map(|constructor| constructor.idndef.clone()),
        PNodeKind::DomainMember(super::parse_ast::PDomainMember::Function { idndef, .. }) => {
            Some(idndef.clone())
        }
        PNodeKind::TypeVarDecl { children } => children.first().cloned(),
        PNodeKind::LetNestedScope { .. } => let_binding(node).map(|(id, _)| id),
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
    scopes: &mut HashMap<usize, (PNodeHandle, DeclarationMap)>,
    resolve_references: bool,
) -> Result<(), NameAnalysisError> {
    let kind = node.read().expect("poisoned parse node").kind.clone();
    if matches!(
        &kind,
        PNodeKind::Member(PMember {
            kind: PMemberKind::Define { .. },
            ..
        })
    ) {
        return Ok(());
    }
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
                PDeclarationKind::AdtField => (
                    DeclarationVisibility::Global,
                    DeclarationUniqueness::Member,
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
                PMemberKind::Extension(extension) if extension.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdt>() => {
                    let adt = extension.as_any().downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdt>().expect("checked ADT");
                    add_named_declaration(current, node, &adt.idndef, DeclarationVisibility::Global, DeclarationUniqueness::None, true, messages)?;
                }
                PMemberKind::Domain { idndef, .. } =>
                {
                    add_named_declaration(current, node, idndef, DeclarationVisibility::Global, DeclarationUniqueness::Global, true, messages)?;
                }
                PMemberKind::Define { .. }
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
            PStatementKind::Seqn { .. } | PStatementKind::Quasihavocall { .. } => scope = Some(DeclarationMap::new(false, false)),
            PStatementKind::Extension(extension) if !extension.statement_name_analysis_passthrough() && !extension.as_any().is::<crate::plugin::standard::refute::refute_past_extension::PRefute>() && !extension.as_any().is::<crate::plugin::standard::smoke::unreachable_past_extension::PUnreachable>() => {
                return Err(NameAnalysisError::Unsupported("statement extension scope"));
            }
            PStatementKind::MacroSeqn { .. } => {
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
            PExpressionKind::Extension(extension) if !extension.expression_name_analysis_passthrough() && !extension.as_any().is::<crate::plugin::standard::predicateinstance::predicate_instance_past_extension::PPredicateInstance>() && !extension.as_any().is::<crate::plugin::sif::sifp_ast_extensions::PSifExpression>() && !extension.as_any().is::<crate::plugin::standard::arp::arppast_extension::PRdPerm>() && !extension.as_any().is::<crate::plugin::standard::termination::termination_past_extension::PDecreasesClause>() => {
                return Err(NameAnalysisError::Unsupported("expression extension name analysis"));
            }
            PExpressionKind::Let { .. } => scope = Some(DeclarationMap::new(false, false)),
            _ => {}
        },
        PNodeKind::IdnRef(_) if resolve_references => current.new_ref(node.clone()),
        PNodeKind::DomainMember(super::parse_ast::PDomainMember::Axiom { .. }) => scope = Some(DeclarationMap::new(true, false)),
        PNodeKind::DomainMember(super::parse_ast::PDomainMember::Function { idndef, .. }) => {
            add_named_declaration(current, node, idndef, DeclarationVisibility::Global, DeclarationUniqueness::Global, true, messages)?;
            scope = Some(DeclarationMap::new(true, false));
        },
        PNodeKind::TypeVarDecl { children } => {
            let idndef = children.first().ok_or(NameAnalysisError::Unsupported("type variable identifier"))?;
            add_named_declaration(current, node, idndef, DeclarationVisibility::Member, DeclarationUniqueness::None, false, messages)?;
        }
        PNodeKind::LetNestedScope { .. } => {
            let (idndef, _) = let_binding(node).ok_or(NameAnalysisError::Unsupported("let binding owner"))?;
            add_named_declaration(current, node, &idndef, DeclarationVisibility::Local, DeclarationUniqueness::Scope, false, messages)?;
        }
        PNodeKind::Extension(extension) if extension.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>() => {
            let ctor = extension.as_any().downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>().expect("checked ADT constructor");
            add_named_declaration(current, node, &ctor.idndef, DeclarationVisibility::Global, DeclarationUniqueness::Global, true, messages)?;
        }
        PNodeKind::Extension(extension) if extension.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdtDerivingInfo>() => {}
        PNodeKind::Extension(extension) if extension.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdtSyntax>() => {}
        PNodeKind::DefineParam { .. }
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
            visit_names(
                &child_node,
                &mut child,
                messages,
                scopes,
                resolve_references,
            )?;
        }
        if !resolve_references {
            scopes.insert(
                std::sync::Arc::as_ptr(node) as usize,
                (node.clone(), child.clone()),
            );
        }
        for (declaration, old) in current.merge(child, |_| false) {
            let idndef = declaration_identifier(&declaration.node)
                .ok_or(NameAnalysisError::Unsupported("declaration identifier"))?;
            report_duplicate(&declaration, &old, &idndef, messages)?;
        }
    } else {
        for child_node in children {
            visit_names(&child_node, current, messages, scopes, resolve_references)?;
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
    #[test]
    fn resolves_domain_type_variables_inside_domain_members() {
        let program = parse_program("domain D[T] { function f(x: T): T }", "test.vpr").unwrap();
        let mut names = NameAnalyser::default();
        assert!(names.run(program.node()).unwrap());
        let mut nodes = Vec::new();
        collect(program.node(), &mut nodes);
        let refs: Vec<_> = nodes
            .into_iter()
            .filter_map(|n| {
                let kind = n.read().unwrap().kind.clone();
                match kind {
                    PNodeKind::IdnRef(r) if r.name == "T" => Some(r.declarations),
                    _ => None,
                }
            })
            .collect();
        assert_eq!(refs.len(), 2);
        assert!(refs.iter().all(|decls| decls.len() == 1
            && matches!(decls[0].read().unwrap().kind, PNodeKind::TypeVarDecl { .. })));
        assert!(names.global_definitions("T").is_empty());
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
    substitution_from_signature, type_from_signature,
};

#[derive(Clone, Debug)]
pub enum TypeCheckError {
    Unsupported(&'static str),
    Undeclared(String),
    AmbiguousIdentifier(String),
    UnresolvedValue {
        name: String,
        identifier: PNodeHandle,
        ambiguous: bool,
    },
    PositionedMessage {
        node: PNodeHandle,
        message: String,
    },
    FunctionPreconditionInDomainAxiom {
        name: String,
        identifier: PNodeHandle,
    },
    InvalidSifRelIndex(num_bigint::BigInt),
    Incompatible {
        expression: PNodeHandle,
        actual: PTypeHandle,
        expected: PTypeHandle,
    },
    Unification(UnificationError),
    /// Independent source type mismatches discovered while checking sibling nodes.
    Mismatches(Vec<TypeCheckError>),
    Positioned {
        node: PNodeHandle,
        message: &'static str,
    },
}
fn retain_type_mismatches<T>(
    errors: &mut Vec<TypeCheckError>,
    result: Result<T, TypeCheckError>,
) -> Result<(), TypeCheckError> {
    match result {
        Ok(_) => Ok(()),
        Err(TypeCheckError::Unification(error @ UnificationError::Mismatch { .. })) => {
            errors.push(TypeCheckError::Unification(error));
            Ok(())
        }
        Err(error @ TypeCheckError::Positioned { .. }) => {
            errors.push(error);
            Ok(())
        }
        Err(error @ TypeCheckError::UnresolvedValue { .. })
        | Err(error @ TypeCheckError::PositionedMessage { .. }) => {
            errors.push(error);
            Ok(())
        }
        Err(error @ TypeCheckError::Incompatible { .. }) => {
            errors.push(error);
            Ok(())
        }
        Err(TypeCheckError::Mismatches(more)) => {
            errors.extend(more);
            Ok(())
        }
        Err(error) => {
            if errors.is_empty() {
                Err(error)
            } else {
                errors.push(error);
                Err(TypeCheckError::Mismatches(std::mem::take(errors)))
            }
        }
    }
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
        PExpressionKind::AnnotatedExp { expression, .. } => {
            let typ = check_expression(&expression, expected)?;
            let substitutions = expression.type_subs_distinct().ok_or(TypeCheckError::Unsupported("annotated expression substitutions"))?;
            (typ, substitutions)
        }
        PExpressionKind::IntLit(_)
        | PExpressionKind::BoolLit(_)
        | PExpressionKind::NullLit(_)
        | PExpressionKind::NoPerm(_)
        | PExpressionKind::FullPerm(_)
        | PExpressionKind::Wildcard(_)
        | PExpressionKind::Epsilon(_) => (expression.typ, vec![PTypeSubstitution::default()]),
        PExpressionKind::ResultLit(_) => {
            if !expression.typ.is_valid_or_undeclared() {
                return Err(TypeCheckError::Unsupported(
                    "`result` can only be used in function postconditions",
                ));
            }
            (expression.typ, vec![PTypeSubstitution::default()])
        }
        PExpressionKind::VersionedIdnUse { .. } => {
            if !expression.typ.is_valid_or_undeclared() {
                return Err(TypeCheckError::Unsupported("unresolved debugger variable type"));
            }
            (expression.typ, vec![PTypeSubstitution::default()])
        }
        PExpressionKind::IdnUse { idnref } => {
            let name = match &idnref.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(reference) => reference.name.clone(),
                _ => return Err(TypeCheckError::Unsupported("identifier reference")),
            };
            let candidates = super::parse_ast::PIdnRef::decls(&idnref, |_| true);
            if candidates.is_empty() {
                return Err(TypeCheckError::UnresolvedValue { name, identifier: idnref, ambiguous: false });
            }
            if candidates.len() != 1 {
                return Err(TypeCheckError::UnresolvedValue { name, identifier: idnref, ambiguous: true });
            }
            let declaration = candidates[0].read().expect("poisoned parse node").kind.clone();
            let typ = match declaration {
                PNodeKind::Declaration(declaration) => declaration.typ,
                PNodeKind::LetNestedScope { .. } => {
                    let (_, value) = let_binding(&candidates[0]).ok_or(TypeCheckError::Unsupported("let binding owner"))?;
                    match &value.node().read().expect("poisoned parse node").kind { PNodeKind::Expression(e) => e.typ.clone(), _ => return Err(TypeCheckError::Unsupported("let value")) }
                }
                _ => return Err(TypeCheckError::Unsupported("identifier declaration")),
            };
            (typ, vec![PTypeSubstitution::default()])
        }
        PExpressionKind::Let { exp, nested_scope, .. } => {
            check_expression(exp.inner(), None)?;
            let body = match &nested_scope.read().expect("poisoned parse node").kind { PNodeKind::LetNestedScope { body } => body.clone(), _ => return Err(TypeCheckError::Unsupported("let body")) };
            let typ = check_expression(&body, None)?;
            let substitutions = input.type_subs_distinct().ok_or(TypeCheckError::Unsupported("let substitutions"))?;
            (typ, substitutions)
        }
        PExpressionKind::UnExp { op, exp } => {
            let signatures = op
                .value()
                .signatures()
                .ok_or(TypeCheckError::Unsupported("unary operator"))?
                .iter()
                .map(substitution_from_signature)
                .collect();
            check_operator(input, Some(signatures), vec![exp], expected, false)?
        }
        PExpressionKind::BinExp { left, op, right } => {
            let signatures = op
                .value()
                .signatures()
                .ok_or(TypeCheckError::Unsupported("binary operator"))?;
            let require_pure = op.value().require_pure_args();
            check_operator(
                input,
                Some(signatures),
                vec![left, right],
                expected,
                require_pure,
            )?
        }
        PExpressionKind::Call {
            idnref,
            call_args,
            type_annotated,
            ..
        } => {
            let name = match &idnref.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(r) => r.name.clone(),
                _ => return Err(TypeCheckError::Unsupported("call identifier")),
            };
            let candidates = super::parse_ast::PIdnRef::decls(&idnref, |_| true);
            if candidates.is_empty() {
                return Err(TypeCheckError::PositionedMessage { node: idnref, message: format!("undeclared call `{name}`, expected function or predicate") });
            }
            let predicate = std::sync::Arc::new(|node: &PNodeHandle| {
                matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Member(member) if matches!(member.kind, PMemberKind::Function { .. } | PMemberKind::Predicate { .. }))
                    || matches!(
                        &node.read().expect("poisoned parse node").kind,
                        PNodeKind::DomainMember(super::parse_ast::PDomainMember::Function { .. })
                    ) || matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Extension(extension) if extension.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>())
            });
            super::parse_ast::PIdnRef::filter_decls(&idnref, predicate, |_| true);
            let candidates = super::parse_ast::PIdnRef::decls(&idnref, |_| true);
            if candidates.is_empty() {
                return Err(TypeCheckError::Unsupported(
                    "call is not a function or predicate",
                ));
            }
            if candidates.len() != 1 {
                return Err(TypeCheckError::PositionedMessage { node: idnref, message: format!("ambiguous call `{name}`") });
            }
            let declaration = candidates[0]
                .read()
                .expect("poisoned parse node")
                .kind
                .clone();
            let (formal_types, result_type, predicate_call) = match declaration {
                PNodeKind::Member(member) => match member.kind {
                    PMemberKind::Function {
                        args, result_type, ..
                    } => {
                        let mut types = Vec::new();
                        for arg in args.inner().to_seq() {
                            match &arg.node().read().expect("poisoned parse node").kind {
                                PNodeKind::Declaration(d) => types.push(d.typ.clone()),
                                _ => return Err(TypeCheckError::Unsupported("formal parameter")),
                            }
                        }
                        (types, result_type, false)
                    }
                    PMemberKind::Predicate { args, .. } => {
                        let mut types = Vec::new();
                        for arg in args.inner().to_seq() {
                            match &arg.node().read().expect("poisoned parse node").kind {
                                PNodeKind::Declaration(d) => types.push(d.typ.clone()),
                                _ => return Err(TypeCheckError::Unsupported("formal parameter")),
                            }
                        }
                        (
                            types,
                            type_from_signature(
                                &super::parse_ast_keyword::SignatureType::Predicate,
                            ),
                            true,
                        )
                    }
                    _ => return Err(TypeCheckError::Unsupported("call declaration")),
                },
                PNodeKind::DomainMember(super::parse_ast::PDomainMember::Function {
                    args,
                    result_type,
                    ..
                }) => {
                    let domain = super::parse_ast::get_ancestor(&candidates[0], |node| {
                        matches!(
                            &node.read().expect("poisoned parse node").kind,
                            PNodeKind::Member(PMember {
                                kind: PMemberKind::Domain { .. },
                                ..
                            })
                        )
                    })
                    .ok_or(TypeCheckError::Unsupported("domain function owner"))?;
                    let (domain_name, names) = match &domain.read().expect("poisoned parse node").kind {
                        PNodeKind::Member(PMember {
                            kind: PMemberKind::Domain { idndef, type_vars, .. },
                            ..
                        }) => {
                            let names = type_vars.as_ref().map(|v| v.inner().to_seq().into_iter().map(|node| declaration_identifier(node).map(|id| definition_name(&id)).ok_or(TypeCheckError::Unsupported("domain type variable"))).collect::<Result<Vec<_>, _>>()).transpose()?.unwrap_or_default();
                            (definition_name(idndef), names)
                        },
                        _ => return Err(TypeCheckError::Unsupported("domain function owner")),
                    };
                    let renaming = super::parse_ast::fresh_type_renaming(&names, Some(&domain_name));
                    let substitution = renaming.as_substitution();
                    if let PNodeKind::Expression(exp) = &mut input.node().write().expect("poisoned parse node").kind {
                        if let PExpressionKind::Call { domain_type_renaming, extra_local_type_variables, .. } = &mut exp.kind {
                            *domain_type_renaming = Some(renaming);
                            *extra_local_type_variables = names.into_iter().map(super::parse_ast::p_type_var).collect();
                        }
                    }
                    (
                        args.inner()
                            .to_seq()
                            .into_iter()
                            .map(|a| a.typ().substitute(&substitution))
                            .collect(),
                        result_type.substitute(&substitution),
                        false,
                    )
                }
                PNodeKind::Extension(extension) if extension.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>() => {
                    use super::parse_ast::{PDomainTypeKind, PExpression, PIdnRef, PNode, PTypeKind};
                    use super::parse_ast_keyword::{PDelimited, PGrouped, PReserved, PSym};
                    let constructor = extension.as_any().downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>().expect("checked ADT constructor");
                    let owner = super::parse_ast::get_ancestor(&candidates[0], |node| matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Member(PMember { kind: PMemberKind::Extension(ext), .. }) if ext.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdt>())).ok_or(TypeCheckError::Unsupported("ADT constructor owner"))?;
                    let adt = match &owner.read().expect("poisoned parse node").kind { PNodeKind::Member(PMember { kind: PMemberKind::Extension(ext), .. }) => ext.as_any().downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdt>().cloned().ok_or(TypeCheckError::Unsupported("ADT constructor owner"))?, _ => return Err(TypeCheckError::Unsupported("ADT constructor owner")) };
                    let adt_name = definition_name(&adt.idndef);
                    let names = adt.type_vars.iter().map(|node| declaration_identifier(node).map(|id| definition_name(&id)).ok_or(TypeCheckError::Unsupported("ADT type variable"))).collect::<Result<Vec<_>, _>>()?;
                    let renaming = super::parse_ast::fresh_type_renaming(&names, Some(&adt_name));
                    let substitution = renaming.as_substitution();
                    if let PNodeKind::Expression(PExpression { kind: PExpressionKind::Call { domain_type_renaming, extra_local_type_variables, .. }, .. }) = &mut input.node().write().expect("poisoned parse node").kind {
                        *domain_type_renaming = Some(renaming);
                        *extra_local_type_variables = names.iter().cloned().map(super::parse_ast::p_type_var).collect();
                    }
                    let no_pos = (crate::ast::position::Position::NoPosition, crate::ast::position::Position::NoPosition);
                    let mut reference = PIdnRef::with_class(adt_name, super::parse_ast::PDeclarationClass::TypeDeclaration);
                    reference.new_decl(&owner);
                    let domain = PNode::new(PNodeKind::IdnRef(reference), no_pos.clone());
                    let args = if adt.type_vars_present {
                        let mut vars = names.iter().map(|name| super::parse_ast::p_type_var(name.clone()));
                        let first = vars.next();
                        let rest = vars.map(|v| (PReserved::new(PSym::Comma, no_pos.clone()), v)).collect();
                        let list = PDelimited::new(first, rest, None, no_pos.clone());
                        Some(PGrouped::new(PReserved::new(PSym::LBracket, no_pos.clone()), list, PReserved::new(PSym::RBracket, no_pos.clone()), no_pos.clone()))
                    } else { None };
                    let result = super::parse_ast::PTypeHandle::new(PTypeKind::Domain { domain, args, kind: PDomainTypeKind::Adt }, no_pos);
                    let formals = constructor.args.inner().to_seq().into_iter().map(|arg| match &arg.node().read().expect("poisoned parse node").kind { PNodeKind::Declaration(d) => Ok(d.typ.substitute(&substitution)), _ => Err(TypeCheckError::Unsupported("ADT field declaration")) }).collect::<Result<Vec<_>, _>>()?;
                    (formals, result.substitute(&substitution), false)
                }
                _ => return Err(TypeCheckError::Unsupported("call declaration")),
            };
            if predicate_call && type_annotated.is_some() {
                return Err(TypeCheckError::Unsupported(
                    "predicate call with explicit type",
                ));
            }
            let args = call_args
                .inner()
                .to_seq()
                .into_iter()
                .cloned()
                .collect::<Vec<_>>();
            if formal_types.len() != args.len() {
                return Err(TypeCheckError::Positioned { node: input.node().clone(), message: "wrong number of arguments" });
            }
            let mut bindings = HashMap::new();
            for (index, typ) in formal_types.into_iter().enumerate() {
                if !typ.is_valid_or_undeclared() {
                    return Err(TypeCheckError::Unsupported("formal parameter type"));
                }
                bindings.insert(format!("#T{index}"), typ);
            }
            bindings.insert("#R".to_string(), result_type);
            let annotation = type_annotated.as_ref().map(|(_, typ)| typ);
            if let Some(annotation) = annotation { check_supported_type(annotation)?; }
            if annotation.is_some() && expected.is_some() {
                return Err(TypeCheckError::Unsupported(
                    "both annotated and contextual call constraints",
                ));
            }
            check_operator(
                input,
                Some(vec![PTypeSubstitution::new(bindings, false)]),
                args,
                annotation.or(expected),
                false,
            )?
        }
        PExpressionKind::AccPred { amount, .. } => {
            let location = amount.inner().first().clone();
            let args = std::iter::once(location.clone())
                .chain(amount.inner().second().map(|(_, e)| e.clone()))
                .collect();
            let result = check_operator(input, None, args, expected, false)?;
            ensure_location_access(&location, false)?;
            result
        }
        PExpressionKind::CurrentPerm { resource, .. } => {
            let location = resource.inner().clone();
            let result = check_operator(input, None, vec![location.clone()], expected, false)?;
            ensure_location_access(&location, true)?;
            result
        }
        PExpressionKind::Unfolding { acc, exp, .. } => {
            let result = check_operator(input, None, vec![acc.clone(), exp], expected, false)?;
            ensure_nonabstract_predicate_access(&acc, false)?;
            result
        }
        PExpressionKind::Applying { wand, exp, .. } => {
            let is_wand = matches!(&wand.node().read().expect("poisoned parse node").kind, PNodeKind::Expression(e) if matches!(e.kind, PExpressionKind::MagicWandExp { .. }));
            if !is_wand {
                return Err(TypeCheckError::Unsupported("expected magic wand"));
            }
            check_operator(input, None, vec![wand, exp], expected, false)?
        }
        PExpressionKind::Asserting { assertion, exp, .. } => {
            check_operator(input, None, vec![assertion, exp], expected, false)?
        }
        PExpressionKind::CondExp { cond, thn, els, .. } => {
            check_operator(input, None, vec![cond, thn, els], expected, false)?
        }
        PExpressionKind::MagicWandExp { left, right, .. } => {
            check_operator(input, None, vec![left, right], expected, false)?
        }
        PExpressionKind::InhaleExhale { inhale, exhale, .. } => {
            check_operator(input, None, vec![inhale, exhale], expected, false)?
        }
        PExpressionKind::FieldAccess { receiver, idnref, .. } => {
            use super::parse_ast::{PDeclarationClass, PDomainTypeKind, PTypeKind};
            let class = match &idnref.read().expect("poisoned parse node").kind { PNodeKind::IdnRef(id) => id.declaration_class, _ => return Err(TypeCheckError::Unsupported("field identifier")) };
            if matches!(class, PDeclarationClass::AdtField | PDeclarationClass::AdtConstructor) {
                let receiver_type = check_expression(&receiver, None)?;
                let receiver_name = match receiver_type.kind() { PTypeKind::Domain { domain, kind: PDomainTypeKind::Adt, .. } => match &domain.read().expect("poisoned parse node").kind { PNodeKind::IdnRef(id) => id.name.clone(), _ => return Err(TypeCheckError::Unsupported("ADT receiver")) }, _ => return Err(TypeCheckError::Unsupported("ADT receiver type")) };
                let candidates = super::parse_ast::PIdnRef::decls(&idnref, |_| true);
                let mut matching = Vec::new();
                for candidate in candidates {
                    let owner = super::parse_ast::get_ancestor(&candidate, |node| matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Member(PMember { kind: PMemberKind::Extension(ext), .. }) if ext.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdt>()));
                    if let Some(owner) = owner {
                        let (name, _, _) = adt_signature(&owner)?;
                        if class == PDeclarationClass::AdtConstructor || name == receiver_name { matching.push((candidate, owner)); }
                    }
                }
                if matching.len() != 1 { return Err(TypeCheckError::Unsupported("undefined or ambiguous ADT member")); }
                let (declaration, owner) = matching.pop().expect("one ADT member");
                let selected = declaration.clone();
                super::parse_ast::PIdnRef::filter_decls(&idnref, std::sync::Arc::new(move |node| std::sync::Arc::ptr_eq(node, &selected)), |_| true);
                let (adt_name, names, receiver_signature) = adt_signature(&owner)?;
                let renaming = super::parse_ast::fresh_type_renaming(&names, Some(&adt_name));
                let substitution = renaming.as_substitution();
                if let PNodeKind::Expression(super::parse_ast::PExpression { kind: PExpressionKind::FieldAccess { adt_type_renaming, .. }, .. }) = &mut input.node().write().expect("poisoned parse node").kind { *adt_type_renaming = Some(renaming); }
                let result_type = if class == PDeclarationClass::AdtConstructor { type_from_signature(&super::parse_ast_keyword::SignatureType::Bool) } else {
                    match &declaration.read().expect("poisoned parse node").kind { PNodeKind::Declaration(d) => d.typ.substitute(&substitution), _ => return Err(TypeCheckError::Unsupported("ADT field declaration")) }
                };
                let bindings = [("#T0".into(), receiver_signature.substitute(&substitution)), ("#R".into(), result_type)].into_iter().collect();
                check_operator(input, Some(vec![PTypeSubstitution::new(bindings, false)]), vec![receiver], expected, false)?
            } else { check_operator(input, None, vec![receiver], expected, false)? }
        }
        PExpressionKind::DebugLabelledOldExp { exp, .. } => {
            check_operator(input, None, vec![exp], expected, false)?
        }
        PExpressionKind::OldExp { exp, .. } => {
            check_operator(input, None, vec![exp.inner().clone()], expected, false)?
        }
        PExpressionKind::EmptySeq(collection) | PExpressionKind::EmptySet(collection) | PExpressionKind::EmptyMultiset(collection) => {
            if let Some(typ) = &collection.annotated_type { check_supported_type(typ.inner())?; }
            check_operator(input, None, vec![], expected, false)?
        }
        PExpressionKind::ExplicitSeq(collection) | PExpressionKind::ExplicitSet(collection) | PExpressionKind::ExplicitMultiset(collection) => {
            let args = collection.call_args().inner().to_seq().into_iter().cloned().collect();
            check_operator(input, None, args, expected, false)?
        }
        PExpressionKind::MapDomain { base, .. } | PExpressionKind::MapRange { base, .. } => check_operator(input, None, vec![base.inner().clone()], expected, false)?,
        PExpressionKind::EmptyMap { annotated_type, .. } => {
            if let Some(types) = &annotated_type { check_supported_type(types.inner().first())?; check_supported_type(types.inner().second())?; }
            check_operator(input, None, vec![], expected, false)?
        }
        PExpressionKind::ExplicitMap(collection) => {
            let args = collection.call_args.inner().to_seq().into_iter().cloned().collect();
            check_operator(input, None, args, expected, false)?
        }
        PExpressionKind::Maplet { key, value, .. } => check_operator(input, None, vec![key, value], expected, false)?,
        PExpressionKind::RangeSeq { low, high, .. } => {
            check_operator(input, None, vec![low, high], expected, false)?
        }
        PExpressionKind::Lookup { base, index, .. } => {
            check_operator(input, None, vec![base, index], expected, false)?
        }
        PExpressionKind::SeqSlice {
            seq, start, end, ..
        } => check_operator(
            input,
            None,
            std::iter::once(seq).chain(start).chain(end).collect(),
            expected,
            false,
        )?,
        PExpressionKind::Update {
            base, key, value, ..
        } => check_operator(input, None, vec![base, key, value], expected, false)?,
        PExpressionKind::Size { seq, .. } => {
            check_operator(input, None, vec![seq], expected, false)?
        }
        PExpressionKind::Extension(extension)
            if extension
                .as_any()
                .is::<crate::plugin::standard::arp::arppast_extension::PRdPerm>() =>
        {
            (expression.typ, vec![PTypeSubstitution::default()])
        }
        PExpressionKind::Extension(extension)
            if extension
                .as_any()
                .is::<crate::plugin::sif::sifp_ast_extensions::PSifExpression>() =>
        {
            let sif = extension
                .as_any()
                .downcast_ref::<crate::plugin::sif::sifp_ast_extensions::PSifExpression>()
                .expect("checked SIF type");
            check_sif_extension(input, sif, None, &mut |_, _| {})?;
            let state = input.node().read().expect("poisoned parse node");
            let PNodeKind::Expression(expression) = &state.kind else {
                unreachable!()
            };
            (
                expression.typ.clone(),
                sif.type_substitutions()
                    .ok_or(TypeCheckError::Unsupported("SIF substitutions"))?,
            )
        }
        PExpressionKind::Extension(extension) if extension.as_any().is::<crate::plugin::standard::termination::termination_past_extension::PDecreasesClause>() => {
            let clause = extension.as_any().downcast_ref::<crate::plugin::standard::termination::termination_past_extension::PDecreasesClause>().expect("checked clause");
            clause.typecheck(|exp, expected| check_top_expression(exp, expected, |_, _| {}).map(|_| ()))?;
            (type_from_signature(&super::parse_ast_keyword::SignatureType::Bool), vec![PTypeSubstitution::default()])
        }
        PExpressionKind::Extension(extension) => {
            if let Some(instance) = extension.as_any().downcast_ref::<crate::plugin::standard::predicateinstance::predicate_instance_past_extension::PPredicateInstance>() {
                if let Some(message) = instance.check_as_predicate_call(input)? {
                    return Err(TypeCheckError::AmbiguousIdentifier(message));
                }
                let state = input.node().read().expect("poisoned parse node");
                let PNodeKind::Expression(expression) = &state.kind else { unreachable!() };
                (expression.typ.clone(), expression.type_substitutions.clone().ok_or(TypeCheckError::Unsupported("predicate instance substitutions"))?)
            } else {
                extension.typecheck_expression(input, expected, &mut |child, expected| check_expression(child, expected))?
            }
        }
        PExpressionKind::ForPerm { vars, trigger, body, .. } => {
            for var in vars.to_seq() {
                let typ = match &var.node().read().expect("poisoned parse node").kind { PNodeKind::Declaration(d) => d.typ.clone(), _ => return Err(TypeCheckError::Unsupported("forperm variable")) };
                check_supported_type(&typ)?;
            }
            let boolean = type_from_signature(&super::parse_ast_keyword::SignatureType::Bool);
            check_expression_context(&body, false, true, false)?;
            check_top_expression(&body, Some(&boolean), |_, _| {})?;
            let access = trigger.access().inner();
            check_top_expression(access, None, |_, _| {})?;
            ensure_location_access(access, true)?;
            let substitutions = body.type_subs_distinct().ok_or(TypeCheckError::Unsupported("forperm substitutions"))?;
            (boolean, substitutions)
        }
        PExpressionKind::Forall(q) | PExpressionKind::Exists(q) => {
            use super::parse_ast_keyword::SignatureType;
            for var in q.vars.to_seq() {
                let typ = match &var.node().read().expect("poisoned parse node").kind {
                    PNodeKind::Declaration(d) => d.typ.clone(),
                    _ => return Err(TypeCheckError::Unsupported("quantifier variable")),
                };
                check_supported_type(&typ)?;
            }
            let expected_body =
                if matches!(q.keyword.value(), super::parse_ast_keyword::PKw::Forall) {
                    type_from_signature(&SignatureType::Impure)
                } else {
                    type_from_signature(&SignatureType::Bool)
                };
            // Source `check` is a top-typed check: infer first, then constrain and
            // ground the selected substitution. Passing the expected type into the
            // operator inference directly can widen a pure Bool body to Impure.
            let body_type = check_top_expression(&q.body, Some(&expected_body), |_, _| {})?;
            for trigger in q.triggers {
                for exp in trigger.expressions().inner().to_seq() {
                    check_top_expression(exp, None, |_, _| {})?;
                }
            }
            let substitutions = q
                .body
                .type_subs_distinct()
                .ok_or(TypeCheckError::Unsupported("quantifier substitution state"))?;
            (body_type, substitutions)
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
fn ensure_location_access(expression: &PExpHandle, allow_wand: bool) -> Result<(), TypeCheckError> {
    let kind = match &expression.node().read().expect("poisoned parse node").kind {
        PNodeKind::Expression(e) => e.kind.clone(),
        _ => return Err(TypeCheckError::Unsupported("resource expression")),
    };
    match kind {
        PExpressionKind::FieldAccess { .. } => Ok(()),
        PExpressionKind::MagicWandExp { .. } if allow_wand => Ok(()),
        PExpressionKind::Call { idnref, .. } => {
            let declarations = super::parse_ast::PIdnRef::decls(&idnref, |_| true);
            if declarations.len() == 1
                && matches!(&declarations[0].read().expect("poisoned parse node").kind, PNodeKind::Member(member) if matches!(member.kind, PMemberKind::Predicate { .. }))
            {
                Ok(())
            } else if !allow_wand {
                Err(TypeCheckError::Positioned {
                    node: expression.node().clone(),
                    message: "specified location is not a field nor a predicate",
                })
            } else {
                Err(TypeCheckError::Unsupported("resource is not a predicate"))
            }
        }
        _ => Err(TypeCheckError::Unsupported("resource access")),
    }
}
/// Source fold/unfold accepts predicate calls or `acc` around a predicate call,
/// and rejects abstract predicates before ordinary expression typechecking.
fn check_new_fields(expression: &PExpHandle) -> Result<bool, TypeCheckError> {
    let kind = match &expression.node().read().expect("poisoned parse node").kind {
        PNodeKind::Expression(e) => e.kind.clone(),
        _ => return Err(TypeCheckError::Unsupported("allocation expression")),
    };
    let PExpressionKind::NewExp { fields, .. } = kind else {
        return Ok(false);
    };
    let mut errors = Vec::new();
    if let super::parse_ast::PNewFields::Fields(fields) = fields.inner() {
        for reference in fields.to_seq() {
            let declarations = super::parse_ast::PIdnRef::decls(reference, |_| true);
            if declarations.len() != 1 {
                let name = match &reference.read().expect("poisoned parse node").kind {
                    PNodeKind::IdnRef(id) => id.name.clone(),
                    _ => return Err(TypeCheckError::Unsupported("allocation field identifier")),
                };
                let message = if declarations.is_empty() {
                    format!("undeclared field `{name}`")
                } else {
                    format!("ambiguous field `{name}`")
                };
                errors.push(TypeCheckError::PositionedMessage {
                    node: reference.clone(),
                    message,
                });
            }
        }
    }
    if !errors.is_empty() {
        return Err(TypeCheckError::Mismatches(errors));
    }
    Ok(true)
}

/// Collect source-positioned abstract-predicate fold/unfold diagnostics after name resolution.
/// This is used when core checking stops at the first such error; unrelated earlier
/// typechecking errors still follow the existing checker path.
pub fn abstract_predicate_access_messages(
    program: &super::parse_ast::PProgramHandle,
) -> Result<super::fast_message::Messages, TypeCheckError> {
    fn walk(
        node: &PNodeHandle,
        out: &mut super::fast_message::Messages,
    ) -> Result<(), TypeCheckError> {
        let kind = node.read().expect("poisoned parse node").kind.clone();
        let access = match kind {
            PNodeKind::Statement(statement) => match statement.kind {
                super::parse_ast::PStatementKind::Fold { exp, .. } => {
                    Some((exp, "abstract predicates cannot be folded"))
                }
                super::parse_ast::PStatementKind::Unfold { exp, .. } => {
                    Some((exp, "abstract predicates cannot be unfolded"))
                }
                _ => None,
            },
            PNodeKind::Expression(expression) => match expression.kind {
                PExpressionKind::Unfolding { acc, .. } => {
                    Some((acc, "abstract predicates cannot be unfolded"))
                }
                _ => None,
            },
            _ => None,
        };
        if let Some((expression, text)) = access {
            let kind = match &expression.node().read().expect("poisoned parse node").kind {
                PNodeKind::Expression(e) => e.kind.clone(),
                _ => return Err(TypeCheckError::Unsupported("predicate access expression")),
            };
            let location = match kind {
                PExpressionKind::AccPred { amount, .. } => Some(amount.inner().first().clone()),
                PExpressionKind::Call { .. } => Some(expression),
                _ => None,
            };
            if let Some(location) = location {
                let kind = match &location.node().read().expect("poisoned parse node").kind {
                    PNodeKind::Expression(e) => e.kind.clone(),
                    _ => return Err(TypeCheckError::Unsupported("predicate access expression")),
                };
                if let PExpressionKind::Call { idnref, .. } = kind {
                    let declarations = super::parse_ast::PIdnRef::decls(
                        &idnref,
                        |decl| matches!(&decl.read().expect("poisoned parse node").kind, PNodeKind::Member(member) if matches!(member.kind, PMemberKind::Predicate { .. })),
                    );
                    if declarations.len() == 1
                        && matches!(&declarations[0].read().expect("poisoned parse node").kind, PNodeKind::Member(member) if matches!(&member.kind, PMemberKind::Predicate { body: None, .. }))
                    {
                        out.extend(
                            super::fast_message::message_for_node(&idnref, text, true, true)
                                .map_err(|_| {
                                    TypeCheckError::Unsupported("predicate diagnostic position")
                                })?,
                        );
                    }
                }
            }
        }
        for child in subnodes(node)
            .map_err(|_| TypeCheckError::Unsupported("predicate diagnostic traversal"))?
        {
            walk(&child, out)?;
        }
        Ok(())
    }
    let mut out = Vec::new();
    walk(program.node(), &mut out)?;
    Ok(super::fast_message::sortmessages(out))
}

fn ensure_nonabstract_predicate_access(
    expression: &PExpHandle,
    fold: bool,
) -> Result<(), TypeCheckError> {
    let kind = match &expression.node().read().expect("poisoned parse node").kind {
        PNodeKind::Expression(e) => e.kind.clone(),
        _ => return Err(TypeCheckError::Unsupported("predicate access expression")),
    };
    let location = match kind {
        PExpressionKind::AccPred { amount, .. } => amount.inner().first().clone(),
        PExpressionKind::Call { .. } => expression.clone(),
        _ => return Err(TypeCheckError::Unsupported("expected predicate access")),
    };
    let kind = match &location.node().read().expect("poisoned parse node").kind {
        PNodeKind::Expression(e) => e.kind.clone(),
        _ => return Err(TypeCheckError::Unsupported("predicate access expression")),
    };
    let PExpressionKind::Call { idnref, .. } = kind else {
        return Err(TypeCheckError::Unsupported("expected predicate access"));
    };
    let predicates = super::parse_ast::PIdnRef::decls(
        &idnref,
        |node| matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Member(member) if matches!(member.kind, PMemberKind::Predicate { .. })),
    );
    if predicates.len() != 1 {
        return Err(TypeCheckError::Unsupported(
            "undefined or ambiguous predicate access",
        ));
    }
    super::parse_ast::PIdnRef::filter_decls(
        &idnref,
        std::sync::Arc::new(
            |node| matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Member(member) if matches!(member.kind, PMemberKind::Predicate { .. })),
        ),
        |_| true,
    );
    let has_body = matches!(&predicates[0].read().expect("poisoned parse node").kind, PNodeKind::Member(member) if matches!(&member.kind, PMemberKind::Predicate { body: Some(_), .. }));
    if !has_body {
        return Err(TypeCheckError::Unsupported(if fold {
            "abstract predicates cannot be folded"
        } else {
            "abstract predicates cannot be unfolded"
        }));
    }
    Ok(())
}

fn check_operator(
    input: &PExpHandle,
    signatures: Option<Vec<PTypeSubstitution>>,
    arguments: Vec<PExpHandle>,
    expected: Option<&PTypeHandle>,
    require_pure: bool,
) -> Result<(PTypeHandle, Vec<PTypeSubstitution>), TypeCheckError> {
    let mut argument_types = Vec::new();
    let mut mismatches = Vec::new();
    for argument in &arguments {
        let typ = match check_expression(argument, None) {
            Ok(typ) => typ,
            Err(TypeCheckError::Unification(error @ UnificationError::Mismatch { .. })) => {
                mismatches.push(TypeCheckError::Unification(error));
                continue;
            }
            Err(error @ TypeCheckError::Incompatible { .. }) => {
                mismatches.push(error);
                continue;
            }
            Err(error @ TypeCheckError::UnresolvedValue { .. })
            | Err(error @ TypeCheckError::PositionedMessage { .. })
            | Err(error @ TypeCheckError::Positioned { .. }) => {
                mismatches.push(error);
                continue;
            }
            Err(TypeCheckError::Mismatches(errors)) => {
                mismatches.extend(errors);
                continue;
            }
            Err(error) => {
                if mismatches.is_empty() {
                    return Err(error);
                }
                mismatches.push(error);
                return Err(TypeCheckError::Mismatches(mismatches));
            }
        };
        if require_pure && !typ.is_pure() {
            let error = TypeCheckError::Unsupported("impure equality argument");
            if mismatches.is_empty() {
                return Err(error);
            }
            mismatches.push(error);
            return Err(TypeCheckError::Mismatches(mismatches));
        }
        argument_types.push(typ);
    }
    if !mismatches.is_empty() {
        return Err(TypeCheckError::Mismatches(mismatches));
    }
    let signatures = match signatures {
        Some(signatures) => signatures,
        None => input
            .signatures()
            .map_err(|_| TypeCheckError::Unsupported("operator signatures"))?,
    };
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
    if let PNodeKind::Expression(expression) =
        &mut input.node().write().expect("poisoned parse node").kind
    {
        let domain = match &mut expression.kind {
            PExpressionKind::Call {
                domain_type_renaming,
                ..
            } => domain_type_renaming.as_mut(),
            PExpressionKind::FieldAccess {
                adt_type_renaming, ..
            } => adt_type_renaming.as_mut(),
            _ => None,
        };
        if let Some(domain) = domain {
            for fresh in domain.mappings.values_mut() {
                *fresh = renaming.rename(fresh).to_owned();
            }
        }
    }
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
    fn empty_sif_event_substitution(expression: &PExpHandle) -> bool {
        use crate::plugin::sif::sifp_ast_extensions::{PSifExpression, PSifKind};
        let kind = expression
            .node()
            .read()
            .expect("poisoned parse node")
            .kind
            .clone();
        match kind {
            PNodeKind::Expression(super::parse_ast::PExpression {
                kind: PExpressionKind::Extension(extension),
                ..
            }) => {
                match extension
                    .as_any()
                    .downcast_ref::<PSifExpression>()
                    .map(|sif| &sif.kind)
                {
                    Some(PSifKind::LowEvent) => true,
                    Some(PSifKind::Low(child) | PSifKind::Rel { exp: child, .. }) => {
                        empty_sif_event_substitution(child)
                    }
                    None => false,
                }
            }
            PNodeKind::Expression(super::parse_ast::PExpression {
                kind: PExpressionKind::AnnotatedExp { expression, .. },
                ..
            }) => empty_sif_event_substitution(&expression),
            _ => false,
        }
    }
    let mut constraints = Vec::new();
    for (index, (expression, actual)) in arguments.iter().zip(argument_types).enumerate() {
        let mut substitutions = expression
            .type_subs_distinct()
            .ok_or(TypeCheckError::Unsupported("binder substitution state"))?;
        // Scala's lowEvent reports an empty substitution list and consequently skips
        // enclosing operator unification. At this boundary only, use the concrete
        // Bool identity candidate so native inference can still validate the operator.
        if substitutions.is_empty() && empty_sif_event_substitution(expression) {
            substitutions.push(PTypeSubstitution::default());
        }
        constraints.push(UnificationArgument {
            actual,
            expected: p_type_var(renaming.rename(&format!("#T{index}"))),
            substitutions,
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

#[cfg(test)]
mod call_tests {
    use super::*;
    use crate::parser::fast_parser::parse_program;
    use crate::parser::parse_ast_keyword::SignatureType;
    #[test]
    fn resolves_and_types_function_call_in_a_method_assertion() {
        let program = parse_program(
            "function f(x: Int): Int { x + 1 } method m(y: Int) { assert f(y) > 0; }",
            "test.vpr",
        )
        .unwrap();
        let mut names = NameAnalyser::default();
        assert!(names.run(program.node()).unwrap());
        fn find_assert(node: &PNodeHandle) -> Option<PExpHandle> {
            if let PNodeKind::Statement(statement) = &node.read().unwrap().kind {
                if let PStatementKind::Assert { exp, .. } = &statement.kind {
                    return Some(exp.clone());
                }
            }
            subnodes(node)
                .unwrap()
                .into_iter()
                .find_map(|child| find_assert(&child))
        }
        let assertion = find_assert(program.node()).unwrap();
        let typ =
            check_expression(&assertion, Some(&type_from_signature(&SignatureType::Bool))).unwrap();
        assert!(typ.structurally_equals(&type_from_signature(&SignatureType::Bool)));
    }
}

fn check_sif_extension(
    input: &PExpHandle,
    sif: &crate::plugin::sif::sifp_ast_extensions::PSifExpression,
    expected: Option<&PTypeHandle>,
    warn: &mut dyn FnMut(&PNodeHandle, &str),
) -> Result<PTypeHandle, TypeCheckError> {
    use crate::plugin::sif::sifp_ast_extensions::SifTypeError;
    let error = sif.typecheck(input, expected, |exp, typ| {
        check_top_expression(exp, typ, &mut *warn).map(|_| ())
    })?;
    match error {
        None => match &input.node().read().expect("poisoned parse node").kind {
            PNodeKind::Expression(e) => Ok(e.typ.clone()),
            _ => Err(TypeCheckError::Unsupported("SIF expression node")),
        },
        Some(SifTypeError::Expected { expected, actual }) => Err(TypeCheckError::Incompatible {
            expression: input.node().clone(),
            expected,
            actual,
        }),
        Some(SifTypeError::InvalidRelIndex(index)) => {
            Err(TypeCheckError::InvalidSifRelIndex(index))
        }
        Some(SifTypeError::NonLiteralRelIndex) => {
            Err(TypeCheckError::Unsupported("SIF rel literal index"))
        }
    }
}

/// Resolve a top-level expression's overloads, select the first surviving substitution,
/// ground remaining free type variables to Int and propagate the substitution down the tree.
/// The callback receives the source warning for each defaulted type variable.
pub fn check_top_expression(
    input: &PExpHandle,
    expected: Option<&PTypeHandle>,
    mut warn: impl FnMut(&PNodeHandle, &str),
) -> Result<PTypeHandle, TypeCheckError> {
    let extension = match &input.node().read().expect("poisoned parse node").kind {
        PNodeKind::Expression(e) => match &e.kind {
            PExpressionKind::Extension(extension) => Some(extension.clone()),
            _ => None,
        },
        _ => None,
    };
    if let Some(extension) = extension {
        if let Some(sif) = extension
            .as_any()
            .downcast_ref::<crate::plugin::sif::sifp_ast_extensions::PSifExpression>()
        {
            return check_sif_extension(input, sif, expected, &mut warn);
        }
    }
    let actual = check_expression(input, None)?;
    let candidates = input
        .type_subs_distinct()
        .ok_or(TypeCheckError::Unsupported("expression substitutions"))?;
    let candidates = if let Some(expected) = expected {
        candidates
            .into_iter()
            .filter_map(|s| s.add(&actual, expected).ok())
            .collect::<Vec<_>>()
    } else {
        candidates
    };
    let Some(mut chosen) = candidates.into_iter().next() else {
        return match expected {
            Some(expected) => Err(TypeCheckError::Incompatible {
                expression: input.node().clone(),
                actual,
                expected: expected.clone(),
            }),
            None => Err(TypeCheckError::Unsupported("no type substitution")),
        };
    };
    let keys = chosen.key_set();
    let mut free = std::collections::HashSet::new();
    for (_, value) in chosen.iter() {
        free.extend(
            value
                .free_type_variables()
                .into_iter()
                .filter(|key| !keys.contains(key)),
        );
    }
    for variable in free {
        warn(
            input.node(),
            "unconstrained type parameter, substituting default type Int",
        );
        chosen = chosen
            .add(
                &p_type_var(variable),
                &type_from_signature(&super::parse_ast_keyword::SignatureType::Int),
            )
            .map_err(|_| TypeCheckError::Unsupported("default type substitution"))?;
    }
    input
        .force_substitution(&chosen)
        .map_err(|_| TypeCheckError::Unsupported("extension substitution"))?;
    let grounded = match &input.node().read().expect("poisoned parse node").kind {
        PNodeKind::Expression(expression) => expression.typ.clone(),
        _ => return Err(TypeCheckError::Unsupported("not an expression")),
    };
    if expected.is_some_and(|e| !is_subtype(&grounded, e)) {
        return Err(TypeCheckError::Incompatible {
            expression: input.node().clone(),
            actual: grounded,
            expected: expected.expect("checked expected").clone(),
        });
    }
    Ok(grounded)
}

#[cfg(test)]
mod ground_tests {
    use super::*;
    use crate::parser::fast_parser::parse_expression;
    use crate::parser::parse_ast_keyword::SignatureType;
    #[test]
    fn ground_selects_expected_division_overload() {
        for expected in [SignatureType::Int, SignatureType::Perm] {
            let expression = parse_expression("1 / 2", "test.vpr").unwrap().expression;
            let expected = type_from_signature(&expected);
            let got = check_top_expression(&expression, Some(&expected), |_, _| {}).unwrap();
            assert!(got.structurally_equals(&expected));
        }
    }
}

fn check_supported_type(typ: &PTypeHandle) -> Result<(), TypeCheckError> {
    let kind = match &typ.node().read().expect("poisoned parse node").kind {
        PNodeKind::Type(kind) => kind.clone(),
        _ => return Err(TypeCheckError::Unsupported("type node")),
    };
    match kind {
        super::parse_ast::PTypeKind::Primitive { .. }
        | super::parse_ast::PTypeKind::ExtensionPrimitive { .. } => Ok(()),
        super::parse_ast::PTypeKind::Seq { element_type, .. }
        | super::parse_ast::PTypeKind::Set { element_type, .. }
        | super::parse_ast::PTypeKind::Multiset { element_type, .. } => {
            check_supported_type(element_type.inner())
        }
        super::parse_ast::PTypeKind::Map { types, .. } => {
            check_supported_type(types.inner().first())?;
            check_supported_type(types.inner().second())
        }
        super::parse_ast::PTypeKind::Domain { domain, args, kind } => {
            use super::parse_ast::{PDomainTypeKind, PIdnRef};
            let declarations = PIdnRef::decls(&domain, |node| {
                if kind == PDomainTypeKind::Adt {
                    matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Member(PMember { kind: PMemberKind::Extension(extension), .. }) if extension.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdt>())
                } else {
                    matches!(
                        &node.read().expect("poisoned parse node").kind,
                        PNodeKind::TypeVarDecl { .. }
                            | PNodeKind::Member(PMember {
                                kind: PMemberKind::Domain { .. },
                                ..
                            })
                    )
                }
            });
            if declarations.len() != 1 {
                return Err(TypeCheckError::Unsupported(
                    "ambiguous or undeclared domain type",
                ));
            }
            let arguments = args
                .as_ref()
                .map(|a| a.inner().to_seq())
                .unwrap_or_default();
            for arg in &arguments {
                check_supported_type(arg)?;
            }
            let (resolved, arity) = match &declarations[0].read().expect("poisoned parse node").kind
            {
                PNodeKind::TypeVarDecl { .. } => (PDomainTypeKind::TypeVar, 0),
                PNodeKind::Member(PMember {
                    kind: PMemberKind::Domain { type_vars, .. },
                    ..
                }) => (
                    PDomainTypeKind::Domain,
                    type_vars.as_ref().map_or(0, |v| v.inner().len()),
                ),
                PNodeKind::Member(PMember {
                    kind: PMemberKind::Extension(extension),
                    ..
                }) => {
                    let adt = extension
                        .as_any()
                        .downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdt>()
                        .ok_or(TypeCheckError::Unsupported("ADT declaration"))?;
                    if adt.type_vars_present != args.is_some() {
                        return Err(TypeCheckError::Unsupported("ADT type argument list"));
                    }
                    (PDomainTypeKind::Adt, adt.type_vars.len())
                }
                _ => unreachable!(),
            };
            if arity != arguments.len() {
                return Err(TypeCheckError::Unsupported("domain type argument count"));
            }
            if let PNodeKind::Type(super::parse_ast::PTypeKind::Domain { kind, .. }) =
                &mut typ.node().write().expect("poisoned parse node").kind
            {
                *kind = resolved;
            }
            Ok(())
        }
        _ => Err(TypeCheckError::Unsupported(
            "domain, macro or internal declaration type",
        )),
    }
}
fn check_declarations(declarations: &super::parse_ast::PFormalArgs) -> Result<(), TypeCheckError> {
    for declaration in declarations.inner().to_seq() {
        let typ = match &declaration.node().read().expect("poisoned parse node").kind {
            PNodeKind::Declaration(d) => d.typ.clone(),
            _ => return Err(TypeCheckError::Unsupported("formal declaration")),
        };
        check_supported_type(&typ)?;
    }
    Ok(())
}
/// Bind result literals to the enclosing function's declared return type.
fn bind_function_results(node: &PNodeHandle, typ: &PTypeHandle) -> Result<(), TypeCheckError> {
    {
        let mut node = node.write().expect("poisoned parse node");
        if let PNodeKind::Expression(expression) = &mut node.kind {
            if matches!(expression.kind, PExpressionKind::ResultLit(_)) {
                expression.typ = typ.clone();
            }
        }
    }
    for child in
        subnodes(node).map_err(|_| TypeCheckError::Unsupported("result expression traversal"))?
    {
        bind_function_results(&child, typ)?;
    }
    Ok(())
}
fn check_program_expression(
    input: &PExpHandle,
    expected: Option<&PTypeHandle>,
    warn: &mut impl FnMut(&PNodeHandle, &str),
) -> Result<PTypeHandle, TypeCheckError> {
    check_top_expression(input, expected, warn)
}
/// Source restrictions on permissions in specifications and wands in function
/// preconditions/predicate bodies. Inhale-exhale nodes shield their children only
/// for the specification permission check, not for the separate wand check.
fn check_expression_context(
    input: &PExpHandle,
    forbid_spec_perm: bool,
    ban_all_perm: bool,
    forbid_wand: bool,
) -> Result<(), TypeCheckError> {
    fn visit(
        node: &PNodeHandle,
        inside_inex: bool,
        forbid_spec_perm: bool,
        ban_all_perm: bool,
        forbid_wand: bool,
        errors: &mut Vec<TypeCheckError>,
    ) -> Result<(), TypeCheckError> {
        let kind = node.read().expect("poisoned parse node").kind.clone();
        let mut inside_inex = inside_inex;
        let mut forbid_wand = forbid_wand;
        if let PNodeKind::Expression(expression) = kind {
            match expression.kind {
                PExpressionKind::CurrentPerm { .. } => {
                    if ban_all_perm {
                        errors.push(TypeCheckError::Positioned { node: node.clone(), message: if forbid_spec_perm { "function postconditions are not allowed to contain `perm` expressions" } else { "forperm quantifier bodies are not allowed to contain `perm` expressions" } });
                    }
                    if forbid_spec_perm && !inside_inex {
                        errors.push(TypeCheckError::Positioned { node: node.clone(), message: "preconditions, postconditions and invariants may only contain `perm` and `forperm` expressions inside of an inhale-exhale" });
                    }
                    return Ok(());
                }
                PExpressionKind::ForPerm { trigger, body, .. } => {
                    if ban_all_perm {
                        errors.push(TypeCheckError::Positioned { node: node.clone(), message: if forbid_spec_perm { "function postconditions are not allowed to contain `forperm` expressions" } else { "forperm quantifier bodies are not allowed to contain `forperm` expressions" } });
                        if !forbid_spec_perm {
                            visit(body.node(), inside_inex, false, true, forbid_wand, errors)?;
                            visit(
                                trigger.node(),
                                inside_inex,
                                false,
                                ban_all_perm,
                                forbid_wand,
                                errors,
                            )?;
                        }
                        return Ok(());
                    } else if forbid_spec_perm && !inside_inex {
                        errors.push(TypeCheckError::Positioned { node: node.clone(), message: "preconditions, postconditions and invariants may only contain `perm` and `forperm` expressions inside of an inhale-exhale" });
                        return Ok(());
                    }
                    visit(
                        body.node(),
                        inside_inex,
                        forbid_spec_perm,
                        true,
                        forbid_wand,
                        errors,
                    )?;
                    visit(
                        trigger.node(),
                        inside_inex,
                        forbid_spec_perm,
                        ban_all_perm,
                        forbid_wand,
                        errors,
                    )?;
                    return Ok(());
                }
                PExpressionKind::MagicWandExp { .. } if forbid_wand => {
                    errors.push(TypeCheckError::Positioned {
                        node: node.clone(),
                        message: "magic wands are not supported in function preconditions or predicates",
                    });
                    forbid_wand = false;
                }
                PExpressionKind::InhaleExhale { .. } => inside_inex = true,
                _ => {}
            }
        }
        for child in subnodes(node)
            .map_err(|_| TypeCheckError::Unsupported("expression context traversal"))?
        {
            visit(
                &child,
                inside_inex,
                forbid_spec_perm,
                ban_all_perm,
                forbid_wand,
                errors,
            )?;
        }
        Ok(())
    }
    let mut errors = Vec::new();
    visit(
        input.node(),
        false,
        forbid_spec_perm,
        ban_all_perm,
        forbid_wand,
        &mut errors,
    )?;
    if errors.is_empty() {
        Ok(())
    } else {
        Err(TypeCheckError::Mismatches(errors))
    }
}
/// Check core program signatures before bodies, as upstream requires. The first unsupported
/// or erroneous construct is returned; full diagnostic accumulation and extensions remain pending.
pub fn check_program_core(
    program: &super::parse_ast::PProgramHandle,
    warn: &mut impl FnMut(&PNodeHandle, &str),
) -> Result<(), TypeCheckError> {
    let members = program.all_members();
    fn global_names(
        node: &PNodeHandle,
        names: &mut std::collections::HashSet<String>,
    ) -> Result<(), TypeCheckError> {
        let kind = node.read().expect("poisoned parse node").kind.clone();
        let global = matches!(
            &kind,
            PNodeKind::Member(PMember {
                kind: PMemberKind::Domain { .. }
                    | PMemberKind::Function { .. }
                    | PMemberKind::Predicate { .. }
                    | PMemberKind::Method { .. },
                ..
            }) | PNodeKind::Declaration(super::parse_ast::PDeclaration {
                kind: PDeclarationKind::Field { .. } | PDeclarationKind::AdtField,
                ..
            }) | PNodeKind::DomainMember(super::parse_ast::PDomainMember::Function { .. })
        ) || matches!(&kind, PNodeKind::Member(PMember { kind: PMemberKind::Extension(ext), .. }) if ext.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdt>())
            || matches!(&kind, PNodeKind::Extension(ext) if ext.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>());
        if global {
            if let Some(id) = declaration_identifier(node) {
                names.insert(definition_name(&id));
            }
        }
        for child in subnodes(node)
            .map_err(|_| TypeCheckError::Unsupported("global declaration traversal"))?
        {
            global_names(&child, names)?;
        }
        Ok(())
    }
    let mut globals = std::collections::HashSet::new();
    if members.iter().any(|node| matches!(&node.node().read().expect("poisoned parse node").kind, PNodeKind::Member(PMember { kind: PMemberKind::Extension(ext), .. }) if ext.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdt>())) { global_names(program.node(), &mut globals)?; }
    for handle in &members {
        let member = match &handle.node().read().expect("poisoned parse node").kind {
            PNodeKind::Member(member) => member.clone(),
            _ => return Err(TypeCheckError::Unsupported("program member")),
        };
        match member.kind {
            PMemberKind::Import { .. } | PMemberKind::Define { .. } => {}
            PMemberKind::Extension(extension)
                if extension
                    .as_any()
                    .is::<crate::plugin::standard::adt::adt_past_extension::PAdt>() =>
            {
                let adt = extension
                    .as_any()
                    .downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdt>()
                    .expect("checked ADT");
                adt.validate_derivations()
                    .map_err(|_| TypeCheckError::Unsupported("invalid ADT derivation"))?;
                for node in &adt.constructors {
                    let constructor = match &node.read().expect("poisoned parse node").kind {
                        PNodeKind::Extension(extension) => extension.as_any().downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>().cloned().ok_or(TypeCheckError::Unsupported("ADT constructor"))?,
                        _ => return Err(TypeCheckError::Unsupported("ADT constructor")),
                    };
                    if globals.contains(&format!("is{}", definition_name(&constructor.idndef))) {
                        return Err(TypeCheckError::Unsupported(
                            "ADT discriminator name is shadowed",
                        ));
                    }
                    check_declarations(&constructor.args)?;
                }
                for node in &adt.deriving {
                    let info = match &node.read().expect("poisoned parse node").kind {
                        PNodeKind::Extension(extension) => extension.as_any().downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdtDerivingInfo>().cloned().ok_or(TypeCheckError::Unsupported("ADT derivation"))?,
                        _ => return Err(TypeCheckError::Unsupported("ADT derivation")),
                    };
                    if let Some(typ) = &info.parameter {
                        check_supported_type(typ)?;
                    }
                    let fields: Vec<_> = adt.constructors.iter().flat_map(|node| {
                        match &node.read().expect("poisoned parse node").kind {
                            PNodeKind::Extension(ext) => ext.as_any().downcast_ref::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>().map(|c| c.formal_args().into_iter().map(|a| a.node().clone()).collect::<Vec<_>>()).unwrap_or_default(),
                            _ => Vec::new(),
                        }
                    }).collect();
                    info.validate_fields(|reference| {
                        super::parse_ast::PIdnRef::decls(reference, |decl| {
                            fields.iter().any(|f| std::sync::Arc::ptr_eq(f, decl))
                        })
                        .len()
                    })
                    .map_err(|_| TypeCheckError::Unsupported("ADT derivation field"))?;
                }
            }
            PMemberKind::Domain { members, .. } => {
                for member in members.inner().to_seq() {
                    let kind = member
                        .node()
                        .read()
                        .expect("poisoned parse node")
                        .kind
                        .clone();
                    if let PNodeKind::DomainMember(super::parse_ast::PDomainMember::Function {
                        args,
                        result_type,
                        ..
                    }) = kind
                    {
                        for arg in args.inner().to_seq() {
                            check_supported_type(arg.typ())?;
                        }
                        check_supported_type(&result_type)?;
                    }
                }
            }
            PMemberKind::Fields { fields, .. } => {
                for field in fields.to_seq() {
                    field.set_field_owner(handle);
                    let typ = match &field.node().read().expect("poisoned parse node").kind {
                        PNodeKind::Declaration(d) => d.typ.clone(),
                        _ => return Err(TypeCheckError::Unsupported("field declaration")),
                    };
                    check_supported_type(&typ)?;
                }
            }
            PMemberKind::Function {
                args, result_type, ..
            } => {
                check_declarations(&args)?;
                check_supported_type(&result_type)?;
            }
            PMemberKind::Predicate { args, .. } => check_declarations(&args)?,
            PMemberKind::Method { args, returns, .. } => {
                check_declarations(&args)?;
                if let Some(returns) = returns {
                    check_declarations(returns.formal_returns())?;
                }
            }
            _ => return Err(TypeCheckError::Unsupported("program signature")),
        }
    }
    let impure = type_from_signature(&super::parse_ast_keyword::SignatureType::Impure);
    let boolean = type_from_signature(&super::parse_ast_keyword::SignatureType::Bool);
    let mut errors = Vec::new();
    for handle in &members {
        let checked = (|| -> Result<(), TypeCheckError> {
            let member = match &handle.node().read().expect("poisoned parse node").kind {
                PNodeKind::Member(member) => member.clone(),
                _ => return Err(TypeCheckError::Unsupported("program member")),
            };
            match member.kind {
                PMemberKind::Fields { .. }
                | PMemberKind::Import { .. }
                | PMemberKind::Define { .. } => {}
                PMemberKind::Extension(extension)
                    if extension
                        .as_any()
                        .is::<crate::plugin::standard::adt::adt_past_extension::PAdt>() => {}
                PMemberKind::Domain { members, .. } => {
                    let mut domain_errors = Vec::new();
                    for member in members.inner().to_seq() {
                        let axiom = match &member.node().read().expect("poisoned parse node").kind {
                            PNodeKind::DomainMember(super::parse_ast::PDomainMember::Axiom {
                                exp,
                                ..
                            }) => exp.clone(),
                            PNodeKind::DomainMember(
                                super::parse_ast::PDomainMember::Function { .. },
                            ) => continue,
                            _ => unreachable!(),
                        };
                        fn no_calls(
                            node: &PNodeHandle,
                            errors: &mut Vec<TypeCheckError>,
                        ) -> Result<(), TypeCheckError> {
                            let kind = node.read().expect("poisoned parse node").kind.clone();
                            if let PNodeKind::Expression(super::parse_ast::PExpression {
                                kind: PExpressionKind::Call { idnref, .. },
                                ..
                            }) = &kind
                            {
                                let candidates = super::parse_ast::PIdnRef::decls(idnref, |_| true);
                                if candidates.len() != 1 {
                                    return Err(TypeCheckError::Unsupported(
                                        "domain axiom call contextual rules",
                                    ));
                                }
                                let declaration =
                                    candidates[0].read().expect("poisoned parse node");
                                match &declaration.kind {
                                    PNodeKind::DomainMember(
                                        super::parse_ast::PDomainMember::Function { .. },
                                    ) => {}
                                    PNodeKind::Extension(extension) if extension.as_any().is::<crate::plugin::standard::adt::adt_past_extension::PAdtConstructor>() => {}
                                    PNodeKind::Member(super::parse_ast::PMember {
                                        kind: PMemberKind::Function { pres, .. },
                                        ..
                                    }) => {
                                        use super::parse_ast::PSpecificationKeyword;
                                        use super::parse_ast_keyword::PKw;
                                        if pres.specs().to_seq().iter().any(|spec| matches!(&spec.keyword,
                                        PSpecificationKeyword::Builtin(token) if *token.value() == PKw::Requires)) {
                                        let name = match &idnref.read().expect("poisoned parse node").kind {
                                            PNodeKind::IdnRef(reference) => reference.name.clone(),
                                            _ => return Err(TypeCheckError::Unsupported("call identifier")),
                                        };
                                        errors.push(TypeCheckError::FunctionPreconditionInDomainAxiom { name, identifier: idnref.clone() });
                                    }
                                    }
                                    _ => {
                                        return Err(TypeCheckError::Unsupported(
                                            "domain axiom call contextual rules",
                                        ));
                                    }
                                }
                            }
                            if let PNodeKind::Expression(super::parse_ast::PExpression {
                                kind: expression,
                                ..
                            }) = &kind
                            {
                                let unsupported = match expression {
                                    // The ADT plugin classifies destructors and discriminators
                                    // before resolution. These are pure ADT operations, not
                                    // heap field accesses, and must still be type-checked below.
                                    PExpressionKind::FieldAccess { idnref, .. } => !matches!(
                                        &idnref.read().expect("poisoned parse node").kind,
                                        PNodeKind::IdnRef(id)
                                            if matches!(id.declaration_class,
                                                super::parse_ast::PDeclarationClass::AdtField
                                                | super::parse_ast::PDeclarationClass::AdtConstructor)
                                    ),
                                    PExpressionKind::AccPred { .. }
                                    | PExpressionKind::Extension(_) => true,
                                    _ => false,
                                };
                                if unsupported {
                                    return Err(TypeCheckError::Unsupported(
                                        "domain axiom contextual expression",
                                    ));
                                }
                            }
                            for child in subnodes(node).map_err(|_| {
                                TypeCheckError::Unsupported("domain axiom traversal")
                            })? {
                                no_calls(&child, errors)?;
                            }
                            Ok(())
                        }
                        no_calls(axiom.exp().inner().node(), &mut domain_errors)?;
                        retain_type_mismatches(
                            &mut domain_errors,
                            check_program_expression(
                                axiom.exp().inner(),
                                Some(&boolean),
                                &mut *warn,
                            ),
                        )?;
                    }
                    if !domain_errors.is_empty() {
                        return Err(TypeCheckError::Mismatches(domain_errors));
                    }
                }
                PMemberKind::Function {
                    pres,
                    posts,
                    body,
                    result_type,
                    ..
                } => {
                    let mut member_errors = Vec::new();
                    for spec in pres.specs().to_seq() {
                        retain_type_mismatches(
                            &mut member_errors,
                            check_expression_context(spec.exp(), true, false, true),
                        )?;
                        retain_type_mismatches(
                            &mut member_errors,
                            check_program_expression(spec.exp(), Some(&impure), &mut *warn),
                        )?;
                    }
                    for spec in posts.specs().to_seq() {
                        retain_type_mismatches(
                            &mut member_errors,
                            check_expression_context(spec.exp(), true, true, false),
                        )?;
                        retain_type_mismatches(
                            &mut member_errors,
                            bind_function_results(spec.exp().node(), &result_type),
                        )?;
                        retain_type_mismatches(
                            &mut member_errors,
                            check_program_expression(spec.exp(), Some(&boolean), &mut *warn),
                        )?;
                    }
                    if let Some(body) = body {
                        // The source keeps resultAllowed set through body typechecking;
                        // the AST consistency check rejects result in a function body.
                        retain_type_mismatches(
                            &mut member_errors,
                            bind_function_results(body.exp().inner().node(), &result_type),
                        )?;
                        retain_type_mismatches(
                            &mut member_errors,
                            check_program_expression(
                                body.exp().inner(),
                                Some(&result_type),
                                &mut *warn,
                            ),
                        )?;
                    }
                    if !member_errors.is_empty() {
                        return Err(TypeCheckError::Mismatches(member_errors));
                    }
                }
                PMemberKind::Predicate { body, .. } => {
                    if let Some(body) = body {
                        let mut errors = Vec::new();
                        retain_type_mismatches(
                            &mut errors,
                            check_expression_context(body.exp().inner(), false, false, true),
                        )?;
                        retain_type_mismatches(
                            &mut errors,
                            check_program_expression(body.exp().inner(), Some(&impure), &mut *warn),
                        )?;
                        if !errors.is_empty() {
                            return Err(TypeCheckError::Mismatches(errors));
                        }
                    }
                }
                PMemberKind::Method {
                    pres, posts, body, ..
                } => {
                    let mut member_errors = Vec::new();
                    for spec in pres
                        .specs()
                        .to_seq()
                        .into_iter()
                        .chain(posts.specs().to_seq())
                    {
                        retain_type_mismatches(
                            &mut member_errors,
                            check_expression_context(spec.exp(), true, false, false),
                        )?;
                        retain_type_mismatches(
                            &mut member_errors,
                            check_program_expression(spec.exp(), Some(&impure), &mut *warn),
                        )?;
                    }
                    if let Some(body) = body {
                        retain_type_mismatches(
                            &mut member_errors,
                            check_statement_core(&body, &mut *warn),
                        )?;
                    }
                    if !member_errors.is_empty() {
                        return Err(TypeCheckError::Mismatches(member_errors));
                    }
                }
                _ => return Err(TypeCheckError::Unsupported("program body")),
            }
            Ok(())
        })();
        match checked {
            Ok(()) => {}
            Err(TypeCheckError::Unification(error @ UnificationError::Mismatch { .. })) => {
                errors.push(TypeCheckError::Unification(error))
            }
            Err(error @ TypeCheckError::UnresolvedValue { .. })
            | Err(error @ TypeCheckError::PositionedMessage { .. })
            | Err(error @ TypeCheckError::Incompatible { .. })
            | Err(error @ TypeCheckError::Positioned { .. }) => errors.push(error),
            Err(TypeCheckError::Mismatches(more)) => errors.extend(more),
            Err(error) => {
                if errors.is_empty() {
                    return Err(error);
                }
                errors.push(error);
                return Err(TypeCheckError::Mismatches(errors));
            }
        }
    }
    if !errors.is_empty() {
        return Err(TypeCheckError::Mismatches(errors));
    }
    Ok(())
}
/// Core statement checks; extensions, method calls and field updates remain explicit gaps.
pub fn check_statement_core(
    statement: &super::parse_ast::PStmtHandle,
    warn: &mut impl FnMut(&PNodeHandle, &str),
) -> Result<(), TypeCheckError> {
    use super::parse_ast::PStatementKind as S;
    use super::parse_ast_keyword::SignatureType;
    let kind = match &statement.node().read().expect("poisoned parse node").kind {
        PNodeKind::Statement(s) => s.kind.clone(),
        _ => return Err(TypeCheckError::Unsupported("statement node")),
    };
    let impure = type_from_signature(&SignatureType::Impure);
    let boolean = type_from_signature(&SignatureType::Bool);
    if let S::Assign { targets, rhs, .. } = &kind {
        let call = match &rhs.node().read().expect("poisoned parse node").kind {
            PNodeKind::Expression(e) => match &e.kind {
                PExpressionKind::Call {
                    idnref,
                    call_args,
                    type_annotated: None,
                    ..
                } => Some((idnref.clone(), call_args.clone())),
                _ => None,
            },
            _ => None,
        };
        if let Some((reference, call_args)) = call {
            let candidates = super::parse_ast::PIdnRef::decls(&reference, |_| true);
            let methods: Vec<_> = candidates
                .into_iter()
                .filter(|n| {
                    matches!(
                        &n.read().expect("poisoned parse node").kind,
                        PNodeKind::Member(PMember {
                            kind: PMemberKind::Method { .. },
                            ..
                        })
                    )
                })
                .collect();
            if !methods.is_empty() {
                if methods.len() != 1 {
                    return Err(TypeCheckError::Unsupported("ambiguous method call"));
                }
                let filter = std::sync::Arc::new(|n: &PNodeHandle| {
                    matches!(
                        &n.read().expect("poisoned parse node").kind,
                        PNodeKind::Member(PMember {
                            kind: PMemberKind::Method { .. },
                            ..
                        })
                    )
                });
                super::parse_ast::PIdnRef::filter_decls(&reference, filter, |_| true);
                let method = methods[0].read().expect("poisoned parse node").kind.clone();
                let PNodeKind::Member(PMember {
                    kind: PMemberKind::Method { args, returns, .. },
                    ..
                }) = method
                else {
                    unreachable!()
                };
                let inputs = call_args.inner().to_seq();
                let formals = args.inner().to_seq();
                let outputs = returns
                    .as_ref()
                    .map(|r| r.formal_returns().inner().to_seq())
                    .unwrap_or_default();
                let actual_targets = targets.to_seq();
                if inputs.len() != formals.len() {
                    return Err(TypeCheckError::Positioned {
                        node: rhs.node().clone(),
                        message: "wrong number of arguments",
                    });
                }
                if actual_targets.len() != outputs.len() {
                    return Err(TypeCheckError::Positioned {
                        node: statement.node().clone(),
                        message: "wrong number of targets",
                    });
                }
                for (actual, formal) in inputs.into_iter().zip(formals) {
                    let typ = match &formal.node().read().expect("poisoned parse node").kind {
                        PNodeKind::Declaration(d) => d.typ.clone(),
                        _ => return Err(TypeCheckError::Unsupported("method formal")),
                    };
                    check_program_expression(actual, Some(&typ), &mut *warn)?;
                }
                for (target, formal) in actual_targets.into_iter().zip(outputs) {
                    let target_kind = match &target.node().read().expect("poisoned parse node").kind
                    {
                        PNodeKind::Expression(e) => e.kind.clone(),
                        _ => return Err(TypeCheckError::Unsupported("method call target")),
                    };
                    let (idnref, local) = match target_kind {
                        PExpressionKind::IdnUse { idnref } => (idnref, true),
                        PExpressionKind::FieldAccess { idnref, .. } => (idnref, false),
                        _ => return Err(TypeCheckError::Unsupported("method call target")),
                    };
                    if let PNodeKind::IdnRef(reference) =
                        &mut idnref.write().expect("poisoned parse node").kind
                    {
                        reference.assign_use = true;
                    }
                    if local {
                        let filter = std::sync::Arc::new(
                            |node: &PNodeHandle| matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Declaration(d) if matches!(d.kind, PDeclarationKind::LocalVar | PDeclarationKind::FormalReturn)),
                        );
                        super::parse_ast::PIdnRef::filter_decls(&idnref, filter, |_| true);
                    }
                    let typ = match &formal.node().read().expect("poisoned parse node").kind {
                        PNodeKind::Declaration(d) => d.typ.clone(),
                        _ => return Err(TypeCheckError::Unsupported("method return")),
                    };
                    check_program_expression(target, Some(&typ), &mut *warn)?;
                }
                return Ok(());
            }
        }
    }
    if let S::Assign {
        targets,
        op: Some(_),
        rhs,
    } = &kind
    {
        if targets.len() != 1
            && !matches!(&rhs.node().read().expect("poisoned parse node").kind, PNodeKind::Expression(e) if matches!(e.kind, PExpressionKind::Call { .. }))
        {
            return Err(TypeCheckError::Positioned {
                node: statement.node().clone(),
                message: "expected a method call when assigning to multiple targets",
            });
        }
    }
    match kind {
        S::Annotated { stmt, .. } => check_statement_core(&stmt, &mut *warn)?,
        S::Seqn { statements, .. } => {
            let mut errors = Vec::new();
            for statement in statements.inner().to_seq() {
                retain_type_mismatches(&mut errors, check_statement_core(statement, &mut *warn))?;
            }
            if !errors.is_empty() {
                return Err(TypeCheckError::Mismatches(errors));
            }
        }
        S::Extension(extension) => {
            if let Some(refute) = extension
                .as_any()
                .downcast_ref::<crate::plugin::standard::refute::refute_past_extension::PRefute>(
            ) {
                check_program_expression(&refute.expression, Some(&boolean), &mut *warn)?;
            } else if !extension
                .as_any()
                .is::<crate::plugin::standard::smoke::unreachable_past_extension::PUnreachable>(
            ) {
                extension
                    .typecheck_statement(&mut |body| check_statement_core(body, &mut *warn))?;
            }
        }
        ref kind @ (S::PackageWand { ref exp, .. } | S::ApplyWand { ref exp, .. }) => {
            let is_wand = matches!(&exp.node().read().expect("poisoned parse node").kind, PNodeKind::Expression(e) if matches!(e.kind, PExpressionKind::MagicWandExp { .. }));
            if !is_wand {
                return Err(TypeCheckError::Unsupported("expected magic wand"));
            }
            let wand = type_from_signature(&SignatureType::Wand);
            check_program_expression(&exp, Some(&wand), &mut *warn)?;
            if let S::PackageWand {
                proof_script: Some(proof),
                ..
            } = kind
            {
                check_statement_core(proof, &mut *warn)?;
            }
        }
        ref kind @ (S::Fold { ref exp, .. } | S::Unfold { ref exp, .. }) => {
            ensure_nonabstract_predicate_access(exp, matches!(kind, S::Fold { .. }))?;
            let predicate = type_from_signature(&SignatureType::Predicate);
            check_program_expression(exp, Some(&predicate), &mut *warn)?;
        }
        S::Quasihavoc { lhs, exp, .. } | S::Quasihavocall { lhs, exp, .. } => {
            if let Some((guard, _)) = lhs {
                check_program_expression(&guard, Some(&boolean), &mut *warn)?;
            }
            let kind = match &exp.node().read().expect("poisoned parse node").kind {
                PNodeKind::Expression(e) => e.kind.clone(),
                _ => return Err(TypeCheckError::Unsupported("havoc resource")),
            };
            match kind {
                PExpressionKind::FieldAccess { .. } => {
                    check_program_expression(&exp, None, &mut *warn)?;
                }
                PExpressionKind::Call { .. } => {
                    let predicate = type_from_signature(&SignatureType::Predicate);
                    check_program_expression(&exp, Some(&predicate), &mut *warn)?;
                }
                PExpressionKind::MagicWandExp { .. } => {
                    let wand = type_from_signature(&SignatureType::Wand);
                    check_program_expression(&exp, Some(&wand), &mut *warn)?;
                }
                _ => {
                    return Err(TypeCheckError::Unsupported(
                        "havoc statement must take a field access, predicate, or wand",
                    ));
                }
            }
        }
        S::Assert { exp, .. }
        | S::Assume { exp, .. }
        | S::Inhale { exp, .. }
        | S::Exhale { exp, .. } => {
            check_program_expression(&exp, Some(&impure), &mut *warn)?;
        }
        S::If { cond, thn, els, .. } => {
            check_program_expression(cond.inner(), Some(&boolean), &mut *warn)?;
            check_statement_core(&thn, &mut *warn)?;
            if let Some(els) = els {
                check_statement_core(&els, &mut *warn)?;
            }
        }
        S::Else { els, .. } => check_statement_core(&els, &mut *warn)?,
        S::While {
            cond, invs, body, ..
        } => {
            check_program_expression(cond.inner(), Some(&boolean), &mut *warn)?;
            for inv in invs.specs().to_seq() {
                check_expression_context(inv.exp(), true, false, false)?;
                check_program_expression(inv.exp(), Some(&impure), &mut *warn)?;
            }
            check_statement_core(&body, &mut *warn)?;
        }
        S::Label { invs, .. } => {
            for inv in invs.to_seq() {
                check_program_expression(inv.exp(), Some(&impure), &mut *warn)?;
            }
        }
        S::Goto { .. } | S::Skip => {}
        S::Vars { vars, init, .. } => {
            for declaration in vars.to_seq() {
                let typ = match &declaration.node().read().expect("poisoned parse node").kind {
                    PNodeKind::Declaration(d) => d.typ.clone(),
                    _ => return Err(TypeCheckError::Unsupported("local declaration")),
                };
                check_supported_type(&typ)?;
            }
            if init.is_some() {
                let generated = statement
                    .vars_assign()
                    .map_err(TypeCheckError::Unsupported)?
                    .ok_or(TypeCheckError::Unsupported("missing generated initializer"))?;
                check_statement_core(&generated, &mut *warn)?;
            }
        }
        S::Assign {
            targets,
            op: Some(_),
            rhs,
        } if targets.len() == 1 => {
            let target = targets.head();
            let target_kind = match &target.node().read().expect("poisoned parse node").kind {
                PNodeKind::Expression(e) => e.kind.clone(),
                _ => return Err(TypeCheckError::Unsupported("assignment target")),
            };
            let mut invalid_target = None;
            match target_kind {
                PExpressionKind::IdnUse { idnref } => {
                    let name = match &idnref.read().expect("poisoned parse node").kind {
                        PNodeKind::IdnRef(reference) => reference.name.clone(),
                        _ => return Err(TypeCheckError::Unsupported("assignment identifier")),
                    };
                    let original_count = super::parse_ast::PIdnRef::decls(&idnref, |_| true).len();
                    if let PNodeKind::IdnRef(reference) =
                        &mut idnref.write().expect("poisoned parse node").kind
                    {
                        reference.assign_use = true;
                    }
                    let filter = std::sync::Arc::new(
                        |node: &PNodeHandle| matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Declaration(d) if matches!(d.kind, PDeclarationKind::LocalVar | PDeclarationKind::FormalReturn)),
                    );
                    super::parse_ast::PIdnRef::filter_decls(&idnref, filter, |_| true);
                    let count = super::parse_ast::PIdnRef::decls(&idnref, |_| true).len();
                    if count != 1 {
                        let message = if original_count == 0 {
                            format!(
                                "undeclared identifier `{name}`, expected parameter or local variable"
                            )
                        } else if count == 0 {
                            format!("expected an assignable identifier `{name}` as lhs")
                        } else {
                            format!(
                                "ambiguous identifier `{name}`, expected single parameter or local variable"
                            )
                        };
                        invalid_target = Some((idnref.clone(), message));
                    }
                }
                PExpressionKind::FieldAccess { idnref, .. } => {
                    if let PNodeKind::IdnRef(reference) =
                        &mut idnref.write().expect("poisoned parse node").kind
                    {
                        reference.assign_use = true;
                    }
                    let fields = super::parse_ast::PIdnRef::decls(
                        &idnref,
                        |node| matches!(&node.read().expect("poisoned parse node").kind, PNodeKind::Declaration(d) if matches!(d.kind, PDeclarationKind::Field { .. })),
                    );
                    if fields.len() != 1 {
                        let name = match &idnref.read().expect("poisoned parse node").kind {
                            PNodeKind::IdnRef(id) => id.name.clone(),
                            _ => return Err(TypeCheckError::Unsupported("assignment field")),
                        };
                        let message = if fields.is_empty() {
                            format!("undeclared field `{name}`")
                        } else {
                            format!("ambiguous field `{name}`")
                        };
                        invalid_target = Some((idnref, message));
                    }
                }
                _ => return Err(TypeCheckError::Unsupported("assignment target")),
            }
            if let Some((node, message)) = invalid_target {
                let mut errors = vec![TypeCheckError::PositionedMessage { node, message }];
                match check_program_expression(&rhs, None, &mut *warn) {
                    Ok(actual) => errors.push(TypeCheckError::Incompatible {
                        expression: rhs.node().clone(),
                        actual,
                        expected: PTypeHandle::new(
                            super::parse_ast::PTypeKind::Unknown,
                            (
                                crate::ast::position::Position::NoPosition,
                                crate::ast::position::Position::NoPosition,
                            ),
                        ),
                    }),
                    Err(error) => retain_type_mismatches(&mut errors, Err::<(), _>(error))?,
                }
                return Err(TypeCheckError::Mismatches(errors));
            }
            let target_type = check_program_expression(target, None, &mut *warn)?;
            if check_new_fields(&rhs)? {
                let reference = type_from_signature(&SignatureType::Ref);
                if !is_subtype(&target_type, &reference) {
                    return Err(TypeCheckError::Unsupported(
                        "allocation target must have Ref type",
                    ));
                }
            } else {
                check_program_expression(&rhs, Some(&target_type), &mut *warn)?;
            }
        }
        _ => return Err(TypeCheckError::Unsupported("statement typechecking")),
    }
    Ok(())
}

#[cfg(test)]
mod program_tests {
    use super::*;
    use crate::parser::fast_parser::parse_program;
    #[test]
    fn domain_axiom_allows_only_precondition_free_function_calls() {
        for (precondition, expected_error) in [("", false), ("requires x > 0", true)] {
            let source = format!(
                "function f(x: Int): Int {precondition} {{ x + 1 }} domain D {{ function g(x: Int): Int axiom {{ forall x: Int :: {{g(x)}} g(x) == f(x) }} }}"
            );
            let program = parse_program(&source, "test.vpr").unwrap();
            crate::parser::parse_ast::init_properties(program.node()).unwrap();
            assert!(NameAnalyser::default().run(program.node()).unwrap());
            let result = check_program_core(&program, &mut |_, _| {});
            if expected_error {
                assert!(
                    matches!(result, Err(TypeCheckError::Mismatches(errors)) if errors.iter().any(|e| matches!(e, TypeCheckError::FunctionPreconditionInDomainAxiom { name, .. } if name == "f")))
                );
            } else {
                result.unwrap();
                crate::parser::translator::translate_program_core(&program).unwrap();
            }
        }
    }
    #[test]
    fn checks_signatures_before_bodies_and_rejects_invalid_assignment() {
        let program = parse_program("function f(x: Int): Int { x + 1 } method m(y: Int) { var z: Int := f(y); assert z > 0; }", "test.vpr").unwrap();
        assert!(NameAnalyser::default().run(program.node()).unwrap());
        check_program_core(&program, &mut |_, _| {}).unwrap();
        let invalid = parse_program("method m(x: Int) { x := 1; }", "test.vpr").unwrap();
        assert!(NameAnalyser::default().run(invalid.node()).unwrap());
        assert!(check_program_core(&invalid, &mut |_, _| {}).is_err());
    }
}

#[cfg(test)]
mod sif_event_operator_tests {
    use crate::frontend::frontend::FrontendPhases;
    use crate::frontend::sil_front_end_config::SilFrontendConfig;
    use crate::frontend::sil_frontend::{SilFrontendPhases, standard_plugin_manager};
    use std::path::PathBuf;

    #[test]
    fn empty_low_event_substitution_is_safe_in_operators() {
        let mut config = SilFrontendConfig::new("test");
        config.plugin = Some("viper.silver.plugin.sif.SIFPlugin".into());
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        for condition in [
            "lowEvent && low(x)",
            "low(x) && lowEvent",
            "(lowEvent && low(x)) && lowEvent",
        ] {
            let source = format!("method m(x: Int) requires {condition} {{ assert lowEvent; }}");
            let parsed = phases.parse(&source).unwrap();
            phases.analyze(parsed).unwrap();
        }
        let parsed = phases
            .parse("method m() { assert lowEvent + 1 == 2; }")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
    }
}

#[cfg(test)]
mod custom_expression_extension_tests {
    use super::*;
    use crate::ast::{ast::Metadata, expression::Exp};
    use crate::frontend::{frontend::FrontendPhases, sil_frontend::SilFrontendPhases};
    use crate::parser::fast_parser::ParserFeature;
    use crate::parser::parse_ast::{
        ForceSubstitutionError, PExpGroup, PExpression, PExtender, PTypeSubstitution,
    };
    use crate::parser::parse_ast_keyword::{PGraphElement, SignatureType, Span};
    use crate::parser::translator::TranslationError;
    use crate::plugin::{silver_plugin::SilverPlugin, silver_plugin_manager::SilverPluginManager};
    use std::{any::Any, path::PathBuf, sync::Arc};

    #[derive(Debug)]
    struct CustomExpression {
        keyword: Span,
        argument: PExpGroup,
        pos: Span,
    }
    impl PExtender for CustomExpression {
        fn as_any(&self) -> &dyn Any {
            self
        }
        fn subnodes(&self) -> Vec<PNodeHandle> {
            self.argument.graph_nodes()
        }
        fn copy_macro_expression(
            &self,
            copy: &dyn Fn(
                &PExpHandle,
            )
                -> Result<PExpHandle, crate::parser::macro_expander::MacroError>,
            _: &dyn Fn(
                &PNodeHandle,
            )
                -> Result<PNodeHandle, crate::parser::macro_expander::MacroError>,
        ) -> Result<Option<PExpHandle>, crate::parser::macro_expander::MacroError> {
            let group = crate::parser::macro_expander::copy_extension_expression_group(
                &self.argument,
                copy,
            )?;
            Ok(Some(custom_factory(
                self.keyword.clone(),
                group,
                self.pos.clone(),
            )))
        }
        fn expression_name_analysis_passthrough(&self) -> bool {
            true
        }
        fn typecheck_expression(
            &self,
            _: &PExpHandle,
            _: Option<&PTypeHandle>,
            check: &mut dyn FnMut(
                &PExpHandle,
                Option<&PTypeHandle>,
            ) -> Result<PTypeHandle, TypeCheckError>,
        ) -> Result<(PTypeHandle, Vec<PTypeSubstitution>), TypeCheckError> {
            let int = type_from_signature(&SignatureType::Int);
            check(self.argument.inner(), Some(&int))?;
            Ok((int, self.argument.inner().type_subs_distinct().unwrap()))
        }
        fn force_expression_substitution(
            &self,
            input: &PExpHandle,
            substitution: &PTypeSubstitution,
        ) -> Result<(), ForceSubstitutionError> {
            self.argument.inner().force_substitution(substitution)?;
            let mut node = input.node().write().unwrap();
            let PNodeKind::Expression(expression) = &mut node.kind else {
                unreachable!()
            };
            expression.typ = expression.typ.substitute(substitution);
            expression.type_substitutions = Some(vec![substitution.clone()]);
            Ok(())
        }
        fn translate_expression(
            &self,
            translate: &mut dyn FnMut(&PExpHandle) -> Result<Exp, TranslationError>,
            _: Metadata,
        ) -> Result<Exp, TranslationError> {
            translate(self.argument.inner())
        }
    }
    fn custom_factory(keyword: Span, argument: PExpGroup, pos: Span) -> PExpHandle {
        PExpHandle::new(
            PExpression::from_kind(PExpressionKind::Extension(Arc::new(CustomExpression {
                keyword,
                argument,
                pos: pos.clone(),
            }))),
            pos,
        )
    }
    struct CustomPlugin;
    impl SilverPlugin for CustomPlugin {
        fn parser_features(&self) -> Vec<ParserFeature> {
            vec![ParserFeature::ExpressionGroup {
                keyword: "custom",
                factory: custom_factory,
            }]
        }
    }
    fn make_phases() -> SilFrontendPhases {
        SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            SilverPluginManager::new(vec![Box::new(CustomPlugin)]),
        )
    }
    #[test]
    fn custom_expression_parses_resolves_types_substitutes_and_translates() {
        let mut phases = make_phases();
        let parsed = phases
            .parse("method m(x:Int) { assert custom(x) > 0; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        phases.check_consistency(program).unwrap();
        let mut phases = make_phases();
        let parsed = phases
            .parse("method m() { assert custom(true) > 0; }")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
        let mut phases = make_phases();
        let parsed = phases
            .parse("method m(x:Int) { assert custom(x); }")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
    }
    #[test]
    fn custom_expression_macro_copy_substitutes_argument_and_preserves_group() {
        let mut phases = make_phases();
        let parsed = phases
            .parse("define f(v) custom(v) method m(x:Int) { assert f(x) > 0; }")
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let crate::ast::statement::StmtKind::Seqn { statements, .. } =
            program.methods[0].body.as_ref().unwrap().kind()
        else {
            panic!("expected method block")
        };
        let crate::ast::statement::StmtKind::Assert(assertion) = statements[0].kind() else {
            panic!("expected assert")
        };
        let crate::ast::expression::ExpKind::GtCmp(left, _) = assertion.kind() else {
            panic!("expected comparison")
        };
        let crate::ast::expression::ExpKind::LocalVar(local) = left.kind() else {
            panic!("expected substituted local")
        };
        assert_eq!(local.name, "x");
        phases.check_consistency(program).unwrap();
    }
    #[test]
    fn unknown_expression_extensions_fail_closed() {
        #[derive(Debug)]
        struct Unknown;
        impl PExtender for Unknown {
            fn as_any(&self) -> &dyn Any {
                self
            }
            fn subnodes(&self) -> Vec<PNodeHandle> {
                vec![]
            }
        }
        fn unknown_factory(_: Span, _: PExpGroup, pos: Span) -> PExpHandle {
            PExpHandle::new(
                PExpression::from_kind(PExpressionKind::Extension(Arc::new(Unknown))),
                pos,
            )
        }
        struct UnknownPlugin;
        impl SilverPlugin for UnknownPlugin {
            fn parser_features(&self) -> Vec<ParserFeature> {
                vec![ParserFeature::ExpressionGroup {
                    keyword: "mystery",
                    factory: unknown_factory,
                }]
            }
        }
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            SilverPluginManager::new(vec![Box::new(UnknownPlugin)]),
        );
        let parsed = phases
            .parse("method m() { assert mystery(true); }")
            .unwrap();
        assert!(phases.analyze(parsed).is_err());
        let mut phases = SilFrontendPhases::new(
            PathBuf::from("test.vpr"),
            SilverPluginManager::new(vec![Box::new(UnknownPlugin)]),
        );
        assert!(
            phases
                .parse("define f mystery(true) method m() { assert f; }")
                .is_err()
        );
        let pos = (
            crate::ast::position::Position::NoPosition,
            crate::ast::position::Position::NoPosition,
        );
        let expression = PExpHandle::new(
            PExpression::from_kind(PExpressionKind::Extension(Arc::new(Unknown))),
            pos,
        );
        assert!(matches!(
            check_expression(&expression, None),
            Err(TypeCheckError::Unsupported(_))
        ));
        assert!(matches!(
            expression.force_substitution(&PTypeSubstitution::default()),
            Err(ForceSubstitutionError::ExtensionNotImplemented)
        ));
        assert!(matches!(
            crate::parser::translator::translate_expression(&expression),
            Err(TranslationError::Unsupported(_))
        ));
    }
}

#[cfg(test)]
mod debugger_scope_tests {
    use super::*;
    use crate::parser::fast_parser;

    #[test]
    fn retained_member_scope_resolves_new_expressions() {
        let program =
            fast_parser::parse_program("method m(x: Int) { assert x > 0 }", "scope.vpr").unwrap();
        super::super::parse_ast::init_properties(program.node()).unwrap();
        let member = program.all_members()[0].node().clone();
        let mut names = NameAnalyser::default();
        assert!(names.run(program.node()).unwrap());
        names.collect_scopes(program.node()).unwrap();
        let input = fast_parser::parse_expression("x > 1", "userInput")
            .unwrap()
            .expression;
        assert!(names.run_in_scope(input.node(), &member).unwrap());
        check_top_expression(&input, None, |_, _| {}).unwrap();
        fn find_seqn(node: &PNodeHandle) -> Option<PNodeHandle> {
            if matches!(&node.read().unwrap().kind, PNodeKind::Statement(statement) if matches!(statement.kind, PStatementKind::Seqn { .. }))
            {
                return Some(node.clone());
            }
            subnodes(node).ok()?.iter().find_map(find_seqn)
        }
        let body = find_seqn(&member).unwrap();
        let nested = fast_parser::parse_expression("x > 1", "userInput")
            .unwrap()
            .expression;
        assert!(names.run_in_scope(nested.node(), &body).unwrap());
        check_top_expression(&nested, None, |_, _| {}).unwrap();
        let unknown = fast_parser::parse_expression("missing > 1", "userInput")
            .unwrap()
            .expression;
        assert!(names.run_in_scope(unknown.node(), &member).unwrap());
        assert!(matches!(
            check_top_expression(&unknown, None, |_, _| {}),
            Err(TypeCheckError::Mismatches(errors)) if errors.iter().any(|error| matches!(error, TypeCheckError::UnresolvedValue { name, .. } if name == "missing"))
        ));
    }
}
