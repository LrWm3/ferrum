//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/parser/ParseAst.scala
//!
//! Purpose:
//! Define the mutable intermediate syntax tree shared by parsing, formatting, resolution and
//! translation.
//!
//! Planned Rust structure:
//! Represent Where, PNode/PLeaf traversal and parent/sibling properties;
//! identifiers/declarations/scopes; PType and substitutions/renaming; PExp/POpApp and literals,
//! resources, quantifiers and collections; PStmt, PProgram, members, annotations, extensions and
//! trivia. Preserve TypeHelper operations and per-variant signatures.
//!
//! Behavior to preserve:
//! Positions and syntax tokens survive parsing; initProperties sets parents, child order and
//! sibling links, while deepCopyAll reconstructs mutable nodes. Name uses accumulate declaration
//! candidates and filters; scopes have stable IDs independent of changing content. Types carry
//! mutable resolution/substitution state and fresh variables. PProgram collects local members
//! before imports and aggregates errors; reformat only local members. Keep temporary macro nodes
//! and extension hooks. PLetNestedScope exposes its binder only in the body, after the
//! initializer; binary expression equality uses operator spelling and operands, not positions.
//! Empty collection literals infer element types; access predicates default to full permission.
//!
//! Integration:
//! parser::fast_parser, resolver, macro_expander, translator, parse_ast_keyword and
//! reformat_pretty_printer; ast::utility visitors/rewriter and verifier parse reports.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors, source positions and collection
//! semantics; parser and node representations are provisional.
//!
//! Open decisions:
//! Agree on mutable node handles, stable scope identity, parent links and copy/rewrite semantics
//! with all parser modules and shared conventions.
//!
//! Status: partial; graph, identifiers, types, expression equality and fresh IDs begun.
//! Macro validity, type-subnode and substitution operations retain upstream's failure before
//! expansion. Extension equality, parser/rewriter integration and graph ownership remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::parse_ast_keyword::{PGraphElement, Span};
use crate::ast::position::{LineColumn, Position, SourcePosition};
use std::sync::atomic::{AtomicI32, AtomicI64, Ordering};
use std::sync::{Arc, RwLock, Weak};

/// The parse graph is distinct from the verification AST and permits resolution mutation.
pub type PNodeHandle = Arc<RwLock<PNode>>;
pub type WeakPNodeHandle = Weak<RwLock<PNode>>;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PIdnDef {
    pub name: String,
}

/// A name use records candidates in insertion order; filtering is performed by the resolver.
/// Candidate handles are strong, as source declarations remain reachable through a
/// reference. A declaration whose subtree refers back to itself can therefore form an
/// Arc cycle. Reclamation needs an owner or tracing strategy; weakening candidates would
/// change the lifetime of resolved declarations.
#[derive(Clone)]
pub struct PIdnRef {
    pub name: String,
    pub assign_use: bool,
    pub declaration_class: PDeclarationClass,
    pub declarations: Vec<PNodeHandle>,
    filters: Vec<Arc<dyn Fn(&PNodeHandle) -> bool + Send + Sync>>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PDeclarationClass {
    Any,
    TypedVar,
    AssignableVar,
    Field,
    Callable,
    Predicate,
    Label,
    TypeDeclaration,
}
impl PDeclarationClass {
    fn matches(self, node: &PNodeHandle) -> bool {
        let kind = node.read().expect("poisoned parse node").kind.clone();
        match self {
            Self::Any => matches!(
                kind,
                PNodeKind::Declaration(_)
                    | PNodeKind::LetNestedScope { .. }
                    | PNodeKind::DefineParam { .. }
                    | PNodeKind::TypeVarDecl { .. }
                    | PNodeKind::Statement(PStatement {
                        kind: PStatementKind::Label { .. }
                    })
                    | PNodeKind::DomainMember(PDomainMember::Function { .. })
                    | PNodeKind::Member(PMember {
                        kind: PMemberKind::Define { .. }
                            | PMemberKind::Domain { .. }
                            | PMemberKind::Function { .. }
                            | PMemberKind::Predicate { .. }
                            | PMemberKind::Method { .. },
                        ..
                    })
                    | PNodeKind::Extension(_)
            ),
            Self::TypedVar => matches!(
                kind,
                PNodeKind::Declaration(PDeclaration {
                    kind: PDeclarationKind::FormalArg
                        | PDeclarationKind::FormalReturn
                        | PDeclarationKind::LogicalVar
                        | PDeclarationKind::LocalVar,
                    ..
                }) | PNodeKind::LetNestedScope { .. }
            ),
            Self::AssignableVar => matches!(
                kind,
                PNodeKind::Declaration(PDeclaration {
                    kind: PDeclarationKind::FormalReturn | PDeclarationKind::LocalVar,
                    ..
                })
            ),
            Self::Field => matches!(
                kind,
                PNodeKind::Declaration(PDeclaration {
                    kind: PDeclarationKind::Field { .. },
                    ..
                })
            ),
            Self::Callable => matches!(
                kind,
                PNodeKind::Member(PMember {
                    kind: PMemberKind::Function { .. }
                        | PMemberKind::Predicate { .. }
                        | PMemberKind::Method { .. },
                    ..
                }) | PNodeKind::DomainMember(PDomainMember::Function { .. })
            ),
            Self::Predicate => matches!(
                kind,
                PNodeKind::Member(PMember {
                    kind: PMemberKind::Predicate { .. },
                    ..
                })
            ),
            Self::Label => matches!(
                kind,
                PNodeKind::Statement(PStatement {
                    kind: PStatementKind::Label { .. }
                })
            ),
            Self::TypeDeclaration => matches!(
                kind,
                PNodeKind::TypeVarDecl { .. }
                    | PNodeKind::Member(PMember {
                        kind: PMemberKind::Domain { .. },
                        ..
                    })
            ),
        }
    }
}
impl PartialEq for PIdnRef {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}
impl Eq for PIdnRef {}
impl std::hash::Hash for PIdnRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.name, state);
    }
}
impl std::fmt::Debug for PIdnRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PIdnRef")
            .field("name", &self.name)
            .field("assign_use", &self.assign_use)
            .field("declaration_class", &self.declaration_class)
            .field("declaration_count", &self.declarations.len())
            .field("filter_count", &self.filters.len())
            .finish()
    }
}
impl PIdnRef {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            assign_use: false,
            declaration_class: PDeclarationClass::Any,
            declarations: Vec::new(),
            filters: Vec::new(),
        }
    }
    pub fn with_class(name: impl Into<String>, declaration_class: PDeclarationClass) -> Self {
        Self {
            declaration_class,
            ..Self::new(name)
        }
    }
    pub fn prepend_decls(&mut self, mut declarations: Vec<PNodeHandle>) {
        declarations.append(&mut self.declarations);
        self.declarations = declarations;
    }
    pub fn new_decl(&mut self, declaration: &PNodeHandle) {
        self.declarations.push(declaration.clone());
    }
    pub fn decls(
        node: &PNodeHandle,
        matches_type: impl Fn(&PNodeHandle) -> bool,
    ) -> Vec<PNodeHandle> {
        let snapshot = match &node.read().expect("poisoned parse node").kind {
            PNodeKind::IdnRef(reference) => reference.clone(),
            _ => panic!("expected identifier reference"),
        };
        snapshot
            .declarations
            .iter()
            .filter(|d| {
                snapshot.declaration_class.matches(d)
                    && matches_type(d)
                    && snapshot.filters.iter().all(|f| f(d))
            })
            .cloned()
            .collect()
    }
    /// Upstream returns true when filtering leaves no candidates, despite its documentation.
    pub fn filter_decls(
        node: &PNodeHandle,
        filter: Arc<dyn Fn(&PNodeHandle) -> bool + Send + Sync>,
        matches_type: impl Fn(&PNodeHandle) -> bool,
    ) -> bool {
        {
            let mut guard = node.write().expect("poisoned parse node");
            match &mut guard.kind {
                PNodeKind::IdnRef(reference) => reference.filters.push(filter),
                _ => panic!("expected identifier reference"),
            }
        }
        Self::decls(node, matches_type).is_empty()
    }
    pub fn rename(&self, name: impl Into<String>) -> Self {
        Self::with_class(name, self.declaration_class)
    }
    pub fn retype(&self, declaration_class: PDeclarationClass) -> Self {
        Self {
            name: self.name.clone(),
            assign_use: false,
            declaration_class,
            declarations: self.declarations.clone(),
            filters: Vec::new(),
        }
    }
}

/// Typed node families will be extended with the remaining source variants as they are ported.
#[derive(Clone, Debug)]
pub struct PDelimitedNewlineParts {
    pub first: Vec<PNodeHandle>,
    pub inner: Vec<(Vec<PNodeHandle>, Vec<PNodeHandle>)>,
    pub end: Vec<PNodeHandle>,
}

#[derive(Clone, Debug)]
pub enum PNodeKind {
    IdnDef(PIdnDef),
    IdnRef(PIdnRef),
    Reserved(super::parse_ast_keyword::PToken),
    Grouped {
        children: Vec<PNodeHandle>,
    },
    ExpressionBrackets {
        left: PNodeHandle,
        inner: WeakPNodeHandle,
        right: PNodeHandle,
    },
    Delimited {
        children: Vec<PNodeHandle>,
        /// Original ND delimiters require linebreaks between logical items.
        newline_parts: Option<PDelimitedNewlineParts>,
    },
    PairArgument {
        children: Vec<PNodeHandle>,
    },
    MaybePairArgument {
        children: Vec<PNodeHandle>,
    },
    RawString(String),
    StringLiteral {
        children: Vec<PNodeHandle>,
    },
    Annotation {
        children: Vec<PNodeHandle>,
    },
    BracedExp {
        children: Vec<PNodeHandle>,
    },
    Specification {
        children: Vec<PNodeHandle>,
    },
    Specs {
        children: Vec<PNodeHandle>,
    },
    Trigger {
        children: Vec<PNodeHandle>,
    },
    PermTrigger {
        children: Vec<PNodeHandle>,
    },
    DomainFunctionArg {
        children: Vec<PNodeHandle>,
    },
    DomainFunctionInterpretation {
        children: Vec<PNodeHandle>,
    },
    DomainInterpretation {
        children: Vec<PNodeHandle>,
    },
    DomainInterpretations {
        children: Vec<PNodeHandle>,
    },
    MethodReturns {
        children: Vec<PNodeHandle>,
    },
    DefineInner {
        children: Vec<PNodeHandle>,
    },
    DefineParam {
        children: Vec<PNodeHandle>,
    },
    TypeVarDecl {
        children: Vec<PNodeHandle>,
    },
    Type(PTypeKind),
    Expression(PExpression),
    Statement(PStatement),
    Declaration(PDeclaration),
    Member(PMember),
    DomainMember(PDomainMember),
    Program(PProgram),
    Extension(Arc<dyn PExtender>),
    LetNestedScope {
        body: PExpHandle,
    },
}

/// Syntax extensions supply their real ordered child handles; typecheck/translation hooks are
/// added when their parser and verifier interfaces are available.
pub trait PExtender: std::fmt::Debug + Send + Sync {
    fn as_any(&self) -> &dyn std::any::Any;
    fn subnodes(&self) -> Vec<PNodeHandle>;
    /// True only when ordinary recursive name analysis handles this statement's scope.
    fn statement_name_analysis_passthrough(&self) -> bool {
        false
    }
    fn typecheck_statement(
        &self,
        _check: &mut dyn FnMut(&PStmtHandle) -> Result<(), super::resolver::TypeCheckError>,
    ) -> Result<(), super::resolver::TypeCheckError> {
        Err(super::resolver::TypeCheckError::Unsupported(
            "statement extension typechecking",
        ))
    }
    fn translate_statement(
        &self,
        _translate: &mut dyn FnMut(
            &PStmtHandle,
        ) -> Result<
            crate::ast::statement::Stmt,
            super::translator::TranslationError,
        >,
        _meta: crate::ast::ast::Metadata,
    ) -> Result<crate::ast::statement::Stmt, super::translator::TranslationError> {
        Err(super::translator::TranslationError::Unsupported(
            "statement extension translation",
        ))
    }
    fn scope_id(&self) -> Option<PScopeId> {
        None
    }
}

#[derive(Debug)]
pub struct PNode {
    pub kind: PNodeKind,
    pub pos: Span,
    /// Unlike JVM references, weak navigation links do not keep the containing
    /// tree alive. Retaining a child or SourcePNodeInfo alone can therefore lose
    /// its ancestor and sibling navigation when the owning tree is dropped.
    pub parent: Option<WeakPNodeHandle>,
    pub index: i32,
    pub next: Option<WeakPNodeHandle>,
    pub prev: Option<WeakPNodeHandle>,
    initialized_children: Vec<WeakPNodeHandle>,
}
impl PNode {
    pub fn new(kind: PNodeKind, pos: Span) -> PNodeHandle {
        Arc::new(RwLock::new(Self {
            kind,
            pos,
            parent: None,
            index: -1,
            next: None,
            prev: None,
            initialized_children: Vec::new(),
        }))
    }
    /// Mirrors Where.errorPosition: retain file identity and an available ending position.
    pub fn error_position(&self) -> Position {
        match (&self.pos.0, &self.pos.1) {
            (Position::LineColumn(LineColumn::File(start)), Position::LineColumn(end)) => {
                Position::LineColumn(LineColumn::Source(Box::new(SourcePosition {
                    file: Some(start.file.clone()),
                    start: Box::new(LineColumn::File(start.clone())),
                    end: Some(Box::new(end.clone())),
                })))
            }
            (Position::LineColumn(LineColumn::File(start)), _) => {
                Position::LineColumn(LineColumn::Source(Box::new(SourcePosition::new(
                    start.file.clone(),
                    start.line,
                    start.column,
                ))))
            }
            (start, _) => start.clone(),
        }
    }
}

static NEXT_SCOPE_ID: AtomicI64 = AtomicI64::new(0);
static NEXT_TYPE_VARIABLE: AtomicI32 = AtomicI32::new(0);
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PScopeId(i64);
impl PScopeId {
    pub fn value(self) -> i64 {
        self.0
    }
}
pub fn fresh_scope_id() -> PScopeId {
    PScopeId(NEXT_SCOPE_ID.fetch_add(1, Ordering::Relaxed))
}
pub fn is_free_ptv_name(name: &str) -> bool {
    name.contains('#')
}
pub fn fresh_type_variable_name(name: &str) -> String {
    format!(
        "{}#{}",
        name,
        NEXT_TYPE_VARIABLE.fetch_add(1, Ordering::Relaxed)
    )
}
/// One shared fresh index is used for a batch of type variables.
pub fn fresh_type_renaming(names: &[String], domain: Option<&str>) -> PTypeRenaming {
    let index = NEXT_TYPE_VARIABLE.fetch_add(1, Ordering::Relaxed);
    let mappings = names
        .iter()
        .map(|name| {
            let prefix = domain.map_or_else(|| name.clone(), |d| format!("{d}%{name}"));
            (name.clone(), format!("{prefix}#{index}"))
        })
        .collect();
    PTypeRenaming { mappings }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PTrivia {
    Space,
    NewLine,
    Comment(PComment),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PComment {
    pub inner: String,
    pub trimmed: bool,
}
impl PComment {
    pub fn new(inner: &str) -> Self {
        // Scala String.trim removes code points <= U+0020, not arbitrary Unicode whitespace.
        Self {
            trimmed: inner.ends_with('\n') || inner.ends_with("\r\n"),
            inner: inner.trim_matches(|c| c <= '\u{20}').to_owned(),
        }
    }
    pub fn str(&self) -> &str {
        &self.inner
    }
}

/// Mutable resolution state of a syntactic domain type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PDomainTypeKind {
    Unresolved,
    Domain,
    TypeVar,
    Undeclared,
}

/// A checked handle to a parse-type node. Child handles stay typed while the common graph
/// supplies identity, position and parent/sibling links.
#[derive(Clone, Debug)]
pub struct PTypeHandle(PNodeHandle);
impl PTypeHandle {
    /// Macro types wrap a call and derive their position from it, as in the parser.
    pub fn macro_type(call: PExpHandle) -> Self {
        Self::new(
            PTypeKind::Macro { call },
            (Position::NoPosition, Position::NoPosition),
        )
    }
    pub fn macro_call(&self) -> Option<PExpHandle> {
        match self.kind() {
            PTypeKind::Macro { call } => Some(call),
            _ => None,
        }
    }
    pub fn new(kind: PTypeKind, pos: Span) -> Self {
        let pos = if let PTypeKind::Macro { call } = &kind {
            let node = call.node().read().expect("poisoned parse node");
            assert!(
                matches!(
                    &node.kind,
                    PNodeKind::Expression(PExpression {
                        kind: PExpressionKind::Call { .. },
                        ..
                    })
                ),
                "macro type requires a call expression"
            );
            node.pos.clone()
        } else {
            pos
        };
        Self(PNode::new(PNodeKind::Type(kind), pos))
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.0
    }
    pub fn from_node(node: PNodeHandle) -> Result<Self, PNodeHandle> {
        let matches = matches!(
            node.read().expect("poisoned parse node").kind,
            PNodeKind::Type(_)
        );
        if matches { Ok(Self(node)) } else { Err(node) }
    }
}

pub type PTypeArguments = super::parse_ast_keyword::PGrouped<
    super::parse_ast_keyword::PSym,
    super::parse_ast_keyword::PDelimited<
        PTypeHandle,
        super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
    >,
    super::parse_ast_keyword::PSym,
>;
pub type PSingleTypeGroup = super::parse_ast_keyword::PGrouped<
    super::parse_ast_keyword::PSym,
    PTypeHandle,
    super::parse_ast_keyword::PSym,
>;

/// Syntactic and internal type forms; macro types exist until macro expansion.
#[derive(Clone, Debug)]
pub enum PTypeKind {
    Primitive {
        name: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>,
    },
    ExtensionPrimitive {
        name: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PExtensionKeyword>,
    },
    Domain {
        domain: PNodeHandle,
        args: Option<PTypeArguments>,
        kind: PDomainTypeKind,
    },
    Seq {
        keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>,
        element_type: PSingleTypeGroup,
    },
    Set {
        keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>,
        element_type: PSingleTypeGroup,
    },
    Multiset {
        keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>,
        element_type: PSingleTypeGroup,
    },
    Map {
        keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>,
        types: super::parse_ast_keyword::PGrouped<
            super::parse_ast_keyword::PSym,
            PPairArgument<PTypeHandle, PTypeHandle>,
            super::parse_ast_keyword::PSym,
        >,
    },
    Macro {
        call: PExpHandle,
    },
    Unknown,
    BoolImpure,
    BoolWand,
    BoolPredicate,
    Function {
        arg_types: Vec<PTypeHandle>,
        result_type: PTypeHandle,
    },
}

#[derive(Clone, Debug)]
pub struct PPairArgument<T, U> {
    pub(crate) first: T,
    pub(crate) comma: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
    pub(crate) second: U,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PMaybePairArgument<T, U> {
    pub(crate) first: T,
    pub(crate) second: Option<(
        super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
        U,
    )>,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
impl<T, U> PPairArgument<T, U> {
    pub fn first(&self) -> &T {
        &self.first
    }
    pub fn comma(&self) -> &super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym> {
        &self.comma
    }
    pub fn second(&self) -> &U {
        &self.second
    }
    pub fn position(&self) -> &Span {
        &self.pos
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.node
    }
}
impl<T, U> PMaybePairArgument<T, U> {
    pub fn first(&self) -> &T {
        &self.first
    }
    pub fn second(
        &self,
    ) -> Option<&(
        super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
        U,
    )> {
        self.second.as_ref()
    }
    pub fn position(&self) -> &Span {
        &self.pos
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.node
    }
}

impl<T, U> super::parse_ast_keyword::PGraphElement for PPairArgument<T, U> {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        vec![self.node.clone()]
    }
}
impl<T, U> super::parse_ast_keyword::PGraphElement for PMaybePairArgument<T, U> {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        vec![self.node.clone()]
    }
}
impl<T: super::parse_ast_keyword::PGraphElement, U: super::parse_ast_keyword::PGraphElement>
    PPairArgument<T, U>
{
    pub fn new(
        first: T,
        comma: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
        second: U,
        pos: Span,
    ) -> Self {
        let mut children = first.graph_nodes();
        children.extend(comma.graph_nodes());
        children.extend(second.graph_nodes());
        let node = PNode::new(PNodeKind::PairArgument { children }, pos.clone());
        Self {
            first,
            comma,
            second,
            pos,
            node,
        }
    }
}
impl<T: super::parse_ast_keyword::PGraphElement, U: super::parse_ast_keyword::PGraphElement>
    PMaybePairArgument<T, U>
{
    pub fn new(
        first: T,
        second: Option<(
            super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
            U,
        )>,
        pos: Span,
    ) -> Self {
        let mut children = first.graph_nodes();
        if let Some((comma, value)) = &second {
            children.extend(comma.graph_nodes());
            children.extend(value.graph_nodes());
        }
        let node = PNode::new(PNodeKind::MaybePairArgument { children }, pos.clone());
        Self {
            first,
            second,
            pos,
            node,
        }
    }
}

impl PTypeHandle {
    fn kind(&self) -> PTypeKind {
        match &self.0.read().expect("poisoned parse node").kind {
            PNodeKind::Type(kind) => kind.clone(),
            _ => panic!("parse type handle points to a different node kind"),
        }
    }
    fn argument_types(args: &Option<PTypeArguments>) -> Vec<PTypeHandle> {
        args.as_ref()
            .map(|group| {
                group
                    .inner
                    .first
                    .iter()
                    .chain(group.inner.inner.iter().map(|(_, value)| value))
                    .cloned()
                    .collect()
            })
            .unwrap_or_default()
    }
    pub fn is_valid_or_undeclared(&self) -> bool {
        use PTypeKind::*;
        match self.kind() {
            Unknown => false,
            Domain { args, kind, .. } => {
                kind != PDomainTypeKind::Unresolved
                    && Self::argument_types(&args)
                        .iter()
                        .all(Self::is_valid_or_undeclared)
            }
            Seq { element_type, .. } | Set { element_type, .. } | Multiset { element_type, .. } => {
                element_type.inner.is_valid_or_undeclared()
            }
            Map { types, .. } => {
                types.inner.first.is_valid_or_undeclared()
                    && types.inner.second.is_valid_or_undeclared()
            }
            Function {
                arg_types,
                result_type,
            } => {
                arg_types.iter().all(Self::is_valid_or_undeclared)
                    && result_type.is_valid_or_undeclared()
            }
            Macro { .. } => panic!("upstream PMacroType validity is unavailable before expansion"),
            Primitive { .. }
            | ExtensionPrimitive { .. }
            | BoolImpure
            | BoolWand
            | BoolPredicate => true,
        }
    }
    pub fn is_ground(&self) -> bool {
        use PTypeKind::*;
        match self.kind() {
            Domain { domain, args, kind } => {
                let name = match &domain.read().expect("poisoned parse identifier").kind {
                    PNodeKind::IdnRef(reference) => reference.name.clone(),
                    _ => panic!("domain type has a non-reference identifier"),
                };
                (kind != PDomainTypeKind::TypeVar || !is_free_ptv_name(&name))
                    && Self::argument_types(&args).iter().all(Self::is_ground)
            }
            Seq { element_type, .. } | Set { element_type, .. } | Multiset { element_type, .. } => {
                element_type.inner.is_ground()
            }
            Map { types, .. } => types.inner.first.is_ground() && types.inner.second.is_ground(),
            // Upstream PFunctionType is an internal type, inheriting PType.isGround=true.
            Primitive { .. }
            | ExtensionPrimitive { .. }
            | Unknown
            | BoolImpure
            | BoolWand
            | BoolPredicate
            | Macro { .. }
            | Function { .. } => true,
        }
    }
    pub fn is_pure(&self) -> bool {
        !matches!(
            self.kind(),
            PTypeKind::BoolImpure | PTypeKind::BoolWand | PTypeKind::BoolPredicate
        )
    }
}

impl PTypeHandle {
    pub fn free_type_variables(&self) -> std::collections::HashSet<String> {
        use PTypeKind::*;
        let mut variables = std::collections::HashSet::new();
        match self.kind() {
            Domain { domain, args, kind } => {
                let name = match &domain.read().expect("poisoned parse identifier").kind {
                    PNodeKind::IdnRef(reference) => reference.name.clone(),
                    _ => panic!("domain type has a non-reference identifier"),
                };
                if kind == PDomainTypeKind::TypeVar && is_free_ptv_name(&name) {
                    variables.insert(name);
                }
                for arg in Self::argument_types(&args) {
                    variables.extend(arg.free_type_variables());
                }
            }
            Seq { element_type, .. } | Set { element_type, .. } | Multiset { element_type, .. } => {
                variables.extend(element_type.inner.free_type_variables())
            }
            Map { types, .. } => {
                variables.extend(types.inner.first.free_type_variables());
                variables.extend(types.inner.second.free_type_variables());
            }
            Function {
                arg_types,
                result_type,
            } => {
                for arg in arg_types {
                    variables.extend(arg.free_type_variables());
                }
                variables.extend(result_type.free_type_variables());
            }
            Macro { .. } => {
                panic!("upstream PMacroType type subnodes are unavailable before expansion")
            }
            Primitive { .. }
            | ExtensionPrimitive { .. }
            | Unknown
            | BoolImpure
            | BoolWand
            | BoolPredicate => {}
        }
        variables
    }
}

#[derive(Clone, Debug)]
pub struct PExpHandle(PNodeHandle);
impl PExpHandle {
    pub fn new(expression: PExpression, pos: Span) -> Self {
        Self(PNode::new(PNodeKind::Expression(expression), pos))
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.0
    }
    pub fn from_node(node: PNodeHandle) -> Result<Self, PNodeHandle> {
        let matches = matches!(
            node.read().expect("poisoned parse node").kind,
            PNodeKind::Expression(_)
        );
        if matches { Ok(Self(node)) } else { Err(node) }
    }
}

#[derive(Clone, Debug)]
pub enum PBinaryOp {
    Symbol(super::parse_ast_keyword::PSymOp),
    Keyword(super::parse_ast_keyword::PKwOp),
}
impl super::parse_ast_keyword::PReservedString for PBinaryOp {
    fn token(&self) -> &str {
        match self {
            Self::Symbol(op) => op.token(),
            Self::Keyword(op) => op.token(),
        }
    }
}
impl super::parse_ast_keyword::PFormatting for PBinaryOp {
    fn formatting(&self) -> super::parse_ast_keyword::Formatting {
        match self {
            Self::Symbol(op) => op.formatting(),
            Self::Keyword(op) => op.formatting(),
        }
    }
}
impl PBinaryOp {
    pub fn signatures(&self) -> Option<Vec<PTypeSubstitution>> {
        let signatures = match self {
            Self::Symbol(op) => op.signatures(),
            Self::Keyword(op) => op.signatures(),
        }?;
        Some(signatures.iter().map(substitution_from_signature).collect())
    }
    pub fn require_pure_args(&self) -> bool {
        match self {
            Self::Symbol(op) => op.require_pure_args(),
            Self::Keyword(_) => false,
        }
    }
}
#[derive(Clone, Debug)]
pub struct PExpression {
    pub kind: PExpressionKind,
    pub typ: PTypeHandle,
    /// Binder substitutions may initially be absent; operator applications start with an empty list.
    pub type_substitutions: Option<Vec<PTypeSubstitution>>,
    brackets: Option<PExpressionBracketMeta>,
}
impl PExpression {
    /// Construct the source's initial expression type and substitution state.
    pub fn from_kind(kind: PExpressionKind) -> Self {
        use super::parse_ast_keyword::SignatureType;
        use PExpressionKind::*;
        let typ = match &kind {
            IntLit(_) => type_from_signature(&SignatureType::Int),
            BoolLit(_) => type_from_signature(&SignatureType::Bool),
            NullLit(_) => type_from_signature(&SignatureType::Ref),
            NoPerm(_) | FullPerm(_) | Wildcard(_) | Epsilon(_) => {
                type_from_signature(&SignatureType::Perm)
            }
            _ => internal_type(PTypeKind::Unknown),
        };
        if let ExplicitSeq(c) | ExplicitSet(c) | ExplicitMultiset(c) = &kind {
            assert!(
                !c.call_args.inner.is_empty(),
                "explicit collection literal must be nonempty"
            );
        }
        let type_substitutions = match &kind {
            IdnUse { .. }
            | VersionedIdnUse { .. }
            | IntLit(_)
            | ResultLit(_)
            | BoolLit(_)
            | NullLit(_)
            | NoPerm(_)
            | FullPerm(_)
            | Wildcard(_)
            | Epsilon(_)
            | NewExp { .. } => Some(vec![PTypeSubstitution::default()]),
            Exists(_)
            | Forall(_)
            | ForPerm { .. }
            | Let { .. }
            | AnnotatedExp { .. }
            | Extension(_) => None,
            _ => Some(Vec::new()),
        };
        Self {
            kind,
            typ,
            type_substitutions,
            brackets: None,
        }
    }
}

/// The expression retains the group node, whose inner edge is weak to avoid a cycle.
#[derive(Clone, Debug)]
struct PExpressionBracketMeta {
    left: SymbolToken,
    right: SymbolToken,
    node: PNodeHandle,
}
/// A typed bracket handle retains the inner expression even when detached. A raw group
/// node handle does not retain it; graph-level ownership remains a separate concern.
#[derive(Clone, Debug)]
pub struct PExpressionBrackets {
    pub left: SymbolToken,
    pub right: SymbolToken,
    pub node: PNodeHandle,
    expression: PExpHandle,
}
impl PExpressionBrackets {
    pub fn new(left: SymbolToken, expression: &PExpHandle, right: SymbolToken, pos: Span) -> Self {
        let node = PNode::new(
            PNodeKind::ExpressionBrackets {
                left: left.node().clone(),
                inner: Arc::downgrade(expression.node()),
                right: right.node().clone(),
            },
            pos,
        );
        Self {
            left,
            right,
            node,
            expression: expression.clone(),
        }
    }
    pub fn expression(&self) -> Option<PExpHandle> {
        Some(self.expression.clone())
    }
}
impl PExpHandle {
    pub fn set_brackets(&self, brackets: PExpressionBrackets) {
        assert!(
            Arc::ptr_eq(self.node(), brackets.expression.node()),
            "brackets must enclose this expression"
        );
        self.update(|exp| {
            exp.brackets = Some(PExpressionBracketMeta {
                left: brackets.left,
                right: brackets.right,
                node: brackets.node,
            })
        });
    }
    pub fn brackets(&self) -> Option<PExpressionBrackets> {
        self.snapshot().brackets.map(|meta| PExpressionBrackets {
            left: meta.left,
            right: meta.right,
            node: meta.node,
            expression: self.clone(),
        })
    }
}

#[derive(Clone, Debug, Default)]
pub struct PTypeSubstitution {
    mappings: std::collections::HashMap<String, PTypeHandle>,
    can_generalise: bool,
}

#[derive(Clone, Debug, Default)]
pub struct PTypeRenaming {
    pub mappings: std::collections::HashMap<String, String>,
}

pub type PExpArguments = super::parse_ast_keyword::PGrouped<
    super::parse_ast_keyword::PSym,
    super::parse_ast_keyword::PDelimited<
        PExpHandle,
        super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
    >,
    super::parse_ast_keyword::PSym,
>;

/// Syntactic forms translated so far; expression type state is carried separately.
#[derive(Clone, Debug)]
pub enum PExpressionKind {
    Extension(Arc<dyn PExtender>),
    AnnotatedExp {
        annotation: PNodeHandle,
        expression: PExpHandle,
    },
    IdnUse {
        idnref: PNodeHandle,
    },
    VersionedIdnUse {
        idnref: PIdnRef,
        version: String,
        separator: String,
    },
    BinExp {
        left: PExpHandle,
        op: super::parse_ast_keyword::PReserved<PBinaryOp>,
        right: PExpHandle,
    },
    MagicWandExp {
        left: PExpHandle,
        wand: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        right: PExpHandle,
    },
    UnExp {
        op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        exp: PExpHandle,
    },
    CondExp {
        cond: PExpHandle,
        question: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        thn: PExpHandle,
        colon: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        els: PExpHandle,
    },
    IntLit(num_bigint::BigInt),
    ResultLit(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>),
    BoolLit(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>),
    NullLit(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>),
    NoPerm(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>),
    FullPerm(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>),
    Wildcard(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>),
    Epsilon(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>),
    FieldAccess {
        receiver: PExpHandle,
        dot: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        idnref: PNodeHandle,
    },
    InhaleExhale {
        left: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        inhale: PExpHandle,
        comma: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        exhale: PExpHandle,
        right: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
    },
    Call {
        idnref: PNodeHandle,
        call_args: PExpArguments,
        type_annotated: Option<(
            super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
            PTypeHandle,
        )>,
        extra_local_type_variables: Vec<PTypeHandle>,
        domain_type_renaming: Option<PTypeRenaming>,
        domain_substitution: Option<PTypeSubstitution>,
    },
    Unfolding {
        unfolding: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        acc: PExpHandle,
        in_token: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        exp: PExpHandle,
    },
    Applying {
        applying: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        wand: PExpHandle,
        in_token: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        exp: PExpHandle,
    },
    Asserting {
        asserting: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        assertion: PExpHandle,
        in_token: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        exp: PExpHandle,
    },
    RangeSeq {
        left: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        low: PExpHandle,
        dots: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        high: PExpHandle,
        right: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
    },
    Lookup {
        base: PExpHandle,
        left: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        index: PExpHandle,
        right: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
    },
    SeqSlice {
        seq: PExpHandle,
        left: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        start: Option<PExpHandle>,
        dots: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        end: Option<PExpHandle>,
        right: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
    },
    Update {
        base: PExpHandle,
        left: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        key: PExpHandle,
        assign: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        value: PExpHandle,
        right: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
    },
    Size {
        left: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        seq: PExpHandle,
        right: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
    },
    Maplet {
        key: PExpHandle,
        assign: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        value: PExpHandle,
    },
    Exists(PQuantifier),
    Forall(PQuantifier),
    ForPerm {
        keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>,
        vars: PLogicalVars,
        trigger: PPermTrigger,
        colons: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
        body: PExpHandle,
        scope_id: PScopeId,
    },
    Let {
        keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        variable: PNodeHandle,
        eq: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>,
        exp: super::parse_ast_keyword::PGrouped<
            super::parse_ast_keyword::PSym,
            PExpHandle,
            super::parse_ast_keyword::PSym,
        >,
        in_token: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        nested_scope: PNodeHandle,
        scope_id: PScopeId,
    },
    CurrentPerm {
        op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        resource: PExpGroup,
    },
    AccPred {
        op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        amount: super::parse_ast_keyword::PGrouped<
            super::parse_ast_keyword::PSym,
            PMaybePairArgument<PExpHandle, PExpHandle>,
            super::parse_ast_keyword::PSym,
        >,
    },
    OldExp {
        op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        label: Option<
            super::parse_ast_keyword::PGrouped<
                super::parse_ast_keyword::PSym,
                POldLabel,
                super::parse_ast_keyword::PSym,
            >,
        >,
        exp: PExpGroup,
    },
    DebugLabelledOldExp {
        op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        label: PExpHandle,
        exp: PExpHandle,
    },
    EmptySeq(PEmptyCollection),
    ExplicitSeq(PExplicitCollection),
    EmptySet(PEmptyCollection),
    ExplicitSet(PExplicitCollection),
    EmptyMultiset(PEmptyCollection),
    ExplicitMultiset(PExplicitCollection),
    EmptyMap {
        op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        annotated_type: Option<
            super::parse_ast_keyword::PGrouped<
                super::parse_ast_keyword::PSym,
                PPairArgument<PTypeHandle, PTypeHandle>,
                super::parse_ast_keyword::PSym,
            >,
        >,
        call_args: PExpArguments,
    },
    ExplicitMap(PExplicitMap),
    MapDomain {
        keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        base: PExpGroup,
    },
    MapRange {
        keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        base: PExpGroup,
    },
    NewExp {
        keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>,
        fields: super::parse_ast_keyword::PGrouped<
            super::parse_ast_keyword::PSym,
            PNewFields,
            super::parse_ast_keyword::PSym,
        >,
    },
}

pub type PExpGroup = super::parse_ast_keyword::PGrouped<
    super::parse_ast_keyword::PSym,
    PExpHandle,
    super::parse_ast_keyword::PSym,
>;
#[derive(Clone, Debug)]
pub enum POldLabel {
    Lhs(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>),
    Label(PNodeHandle),
}
#[derive(Clone, Debug)]
pub enum PNewFields {
    All(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>),
    Fields(
        super::parse_ast_keyword::PDelimited<
            PNodeHandle,
            super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
        >,
    ),
}
#[derive(Clone, Debug)]
pub struct PEmptyCollection {
    pub op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
    pub annotated_type: Option<PSingleTypeGroup>,
    pub call_args: PExpArguments,
}
#[derive(Clone, Debug)]
pub struct PExplicitCollection {
    op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
    call_args: PExpArguments,
    element_type: PTypeHandle,
}
impl PExplicitCollection {
    pub fn new(
        op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
        call_args: PExpArguments,
    ) -> Self {
        let element_type = call_args.inner.head().snapshot().typ;
        Self {
            op,
            call_args,
            element_type,
        }
    }
    pub fn element_type(&self) -> &PTypeHandle {
        &self.element_type
    }
    pub fn op(&self) -> &super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp> {
        &self.op
    }
    pub fn call_args(&self) -> &PExpArguments {
        &self.call_args
    }
}
#[derive(Clone, Debug)]
pub struct PExplicitMap {
    pub op: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKwOp>,
    pub call_args: PExpArguments,
}
pub type PLogicalVars = super::parse_ast_keyword::PDelimited<
    PDeclarationHandle,
    super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
>;
#[derive(Clone, Debug)]
pub struct PTrigger {
    pub(crate) expressions: PExpArguments,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PPermTrigger {
    pub(crate) access: super::parse_ast_keyword::PGrouped<
        super::parse_ast_keyword::PSym,
        PExpHandle,
        super::parse_ast_keyword::PSym,
    >,
    pub(crate) node: PNodeHandle,
}
impl PPermTrigger {
    pub fn new(access: PExpGroup) -> Self {
        let node = PNode::new(
            PNodeKind::PermTrigger {
                children: access.graph_nodes(),
            },
            access.position().clone(),
        );
        Self { access, node }
    }
    pub fn access(&self) -> &PExpGroup {
        &self.access
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.node
    }
}
impl PGraphElement for PPermTrigger {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        vec![self.node.clone()]
    }
}
#[derive(Clone, Debug)]
pub struct PQuantifier {
    pub keyword: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>,
    pub vars: PLogicalVars,
    pub colons: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
    pub triggers: Vec<PTrigger>,
    pub body: PExpHandle,
    pub scope_id: PScopeId,
}

#[derive(Clone, Debug)]
pub struct PDeclarationHandle(PNodeHandle);
impl PDeclarationHandle {
    pub fn new(declaration: PDeclaration, pos: Span) -> Self {
        Self(PNode::new(PNodeKind::Declaration(declaration), pos))
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.0
    }
    pub fn from_node(node: PNodeHandle) -> Result<Self, PNodeHandle> {
        let matches = matches!(
            node.read().expect("poisoned parse node").kind,
            PNodeKind::Declaration(_)
        );
        if matches { Ok(Self(node)) } else { Err(node) }
    }
}
#[derive(Clone, Debug)]
pub enum PDeclarationKind {
    FormalArg,
    FormalReturn,
    LogicalVar,
    LocalVar,
    /// Owner identity is weak to avoid a cycle; cached annotations keep detached
    /// field metadata available after the enclosing PFields node is dropped.
    Field {
        fields: Option<WeakPNodeHandle>,
        annotations: Arc<[PAnnotation]>,
    },
}
impl PDeclarationKind {
    pub fn field() -> Self {
        Self::Field {
            fields: None,
            annotations: Arc::from([]),
        }
    }
}
#[derive(Clone, Debug)]
pub struct PDeclaration {
    pub kind: PDeclarationKind,
    pub idndef: PNodeHandle,
    pub colon: super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>,
    pub typ: PTypeHandle,
}

#[derive(Clone, Debug)]
pub struct PStmtHandle(PNodeHandle);
impl PStmtHandle {
    pub fn new(statement: PStatement, pos: Span) -> Self {
        Self(PNode::new(PNodeKind::Statement(statement), pos))
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.0
    }
    pub fn from_node(node: PNodeHandle) -> Result<Self, PNodeHandle> {
        let matches = matches!(
            node.read().expect("poisoned parse node").kind,
            PNodeKind::Statement(_)
                | PNodeKind::Member(PMember {
                    kind: PMemberKind::Define { .. },
                    ..
                })
        );
        if matches { Ok(Self(node)) } else { Err(node) }
    }
}
pub type KeywordToken = super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PKw>;
pub type SymbolToken = super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSym>;
pub type SymbolOperatorToken =
    super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PSymOp>;
pub type OptionalSemi = super::parse_ast_keyword::ND<Option<SymbolToken>>;
#[derive(Clone, Debug)]
pub enum PSpecificationKeyword {
    Builtin(KeywordToken),
    Extension(super::parse_ast_keyword::PReserved<super::parse_ast_keyword::PExtensionKeyword>),
}
impl PGraphElement for PSpecificationKeyword {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        match self {
            Self::Builtin(token) => token.graph_nodes(),
            Self::Extension(token) => token.graph_nodes(),
        }
    }
}
pub type PStmtBlock = super::parse_ast_keyword::PGrouped<
    super::parse_ast_keyword::PSym,
    super::parse_ast_keyword::PDelimited<PStmtHandle, OptionalSemi>,
    super::parse_ast_keyword::PSym,
>;
#[derive(Clone, Debug)]
pub struct PSpecification {
    pub(crate) keyword: PSpecificationKeyword,
    pub(crate) exp: PExpHandle,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PSpecs {
    pub(crate) specs: super::parse_ast_keyword::PDelimited<PSpecification, OptionalSemi>,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PStatement {
    pub kind: PStatementKind,
}
#[derive(Clone, Debug)]
pub enum PStatementKind {
    Extension(Arc<dyn PExtender>),
    Annotated {
        annotation: PNodeHandle,
        stmt: PStmtHandle,
    },
    Seqn {
        statements: PStmtBlock,
        scope_id: PScopeId,
    },
    MacroSeqn {
        statements: PStmtBlock,
    },
    Fold {
        keyword: KeywordToken,
        exp: PExpHandle,
    },
    Unfold {
        keyword: KeywordToken,
        exp: PExpHandle,
    },
    PackageWand {
        keyword: KeywordToken,
        exp: PExpHandle,
        proof_script: Option<PStmtHandle>,
    },
    ApplyWand {
        keyword: KeywordToken,
        exp: PExpHandle,
    },
    Exhale {
        keyword: KeywordToken,
        exp: PExpHandle,
    },
    Assert {
        keyword: KeywordToken,
        exp: PExpHandle,
    },
    Assume {
        keyword: KeywordToken,
        exp: PExpHandle,
    },
    Inhale {
        keyword: KeywordToken,
        exp: PExpHandle,
    },
    Assign {
        targets: super::parse_ast_keyword::PDelimited<PExpHandle, SymbolToken>,
        op: Option<SymbolOperatorToken>,
        rhs: PExpHandle,
    },
    If {
        keyword: KeywordToken,
        cond: PExpGroup,
        thn: PStmtHandle,
        els: Option<PStmtHandle>,
    },
    Else {
        keyword: KeywordToken,
        els: PStmtHandle,
    },
    While {
        keyword: KeywordToken,
        cond: PExpGroup,
        invs: PSpecs,
        body: PStmtHandle,
    },
    Vars {
        keyword: KeywordToken,
        vars: super::parse_ast_keyword::PDelimited<PDeclarationHandle, SymbolToken>,
        init: Option<(SymbolOperatorToken, PExpHandle)>,
    },
    Label {
        keyword: KeywordToken,
        idndef: PNodeHandle,
        invs: super::parse_ast_keyword::PDelimited<PSpecification, OptionalSemi>,
    },
    Goto {
        keyword: KeywordToken,
        target: PNodeHandle,
    },
    Skip,
    Quasihavoc {
        keyword: KeywordToken,
        lhs: Option<(PExpHandle, SymbolOperatorToken)>,
        exp: PExpHandle,
    },
    Quasihavocall {
        keyword: KeywordToken,
        vars: PLogicalVars,
        colons: SymbolToken,
        lhs: Option<(PExpHandle, SymbolOperatorToken)>,
        exp: PExpHandle,
        scope_id: PScopeId,
    },
}

#[derive(Clone, Debug)]
pub struct PMemberHandle(PNodeHandle);
impl PMemberHandle {
    pub fn new(member: PMember, pos: Span) -> Self {
        Self(PNode::new(PNodeKind::Member(member), pos))
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.0
    }
    pub fn from_node(node: PNodeHandle) -> Result<Self, PNodeHandle> {
        let matches = matches!(
            node.read().expect("poisoned parse node").kind,
            PNodeKind::Member(_) | PNodeKind::DomainMember(PDomainMember::Function { .. })
        );
        if matches { Ok(Self(node)) } else { Err(node) }
    }
}
#[derive(Clone, Debug)]
pub struct PRawString {
    pub(crate) text: String,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PStringLiteral {
    pub(crate) grouped: super::parse_ast_keyword::PGrouped<
        super::parse_ast_keyword::PSym,
        PRawString,
        super::parse_ast_keyword::PSym,
    >,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PAnnotation {
    pub(crate) at: SymbolToken,
    pub(crate) key: PRawString,
    pub(crate) values: super::parse_ast_keyword::PGrouped<
        super::parse_ast_keyword::PSym,
        super::parse_ast_keyword::PDelimited<PStringLiteral, SymbolToken>,
        super::parse_ast_keyword::PSym,
    >,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PBracedExp {
    pub(crate) exp: PExpGroup,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
pub type PFormalArgs = super::parse_ast_keyword::PGrouped<
    super::parse_ast_keyword::PSym,
    super::parse_ast_keyword::PDelimited<PDeclarationHandle, SymbolToken>,
    super::parse_ast_keyword::PSym,
>;
#[derive(Clone, Debug)]
pub struct PMethodReturns {
    pub(crate) keyword: KeywordToken,
    pub(crate) formal_returns: PFormalArgs,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PMember {
    annotations: Arc<[PAnnotation]>,
    pub scope_id: PScopeId,
    pub kind: PMemberKind,
}
impl PMember {
    pub fn new(annotations: Vec<PAnnotation>, kind: PMemberKind) -> Self {
        Self {
            annotations: annotations.into(),
            scope_id: fresh_scope_id(),
            kind,
        }
    }
    pub fn annotations(&self) -> &[PAnnotation] {
        &self.annotations
    }
}
#[derive(Clone, Debug)]
pub enum PDefineBody {
    Expression(PExpHandle),
    Statement(PStmtHandle),
}
impl PGraphElement for PDefineBody {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        match self {
            Self::Expression(exp) => exp.graph_nodes(),
            Self::Statement(stmt) => stmt.graph_nodes(),
        }
    }
}
#[derive(Clone, Debug)]
pub struct PDefineInner {
    body: PDefineBody,
    node: PNodeHandle,
}
impl PDefineInner {
    pub fn new(body: PDefineBody) -> Self {
        let child = body
            .graph_nodes()
            .into_iter()
            .next()
            .expect("define body has no node");
        let pos = child.read().expect("poisoned parse node").pos.clone();
        let node = PNode::new(
            PNodeKind::DefineInner {
                children: vec![child],
            },
            pos,
        );
        Self { body, node }
    }
    pub fn body(&self) -> &PDefineBody {
        &self.body
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.node
    }
}
impl PGraphElement for PDefineInner {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        vec![self.node.clone()]
    }
}
#[derive(Clone, Debug)]
pub enum PMemberKind {
    Extension(Arc<dyn PExtender>),
    Import {
        keyword: KeywordToken,
        file: PStringLiteral,
        local: bool,
        resolved: Option<std::path::PathBuf>,
    },
    Define {
        keyword: KeywordToken,
        idndef: PNodeHandle,
        parameters: Option<
            super::parse_ast_keyword::PGrouped<
                super::parse_ast_keyword::PSym,
                super::parse_ast_keyword::PDelimited<PNodeHandle, SymbolToken>,
                super::parse_ast_keyword::PSym,
            >,
        >,
        body: PDefineInner,
    },
    Domain {
        keyword: KeywordToken,
        idndef: PNodeHandle,
        type_vars: Option<
            super::parse_ast_keyword::PGrouped<
                super::parse_ast_keyword::PSym,
                super::parse_ast_keyword::PDelimited<PNodeHandle, SymbolToken>,
                super::parse_ast_keyword::PSym,
            >,
        >,
        interpretations: Option<PDomainInterpretations>,
        members: super::parse_ast_keyword::PGrouped<
            super::parse_ast_keyword::PSym,
            super::parse_ast_keyword::PDelimited<PDomainMemberHandle, OptionalSemi>,
            super::parse_ast_keyword::PSym,
        >,
    },
    Fields {
        keyword: KeywordToken,
        fields: super::parse_ast_keyword::PDelimited<PDeclarationHandle, SymbolToken>,
        semi: Option<SymbolToken>,
    },
    Function {
        keyword: KeywordToken,
        idndef: PNodeHandle,
        args: PFormalArgs,
        colon: SymbolToken,
        result_type: PTypeHandle,
        pres: PSpecs,
        posts: PSpecs,
        body: Option<PBracedExp>,
    },
    Predicate {
        keyword: KeywordToken,
        idndef: PNodeHandle,
        args: PFormalArgs,
        body: Option<PBracedExp>,
    },
    Method {
        keyword: KeywordToken,
        idndef: PNodeHandle,
        args: PFormalArgs,
        returns: Option<PMethodReturns>,
        pres: PSpecs,
        posts: PSpecs,
        body: Option<PStmtHandle>,
    },
}

#[derive(Clone, Debug)]
pub struct PProgramHandle(PNodeHandle);
impl PProgramHandle {
    pub fn new(program: PProgram, pos: Span) -> Self {
        Self(PNode::new(PNodeKind::Program(program), pos))
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.0
    }
    pub fn from_node(node: PNodeHandle) -> Result<Self, PNodeHandle> {
        let matches = matches!(
            node.read().expect("poisoned parse node").kind,
            PNodeKind::Program(_)
        );
        if matches { Ok(Self(node)) } else { Err(node) }
    }
    fn snapshot(&self) -> PProgram {
        match &self.0.read().expect("poisoned parse node").kind {
            PNodeKind::Program(program) => program.clone(),
            _ => panic!("parse program handle points to a different node kind"),
        }
    }
    /// Local members precede members of each imported program, recursively.
    pub fn all_members(&self) -> Vec<PMemberHandle> {
        let program = self.snapshot();
        let mut result = program.members;
        for imported in program.imported {
            result.extend(imported.all_members());
        }
        result
    }
    pub fn errors(&self) -> Vec<crate::verifier::verification_result::ParseReport> {
        let program = self.snapshot();
        let mut result = program.local_errors;
        for imported in program.imported {
            result.extend(imported.errors());
        }
        result
    }
    pub fn error(report: crate::verifier::verification_result::ParseReport) -> Self {
        let pos = report.pos().clone();
        Self::new(
            PProgram {
                imported: Vec::new(),
                members: Vec::new(),
                local_errors: vec![report],
                offsets: Vec::new(),
                raw_program: String::new(),
            },
            (pos.clone(), pos),
        )
    }
}
#[derive(Clone, Debug)]
pub struct PProgram {
    pub imported: Vec<PProgramHandle>,
    pub members: Vec<PMemberHandle>,
    pub local_errors: Vec<crate::verifier::verification_result::ParseReport>,
    pub offsets: Vec<i32>,
    pub raw_program: String,
}

impl super::parse_ast_keyword::PGraphElement for PNodeHandle {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        vec![self.clone()]
    }
}
macro_rules! graph_handle {
    ($($handle:ty),* $(,)?) => {$ (
        impl super::parse_ast_keyword::PGraphElement for $handle {
            fn graph_nodes(&self) -> Vec<PNodeHandle> { vec![self.node().clone()] }
        }
    )*};
}
graph_handle!(
    PTypeHandle,
    PExpHandle,
    PStmtHandle,
    PDeclarationHandle,
    PMemberHandle,
    PProgramHandle
);

/// An explicit boundary for graph families whose source-order child enumeration is still pending.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChildrenNotPorted(pub &'static str);

pub fn subnodes(node: &PNodeHandle) -> Result<Vec<PNodeHandle>, ChildrenNotPorted> {
    let kind = node.read().expect("poisoned parse node").kind.clone();
    use PNodeKind::*;
    match kind {
        IdnDef(_) | IdnRef(_) | Reserved(_) | RawString(_) => Ok(Vec::new()),
        ExpressionBrackets { left, inner, right } => Ok(vec![
            left,
            inner
                .upgrade()
                .ok_or(ChildrenNotPorted("bracket expression no longer owned"))?,
            right,
        ]),
        Grouped { children }
        | Delimited { children, .. }
        | PairArgument { children }
        | MaybePairArgument { children }
        | StringLiteral { children }
        | Annotation { children }
        | BracedExp { children }
        | Specification { children }
        | Specs { children }
        | Trigger { children }
        | PermTrigger { children }
        | DomainFunctionArg { children }
        | DomainFunctionInterpretation { children }
        | DomainInterpretation { children }
        | DomainInterpretations { children }
        | MethodReturns { children }
        | DefineInner { children }
        | DefineParam { children }
        | TypeVarDecl { children } => Ok(children),
        LetNestedScope { body } => Ok(body.graph_nodes()),
        Declaration(decl) => {
            let mut children = decl.idndef.graph_nodes();
            children.extend(decl.colon.graph_nodes());
            children.extend(decl.typ.graph_nodes());
            Ok(children)
        }
        Type(kind) => {
            let mut children = Vec::new();
            match kind {
                PTypeKind::Primitive { name } => children.extend(name.graph_nodes()),
                PTypeKind::ExtensionPrimitive { name } => children.extend(name.graph_nodes()),
                PTypeKind::Domain { domain, args, .. } => {
                    children.extend(domain.graph_nodes());
                    children.extend(args.graph_nodes());
                }
                PTypeKind::Seq {
                    keyword,
                    element_type,
                }
                | PTypeKind::Set {
                    keyword,
                    element_type,
                }
                | PTypeKind::Multiset {
                    keyword,
                    element_type,
                } => {
                    children.extend(keyword.graph_nodes());
                    children.extend(element_type.graph_nodes());
                }
                PTypeKind::Map { keyword, types } => {
                    children.extend(keyword.graph_nodes());
                    children.extend(types.graph_nodes());
                }
                PTypeKind::Function {
                    arg_types,
                    result_type,
                } => {
                    for arg in arg_types {
                        children.extend(arg.graph_nodes());
                    }
                    children.extend(result_type.graph_nodes());
                }
                PTypeKind::Macro { call } => children.extend(call.graph_nodes()),
                PTypeKind::Unknown
                | PTypeKind::BoolImpure
                | PTypeKind::BoolWand
                | PTypeKind::BoolPredicate => {}
            }
            Ok(children)
        }
        Extension(extension) => Ok(extension.subnodes()),
        Expression(expression) => Ok(expression_subnodes(expression.kind)),
        Statement(statement) => Ok(statement_subnodes(statement.kind)),
        Member(member) => Ok(member_subnodes(member)),
        DomainMember(member) => Ok(domain_member_subnodes(member)),
        Program(program) => {
            let mut nodes = program.imported.graph_nodes();
            nodes.extend(program.members.graph_nodes());
            Ok(nodes)
        }
    }
}

/// Initialize parent/index/sibling links, after validating that all node families can be traversed.
/// No visitor callback runs while a graph lock is held.
pub fn init_properties(root: &PNodeHandle) -> Result<(), ChildrenNotPorted> {
    struct Prepared {
        node: PNodeHandle,
        children: Vec<Prepared>,
    }
    fn prepare(node: &PNodeHandle) -> Result<Prepared, ChildrenNotPorted> {
        let children = subnodes(node)?
            .iter()
            .map(prepare)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Prepared {
            node: node.clone(),
            children,
        })
    }
    fn apply(tree: &Prepared) {
        let nodes: Vec<PNodeHandle> = tree
            .children
            .iter()
            .map(|child| child.node.clone())
            .collect();
        tree.node
            .write()
            .expect("poisoned parse node")
            .initialized_children = nodes.iter().map(Arc::downgrade).collect();
        let mut previous: Option<PNodeHandle> = None;
        for (index, child) in tree.children.iter().enumerate() {
            {
                let mut node = child.node.write().expect("poisoned parse node");
                node.parent = Some(Arc::downgrade(&tree.node));
                node.index = index as i32;
                node.prev = previous.as_ref().map(Arc::downgrade);
                node.next = None;
            }
            if let Some(previous) = &previous {
                previous.write().expect("poisoned parse node").next =
                    Some(Arc::downgrade(&child.node));
            }
            previous = Some(child.node.clone());
            apply(child);
        }
    }
    let tree = prepare(root)?;
    apply(&tree);
    Ok(())
}

/// Search from the immediate parent upward, releasing each read lock before the callback.
pub fn get_ancestor(
    node: &PNodeHandle,
    predicate: impl Fn(&PNodeHandle) -> bool,
) -> Option<PNodeHandle> {
    let mut parent = node
        .read()
        .expect("poisoned parse node")
        .parent
        .as_ref()
        .and_then(Weak::upgrade);
    while let Some(candidate) = parent {
        if predicate(&candidate) {
            return Some(candidate);
        }
        parent = candidate
            .read()
            .expect("poisoned parse node")
            .parent
            .as_ref()
            .and_then(Weak::upgrade);
    }
    None
}

#[derive(Clone, Debug)]
pub struct PDomainMemberHandle(PNodeHandle);
impl PDomainMemberHandle {
    pub fn new(member: PDomainMember, pos: Span) -> Self {
        Self(PNode::new(PNodeKind::DomainMember(member), pos))
    }
    pub fn node(&self) -> &PNodeHandle {
        &self.0
    }
    pub fn from_node(node: PNodeHandle) -> Result<Self, PNodeHandle> {
        let matches = matches!(
            node.read().expect("poisoned parse node").kind,
            PNodeKind::DomainMember(_)
        );
        if matches { Ok(Self(node)) } else { Err(node) }
    }
}
impl PGraphElement for PDomainMemberHandle {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        vec![self.0.clone()]
    }
}
#[derive(Clone, Debug)]
pub struct PDomainFunctionArg {
    pub(crate) name: Option<PNodeHandle>,
    pub(crate) colon: Option<SymbolToken>,
    pub(crate) typ: PTypeHandle,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PDomainFunctionInterpretation {
    pub(crate) keyword: KeywordToken,
    pub(crate) interpretation: PStringLiteral,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub enum PDomainMember {
    Function {
        annotations: Vec<PAnnotation>,
        unique: Option<KeywordToken>,
        keyword: KeywordToken,
        idndef: PNodeHandle,
        args: super::parse_ast_keyword::PGrouped<
            super::parse_ast_keyword::PSym,
            super::parse_ast_keyword::PDelimited<PDomainFunctionArg, SymbolToken>,
            super::parse_ast_keyword::PSym,
        >,
        colon: SymbolToken,
        result_type: PTypeHandle,
        interpretation: Option<PDomainFunctionInterpretation>,
        scope_id: PScopeId,
    },
    Axiom {
        annotations: Vec<PAnnotation>,
        keyword: KeywordToken,
        idndef: Option<PNodeHandle>,
        exp: PBracedExp,
        scope_id: PScopeId,
    },
}
#[derive(Clone, Debug)]
pub struct PDomainInterpretation {
    pub(crate) name: PRawString,
    pub(crate) colon: SymbolToken,
    pub(crate) lit: PStringLiteral,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
#[derive(Clone, Debug)]
pub struct PDomainInterpretations {
    pub(crate) keyword: KeywordToken,
    pub(crate) interpretations: super::parse_ast_keyword::PGrouped<
        super::parse_ast_keyword::PSym,
        super::parse_ast_keyword::PDelimited<PDomainInterpretation, SymbolToken>,
        super::parse_ast_keyword::PSym,
    >,
    pub(crate) pos: Span,
    pub(crate) node: PNodeHandle,
}
impl PDomainInterpretations {
    pub fn interps(&self) -> std::collections::HashMap<String, String> {
        self.interpretations
            .inner
            .to_seq()
            .into_iter()
            .map(|i| (i.name.text.clone(), i.lit.grouped.inner.text.clone()))
            .collect()
    }
}

macro_rules! graph_record { ($($record:ty),* $(,)?) => {$ (
    impl PGraphElement for $record { fn graph_nodes(&self) -> Vec<PNodeHandle> { vec![self.node.clone()] } }
    impl $record { pub fn node(&self) -> &PNodeHandle { &self.node } }
)*}; }
graph_record!(
    PRawString,
    PStringLiteral,
    PAnnotation,
    PBracedExp,
    PSpecification,
    PSpecs,
    PTrigger,
    PDomainFunctionArg,
    PDomainFunctionInterpretation,
    PDomainInterpretation,
    PDomainInterpretations,
    PMethodReturns
);

macro_rules! graph_record_new {
    ($record:ident, $variant:ident, $( $field:ident : $field_type:ty ),+ $(,)?) => {
        impl $record {
            pub fn new($( $field: $field_type, )+ pos: Span) -> Self {
                let mut children = Vec::new();
                $( children.extend($field.graph_nodes()); )+
                let node = PNode::new(PNodeKind::$variant { children }, pos.clone());
                Self { $( $field, )+ pos, node }
            }
            $( pub fn $field(&self) -> &$field_type { &self.$field } )+
            pub fn position(&self) -> &Span { &self.pos }
        }
    };
}
impl PRawString {
    pub fn new(text: String, pos: Span) -> Self {
        let node = PNode::new(PNodeKind::RawString(text.clone()), pos.clone());
        Self { text, pos, node }
    }
    pub fn text(&self) -> &str {
        &self.text
    }
    pub fn position(&self) -> &Span {
        &self.pos
    }
}
graph_record_new!(PStringLiteral, StringLiteral,
    grouped: super::parse_ast_keyword::PGrouped<super::parse_ast_keyword::PSym, PRawString, super::parse_ast_keyword::PSym>);
graph_record_new!(PAnnotation, Annotation,
    at: SymbolToken, key: PRawString,
    values: super::parse_ast_keyword::PGrouped<super::parse_ast_keyword::PSym, super::parse_ast_keyword::PDelimited<PStringLiteral, SymbolToken>, super::parse_ast_keyword::PSym>);
graph_record_new!(PBracedExp, BracedExp, exp: PExpGroup);
graph_record_new!(PSpecification, Specification, keyword: PSpecificationKeyword, exp: PExpHandle);
graph_record_new!(PSpecs, Specs, specs: super::parse_ast_keyword::PDelimited<PSpecification, OptionalSemi>);
graph_record_new!(PTrigger, Trigger, expressions: PExpArguments);
graph_record_new!(PDomainFunctionArg, DomainFunctionArg, name: Option<PNodeHandle>, colon: Option<SymbolToken>, typ: PTypeHandle);
graph_record_new!(PDomainFunctionInterpretation, DomainFunctionInterpretation, keyword: KeywordToken, interpretation: PStringLiteral);
graph_record_new!(PDomainInterpretation, DomainInterpretation, name: PRawString, colon: SymbolToken, lit: PStringLiteral);
graph_record_new!(PDomainInterpretations, DomainInterpretations, keyword: KeywordToken,
    interpretations: super::parse_ast_keyword::PGrouped<super::parse_ast_keyword::PSym, super::parse_ast_keyword::PDelimited<PDomainInterpretation, SymbolToken>, super::parse_ast_keyword::PSym>);
graph_record_new!(PMethodReturns, MethodReturns, keyword: KeywordToken, formal_returns: PFormalArgs);

impl PGraphElement for POldLabel {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        match self {
            Self::Lhs(token) => token.graph_nodes(),
            Self::Label(label) => label.graph_nodes(),
        }
    }
}
impl PGraphElement for PNewFields {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        match self {
            Self::All(token) => token.graph_nodes(),
            Self::Fields(fields) => fields.graph_nodes(),
        }
    }
}
impl PGraphElement for PEmptyCollection {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        let mut nodes = self.op.graph_nodes();
        nodes.extend(self.annotated_type.graph_nodes());
        nodes.extend(self.call_args.graph_nodes());
        nodes
    }
}
impl PGraphElement for PExplicitCollection {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        let mut nodes = self.op.graph_nodes();
        nodes.extend(self.call_args.graph_nodes());
        nodes
    }
}
impl PGraphElement for PExplicitMap {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        let mut nodes = self.op.graph_nodes();
        nodes.extend(self.call_args.graph_nodes());
        nodes
    }
}
impl PGraphElement for PQuantifier {
    fn graph_nodes(&self) -> Vec<PNodeHandle> {
        let mut nodes = self.keyword.graph_nodes();
        nodes.extend(self.vars.graph_nodes());
        nodes.extend(self.colons.graph_nodes());
        nodes.extend(self.triggers.graph_nodes());
        nodes.extend(self.body.graph_nodes());
        nodes
    }
}

fn expression_subnodes(kind: PExpressionKind) -> Vec<PNodeHandle> {
    use PExpressionKind::*;
    let mut nodes = Vec::new();
    macro_rules! add { ($($item:expr),* $(,)?) => {{ $( nodes.extend($item.graph_nodes()); )* }}; }
    match kind {
        Extension(extension) => nodes.extend(extension.subnodes()),
        AnnotatedExp {
            annotation,
            expression,
        } => add!(annotation, expression),
        IdnUse { idnref } => add!(idnref),
        VersionedIdnUse { .. } | IntLit(_) => {}
        BinExp { left, op, right } => add!(left, op, right),
        MagicWandExp { left, wand, right } => add!(left, wand, right),
        UnExp { op, exp } => add!(op, exp),
        CondExp {
            cond,
            question,
            thn,
            colon,
            els,
        } => add!(cond, question, thn, colon, els),
        ResultLit(token) | BoolLit(token) | NullLit(token) | NoPerm(token) | FullPerm(token)
        | Wildcard(token) | Epsilon(token) => add!(token),
        FieldAccess {
            receiver,
            dot,
            idnref,
        } => add!(receiver, dot, idnref),
        InhaleExhale {
            left,
            inhale,
            comma,
            exhale,
            right,
        } => add!(left, inhale, comma, exhale, right),
        Call {
            idnref,
            call_args,
            type_annotated,
            ..
        } => {
            add!(idnref, call_args);
            if let Some((colon, typ)) = type_annotated {
                add!(colon, typ);
            }
        }
        Unfolding {
            unfolding,
            acc,
            in_token,
            exp,
        } => add!(unfolding, acc, in_token, exp),
        Applying {
            applying,
            wand,
            in_token,
            exp,
        } => add!(applying, wand, in_token, exp),
        Asserting {
            asserting,
            assertion,
            in_token,
            exp,
        } => add!(asserting, assertion, in_token, exp),
        RangeSeq {
            left,
            low,
            dots,
            high,
            right,
        } => add!(left, low, dots, high, right),
        Lookup {
            base,
            left,
            index,
            right,
        } => add!(base, left, index, right),
        SeqSlice {
            seq,
            left,
            start,
            dots,
            end,
            right,
        } => add!(seq, left, start, dots, end, right),
        Update {
            base,
            left,
            key,
            assign,
            value,
            right,
        } => add!(base, left, key, assign, value, right),
        Size { left, seq, right } => add!(left, seq, right),
        Maplet { key, assign, value } => add!(key, assign, value),
        Exists(quantifier) | Forall(quantifier) => add!(quantifier),
        ForPerm {
            keyword,
            vars,
            trigger,
            colons,
            body,
            ..
        } => add!(keyword, vars, trigger, colons, body),
        Let {
            keyword,
            variable,
            eq,
            exp,
            in_token,
            nested_scope,
            ..
        } => add!(keyword, variable, eq, exp, in_token, nested_scope),
        CurrentPerm { op, resource } => add!(op, resource),
        AccPred { op, amount } => add!(op, amount),
        OldExp { op, label, exp } => add!(op, label, exp),
        DebugLabelledOldExp { op, label, exp } => add!(op, label, exp),
        EmptySeq(c) | EmptySet(c) | EmptyMultiset(c) => add!(c),
        ExplicitSeq(c) | ExplicitSet(c) | ExplicitMultiset(c) => add!(c),
        ExplicitMap(c) => add!(c),
        EmptyMap {
            op,
            annotated_type,
            call_args,
        } => add!(op, annotated_type, call_args),
        MapDomain { keyword, base } | MapRange { keyword, base } => add!(keyword, base),
        NewExp { keyword, fields } => add!(keyword, fields),
    }
    nodes
}

fn statement_subnodes(kind: PStatementKind) -> Vec<PNodeHandle> {
    use PStatementKind::*;
    let mut nodes = Vec::new();
    macro_rules! add { ($($item:expr),* $(,)?) => {{ $( nodes.extend($item.graph_nodes()); )* }}; }
    match kind {
        Extension(extension) => nodes.extend(extension.subnodes()),
        Annotated { annotation, stmt } => add!(annotation, stmt),
        Seqn { statements, .. } | MacroSeqn { statements } => add!(statements),
        Fold { keyword, exp }
        | Unfold { keyword, exp }
        | ApplyWand { keyword, exp }
        | Exhale { keyword, exp }
        | Assert { keyword, exp }
        | Assume { keyword, exp }
        | Inhale { keyword, exp } => add!(keyword, exp),
        PackageWand {
            keyword,
            exp,
            proof_script,
        } => add!(keyword, exp, proof_script),
        Assign { targets, op, rhs } => add!(targets, op, rhs),
        If {
            keyword,
            cond,
            thn,
            els,
        } => add!(keyword, cond, thn, els),
        Else { keyword, els } => add!(keyword, els),
        While {
            keyword,
            cond,
            invs,
            body,
        } => add!(keyword, cond, invs, body),
        Vars {
            keyword,
            vars,
            init,
        } => {
            add!(keyword, vars);
            if let Some((assign, exp)) = init {
                add!(assign, exp);
            }
        }
        Label {
            keyword,
            idndef,
            invs,
        } => add!(keyword, idndef, invs),
        Goto { keyword, target } => add!(keyword, target),
        Skip => {}
        Quasihavoc { keyword, lhs, exp } => {
            add!(keyword);
            if let Some((condition, implies)) = lhs {
                add!(condition, implies);
            }
            add!(exp);
        }
        Quasihavocall {
            keyword,
            vars,
            colons,
            lhs,
            exp,
            ..
        } => {
            add!(keyword, vars, colons);
            if let Some((condition, implies)) = lhs {
                add!(condition, implies);
            }
            add!(exp);
        }
    }
    nodes
}

fn member_subnodes(member: PMember) -> Vec<PNodeHandle> {
    use PMemberKind::*;
    let mut nodes: Vec<_> = member
        .annotations
        .iter()
        .flat_map(PGraphElement::graph_nodes)
        .collect();
    macro_rules! add { ($($item:expr),* $(,)?) => {{ $( nodes.extend($item.graph_nodes()); )* }}; }
    match member.kind {
        Extension(extension) => nodes.extend(extension.subnodes()),
        Import { keyword, file, .. } => add!(keyword, file),
        Define {
            keyword,
            idndef,
            parameters,
            body,
        } => add!(keyword, idndef, parameters, body),
        Domain {
            keyword,
            idndef,
            type_vars,
            interpretations,
            members,
        } => add!(keyword, idndef, type_vars, interpretations, members),
        Fields {
            keyword,
            fields,
            semi,
        } => add!(keyword, fields, semi),
        Function {
            keyword,
            idndef,
            args,
            colon,
            result_type,
            pres,
            posts,
            body,
        } => add!(keyword, idndef, args, colon, result_type, pres, posts, body),
        Predicate {
            keyword,
            idndef,
            args,
            body,
        } => add!(keyword, idndef, args, body),
        Method {
            keyword,
            idndef,
            args,
            returns,
            pres,
            posts,
            body,
        } => add!(keyword, idndef, args, returns, pres, posts, body),
    }
    nodes
}
fn domain_member_subnodes(member: PDomainMember) -> Vec<PNodeHandle> {
    use PDomainMember::*;
    let mut nodes = Vec::new();
    macro_rules! add { ($($item:expr),* $(,)?) => {{ $( nodes.extend($item.graph_nodes()); )* }}; }
    match member {
        Function {
            annotations,
            unique,
            keyword,
            idndef,
            args,
            colon,
            result_type,
            interpretation,
            ..
        } => add!(
            annotations,
            unique,
            keyword,
            idndef,
            args,
            colon,
            result_type,
            interpretation
        ),
        Axiom {
            annotations,
            keyword,
            idndef,
            exp,
            ..
        } => add!(annotations, keyword, idndef, exp),
    }
    nodes
}

pub fn define_param(idndef: PNodeHandle, pos: Span) -> PNodeHandle {
    PNode::new(
        PNodeKind::DefineParam {
            children: vec![idndef],
        },
        pos,
    )
}
pub fn type_var_decl(idndef: PNodeHandle, pos: Span) -> PNodeHandle {
    PNode::new(
        PNodeKind::TypeVarDecl {
            children: vec![idndef],
        },
        pos,
    )
}

impl PTypeHandle {
    /// Type syntax equality ignores positions and mutable domain-resolution state, as case-class equality does.
    pub fn structurally_equals(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        fn idn_name(node: &PNodeHandle) -> String {
            match &node.read().expect("poisoned parse node").kind {
                PNodeKind::IdnRef(reference) => reference.name.clone(),
                _ => panic!("domain type has a non-reference identifier"),
            }
        }
        fn delimited_eq(
            a: &super::parse_ast_keyword::PDelimited<PTypeHandle, SymbolToken>,
            b: &super::parse_ast_keyword::PDelimited<PTypeHandle, SymbolToken>,
        ) -> bool {
            let first = match (&a.first, &b.first) {
                (None, None) => true,
                (Some(a), Some(b)) => a.structurally_equals(b),
                _ => false,
            };
            first
                && a.end == b.end
                && a.inner.len() == b.inner.len()
                && a.inner
                    .iter()
                    .zip(&b.inner)
                    .all(|((ad, at), (bd, bt))| ad == bd && at.structurally_equals(bt))
        }
        fn group_eq(a: &PSingleTypeGroup, b: &PSingleTypeGroup) -> bool {
            a.left == b.left && a.right == b.right && a.inner.structurally_equals(&b.inner)
        }
        use PTypeKind::*;
        match (self.kind(), other.kind()) {
            (Primitive { name: a }, Primitive { name: b }) => a == b,
            (ExtensionPrimitive { name: a }, ExtensionPrimitive { name: b }) => a == b,
            (
                Domain {
                    domain: a,
                    args: aa,
                    ..
                },
                Domain {
                    domain: b,
                    args: ba,
                    ..
                },
            ) => {
                idn_name(&a) == idn_name(&b)
                    && match (&aa, &ba) {
                        (None, None) => true,
                        (Some(a), Some(b)) => {
                            a.left == b.left
                                && a.right == b.right
                                && delimited_eq(&a.inner, &b.inner)
                        }
                        _ => false,
                    }
            }
            (
                Seq {
                    keyword: a,
                    element_type: at,
                },
                Seq {
                    keyword: b,
                    element_type: bt,
                },
            )
            | (
                Set {
                    keyword: a,
                    element_type: at,
                },
                Set {
                    keyword: b,
                    element_type: bt,
                },
            )
            | (
                Multiset {
                    keyword: a,
                    element_type: at,
                },
                Multiset {
                    keyword: b,
                    element_type: bt,
                },
            ) => a == b && group_eq(&at, &bt),
            (
                Map {
                    keyword: a,
                    types: at,
                },
                Map {
                    keyword: b,
                    types: bt,
                },
            ) => {
                a == b
                    && at.left == bt.left
                    && at.right == bt.right
                    && at.inner.comma == bt.inner.comma
                    && at.inner.first.structurally_equals(&bt.inner.first)
                    && at.inner.second.structurally_equals(&bt.inner.second)
            }
            (Unknown, Unknown)
            | (BoolImpure, BoolImpure)
            | (BoolWand, BoolWand)
            | (BoolPredicate, BoolPredicate) => true,
            (Macro { call: a }, Macro { call: b }) => a
                .try_structurally_equals(&b)
                .expect("macro type equality requires extension-specific expression equality"),
            (
                Function {
                    arg_types: a,
                    result_type: ar,
                },
                Function {
                    arg_types: b,
                    result_type: br,
                },
            ) => {
                a.len() == b.len()
                    && a.iter().zip(&b).all(|(a, b)| a.structurally_equals(b))
                    && ar.structurally_equals(&br)
            }
            _ => false,
        }
    }
}

impl PTypeHandle {
    /// Substitute resolved type variables and reconstruct composite type syntax.
    pub fn substitute(&self, substitution: &PTypeSubstitution) -> Self {
        let pos = self.0.read().expect("poisoned parse node").pos.clone();
        use PTypeKind::*;
        match self.kind() {
            Domain { domain, args, kind } => {
                assert!(
                    kind != PDomainTypeKind::Unresolved,
                    "domain type must be resolved before substitution"
                );
                let name = match &domain.read().expect("poisoned parse identifier").kind {
                    PNodeKind::IdnRef(reference) => reference.name.clone(),
                    _ => panic!("domain type has a non-reference identifier"),
                };
                if kind == PDomainTypeKind::TypeVar {
                    return substitution
                        .mappings
                        .get(&name)
                        .cloned()
                        .unwrap_or_else(|| self.clone());
                }
                let old = Self::argument_types(&args);
                let replacements: Vec<_> = old.iter().map(|t| t.substitute(substitution)).collect();
                if old
                    .iter()
                    .zip(&replacements)
                    .all(|(a, b)| a.structurally_equals(b))
                {
                    return self.clone();
                }
                let group = args.expect("nonempty domain arguments require a group");
                let delimited = group.inner.clone().update(replacements);
                Self::new(
                    Domain {
                        domain,
                        args: Some(group.update(delimited)),
                        kind: PDomainTypeKind::Domain,
                    },
                    pos,
                )
            }
            Seq {
                keyword,
                element_type,
            } => {
                let inner = element_type.inner.substitute(substitution);
                Self::new(
                    Seq {
                        keyword,
                        element_type: element_type.update(inner),
                    },
                    pos,
                )
            }
            Set {
                keyword,
                element_type,
            } => {
                let inner = element_type.inner.substitute(substitution);
                Self::new(
                    Set {
                        keyword,
                        element_type: element_type.update(inner),
                    },
                    pos,
                )
            }
            Multiset {
                keyword,
                element_type,
            } => {
                let inner = element_type.inner.substitute(substitution);
                Self::new(
                    Multiset {
                        keyword,
                        element_type: element_type.update(inner),
                    },
                    pos,
                )
            }
            Map { keyword, types } => {
                let pair = &types.inner;
                let replacement = PPairArgument::new(
                    pair.first.substitute(substitution),
                    pair.comma.clone(),
                    pair.second.substitute(substitution),
                    pair.pos.clone(),
                );
                Self::new(
                    Map {
                        keyword,
                        types: types.update(replacement),
                    },
                    pos,
                )
            }
            Function {
                arg_types,
                result_type,
            } => Self::new(
                Function {
                    arg_types: arg_types
                        .iter()
                        .map(|t| t.substitute(substitution))
                        .collect(),
                    result_type: result_type.substitute(substitution),
                },
                pos,
            ),
            Macro { .. } => {
                panic!("upstream PMacroType substitution is unavailable before expansion")
            }
            Primitive { .. }
            | ExtensionPrimitive { .. }
            | Unknown
            | BoolImpure
            | BoolWand
            | BoolPredicate => self.clone(),
        }
    }
}

fn internal_type(kind: PTypeKind) -> PTypeHandle {
    PTypeHandle::new(kind, (Position::NoPosition, Position::NoPosition))
}
fn type_umbrella(typ: &PTypeHandle) -> Option<PTypeHandle> {
    use super::parse_ast_keyword::{PKw, PReserved};
    match typ.kind() {
        PTypeKind::Primitive { name } if *name.value() == PKw::Bool => {
            Some(internal_type(PTypeKind::BoolImpure))
        }
        PTypeKind::Primitive { name } if *name.value() == PKw::Rational => {
            Some(internal_type(PTypeKind::Primitive {
                name: PReserved::implied(PKw::Perm),
            }))
        }
        PTypeKind::BoolWand | PTypeKind::BoolPredicate => {
            Some(internal_type(PTypeKind::BoolImpure))
        }
        _ => None,
    }
}
pub fn common_supertype(a: &PTypeHandle, b: &PTypeHandle) -> Option<PTypeHandle> {
    if a.structurally_equals(b) {
        return Some(a.clone());
    }
    if let (
        PTypeKind::Function {
            arg_types: aa,
            result_type: ar,
        },
        PTypeKind::Function {
            arg_types: ba,
            result_type: br,
        },
    ) = (a.kind(), b.kind())
    {
        if aa.len() != ba.len() {
            return None;
        }
        let args = aa
            .iter()
            .zip(&ba)
            .map(|(x, y)| common_subtype(x, y))
            .collect::<Option<Vec<_>>>()?;
        let result_type = common_supertype(&ar, &br)?;
        return Some(internal_type(PTypeKind::Function {
            arg_types: args,
            result_type,
        }));
    }
    match (type_umbrella(a), type_umbrella(b)) {
        (Some(au), Some(bu)) if au.structurally_equals(&bu) => Some(au),
        (Some(au), None) if au.structurally_equals(b) => Some(au),
        (None, Some(bu)) if a.structurally_equals(&bu) => Some(a.clone()),
        _ => None,
    }
}
pub fn common_subtype(a: &PTypeHandle, b: &PTypeHandle) -> Option<PTypeHandle> {
    if a.structurally_equals(b) {
        return Some(a.clone());
    }
    if let (
        PTypeKind::Function {
            arg_types: aa,
            result_type: ar,
        },
        PTypeKind::Function {
            arg_types: ba,
            result_type: br,
        },
    ) = (a.kind(), b.kind())
    {
        if aa.len() != ba.len() {
            return None;
        }
        let args = aa
            .iter()
            .zip(&ba)
            .map(|(x, y)| common_supertype(x, y))
            .collect::<Option<Vec<_>>>()?;
        let result_type = common_subtype(&ar, &br)?;
        return Some(internal_type(PTypeKind::Function {
            arg_types: args,
            result_type,
        }));
    }
    match (type_umbrella(a), type_umbrella(b)) {
        (Some(au), None) if au.structurally_equals(b) => Some(a.clone()),
        (None, Some(bu)) if a.structurally_equals(&bu) => Some(b.clone()),
        _ => None,
    }
}
pub fn is_subtype(sub: &PTypeHandle, sup: &PTypeHandle) -> bool {
    common_supertype(sub, sup).is_some_and(|common| common.structurally_equals(sup))
}

impl PTypeHandle {
    fn type_variable_name(&self) -> Option<String> {
        if let PTypeKind::Domain {
            domain,
            kind: PDomainTypeKind::TypeVar,
            ..
        } = self.kind()
        {
            let name = match &domain.read().expect("poisoned parse identifier").kind {
                PNodeKind::IdnRef(reference) => reference.name.clone(),
                _ => panic!("type variable has a non-reference identifier"),
            };
            Some(name)
        } else {
            None
        }
    }
    fn generic_parts(&self) -> Option<(String, Vec<PTypeHandle>)> {
        match self.kind() {
            PTypeKind::Domain { domain, args, .. } => {
                let name = match &domain.read().expect("poisoned parse identifier").kind {
                    PNodeKind::IdnRef(reference) => reference.name.clone(),
                    _ => panic!("domain type has a non-reference identifier"),
                };
                Some((name, Self::argument_types(&args)))
            }
            PTypeKind::Seq { element_type, .. } => Some(("Seq".into(), vec![element_type.inner])),
            PTypeKind::Set { element_type, .. } => Some(("Set".into(), vec![element_type.inner])),
            PTypeKind::Multiset { element_type, .. } => {
                Some(("Multiset".into(), vec![element_type.inner]))
            }
            PTypeKind::Map { types, .. } => {
                Some(("Map".into(), vec![types.inner.first, types.inner.second]))
            }
            _ => None,
        }
    }
    fn with_type_arguments(&self, arguments: Vec<PTypeHandle>) -> Self {
        let pos = self.0.read().expect("poisoned parse node").pos.clone();
        match self.kind() {
            PTypeKind::Domain { domain, args, .. } => {
                if arguments.is_empty() && args.is_none() {
                    return self.clone();
                }
                let group = args.expect("domain arguments require existing syntax");
                let delimited = group.inner.clone().update(arguments);
                Self::new(
                    PTypeKind::Domain {
                        domain,
                        args: Some(group.update(delimited)),
                        // `copy` constructs a fresh PDomainType whose mutable
                        // resolution kind starts Unresolved. Substitution
                        // explicitly sets Domain afterward in upstream.
                        kind: PDomainTypeKind::Unresolved,
                    },
                    pos,
                )
            }
            PTypeKind::Seq {
                keyword,
                element_type,
            } => Self::new(
                PTypeKind::Seq {
                    keyword,
                    element_type: element_type.update(arguments[0].clone()),
                },
                pos,
            ),
            PTypeKind::Set {
                keyword,
                element_type,
            } => Self::new(
                PTypeKind::Set {
                    keyword,
                    element_type: element_type.update(arguments[0].clone()),
                },
                pos,
            ),
            PTypeKind::Multiset {
                keyword,
                element_type,
            } => Self::new(
                PTypeKind::Multiset {
                    keyword,
                    element_type: element_type.update(arguments[0].clone()),
                },
                pos,
            ),
            PTypeKind::Map { keyword, types } => {
                let pair = &types.inner;
                let pair = PPairArgument::new(
                    arguments[0].clone(),
                    pair.comma.clone(),
                    arguments[1].clone(),
                    pair.pos.clone(),
                );
                Self::new(
                    PTypeKind::Map {
                        keyword,
                        types: types.update(pair),
                    },
                    pos,
                )
            }
            _ => panic!("type is not generic"),
        }
    }
}

pub type PTypeMismatch = (PTypeHandle, PTypeHandle);
impl PTypeSubstitution {
    pub fn new(
        mappings: std::collections::HashMap<String, PTypeHandle>,
        can_generalise: bool,
    ) -> Self {
        assert!(
            mappings.values().all(PTypeHandle::is_valid_or_undeclared),
            "invalid type substitution"
        );
        let result = Self {
            mappings,
            can_generalise,
        };
        assert!(
            result.is_fully_reduced(),
            "type substitution must be fully reduced"
        );
        result
    }
    pub fn get(&self, name: &str) -> Option<&PTypeHandle> {
        self.mappings.get(name)
    }
    pub fn can_generalise(&self) -> bool {
        self.can_generalise
    }
    pub fn is_fully_reduced(&self) -> bool {
        self.mappings.values().all(|t| {
            t.free_type_variables()
                .iter()
                .all(|name| !self.mappings.contains_key(name))
        })
    }
    pub fn restrict(&self, names: &std::collections::HashSet<String>) -> Self {
        Self {
            mappings: self
                .mappings
                .iter()
                .filter(|(name, _)| names.contains(*name))
                .map(|(a, b)| (a.clone(), b.clone()))
                .collect(),
            can_generalise: self.can_generalise,
        }
    }
    pub fn insert(&self, name: String, typ: PTypeHandle) -> Self {
        assert!(
            !self.mappings.contains_key(&name),
            "duplicate type substitution"
        );
        assert!(typ.is_valid_or_undeclared(), "invalid type substitution");
        let replacement = Self {
            mappings: [(name.clone(), typ.clone())].into_iter().collect(),
            can_generalise: false,
        };
        let mut mappings: std::collections::HashMap<_, _> = self
            .mappings
            .iter()
            .map(|(key, value)| (key.clone(), value.substitute(&replacement)))
            .collect();
        mappings.insert(name, typ);
        let result = Self {
            mappings,
            can_generalise: self.can_generalise,
        };
        assert!(
            result.is_fully_reduced(),
            "type substitution must be fully reduced"
        );
        result
    }
    fn replace(&self, name: &str, typ: PTypeHandle) -> Self {
        assert!(self.can_generalise && self.mappings.contains_key(name));
        let mut result = self.clone();
        result.mappings.insert(name.to_owned(), typ);
        assert!(result.is_fully_reduced());
        result
    }
    pub fn add(&self, a: &PTypeHandle, b: &PTypeHandle) -> Result<Self, PTypeMismatch> {
        let actual = a.substitute(self);
        let expected = b.substitute(self);
        if actual.structurally_equals(&expected) {
            return Ok(self.clone());
        }
        let sup = common_supertype(&actual, &expected);
        if self.can_generalise {
            let mut generalised: Option<Self> = None;
            for (original, current) in [(a, &actual), (b, &expected)] {
                if let (Some(name), Some(common)) = (original.type_variable_name(), &sup) {
                    if is_free_ptv_name(&name) && !common.structurally_equals(current) {
                        generalised = Some(
                            generalised
                                .unwrap_or_else(|| self.clone())
                                .replace(&name, common.clone()),
                        );
                    }
                }
            }
            if let Some(result) = generalised {
                return Ok(result);
            }
        }
        if sup
            .as_ref()
            .is_some_and(|s| s.structurally_equals(&expected))
            || (self.can_generalise && sup.as_ref().is_some_and(|s| s.structurally_equals(&actual)))
        {
            return Ok(self.clone());
        }
        if let Some(name) = actual.type_variable_name().filter(|n| is_free_ptv_name(n)) {
            return Ok(self.insert(name, expected));
        }
        if let Some(name) = expected
            .type_variable_name()
            .filter(|n| is_free_ptv_name(n))
        {
            return Ok(self.insert(name, actual));
        }
        if let (Some((an, aa)), Some((bn, ba))) = (actual.generic_parts(), expected.generic_parts())
        {
            if an == bn {
                let pairs: Vec<_> = aa.into_iter().zip(ba).collect();
                let mut result = self.clone();
                for (left, right) in &pairs {
                    match result.add(left, right) {
                        Ok(next) => result = next,
                        Err((x, y)) => {
                            if let Some(index) = pairs.iter().position(|(l, r)| {
                                l.structurally_equals(&x) && r.structurally_equals(&y)
                            }) {
                                let mut changed = pairs.clone();
                                changed[index] = (x, y);
                                let (lefts, rights): (Vec<_>, Vec<_>) = changed.into_iter().unzip();
                                return Err((
                                    actual.with_type_arguments(lefts),
                                    actual.with_type_arguments(rights),
                                ));
                            }
                            return Err((x, y));
                        }
                    }
                }
                return Ok(result);
            }
        }
        Err((actual, expected))
    }
}

pub fn p_type_var(name: impl Into<String>) -> PTypeHandle {
    let pos = (Position::NoPosition, Position::NoPosition);
    let reference = PNode::new(
        PNodeKind::IdnRef(PIdnRef::with_class(
            name,
            PDeclarationClass::TypeDeclaration,
        )),
        pos.clone(),
    );
    PTypeHandle::new(
        PTypeKind::Domain {
            domain: reference,
            args: None,
            kind: PDomainTypeKind::TypeVar,
        },
        pos,
    )
}
impl PTypeSubstitution {
    pub fn compose(&self, other: &Self) -> Result<Self, PTypeMismatch> {
        let mut result = self.clone();
        for (name, typ) in &other.mappings {
            result = result.add(&p_type_var(name), typ)?;
        }
        Ok(result)
    }
    pub fn substitute_mapping(&self, name: &str, typ: &PTypeHandle) -> Self {
        assert!(
            !self.mappings.contains_key(name),
            "substitution key already exists"
        );
        let replacement = Self::new(
            [(name.to_owned(), typ.clone())].into_iter().collect(),
            false,
        );
        Self::new(
            self.mappings
                .iter()
                .map(|(key, value)| (key.clone(), value.substitute(&replacement)))
                .collect(),
            self.can_generalise,
        )
    }
}
impl PTypeRenaming {
    pub fn rename<'a>(&'a self, name: &'a str) -> &'a str {
        self.mappings.get(name).map_or(name, String::as_str)
    }
    pub fn as_substitution(&self) -> PTypeSubstitution {
        PTypeSubstitution::new(
            self.mappings
                .iter()
                .map(|(key, value)| (key.clone(), p_type_var(value)))
                .collect(),
            false,
        )
    }
}
/// Construction-time pair of a nongeneralising substitution and a generalising delta.
#[derive(Clone, Debug)]
pub struct PTypeSubstitutionInternal {
    base: PTypeSubstitution,
    added: PTypeSubstitution,
}
impl PTypeSubstitutionInternal {
    pub fn new(base: PTypeSubstitution, added: PTypeSubstitution) -> Self {
        assert!(!base.can_generalise && added.can_generalise);
        Self { base, added }
    }
    pub fn get(&self, key: &str) -> Option<&PTypeHandle> {
        self.added.get(key).or_else(|| self.base.get(key))
    }
    pub fn compose(&self, other: &PTypeSubstitution) -> Result<Self, PTypeMismatch> {
        for (key, left) in &self.base.mappings {
            if let Some(right) = other.mappings.get(key) {
                if !left.structurally_equals(right) {
                    return Err((left.clone(), right.clone()));
                }
            }
        }
        let mut mappings: std::collections::HashMap<_, _> = self
            .base
            .mappings
            .iter()
            .map(|(key, value)| (key.clone(), value.substitute(other)))
            .collect();
        mappings.extend(
            other
                .mappings
                .iter()
                .map(|(key, value)| (key.clone(), value.substitute(&self.base))),
        );
        Ok(Self::new(
            PTypeSubstitution::new(mappings, false),
            self.added.clone(),
        ))
    }
    pub fn collapse(&self) -> PTypeSubstitution {
        self.added
            .mappings
            .iter()
            .fold(self.base.clone(), |current, (name, typ)| {
                let replacement = typ.substitute(&current);
                current
                    .substitute_mapping(name, typ)
                    .insert(name.clone(), replacement)
            })
    }
}

pub fn scope_id(node: &PNodeHandle) -> Option<PScopeId> {
    let snapshot = node.read().expect("poisoned parse node").kind.clone();
    match snapshot {
        PNodeKind::Expression(PExpression {
            kind: PExpressionKind::Exists(q) | PExpressionKind::Forall(q),
            ..
        }) => Some(q.scope_id),
        PNodeKind::Expression(PExpression {
            kind: PExpressionKind::ForPerm { scope_id, .. } | PExpressionKind::Let { scope_id, .. },
            ..
        }) => Some(scope_id),
        PNodeKind::Statement(PStatement {
            kind:
                PStatementKind::Seqn { scope_id, .. } | PStatementKind::Quasihavocall { scope_id, .. },
        }) => Some(scope_id),
        PNodeKind::Member(member) => Some(member.scope_id),
        PNodeKind::Extension(extension)
        | PNodeKind::Expression(PExpression {
            kind: PExpressionKind::Extension(extension),
            ..
        })
        | PNodeKind::Statement(PStatement {
            kind: PStatementKind::Extension(extension),
        }) => extension.scope_id(),
        PNodeKind::DomainMember(
            PDomainMember::Function { scope_id, .. } | PDomainMember::Axiom { scope_id, .. },
        ) => Some(scope_id),
        _ => None,
    }
}
pub fn get_enclosing_scope(node: &PNodeHandle) -> Option<PNodeHandle> {
    get_ancestor(node, |ancestor| scope_id(ancestor).is_some())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PMemberCategory {
    Import,
    Define,
    Domain,
    DomainFunction,
    Fields,
    Function,
    Predicate,
    Method,
    Extension,
}
impl PMemberHandle {
    pub fn category(&self) -> PMemberCategory {
        let member = match &self.0.read().expect("poisoned parse node").kind {
            PNodeKind::Member(member) => member.clone(),
            PNodeKind::DomainMember(PDomainMember::Function { .. }) => {
                return PMemberCategory::DomainFunction;
            }
            _ => panic!("parse member handle points to a different node kind"),
        };
        match member.kind {
            PMemberKind::Import { .. } => PMemberCategory::Import,
            PMemberKind::Define { .. } => PMemberCategory::Define,
            PMemberKind::Domain { .. } => PMemberCategory::Domain,
            PMemberKind::Fields { .. } => PMemberCategory::Fields,
            PMemberKind::Function { .. } => PMemberCategory::Function,
            PMemberKind::Predicate { .. } => PMemberCategory::Predicate,
            PMemberKind::Method { .. } => PMemberCategory::Method,
            PMemberKind::Extension(_) => PMemberCategory::Extension,
        }
    }
}
impl PProgramHandle {
    pub fn members_of(&self, category: PMemberCategory) -> Vec<PMemberHandle> {
        self.all_members()
            .into_iter()
            .filter(|member| member.category() == category)
            .collect()
    }
    pub fn filter_members(&self, predicate: &impl Fn(&PMemberHandle) -> bool) -> Self {
        let program = self.snapshot();
        let pos = self.0.read().expect("poisoned parse node").pos.clone();
        let imported = program
            .imported
            .iter()
            .map(|p| p.filter_members(predicate))
            .collect();
        let members = program.members.into_iter().filter(predicate).collect();
        Self::new(
            PProgram {
                imported,
                members,
                local_errors: program.local_errors,
                offsets: program.offsets,
                raw_program: program.raw_program,
            },
            pos,
        )
    }
    pub fn new_imported(&self, more: Vec<PProgramHandle>) -> Self {
        if more.is_empty() {
            return self.clone();
        }
        let mut program = self.snapshot();
        program.imported.extend(more);
        let pos = self.0.read().expect("poisoned parse node").pos.clone();
        Self::new(program, pos)
    }
}

impl PTypeSubstitutionInternal {
    /// Add a constraint using the base map while accumulating new constraints in the generalising delta.
    pub fn add(&self, a: &PTypeHandle, b: &PTypeHandle) -> Result<Self, PTypeMismatch> {
        let actual = a.substitute(&self.base);
        let expected = b.substitute(&self.base);
        if actual.structurally_equals(&expected)
            || common_supertype(&actual, &expected)
                .is_some_and(|s| s.structurally_equals(&expected))
        {
            return Ok(self.clone());
        }
        let insert = |name: String, typ: PTypeHandle| -> Result<Self, PTypeMismatch> {
            let added = self.added.add(&p_type_var(name), &typ)?;
            Ok(Self::new(self.base.clone(), added))
        };
        if let Some(name) = actual.type_variable_name().filter(|n| is_free_ptv_name(n)) {
            return insert(name, expected);
        }
        if let Some(name) = expected
            .type_variable_name()
            .filter(|n| is_free_ptv_name(n))
        {
            return insert(name, actual);
        }
        if let (Some((an, aa)), Some((bn, ba))) = (actual.generic_parts(), expected.generic_parts())
        {
            if an == bn {
                let pairs: Vec<_> = aa.into_iter().zip(ba).collect();
                let mut result = self.clone();
                for (left, right) in &pairs {
                    match result.add(left, right) {
                        Ok(next) => result = next,
                        Err((x, y)) => {
                            if let Some(index) = pairs.iter().position(|(l, r)| {
                                l.structurally_equals(&x) && r.structurally_equals(&y)
                            }) {
                                let mut changed = pairs.clone();
                                changed[index] = (x, y);
                                let (lefts, rights): (Vec<_>, Vec<_>) = changed.into_iter().unzip();
                                return Err((
                                    actual.with_type_arguments(lefts),
                                    actual.with_type_arguments(rights),
                                ));
                            }
                            return Err((x, y));
                        }
                    }
                }
                return Ok(result);
            }
        }
        Err((actual, expected))
    }
}

/// Convert the operator signature vocabulary to the parser's syntactic type representation.
pub fn type_from_signature(pattern: &super::parse_ast_keyword::SignatureType) -> PTypeHandle {
    use super::parse_ast_keyword::{PGrouped, PKw, PReserved, PSym, SignatureType};
    let pos = (Position::NoPosition, Position::NoPosition);
    match pattern {
        SignatureType::Int => PTypeHandle::new(
            PTypeKind::Primitive {
                name: PReserved::implied(PKw::Int),
            },
            pos,
        ),
        SignatureType::Bool => PTypeHandle::new(
            PTypeKind::Primitive {
                name: PReserved::implied(PKw::Bool),
            },
            pos,
        ),
        SignatureType::Perm => PTypeHandle::new(
            PTypeKind::Primitive {
                name: PReserved::implied(PKw::Perm),
            },
            pos,
        ),
        SignatureType::Ref => PTypeHandle::new(
            PTypeKind::Primitive {
                name: PReserved::implied(PKw::Ref),
            },
            pos,
        ),
        SignatureType::Impure => PTypeHandle::new(PTypeKind::BoolImpure, pos),
        SignatureType::Wand => PTypeHandle::new(PTypeKind::BoolWand, pos),
        SignatureType::Predicate => PTypeHandle::new(PTypeKind::BoolPredicate, pos),
        SignatureType::Var(name) => p_type_var(*name),
        SignatureType::Seq(t) | SignatureType::Set(t) | SignatureType::Multiset(t) => {
            let element_type =
                PGrouped::implied(PSym::LBracket, type_from_signature(t), PSym::RBracket);
            let (keyword, kind) = match pattern {
                SignatureType::Seq(_) => (PKw::Seq, 0),
                SignatureType::Set(_) => (PKw::Set, 1),
                _ => (PKw::Multiset, 2),
            };
            let keyword = PReserved::implied(keyword);
            let kind = match kind {
                0 => PTypeKind::Seq {
                    keyword,
                    element_type,
                },
                1 => PTypeKind::Set {
                    keyword,
                    element_type,
                },
                _ => PTypeKind::Multiset {
                    keyword,
                    element_type,
                },
            };
            PTypeHandle::new(kind, pos)
        }
        SignatureType::Map(key, value) => {
            let pair = PPairArgument::new(
                type_from_signature(key),
                PReserved::implied(PSym::Comma),
                type_from_signature(value),
                pos.clone(),
            );
            let types = PGrouped::implied(PSym::LBracket, pair, PSym::RBracket);
            PTypeHandle::new(
                PTypeKind::Map {
                    keyword: PReserved::implied(PKw::Map),
                    types,
                },
                pos,
            )
        }
    }
}
pub fn substitution_from_signature(
    signature: &super::parse_ast_keyword::OperatorSignature,
) -> PTypeSubstitution {
    PTypeSubstitution::new(
        signature
            .iter()
            .map(|(name, typ)| ((*name).to_owned(), type_from_signature(typ)))
            .collect(),
        false,
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForceSubstitutionError {
    ExtensionNotImplemented,
}
impl PExpHandle {
    fn snapshot(&self) -> PExpression {
        match &self.0.read().expect("poisoned parse node").kind {
            PNodeKind::Expression(exp) => exp.clone(),
            _ => panic!("parse expression handle points to a different node kind"),
        }
    }
    fn update(&self, f: impl FnOnce(&mut PExpression)) {
        match &mut self.0.write().expect("poisoned parse node").kind {
            PNodeKind::Expression(exp) => f(exp),
            _ => panic!("parse expression handle points to a different node kind"),
        }
    }
    /// Apply the source's force-substitution rules; extension-owned behavior remains explicit.
    pub fn force_substitution(
        &self,
        substitution: &PTypeSubstitution,
    ) -> Result<(), ForceSubstitutionError> {
        use PExpressionKind::*;
        let expression = self.snapshot();
        match expression.kind.clone() {
            Extension(extension) => {
                if extension.as_any().is::<crate::plugin::standard::arp::arppast_extension::PRdPerm>() { Ok(()) }
                else if let Some(sif) = extension.as_any().downcast_ref::<crate::plugin::sif::sifp_ast_extensions::PSifExpression>() { sif.force_substitution(substitution) }
                else if let Some(instance) = extension.as_any().downcast_ref::<crate::plugin::standard::predicateinstance::predicate_instance_past_extension::PPredicateInstance>() { instance.force_substitution(substitution) }
                else if let Some(clause) = extension.as_any().downcast_ref::<crate::plugin::standard::termination::termination_past_extension::PDecreasesClause>() { clause.force_substitution(substitution); Ok(()) }
                else { Err(ForceSubstitutionError::ExtensionNotImplemented) }
            }
            IntLit(_)
            | ResultLit(_)
            | BoolLit(_)
            | NullLit(_)
            | NoPerm(_)
            | FullPerm(_)
            | Wildcard(_)
            | Epsilon(_)
            | NewExp { .. } => Ok(()),
            AnnotatedExp { expression, .. } => expression.force_substitution(substitution),
            IdnUse { .. } | VersionedIdnUse { .. } => {
                let typ = expression.typ.substitute(substitution);
                assert!(typ.is_ground());
                self.update(|exp| exp.typ = typ);
                Ok(())
            }
            Exists(q) | Forall(q) => {
                let typ = expression.typ.substitute(substitution);
                self.update(|exp| {
                    exp.type_substitutions = Some(vec![substitution.clone()]);
                    exp.typ = typ;
                });
                q.body.force_substitution(substitution)
            }
            ForPerm { body, .. } => {
                let typ = expression.typ.substitute(substitution);
                self.update(|exp| {
                    exp.type_substitutions = Some(vec![substitution.clone()]);
                    exp.typ = typ;
                });
                body.force_substitution(substitution)
            }
            Let {
                exp, nested_scope, ..
            } => {
                exp.inner.force_substitution(substitution)?;
                let body = match &nested_scope.read().expect("poisoned parse node").kind {
                    PNodeKind::LetNestedScope { body } => body.clone(),
                    _ => panic!("let nested scope has the wrong node kind"),
                };
                body.force_substitution(substitution)?;
                let typ = body.snapshot().typ;
                self.update(|exp| exp.typ = typ);
                Ok(())
            }
            kind => {
                let mut effective = substitution.clone();
                if let Call {
                    domain_type_renaming: Some(renaming),
                    ..
                } = &kind
                {
                    let default =
                        type_from_signature(&super::parse_ast_keyword::SignatureType::Int);
                    let domain_mappings = renaming
                        .mappings
                        .iter()
                        .map(|(original, fresh)| {
                            (
                                original.clone(),
                                substitution
                                    .get(fresh)
                                    .cloned()
                                    .unwrap_or_else(|| default.clone()),
                            )
                        })
                        .collect();
                    let domain_substitution = PTypeSubstitution::new(domain_mappings, false);
                    assert!(
                        domain_substitution
                            .mappings
                            .values()
                            .all(PTypeHandle::is_ground)
                    );
                    for fresh in renaming.mappings.values() {
                        if effective.get(fresh).is_none() {
                            effective = effective
                                .add(&p_type_var(fresh), &default)
                                .expect("default type substitution failed");
                        }
                    }
                    self.update(|exp| {
                        if let Call {
                            domain_substitution: slot,
                            ..
                        } = &mut exp.kind
                        {
                            *slot = Some(domain_substitution);
                        }
                    });
                }
                let typ = expression.typ.substitute(&effective);
                assert!(typ.is_ground());
                self.update(|exp| {
                    exp.type_substitutions = Some(vec![effective.clone()]);
                    exp.typ = typ;
                });
                for arg in expression_args(kind) {
                    arg.force_substitution(&effective)?;
                }
                Ok(())
            }
        }
    }
}
fn expression_args(kind: PExpressionKind) -> Vec<PExpHandle> {
    use PExpressionKind::*;
    let list = |args: PExpArguments| args.inner.to_seq().into_iter().cloned().collect::<Vec<_>>();
    match kind {
        BinExp { left, right, .. } | MagicWandExp { left, right, .. } => vec![left, right],
        UnExp { exp, .. } => vec![exp],
        CondExp { cond, thn, els, .. } => vec![cond, thn, els],
        FieldAccess { receiver, .. } => vec![receiver],
        InhaleExhale { inhale, exhale, .. } => vec![inhale, exhale],
        Call { call_args, .. } => list(call_args),
        Unfolding { acc, exp, .. } => vec![acc, exp],
        Applying { wand, exp, .. } => vec![wand, exp],
        Asserting { assertion, exp, .. } => vec![assertion, exp],
        RangeSeq { low, high, .. } => vec![low, high],
        Lookup { base, index, .. } => vec![base, index],
        SeqSlice {
            seq, start, end, ..
        } => std::iter::once(seq).chain(start).chain(end).collect(),
        Update {
            base, key, value, ..
        } => vec![base, key, value],
        Size { seq, .. } => vec![seq],
        Maplet { key, value, .. } => vec![key, value],
        CurrentPerm { resource, .. } => vec![resource.inner],
        AccPred { amount, .. } => std::iter::once(amount.inner.first)
            .chain(amount.inner.second.map(|(_, e)| e))
            .collect(),
        OldExp { exp, .. } => vec![exp.inner],
        DebugLabelledOldExp { exp, .. } => vec![exp],
        EmptySeq(c) | EmptySet(c) | EmptyMultiset(c) => list(c.call_args),
        ExplicitSeq(c) | ExplicitSet(c) | ExplicitMultiset(c) => list(c.call_args),
        ExplicitMap(c) => list(c.call_args),
        EmptyMap { call_args, .. } => list(call_args),
        MapDomain { base, .. } | MapRange { base, .. } => vec![base.inner],
        _ => panic!("expression has no operator arguments"),
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperatorSignaturesError {
    NotOperator,
    ExtensionNotImplemented,
}
fn make_collection_type(keyword: super::parse_ast_keyword::PKw, typ: PTypeHandle) -> PTypeHandle {
    use super::parse_ast_keyword::{PGrouped, PKw, PReserved, PSym};
    if matches!(typ.kind(), PTypeKind::Unknown) {
        return internal_type(PTypeKind::Unknown);
    }
    let element_type = PGrouped::implied(PSym::LBracket, typ, PSym::RBracket);
    let token = PReserved::implied(keyword);
    let kind = match keyword {
        PKw::Seq => PTypeKind::Seq {
            keyword: token,
            element_type,
        },
        PKw::Set => PTypeKind::Set {
            keyword: token,
            element_type,
        },
        PKw::Multiset => PTypeKind::Multiset {
            keyword: token,
            element_type,
        },
        _ => panic!("not a collection keyword"),
    };
    internal_type(kind)
}
fn make_map_type(key: PTypeHandle, value: PTypeHandle) -> PTypeHandle {
    use super::parse_ast_keyword::{PGrouped, PKw, PReserved, PSym};
    if matches!(key.kind(), PTypeKind::Unknown) || matches!(value.kind(), PTypeKind::Unknown) {
        return internal_type(PTypeKind::Unknown);
    }
    let pos = (Position::NoPosition, Position::NoPosition);
    let pair = PPairArgument::new(key, PReserved::implied(PSym::Comma), value, pos.clone());
    PTypeHandle::new(
        PTypeKind::Map {
            keyword: PReserved::implied(PKw::Map),
            types: PGrouped::implied(PSym::LBracket, pair, PSym::RBracket),
        },
        pos,
    )
}
fn signature_bindings(pairs: Vec<(String, PTypeHandle)>) -> PTypeSubstitution {
    PTypeSubstitution::new(pairs.into_iter().collect(), false)
}
fn signature_patterns(
    pairs: &[(&'static str, super::parse_ast_keyword::SignatureType)],
) -> PTypeSubstitution {
    substitution_from_signature(&pairs.to_vec())
}
impl PExpHandle {
    /// Ordered static overloads; calls and extensions need their respective resolution interfaces.
    pub fn signatures(&self) -> Result<Vec<PTypeSubstitution>, OperatorSignaturesError> {
        use super::parse_ast_keyword::{PKw, SignatureType as T};
        use PExpressionKind::*;
        let signature = |items: Vec<(&'static str, T)>| signature_patterns(&items);
        Ok(match self.snapshot().kind {
            BinExp { op, .. } => op
                .value()
                .signatures()
                .ok_or(OperatorSignaturesError::NotOperator)?,
            MagicWandExp { wand, .. } | UnExp { op: wand, .. } => wand
                .value()
                .signatures()
                .ok_or(OperatorSignaturesError::NotOperator)?
                .iter()
                .map(substitution_from_signature)
                .collect(),
            CondExp { .. } => vec![signature(vec![
                ("#T0", T::Bool),
                ("#T2", T::Var("#T1")),
                ("#R", T::Var("#T1")),
            ])],
            FieldAccess {
                receiver, idnref, ..
            } => {
                let declarations = PIdnRef::decls(&idnref, |d| {
                    matches!(
                        &d.read().expect("poisoned parse node").kind,
                        PNodeKind::Declaration(PDeclaration {
                            kind: PDeclarationKind::Field { .. },
                            ..
                        })
                    )
                });
                if declarations.len() != 1 {
                    Vec::new()
                } else {
                    let field = match &declarations[0].read().expect("poisoned parse node").kind {
                        PNodeKind::Declaration(decl) => decl.clone(),
                        _ => unreachable!(),
                    };
                    if !field.typ.is_valid_or_undeclared()
                        || !receiver.snapshot().typ.is_valid_or_undeclared()
                    {
                        Vec::new()
                    } else {
                        vec![signature_bindings(vec![
                            ("#T0".into(), type_from_signature(&T::Ref)),
                            ("#R".into(), field.typ),
                        ])]
                    }
                }
            }
            Unfolding { .. } => vec![signature(vec![
                ("#T0", T::Predicate),
                ("#R", T::Var("#T1")),
            ])],
            Applying { .. } => vec![signature(vec![("#T0", T::Wand), ("#R", T::Var("#T1"))])],
            Asserting { .. } => vec![signature(vec![("#T0", T::Impure), ("#R", T::Var("#T1"))])],
            InhaleExhale { .. } => vec![
                signature(vec![("#T0", T::Bool), ("#T1", T::Bool), ("#R", T::Bool)]),
                signature(vec![
                    ("#T0", T::Impure),
                    ("#T1", T::Impure),
                    ("#R", T::Impure),
                ]),
            ],
            CurrentPerm { .. } => vec![signature(vec![("#R", T::Perm)])],
            AccPred { .. } => vec![
                signature(vec![
                    ("#T0", T::Predicate),
                    ("#T1", T::Perm),
                    ("#R", T::Predicate),
                ]),
                signature(vec![("#T1", T::Perm), ("#R", T::Impure)]),
            ],
            OldExp { .. } | DebugLabelledOldExp { .. } => {
                vec![signature(vec![("#R", T::Var("#T0"))])]
            }
            RangeSeq { .. } => vec![signature(vec![
                ("#T0", T::Int),
                ("#T1", T::Int),
                ("#R", T::Seq(Box::new(T::Int))),
            ])],
            Lookup { .. } => vec![
                signature(vec![
                    ("#T0", T::Seq(Box::new(T::Var("#R")))),
                    ("#T1", T::Int),
                ]),
                signature(vec![(
                    "#T0",
                    T::Map(Box::new(T::Var("#T1")), Box::new(T::Var("#R"))),
                )]),
            ],
            SeqSlice { start, end, .. } => {
                let mut pairs = vec![
                    ("#T0", T::Seq(Box::new(T::Var("#E")))),
                    ("#R", T::Seq(Box::new(T::Var("#E")))),
                ];
                if start.is_some() || end.is_some() {
                    pairs.push(("#T1", T::Int));
                }
                if start.is_some() && end.is_some() {
                    pairs.push(("#T2", T::Int));
                }
                vec![signature(pairs)]
            }
            Update { .. } => vec![
                signature(vec![
                    ("#T0", T::Seq(Box::new(T::Var("#T2")))),
                    ("#T1", T::Int),
                    ("#R", T::Seq(Box::new(T::Var("#T2")))),
                ]),
                signature(vec![
                    (
                        "#T0",
                        T::Map(Box::new(T::Var("#T1")), Box::new(T::Var("#T2"))),
                    ),
                    (
                        "#R",
                        T::Map(Box::new(T::Var("#T1")), Box::new(T::Var("#T2"))),
                    ),
                ]),
            ],
            Size { .. } => vec![
                T::Seq(Box::new(T::Var("#E"))),
                T::Set(Box::new(T::Var("#E"))),
                T::Multiset(Box::new(T::Var("#E"))),
                T::Map(Box::new(T::Var("#K")), Box::new(T::Var("#E"))),
            ]
            .into_iter()
            .map(|t| signature(vec![("#T0", t), ("#R", T::Int)]))
            .collect(),
            EmptySeq(c) | EmptySet(c) | EmptyMultiset(c) => {
                let keyword = match c.op.value() {
                    super::parse_ast_keyword::PKwOp::Seq => PKw::Seq,
                    super::parse_ast_keyword::PKwOp::Set => PKw::Set,
                    super::parse_ast_keyword::PKwOp::Multiset => PKw::Multiset,
                    _ => panic!("wrong collection operator"),
                };
                let typ = c
                    .annotated_type
                    .map(|g| g.inner)
                    .unwrap_or_else(|| p_type_var("#E"));
                vec![signature_bindings(vec![(
                    "#R".into(),
                    make_collection_type(keyword, typ),
                )])]
            }
            ExplicitSeq(c) | ExplicitSet(c) | ExplicitMultiset(c) => {
                assert!(
                    !c.call_args.inner.is_empty(),
                    "explicit collection literal must be nonempty"
                );
                let keyword = match c.op.value() {
                    super::parse_ast_keyword::PKwOp::Seq => PKw::Seq,
                    super::parse_ast_keyword::PKwOp::Set => PKw::Set,
                    super::parse_ast_keyword::PKwOp::Multiset => PKw::Multiset,
                    _ => panic!("wrong collection operator"),
                };
                let mut pairs = Vec::new();
                for n in 0..c.call_args.inner.len() {
                    if n == 0 {
                        pairs.push((
                            "#R".into(),
                            make_collection_type(keyword, p_type_var("#T0")),
                        ));
                    } else {
                        pairs.push((format!("#T{n}"), p_type_var("#T0")));
                    }
                }
                vec![signature_bindings(pairs)]
            }
            EmptyMap { annotated_type, .. } => {
                let (key, value) = annotated_type
                    .map(|g| (g.inner.first, g.inner.second))
                    .unwrap_or_else(|| (p_type_var("#K"), p_type_var("#E")));
                vec![signature_bindings(vec![(
                    "#R".into(),
                    make_map_type(key, value),
                )])]
            }
            ExplicitMap(c) => {
                let pairs = (0..c.call_args.inner.len())
                    .map(|n| {
                        (
                            if n == 0 {
                                "#R".into()
                            } else {
                                format!("#T{n}")
                            },
                            p_type_var("#T0"),
                        )
                    })
                    .collect();
                vec![signature_bindings(pairs)]
            }
            Maplet { .. } => vec![signature_bindings(vec![(
                "#R".into(),
                make_map_type(p_type_var("#T0"), p_type_var("#T1")),
            )])],
            MapDomain { .. } | MapRange { .. } => {
                let is_domain = matches!(self.snapshot().kind, MapDomain { .. });
                vec![signature_bindings(vec![
                    (
                        "#T0".into(),
                        make_map_type(p_type_var("#K"), p_type_var("#E")),
                    ),
                    (
                        "#R".into(),
                        make_collection_type(
                            PKw::Set,
                            p_type_var(if is_domain { "#K" } else { "#E" }),
                        ),
                    ),
                ])]
            }
            Call {
                idnref,
                call_args,
                domain_type_renaming,
                ..
            } => call_signatures(
                &idnref,
                call_args.inner.len(),
                domain_type_renaming.as_ref(),
            ),
            Extension(_) => return Err(OperatorSignaturesError::ExtensionNotImplemented),
            _ => return Err(OperatorSignaturesError::NotOperator),
        })
    }
}

fn call_signatures(
    idnref: &PNodeHandle,
    argument_count: usize,
    renaming: Option<&PTypeRenaming>,
) -> Vec<PTypeSubstitution> {
    let declarations = PIdnRef::decls(idnref, |node| {
        match &node.read().expect("poisoned parse node").kind {
            PNodeKind::Member(PMember {
                kind:
                    PMemberKind::Function { .. }
                    | PMemberKind::Predicate { .. }
                    | PMemberKind::Method { .. },
                ..
            }) => true,
            PNodeKind::DomainMember(PDomainMember::Function { .. }) => true,
            _ => false,
        }
    });
    if declarations.len() != 1 {
        return Vec::new();
    }
    let kind = declarations[0]
        .read()
        .expect("poisoned parse node")
        .kind
        .clone();
    let (arguments, result) = match kind {
        PNodeKind::Member(PMember {
            kind: PMemberKind::Function {
                args, result_type, ..
            },
            ..
        }) => {
            let args = args
                .inner
                .to_seq()
                .into_iter()
                .map(
                    |arg| match &arg.node().read().expect("poisoned parse declaration").kind {
                        PNodeKind::Declaration(decl) => decl.typ.clone(),
                        _ => panic!("formal argument has the wrong node kind"),
                    },
                )
                .collect::<Vec<_>>();
            (args, result_type)
        }
        PNodeKind::Member(PMember {
            kind: PMemberKind::Predicate { args, .. },
            ..
        }) => {
            let args = args
                .inner
                .to_seq()
                .into_iter()
                .map(
                    |arg| match &arg.node().read().expect("poisoned parse declaration").kind {
                        PNodeKind::Declaration(decl) => decl.typ.clone(),
                        _ => panic!("formal argument has the wrong node kind"),
                    },
                )
                .collect::<Vec<_>>();
            (args, internal_type(PTypeKind::BoolPredicate))
        }
        PNodeKind::DomainMember(PDomainMember::Function {
            args, result_type, ..
        }) => {
            let Some(renaming) = renaming else {
                return Vec::new();
            };
            let substitution = renaming.as_substitution();
            let args = args
                .inner
                .to_seq()
                .into_iter()
                .map(|arg| arg.typ.substitute(&substitution))
                .collect();
            (args, result_type.substitute(&substitution))
        }
        _ => return Vec::new(),
    };
    if arguments.len() != argument_count {
        return Vec::new();
    }
    let mut bindings: Vec<_> = arguments
        .into_iter()
        .enumerate()
        .map(|(i, typ)| (format!("#T{i}"), typ))
        .collect();
    bindings.push(("#R".into(), result));
    vec![signature_bindings(bindings)]
}

impl PTypeSubstitution {
    pub fn structurally_equals(&self, other: &Self) -> bool {
        self.can_generalise == other.can_generalise
            && self.mappings.len() == other.mappings.len()
            && self.mappings.iter().all(|(key, value)| {
                other
                    .get(key)
                    .is_some_and(|other| value.structurally_equals(other))
            })
    }
}
impl PExpHandle {
    /// `None` corresponds to an uninitialized binder substitution list.
    pub fn type_substitutions(&self) -> Option<Vec<PTypeSubstitution>> {
        match self.snapshot() {
            PExpression {
                kind: PExpressionKind::AnnotatedExp { expression, .. },
                ..
            } => expression.type_substitutions(),
            PExpression {
                kind:
                    PExpressionKind::Let {
                        exp, nested_scope, ..
                    },
                ..
            } => {
                let body = match &nested_scope.read().expect("poisoned parse node").kind {
                    PNodeKind::LetNestedScope { body } => body.clone(),
                    _ => panic!("let nested scope has the wrong node kind"),
                };
                let bodies = body.type_substitutions()?;
                let values = exp.inner.type_substitutions()?;
                let mut result: Vec<PTypeSubstitution> = Vec::new();
                for body in &bodies {
                    for value in &values {
                        if let Ok(combined) = body.compose(value) {
                            if !result.iter().any(|old| old.structurally_equals(&combined)) {
                                result.push(combined);
                            }
                        }
                    }
                }
                Some(result)
            }
            expression => expression.type_substitutions,
        }
    }
    pub fn type_subs_distinct(&self) -> Option<Vec<PTypeSubstitution>> {
        let mut unique: Vec<PTypeSubstitution> = Vec::new();
        for substitution in self.type_substitutions()? {
            if !unique
                .iter()
                .any(|old| old.structurally_equals(&substitution))
            {
                unique.push(substitution);
            }
        }
        Some(
            unique
                .iter()
                .enumerate()
                .filter(|(i, sub)| {
                    unique.iter().enumerate().all(|(j, sup)| {
                        i == &j
                            || !sub.mappings.iter().all(|(name, typ)| {
                                sup.get(name).is_some_and(|other| is_subtype(other, typ))
                            })
                    })
                })
                .map(|(_, sub)| sub.clone())
                .collect(),
        )
    }
}

impl PExpHandle {
    pub fn full_perm_implied() -> Self {
        let pos = (Position::NoPosition, Position::NoPosition);
        let token =
            super::parse_ast_keyword::PReserved::implied(super::parse_ast_keyword::PKw::Write);
        Self::new(
            PExpression::from_kind(PExpressionKind::FullPerm(token)),
            pos,
        )
    }
    /// Access assertions and calls default an omitted permission to full permission.
    pub fn access_permission(&self) -> Option<Self> {
        match self.snapshot().kind {
            PExpressionKind::Call { .. } => Some(Self::full_perm_implied()),
            PExpressionKind::AccPred { amount, .. } => Some(
                amount
                    .inner
                    .second
                    .map(|(_, permission)| permission)
                    .unwrap_or_else(Self::full_perm_implied),
            ),
            _ => None,
        }
    }
    pub fn access_location(&self) -> Option<Self> {
        match self.snapshot().kind {
            PExpressionKind::Call { .. } => Some(self.clone()),
            PExpressionKind::AccPred { amount, .. } => Some(amount.inner.first),
            _ => None,
        }
    }
    pub fn bool_value(&self) -> Option<bool> {
        match self.snapshot().kind {
            PExpressionKind::BoolLit(token) => match token.value() {
                super::parse_ast_keyword::PKw::True => Some(true),
                super::parse_ast_keyword::PKw::False => Some(false),
                _ => panic!("boolean literal has a nonboolean keyword"),
            },
            _ => None,
        }
    }
}

/// Parsing-only binding; this helper is not itself a graph node upstream.
#[derive(Clone, Debug)]
pub struct PIdnTypeBinding {
    pub idndef: PNodeHandle,
    pub colon: SymbolToken,
    pub typ: PTypeHandle,
    pub pos: Span,
}
impl PDomainFunctionArg {
    pub fn from_binding(binding: PIdnTypeBinding) -> Self {
        Self::new(
            Some(binding.idndef),
            Some(binding.colon),
            binding.typ,
            binding.pos,
        )
    }
}
impl PDeclarationHandle {
    /// Resolver links a field to its PFields declaration before checking its type.
    pub fn set_field_owner(&self, owner: &PMemberHandle) {
        let annotations = match &owner.0.read().expect("poisoned parse node").kind {
            PNodeKind::Member(PMember {
                kind: PMemberKind::Fields { .. },
                annotations,
                ..
            }) => annotations.clone(),
            _ => panic!("field owner must be PFields"),
        };
        let mut node = self.0.write().expect("poisoned parse node");
        match &mut node.kind {
            PNodeKind::Declaration(PDeclaration {
                kind:
                    PDeclarationKind::Field {
                        fields,
                        annotations: cached,
                    },
                ..
            }) => {
                *fields = Some(Arc::downgrade(owner.node()));
                *cached = annotations;
            }
            _ => panic!("expected a field declaration"),
        }
    }
    pub fn field_annotations(&self) -> Vec<PAnnotation> {
        let (owner, cached) = match &self.0.read().expect("poisoned parse node").kind {
            PNodeKind::Declaration(PDeclaration {
                kind:
                    PDeclarationKind::Field {
                        fields,
                        annotations,
                    },
                ..
            }) => (fields.as_ref().and_then(Weak::upgrade), annotations.clone()),
            _ => panic!("expected a field declaration"),
        };
        match owner {
            Some(owner) => match &owner.read().expect("poisoned parse node").kind {
                PNodeKind::Member(PMember {
                    kind: PMemberKind::Fields { .. },
                    annotations,
                    ..
                }) => annotations.to_vec(),
                _ => panic!("field owner must be PFields"),
            },
            None => cached.to_vec(),
        }
    }
    pub fn from_binding(kind: PDeclarationKind, binding: PIdnTypeBinding) -> Self {
        Self::new(
            PDeclaration {
                kind,
                idndef: binding.idndef,
                colon: binding.colon,
                typ: binding.typ,
            },
            binding.pos,
        )
    }
    /// Typed variables can produce a resolved identifier-use expression.
    pub fn to_idn_use(&self) -> Result<PExpHandle, &'static str> {
        let declaration = match &self.0.read().expect("poisoned parse node").kind {
            PNodeKind::Declaration(decl) => decl.clone(),
            _ => panic!("declaration handle points to a different node kind"),
        };
        if matches!(declaration.kind, PDeclarationKind::Field { .. }) {
            return Err("field is not a typed variable declaration");
        }
        let (name, pos) = {
            let guard = declaration.idndef.read().expect("poisoned parse node");
            let name = match &guard.kind {
                PNodeKind::IdnDef(def) => def.name.clone(),
                _ => panic!("declaration has a non-definition identifier"),
            };
            (name, guard.pos.clone())
        };
        let mut reference = PIdnRef::with_class(name, PDeclarationClass::TypedVar);
        reference.new_decl(&self.0);
        let idnref = PNode::new(PNodeKind::IdnRef(reference), pos.clone());
        let mut expression = PExpression::from_kind(PExpressionKind::IdnUse { idnref });
        expression.typ = declaration.typ;
        Ok(PExpHandle::new(expression, pos))
    }
}

impl PStmtHandle {
    pub fn vars_assign(&self) -> Result<Option<PStmtHandle>, &'static str> {
        let (kind, pos) = {
            let node = self.0.read().expect("poisoned parse node");
            match &node.kind {
                PNodeKind::Statement(stmt) => (stmt.kind.clone(), node.pos.clone()),
                PNodeKind::Member(PMember {
                    kind: PMemberKind::Define { .. },
                    ..
                }) => return Err("statement is not a variable declaration"),
                _ => panic!("statement handle points to a different node kind"),
            }
        };
        match kind {
            PStatementKind::Vars {
                vars,
                init: Some((op, rhs)),
                ..
            } => {
                let targets = vars
                    .to_seq()
                    .into_iter()
                    .map(PDeclarationHandle::to_idn_use)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Some(Self::new(
                    PStatement {
                        kind: PStatementKind::Assign {
                            targets: vars.update(targets),
                            op: Some(op),
                            rhs,
                        },
                    },
                    pos,
                )))
            }
            PStatementKind::Vars { init: None, .. } => Ok(None),
            _ => Err("statement is not a variable declaration"),
        }
    }
}

pub fn fresh_type_var(old: &PTypeHandle) -> PTypeHandle {
    let name = old
        .type_variable_name()
        .expect("fresh type variable requires a type-variable node");
    p_type_var(fresh_type_variable_name(&name))
}
pub fn fresh_type_substitution_ptvs(variables: &[PTypeHandle]) -> PTypeRenaming {
    let names: Vec<_> = variables
        .iter()
        .map(|v| {
            v.type_variable_name()
                .expect("expected a type-variable node")
        })
        .collect();
    fresh_type_renaming(&names, None)
}
impl PTypeRenaming {
    pub fn get_s(&self, name: &str) -> Option<&str> {
        self.mappings.get(name).map(String::as_str)
    }
    pub fn with_mapping(&self, name: String, value: String) -> Self {
        let mut mappings = self.mappings.clone();
        mappings.insert(name, value);
        Self { mappings }
    }
}
impl PTypeSubstitution {
    pub fn contains(&self, name: &str) -> bool {
        self.mappings.contains_key(name)
    }
    pub fn key_set(&self) -> std::collections::HashSet<String> {
        self.mappings.keys().cloned().collect()
    }
    pub fn without(&self, name: &str) -> Self {
        let mut mappings = self.mappings.clone();
        mappings.remove(name);
        Self::new(mappings, self.can_generalise)
    }
    pub fn iter(&self) -> impl Iterator<Item = (&String, &PTypeHandle)> {
        self.mappings.iter()
    }
}
impl PTypeSubstitutionInternal {
    pub fn key_set(&self) -> std::collections::HashSet<String> {
        self.base
            .key_set()
            .union(&self.added.key_set())
            .cloned()
            .collect()
    }
}

pub fn visit(
    root: &PNodeHandle,
    enter: &mut impl FnMut(&PNodeHandle),
    exit: &mut impl FnMut(&PNodeHandle),
) -> Result<(), ChildrenNotPorted> {
    enter(root);
    for child in subnodes(root)? {
        visit(&child, enter, exit)?;
    }
    exit(root);
    Ok(())
}
pub fn visit_opt(
    root: &PNodeHandle,
    enter: &mut impl FnMut(&PNodeHandle) -> bool,
    exit: &mut impl FnMut(&PNodeHandle),
) -> Result<(), ChildrenNotPorted> {
    if enter(root) {
        for child in subnodes(root)? {
            visit_opt(&child, enter, exit)?;
        }
    }
    exit(root);
    Ok(())
}
pub fn reduce_tree<R>(
    root: &PNodeHandle,
    combine: &mut impl FnMut(&PNodeHandle, Vec<R>) -> R,
) -> Result<R, ChildrenNotPorted> {
    let children = subnodes(root)?
        .iter()
        .map(|child| reduce_tree(child, combine))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(combine(root, children))
}
pub fn reduce_with_context<C: Clone, R>(
    root: &PNodeHandle,
    context: C,
    enter: &mut impl FnMut(&PNodeHandle, &C) -> C,
    combine: &mut impl FnMut(&PNodeHandle, &C, Vec<R>) -> R,
) -> Result<R, ChildrenNotPorted> {
    let next = enter(root, &context);
    let children = subnodes(root)?
        .iter()
        .map(|child| reduce_with_context(child, next.clone(), enter, combine))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(combine(root, &context, children))
}
pub fn deep_collect<R>(
    root: &PNodeHandle,
    f: &mut impl FnMut(&PNodeHandle) -> Option<R>,
) -> Result<Vec<R>, ChildrenNotPorted> {
    reduce_tree(root, &mut |node, children: Vec<Vec<R>>| {
        let mut result: Vec<R> = f(node).into_iter().collect();
        result.extend(children.into_iter().flatten());
        result
    })
}
pub fn shallow_collect<R>(
    root: &PNodeHandle,
    f: &mut impl FnMut(&PNodeHandle) -> Option<R>,
) -> Result<Vec<R>, ChildrenNotPorted> {
    if let Some(value) = f(root) {
        return Ok(vec![value]);
    }
    let mut result = Vec::new();
    for child in subnodes(root)? {
        result.extend(shallow_collect(&child, f)?);
    }
    Ok(result)
}

/// Annotations paired with the parser's exact file endpoints for a top-level member.
#[derive(Clone, Debug)]
pub struct PAnnotationsPosition {
    pub annotations: Vec<PAnnotation>,
    pub pos: (
        crate::ast::position::FilePosition,
        crate::ast::position::FilePosition,
    ),
}

/// Extension-owned nodes need an equality implementation from their plugin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExtensionEqualityUnavailable;

fn source_node_equals(
    a: &PNodeHandle,
    b: &PNodeHandle,
) -> Result<bool, ExtensionEqualityUnavailable> {
    if Arc::ptr_eq(a, b) {
        return Ok(true);
    }
    let left = a.read().expect("poisoned parse node").kind.clone();
    let right = b.read().expect("poisoned parse node").kind.clone();
    // An extension can define equality against other node classes too; its
    // result is not known merely because the other discriminant differs.
    fn is_extension(kind: &PNodeKind) -> bool {
        matches!(
            kind,
            PNodeKind::Extension(_)
                | PNodeKind::Expression(PExpression {
                    kind: PExpressionKind::Extension(_),
                    ..
                })
                | PNodeKind::Statement(PStatement {
                    kind: PStatementKind::Extension(_)
                })
                | PNodeKind::Member(PMember {
                    kind: PMemberKind::Extension(_),
                    ..
                })
        )
    }
    if is_extension(&left) || is_extension(&right) {
        return Err(ExtensionEqualityUnavailable);
    }
    match (&left, &right) {
        (PNodeKind::IdnDef(a), PNodeKind::IdnDef(b)) => return Ok(a.name == b.name),
        (PNodeKind::IdnRef(a), PNodeKind::IdnRef(b)) => return Ok(a.name == b.name),
        (PNodeKind::Reserved(a), PNodeKind::Reserved(b)) => return Ok(a == b),
        (PNodeKind::RawString(a), PNodeKind::RawString(b)) => return Ok(a == b),
        (PNodeKind::Type(_), PNodeKind::Type(_)) => {
            reject_extension_equality(a)?;
            reject_extension_equality(b)?;
            let a = PTypeHandle::from_node(a.clone()).expect("expected type");
            let b = PTypeHandle::from_node(b.clone()).expect("expected type");
            return Ok(a.structurally_equals(&b));
        }
        (PNodeKind::Expression(a), PNodeKind::Expression(b)) => {
            return expression_kind_equals(&a.kind, &b.kind);
        }
        (
            PNodeKind::Statement(PStatement {
                kind: PStatementKind::Extension(_),
            }),
            PNodeKind::Statement(PStatement {
                kind: PStatementKind::Extension(_),
            }),
        )
        | (
            PNodeKind::Member(PMember {
                kind: PMemberKind::Extension(_),
                ..
            }),
            PNodeKind::Member(PMember {
                kind: PMemberKind::Extension(_),
                ..
            }),
        ) => return Err(ExtensionEqualityUnavailable),
        (PNodeKind::Declaration(a), PNodeKind::Declaration(b))
            if std::mem::discriminant(&a.kind) != std::mem::discriminant(&b.kind) =>
        {
            return Ok(false);
        }
        (PNodeKind::Member(a), PNodeKind::Member(b))
            if std::mem::discriminant(&a.kind) != std::mem::discriminant(&b.kind) =>
        {
            return Ok(false);
        }
        (PNodeKind::DomainMember(a), PNodeKind::DomainMember(b))
            if std::mem::discriminant(a) != std::mem::discriminant(b) =>
        {
            return Ok(false);
        }
        (PNodeKind::Statement(a), PNodeKind::Statement(b))
            if std::mem::discriminant(&a.kind) != std::mem::discriminant(&b.kind) =>
        {
            return Ok(false);
        }
        (PNodeKind::Extension(_), PNodeKind::Extension(_)) => {
            return Err(ExtensionEqualityUnavailable);
        }
        _ if std::mem::discriminant(&left) != std::mem::discriminant(&right)
            && !matches!(
                (&left, &right),
                (
                    PNodeKind::Grouped { .. },
                    PNodeKind::ExpressionBrackets { .. }
                ) | (
                    PNodeKind::ExpressionBrackets { .. },
                    PNodeKind::Grouped { .. }
                )
            ) =>
        {
            return Ok(false);
        }
        _ => {}
    }
    let left_children = subnodes(a).expect("known parse node children");
    let right_children = subnodes(b).expect("known parse node children");
    if left_children.len() != right_children.len() {
        return Ok(false);
    }
    for (left, right) in left_children.iter().zip(&right_children) {
        if !source_node_equals(left, right)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn reject_extension_equality(node: &PNodeHandle) -> Result<(), ExtensionEqualityUnavailable> {
    let kind = node.read().expect("poisoned parse node").kind.clone();
    if matches!(
        kind,
        PNodeKind::Extension(_)
            | PNodeKind::Expression(PExpression {
                kind: PExpressionKind::Extension(_),
                ..
            })
            | PNodeKind::Statement(PStatement {
                kind: PStatementKind::Extension(_)
            })
            | PNodeKind::Member(PMember {
                kind: PMemberKind::Extension(_),
                ..
            })
    ) {
        return Err(ExtensionEqualityUnavailable);
    }
    for child in subnodes(node).expect("known parse node children") {
        reject_extension_equality(&child)?;
    }
    Ok(())
}

fn expression_kind_equals(
    a: &PExpressionKind,
    b: &PExpressionKind,
) -> Result<bool, ExtensionEqualityUnavailable> {
    use PExpressionKind::*;
    // PMagicWandExp is a PBinExp; upstream compares binary operator spelling rather than its token object.
    fn binary(exp: &PExpressionKind) -> Option<(&PExpHandle, &str, &PExpHandle)> {
        match exp {
            BinExp { left, op, right } => Some((left, op.display(), right)),
            MagicWandExp { left, wand, right } => Some((left, wand.display(), right)),
            _ => None,
        }
    }
    if let (Some((al, ao, ar)), Some((bl, bo, br))) = (binary(a), binary(b)) {
        return Ok(ao == bo
            && al.try_structurally_equals(bl)?
            && ar.try_structurally_equals(br)?);
    }
    if std::mem::discriminant(a) != std::mem::discriminant(b) {
        return Ok(false);
    }
    match (a, b) {
        (Extension(_), Extension(_)) => return Err(ExtensionEqualityUnavailable),
        (IntLit(a), IntLit(b)) => return Ok(a == b),
        (
            VersionedIdnUse {
                idnref: a,
                version: av,
                separator: as_,
            },
            VersionedIdnUse {
                idnref: b,
                version: bv,
                separator: bs,
            },
        ) => return Ok(a.name == b.name && av == bv && as_ == bs),
        (
            SeqSlice {
                start: as_,
                end: ae,
                ..
            },
            SeqSlice {
                start: bs, end: be, ..
            },
        ) if as_.is_some() != bs.is_some() || ae.is_some() != be.is_some() => return Ok(false),
        _ => {}
    }
    let left = expression_subnodes(a.clone());
    let right = expression_subnodes(b.clone());
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(&right) {
        if !source_node_equals(left, right)? {
            return Ok(false);
        }
    }
    Ok(true)
}
impl PExpHandle {
    pub fn try_structurally_equals(
        &self,
        other: &Self,
    ) -> Result<bool, ExtensionEqualityUnavailable> {
        source_node_equals(self.node(), other.node())
    }
}
impl PartialEq for PExpHandle {
    fn eq(&self, other: &Self) -> bool {
        self.try_structurally_equals(other)
            .expect("structural equality requires an extension-specific implementation")
    }
}

#[cfg(test)]
mod source_equality_and_lifetime_tests {
    use super::*;
    use crate::ast::position::LineColumnPosition;
    use crate::parser::parse_ast_keyword::{PDelimited, PGrouped, PKw, PReserved, PSym, PSymOp};

    fn pos(line: i32) -> Span {
        let p = Position::LineColumn(LineColumnPosition::new(line, 1).into());
        (p.clone(), p)
    }
    fn int(value: i32, line: i32) -> PExpHandle {
        PExpHandle::new(
            PExpression::from_kind(PExpressionKind::IntLit(value.into())),
            pos(line),
        )
    }
    fn binary(left: PExpHandle, op: PSymOp, right: PExpHandle, line: i32) -> PExpHandle {
        PExpHandle::new(
            PExpression::from_kind(PExpressionKind::BinExp {
                left,
                op: PReserved::new(PBinaryOp::Symbol(op), pos(line)),
                right,
            }),
            pos(line),
        )
    }
    #[test]
    fn expression_equality_uses_source_structure_and_binary_spelling() {
        let a = binary(int(1, 1), PSymOp::Plus, int(2, 1), 1);
        let b = binary(int(1, 5), PSymOp::Plus, int(2, 6), 9);
        let c = binary(int(1, 1), PSymOp::Minus, int(2, 1), 1);
        assert_eq!(a, b);
        assert_ne!(a, c);
        let w = PExpHandle::new(
            PExpression::from_kind(PExpressionKind::MagicWandExp {
                left: int(1, 1),
                wand: PReserved::implied(PSymOp::Wand),
                right: int(2, 1),
            }),
            pos(1),
        );
        assert_eq!(w, binary(int(1, 5), PSymOp::Wand, int(2, 5), 5));
        let slice = |start: Option<PExpHandle>, end: Option<PExpHandle>| {
            PExpHandle::new(
                PExpression::from_kind(PExpressionKind::SeqSlice {
                    seq: int(0, 1),
                    left: PReserved::implied(PSymOp::LBracket),
                    start,
                    dots: PReserved::implied(PSymOp::DotDot),
                    end,
                    right: PReserved::implied(PSymOp::RBracket),
                }),
                pos(1),
            )
        };
        assert_ne!(slice(Some(int(2, 1)), None), slice(None, Some(int(2, 1))));
    }
    #[test]
    fn typed_brackets_keep_expression_without_forming_cycle() {
        let exp = int(3, 1);
        let weak = Arc::downgrade(exp.node());
        let brackets = PExpressionBrackets::new(
            PReserved::implied(PSym::LParen),
            &exp,
            PReserved::implied(PSym::RParen),
            pos(1),
        );
        exp.set_brackets(brackets.clone());
        assert!(Arc::ptr_eq(&exp.brackets().unwrap().node, &brackets.node));
        drop(exp);
        assert!(brackets.expression().is_some());
        drop(brackets);
        assert!(weak.upgrade().is_none());
    }
    #[test]
    fn linked_field_retains_shared_annotations_after_owner_drop() {
        let annotation = PAnnotation::new(
            PReserved::implied(PSym::At),
            PRawString::new("key".into(), pos(1)),
            PGrouped::implied(
                PSym::LParen,
                PDelimited::<PStringLiteral, SymbolToken>::empty(),
                PSym::RParen,
            ),
            pos(1),
        );
        let field = PDeclarationHandle::from_binding(
            PDeclarationKind::field(),
            PIdnTypeBinding {
                idndef: PNode::new(PNodeKind::IdnDef(PIdnDef { name: "f".into() }), pos(1)),
                colon: PReserved::implied(PSym::Colon),
                typ: PTypeHandle::new(
                    PTypeKind::Primitive {
                        name: PReserved::implied(PKw::Int),
                    },
                    pos(1),
                ),
                pos: pos(1),
            },
        );
        let fields = PDelimited::implied(vec![field.clone()], PReserved::implied(PSym::Comma));
        let owner = PMemberHandle::new(
            PMember::new(
                vec![annotation.clone()],
                PMemberKind::Fields {
                    keyword: PReserved::implied(PKw::Field),
                    fields,
                    semi: None,
                },
            ),
            pos(1),
        );
        field.set_field_owner(&owner);
        drop(owner);
        let retained = field.field_annotations();
        assert_eq!(retained.len(), 1);
        assert!(Arc::ptr_eq(retained[0].node(), annotation.node()));
    }
    #[test]
    fn macro_type_keeps_call_and_upstream_unavailable_operations() {
        let args = PGrouped::implied(
            PSym::LParen,
            PDelimited::<PExpHandle, SymbolToken>::empty(),
            PSym::RParen,
        );
        let call = PExpHandle::new(
            PExpression::from_kind(PExpressionKind::Call {
                idnref: PNode::new(PNodeKind::IdnRef(PIdnRef::new("m")), pos(4)),
                call_args: args,
                type_annotated: None,
                extra_local_type_variables: vec![],
                domain_type_renaming: None,
                domain_substitution: None,
            }),
            pos(4),
        );
        let macro_type = PTypeHandle::macro_type(call.clone());
        assert_eq!(macro_type.node().read().unwrap().pos, pos(4));
        assert!(Arc::ptr_eq(
            macro_type.macro_call().unwrap().node(),
            call.node()
        ));
        assert!(macro_type.is_ground() && macro_type.is_pure());
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                || macro_type.is_valid_or_undeclared()
            ))
            .is_err()
        );
    }
}
