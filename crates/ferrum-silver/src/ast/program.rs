//! Silver programs, declarations, domains and built-in operators.
//!
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Program.scala
//!
//! Status: partial. Declaration representations and direct lookup are implemented;
//! consistency, dependency hashing, domain instantiation and CFG conversion remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::ast::Metadata;
use super::expression::{Exp, LocalVar};
use super::statement::Stmt;
use super::r#type::{DomainType, Type, TypeSubstitution, TypeVar};
use std::any::Any;
use std::collections::HashMap;
use std::fmt::Debug;
use std::sync::{Arc, Mutex, OnceLock};

// Scala case-class metadata and the second argument list do not participate in equality.
macro_rules! structural_eq {
    ($name:ident, $($field:ident),+ $(,)?) => {
        impl PartialEq for $name { fn eq(&self, other: &Self) -> bool { true $(&& self.$field == other.$field)+ } }
        impl Eq for $name {}
    };
}

#[derive(Debug)]
pub struct LocalVarDeclNode {
    pub name: String,
    pub typ: Type,
    pub meta: Metadata,
    local_var: OnceLock<LocalVar>,
}
#[derive(Clone, Debug)]
pub struct LocalVarDecl(pub Arc<LocalVarDeclNode>);
structural_eq!(LocalVarDecl, name, typ);
impl LocalVarDecl {
    pub fn new(name: String, typ: Type, meta: Metadata) -> Self {
        Self(Arc::new(LocalVarDeclNode {
            name,
            typ,
            meta,
            local_var: OnceLock::new(),
        }))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn local_var(&self) -> LocalVar {
        self.local_var
            .get_or_init(|| LocalVar::new(self.name.clone(), self.typ.clone(), self.meta.clone()))
            .clone()
    }
}
impl std::ops::Deref for LocalVarDecl {
    type Target = LocalVarDeclNode;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
#[derive(Clone, Debug)]
pub struct UnnamedLocalVarDeclData {
    pub typ: Type,
    pub meta: Metadata,
}
/// Immutable identity-bearing UnnamedLocalVarDecl handle. Mutation uses copy-on-write with fresh identity.
#[derive(Clone, Debug)]
pub struct UnnamedLocalVarDecl(Arc<UnnamedLocalVarDeclData>);
impl UnnamedLocalVarDecl {
    pub fn new(data: UnnamedLocalVarDeclData) -> Self {
        Self(Arc::new(data))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn copy_with(&self, edit: impl FnOnce(&mut UnnamedLocalVarDeclData)) -> Self {
        let mut data = (*self.0).clone();
        edit(&mut data);
        Self::new(data)
    }
}
impl std::ops::Deref for UnnamedLocalVarDecl {
    type Target = UnnamedLocalVarDeclData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for UnnamedLocalVarDecl {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0 = Arc::new((*self.0).clone());
        Arc::get_mut(&mut self.0).expect("fresh identity")
    }
}
structural_eq!(UnnamedLocalVarDecl, typ);
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnyLocalVarDecl {
    Named(LocalVarDecl),
    Unnamed(UnnamedLocalVarDecl),
}
impl AnyLocalVarDecl {
    pub fn typ(&self) -> &Type {
        match self {
            Self::Named(v) => &v.typ,
            Self::Unnamed(v) => &v.typ,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldData {
    pub name: String,
    pub typ: Type,
    pub meta: Metadata,
}
/// Immutable identity-bearing Field handle. Mutation uses copy-on-write with fresh identity.
#[derive(Clone, Debug)]
pub struct Field(Arc<FieldData>);
impl Field {
    pub fn new(data: FieldData) -> Self {
        Self(Arc::new(data))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn copy_with(&self, edit: impl FnOnce(&mut FieldData)) -> Self {
        let mut data = (*self.0).clone();
        edit(&mut data);
        Self::new(data)
    }
}
impl std::ops::Deref for Field {
    type Target = FieldData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for Field {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0 = Arc::new((*self.0).clone());
        Arc::get_mut(&mut self.0).expect("fresh identity")
    }
}
structural_eq!(Field, name, typ);
#[derive(Clone, Debug)]
pub struct PredicateData {
    pub name: String,
    pub formal_args: Vec<LocalVarDecl>,
    pub body: Option<Exp>,
    pub meta: Metadata,
}
/// Immutable identity-bearing Predicate handle. Mutation uses copy-on-write with fresh identity.
#[derive(Clone, Debug)]
pub struct Predicate(Arc<PredicateData>);
impl Predicate {
    pub fn new(data: PredicateData) -> Self {
        Self(Arc::new(data))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn copy_with(&self, edit: impl FnOnce(&mut PredicateData)) -> Self {
        let mut data = (*self.0).clone();
        edit(&mut data);
        Self::new(data)
    }
}
impl std::ops::Deref for Predicate {
    type Target = PredicateData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for Predicate {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0 = Arc::new((*self.0).clone());
        Arc::get_mut(&mut self.0).expect("fresh identity")
    }
}
structural_eq!(Predicate, name, formal_args, body);
impl Predicate {
    pub fn is_abstract(&self) -> bool {
        self.body.is_none()
    }
}
#[derive(Clone, Debug)]
pub struct MethodData {
    pub name: String,
    pub formal_args: Vec<LocalVarDecl>,
    pub formal_returns: Vec<LocalVarDecl>,
    pub pres: Vec<Exp>,
    pub posts: Vec<Exp>,
    pub body: Option<Stmt>,
    pub meta: Metadata,
}
/// Immutable identity-bearing Method handle. Mutation uses copy-on-write with fresh identity.
#[derive(Clone, Debug)]
pub struct Method(Arc<MethodData>);
impl Method {
    pub fn new(data: MethodData) -> Self {
        Self(Arc::new(data))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn copy_with(&self, edit: impl FnOnce(&mut MethodData)) -> Self {
        let mut data = (*self.0).clone();
        edit(&mut data);
        Self::new(data)
    }
}
impl std::ops::Deref for Method {
    type Target = MethodData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for Method {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0 = Arc::new((*self.0).clone());
        Arc::get_mut(&mut self.0).expect("fresh identity")
    }
}
structural_eq!(Method, name, formal_args, formal_returns, pres, posts, body);
#[derive(Clone, Debug)]
pub struct FunctionData {
    pub name: String,
    pub formal_args: Vec<LocalVarDecl>,
    pub typ: Type,
    pub pres: Vec<Exp>,
    pub posts: Vec<Exp>,
    pub body: Option<Exp>,
    pub meta: Metadata,
}
/// Immutable identity-bearing Function handle. Mutation uses copy-on-write with fresh identity.
#[derive(Clone, Debug)]
pub struct Function(Arc<FunctionData>);
impl Function {
    pub fn new(data: FunctionData) -> Self {
        Self(Arc::new(data))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn copy_with(&self, edit: impl FnOnce(&mut FunctionData)) -> Self {
        let mut data = (*self.0).clone();
        edit(&mut data);
        Self::new(data)
    }
}
impl std::ops::Deref for Function {
    type Target = FunctionData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for Function {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0 = Arc::new((*self.0).clone());
        Arc::get_mut(&mut self.0).expect("fresh identity")
    }
}
structural_eq!(Function, name, formal_args, typ, pres, posts, body);
impl Function {
    pub fn is_abstract(&self) -> bool {
        self.body.is_none()
    }

    /// Upstream classifies a function by its preconditions' purity.
    pub fn is_pure(&self) -> bool {
        self.pres.iter().all(Exp::is_pure)
    }
}

#[derive(Clone, Debug)]
pub struct DomainFuncData {
    pub name: String,
    pub formal_args: Vec<AnyLocalVarDecl>,
    pub typ: Type,
    pub unique: bool,
    pub interpretation: Option<String>,
    pub domain_name: String,
    pub meta: Metadata,
}
/// Immutable identity-bearing DomainFunc handle. Mutation uses copy-on-write with fresh identity.
#[derive(Clone, Debug)]
pub struct DomainFunc(Arc<DomainFuncData>);
impl DomainFunc {
    pub fn new(data: DomainFuncData) -> Self {
        Self(Arc::new(data))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn copy_with(&self, edit: impl FnOnce(&mut DomainFuncData)) -> Self {
        let mut data = (*self.0).clone();
        edit(&mut data);
        Self::new(data)
    }
}
impl std::ops::Deref for DomainFunc {
    type Target = DomainFuncData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for DomainFunc {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0 = Arc::new((*self.0).clone());
        Arc::get_mut(&mut self.0).expect("fresh identity")
    }
}
structural_eq!(DomainFunc, name, formal_args, typ, unique, interpretation);
#[derive(Clone, Debug)]
pub enum DomainAxiomKind {
    Named {
        name: String,
        exp: Exp,
        domain_name: String,
        meta: Metadata,
    },
    Anonymous {
        exp: Exp,
        domain_name: String,
        meta: Metadata,
    },
}
/// Named and anonymous axioms retain source object identity across handle clones.
#[derive(Clone, Debug)]
pub struct DomainAxiom(Arc<DomainAxiomKind>);
impl DomainAxiom {
    pub fn new(kind: DomainAxiomKind) -> Self {
        Self(Arc::new(kind))
    }
    pub fn kind(&self) -> &DomainAxiomKind {
        &self.0
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn copy_with(&self, edit: impl FnOnce(&mut DomainAxiomKind)) -> Self {
        let mut kind = (*self.0).clone();
        edit(&mut kind);
        Self::new(kind)
    }
}
impl PartialEq for DomainAxiom {
    fn eq(&self, other: &Self) -> bool {
        match (self.kind(), other.kind()) {
            (
                DomainAxiomKind::Named {
                    name: a, exp: x, ..
                },
                DomainAxiomKind::Named {
                    name: b, exp: y, ..
                },
            ) => a == b && x == y,
            (
                DomainAxiomKind::Anonymous { exp: x, .. },
                DomainAxiomKind::Anonymous { exp: y, .. },
            ) => x == y,
            _ => false,
        }
    }
}
impl Eq for DomainAxiom {}
impl DomainAxiom {
    pub fn exp(&self) -> &Exp {
        match self.kind() {
            DomainAxiomKind::Named { exp, .. } | DomainAxiomKind::Anonymous { exp, .. } => exp,
        }
    }
}
#[derive(Clone, Debug)]
pub struct DomainData {
    pub name: String,
    pub functions: Vec<DomainFunc>,
    pub axioms: Vec<DomainAxiom>,
    pub type_vars: Vec<TypeVar>,
    pub interpretations: Option<HashMap<String, String>>,
    pub meta: Metadata,
}
/// Immutable identity-bearing Domain handle. Mutation uses copy-on-write with fresh identity.
#[derive(Clone, Debug)]
pub struct Domain(Arc<DomainData>);
impl Domain {
    pub fn new(data: DomainData) -> Self {
        Self(Arc::new(data))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn copy_with(&self, edit: impl FnOnce(&mut DomainData)) -> Self {
        let mut data = (*self.0).clone();
        edit(&mut data);
        Self::new(data)
    }
}
impl std::ops::Deref for Domain {
    type Target = DomainData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for Domain {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0 = Arc::new((*self.0).clone());
        Arc::get_mut(&mut self.0).expect("fresh identity")
    }
}
structural_eq!(Domain, name, functions, axioms, type_vars, interpretations);
impl Domain {
    pub fn domain_type(&self, substitutions: TypeSubstitution) -> DomainType {
        DomainType::new(self.name.clone(), substitutions, self.type_vars.clone())
    }
}

pub trait ExtensionMember: Debug + Send + Sync {
    /// Complete source local check, or an explicit unsupported error.
    fn check(
        &self,
    ) -> Result<
        Vec<crate::verifier::verification_result::FrontendError>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension local consistency",
            ),
        )
    }
    /// Source scope membership and declarations; default deliberately fails closed.
    fn scope_declarations(
        &self,
    ) -> Result<Vec<Declaration>, crate::verifier::verification_result::DiagnosticError> {
        Err(crate::verifier::verification_result::DiagnosticError::Unsupported("extension scope"))
    }

    /// First-constructor Node products visited by source checkTransitively; excludes maps.
    fn check_product_nodes(
        &self,
    ) -> Result<
        Vec<super::utility::nodes::Node>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension consistency product traversal",
            ),
        )
    }

    /// Render the source extension or report that its printer is unavailable.
    fn pretty_print(&self) -> Result<String, super::pretty::pretty_printer::PrintError> {
        Err(super::pretty::pretty_printer::PrintError::Unsupported(
            "extension pretty printer",
        ))
    }
    /// Source document, kept unrendered so outer groups and indentation remain effective.
    fn pretty_doc(
        &self,
    ) -> Result<super::pretty::pretty_printer::Doc, super::pretty::pretty_printer::PrintError> {
        Err(super::pretty::pretty_printer::PrintError::Unsupported(
            "extension document printer",
        ))
    }
    fn as_any(&self) -> &dyn Any;
    fn name(&self) -> &str;
    fn equals(&self, other: &dyn ExtensionMember) -> bool;
    fn metadata(&self) -> Result<&Metadata, crate::verifier::verification_result::DiagnosticError> {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension member metadata",
            ),
        )
    }
    fn with_metadata(
        &self,
        _metadata: Metadata,
    ) -> Result<ExtensionMemberHandle, crate::verifier::verification_result::DiagnosticError> {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension member metadata reconstruction",
            ),
        )
    }
    /// Rebuild all product node fields; extensions with unhandled fields fail explicitly.
    fn map_nodes(
        &self,
        _map: &dyn Fn(
            &super::utility::nodes::Node,
        ) -> Result<
            super::utility::nodes::Node,
            crate::verifier::verification_result::DiagnosticError,
        >,
    ) -> Result<ExtensionMemberHandle, crate::verifier::verification_result::DiagnosticError> {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension member reconstruction",
            ),
        )
    }
    fn subnodes(
        &self,
    ) -> Result<Vec<super::utility::nodes::Node>, super::utility::nodes::TraversalError> {
        Err(super::utility::nodes::TraversalError::Extension(
            "member subnodes",
        ))
    }
}
#[derive(Clone, Debug)]
pub struct ExtensionMemberHandle(pub Arc<dyn ExtensionMember>);
impl PartialEq for ExtensionMemberHandle {
    fn eq(&self, other: &Self) -> bool {
        self.0.equals(other.0.as_ref())
    }
}
impl Eq for ExtensionMemberHandle {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Member {
    Domain(Domain),
    Field(Field),
    Function(Function),
    Predicate(Predicate),
    Method(Method),
    Extension(ExtensionMemberHandle),
}
impl Member {
    pub fn name(&self) -> &str {
        match self {
            Self::Domain(v) => &v.name,
            Self::Field(v) => &v.name,
            Self::Function(v) => &v.name,
            Self::Predicate(v) => &v.name,
            Self::Method(v) => &v.name,
            Self::Extension(v) => v.0.name(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct ProgramContents {
    pub domains: Vec<Domain>,
    pub fields: Vec<Field>,
    pub functions: Vec<Function>,
    pub predicates: Vec<Predicate>,
    pub methods: Vec<Method>,
    pub extensions: Vec<ExtensionMemberHandle>,
    pub meta: Metadata,
}
#[derive(Debug)]
struct ProgramData {
    contents: ProgramContents,
    source_program: Option<crate::parser::parse_ast::PProgramHandle>,
    magic_wand_structures: Mutex<Option<Vec<Exp>>>,
    ground_type_instances: Mutex<Option<std::collections::HashSet<Type>>>,
}
/// An immutable source program. Clones share its identity and lazy cache.
#[derive(Clone, Debug)]
pub struct Program(Arc<ProgramData>);
impl std::ops::Deref for Program {
    type Target = ProgramContents;
    fn deref(&self) -> &Self::Target {
        &self.0.contents
    }
}
structural_eq!(
    Program, domains, fields, functions, predicates, methods, extensions
);
impl Program {
    pub fn new(
        domains: Vec<Domain>,
        fields: Vec<Field>,
        functions: Vec<Function>,
        predicates: Vec<Predicate>,
        methods: Vec<Method>,
        extensions: Vec<ExtensionMemberHandle>,
        meta: Metadata,
    ) -> Self {
        Self::from_contents(ProgramContents {
            domains,
            fields,
            functions,
            predicates,
            methods,
            extensions,
            meta,
        })
    }
    pub fn from_contents(contents: ProgramContents) -> Self {
        Self(Arc::new(ProgramData {
            contents,
            source_program: None,
            magic_wand_structures: Mutex::new(None),
            ground_type_instances: Mutex::new(None),
        }))
    }
    /// Produce a fresh program and cache even if the edited contents compare equal.
    pub fn copy_with(&self, edit: impl FnOnce(&mut ProgramContents)) -> Self {
        let mut contents = self.0.contents.clone();
        edit(&mut contents);
        let mut result = Self::from_contents(contents);
        Arc::get_mut(&mut result.0)
            .expect("fresh program")
            .source_program = self.0.source_program.clone();
        result
    }
    /// Retain the parsed source tree for interactive debugger scope lookup.
    pub fn with_source_program(&self, source: crate::parser::parse_ast::PProgramHandle) -> Self {
        let mut result = self.copy_with(|_| {});
        Arc::get_mut(&mut result.0)
            .expect("fresh program")
            .source_program = Some(source);
        result
    }
    pub fn source_program(&self) -> Option<&crate::parser::parse_ast::PProgramHandle> {
        self.0.source_program.as_ref()
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn members(&self) -> Vec<Member> {
        self.domains
            .iter()
            .cloned()
            .map(Member::Domain)
            .chain(self.fields.iter().cloned().map(Member::Field))
            .chain(self.functions.iter().cloned().map(Member::Function))
            .chain(self.predicates.iter().cloned().map(Member::Predicate))
            .chain(self.methods.iter().cloned().map(Member::Method))
            .chain(self.extensions.iter().cloned().map(Member::Extension))
            .collect()
    }
    // Scala's toMap keeps the last declaration for duplicate names.
    pub fn find_domain_optionally(&self, name: &str) -> Option<&Domain> {
        self.domains.iter().rev().find(|x| x.name == name)
    }
    pub fn find_field_optionally(&self, name: &str) -> Option<&Field> {
        self.fields.iter().rev().find(|x| x.name == name)
    }
    pub fn find_function_optionally(&self, name: &str) -> Option<&Function> {
        self.functions.iter().rev().find(|x| x.name == name)
    }
    pub fn find_predicate_optionally(&self, name: &str) -> Option<&Predicate> {
        self.predicates.iter().rev().find(|x| x.name == name)
    }
    pub fn find_method_optionally(&self, name: &str) -> Option<&Method> {
        self.methods.iter().rev().find(|x| x.name == name)
    }
    pub fn find_domain_function_optionally(&self, name: &str) -> Option<&DomainFunc> {
        self.domains
            .iter()
            .rev()
            .flat_map(|d| d.functions.iter().rev())
            .find(|x| x.name == name)
    }
    pub fn find_domain(&self, name: &str) -> Result<&Domain, MissingMember> {
        self.find_domain_optionally(name)
            .ok_or_else(|| MissingMember::new("Domain", name))
    }
    pub fn find_field(&self, name: &str) -> Result<&Field, MissingMember> {
        self.find_field_optionally(name)
            .ok_or_else(|| MissingMember::new("Field", name))
    }
    pub fn find_function(&self, name: &str) -> Result<&Function, MissingMember> {
        self.find_function_optionally(name)
            .ok_or_else(|| MissingMember::new("Function", name))
    }
    pub fn find_predicate(&self, name: &str) -> Result<&Predicate, MissingMember> {
        self.find_predicate_optionally(name)
            .ok_or_else(|| MissingMember::new("Predicate", name))
    }
    pub fn find_method(&self, name: &str) -> Result<&Method, MissingMember> {
        self.find_method_optionally(name)
            .ok_or_else(|| MissingMember::new("Method", name))
    }
    pub fn find_domain_function(&self, name: &str) -> Result<&DomainFunc, MissingMember> {
        self.find_domain_function_optionally(name)
            .ok_or_else(|| MissingMember::new("Domain function", name))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MissingMember {
    pub kind: &'static str,
    pub name: String,
}
impl MissingMember {
    fn new(kind: &'static str, name: &str) -> Self {
        Self {
            kind,
            name: name.to_owned(),
        }
    }
}
impl std::fmt::Display for MissingMember {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.kind == "Domain function" {
            write!(f, "Domain function {} not found in program.", self.name)
        } else {
            write!(f, "{} name {} not found in program.", self.kind, self.name)
        }
    }
}
impl std::error::Error for MissingMember {}

/// Operators have distinct source identities, including the permission variants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BuiltinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    PermAdd,
    PermSub,
    PermMul,
    DebugPermMin,
    IntPermMul,
    PermDiv,
    Frac,
    Neg,
    PermNeg,
    Lt,
    Le,
    Gt,
    Ge,
    PermLt,
    PermLe,
    PermGt,
    PermGe,
    Or,
    And,
    Implies,
    MagicWand,
    Not,
}

/// Plugin declarations need not be members of the program.
pub trait ExtensionDeclaration: Debug + Send + Sync {
    fn metadata(&self) -> Result<&Metadata, crate::verifier::verification_result::DiagnosticError> {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension declaration metadata",
            ),
        )
    }
    fn as_any(&self) -> &dyn Any;
    fn name(&self) -> &str;
    fn equals(&self, other: &dyn ExtensionDeclaration) -> bool;
}
#[derive(Clone, Debug)]
pub struct ExtensionDeclarationHandle(pub Arc<dyn ExtensionDeclaration>);
impl PartialEq for ExtensionDeclarationHandle {
    fn eq(&self, other: &Self) -> bool {
        self.0.equals(other.0.as_ref())
    }
}
impl Eq for ExtensionDeclarationHandle {}
#[derive(Clone, Debug)]
pub struct LabelDeclarationData {
    pub name: String,
    pub invariants: Vec<Exp>,
    pub meta: Metadata,
}
/// Immutable identity-bearing LabelDeclaration handle. Mutation uses copy-on-write with fresh identity.
#[derive(Clone, Debug)]
pub struct LabelDeclaration(Arc<LabelDeclarationData>);
impl LabelDeclaration {
    pub fn new(data: LabelDeclarationData) -> Self {
        Self(Arc::new(data))
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
    pub fn copy_with(&self, edit: impl FnOnce(&mut LabelDeclarationData)) -> Self {
        let mut data = (*self.0).clone();
        edit(&mut data);
        Self::new(data)
    }
}
impl std::ops::Deref for LabelDeclaration {
    type Target = LabelDeclarationData;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl std::ops::DerefMut for LabelDeclaration {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.0 = Arc::new((*self.0).clone());
        Arc::get_mut(&mut self.0).expect("fresh identity")
    }
}
structural_eq!(LabelDeclaration, name, invariants);

/// Declarations admitted by a scope, including plugin-provided declarations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Declaration {
    Local(LocalVarDecl),
    Field(Field),
    Predicate(Predicate),
    Method(Method),
    Function(Function),
    Domain(Domain),
    DomainFunc(DomainFunc),
    NamedDomainAxiom(DomainAxiom),
    Label(LabelDeclaration),
    Extension(ExtensionDeclarationHandle),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperatorFixity {
    Prefix,
    InfixLeft,
    InfixRight,
    InfixNonAssociative,
}
impl BuiltinOp {
    pub fn spelling(self) -> &'static str {
        use BuiltinOp::*;
        match self {
            Add | PermAdd => "+",
            Sub | PermSub | Neg | PermNeg => "-",
            Mul | PermMul | IntPermMul => "*",
            Div => "\\",
            Mod => "%",
            PermDiv | Frac => "/",
            DebugPermMin => "min",
            Lt | PermLt => "<",
            Le | PermLe => "<=",
            Gt | PermGt => ">",
            Ge | PermGe => ">=",
            Or => "||",
            And => "&&",
            Implies => "==>",
            MagicWand => "--*",
            Not => "!",
        }
    }
    pub fn result_type(self) -> Type {
        use BuiltinOp::*;
        match self {
            Add | Sub | Mul | Div | Mod | Neg => Type::Int,
            PermAdd | PermSub | PermMul | DebugPermMin | IntPermMul | PermDiv | Frac | PermNeg => {
                Type::Perm
            }
            MagicWand => Type::Wand,
            _ => Type::Bool,
        }
    }
    pub fn argument_types(self) -> Vec<Type> {
        use BuiltinOp::*;
        match self {
            Neg => vec![Type::Int],
            PermNeg => vec![Type::Perm],
            Not => vec![Type::Bool],
            Add | Sub | Mul | Div | Mod | Lt | Le | Gt | Ge | Frac => vec![Type::Int, Type::Int],
            PermAdd | PermSub | PermMul | DebugPermMin | PermLt | PermLe | PermGt | PermGe => {
                vec![Type::Perm, Type::Perm]
            }
            IntPermMul => vec![Type::Int, Type::Perm],
            PermDiv => vec![Type::Perm, Type::Int],
            Or | And | Implies | MagicWand => vec![Type::Bool, Type::Bool],
        }
    }
    pub fn priority(self) -> u8 {
        use BuiltinOp::*;
        match self {
            Implies => 2,
            MagicWand => 3,
            Or => 4,
            And => 5,
            Lt | Le | Gt | Ge | PermLt | PermLe | PermGt | PermGe => 7,
            Add | Sub | PermAdd | PermSub | DebugPermMin => 8,
            Mul | Div | Mod | PermMul | IntPermMul | PermDiv | Frac => 9,
            Neg | PermNeg | Not => 10,
        }
    }
    pub fn fixity(self) -> OperatorFixity {
        use BuiltinOp::*;
        match self {
            Neg | PermNeg | Not => OperatorFixity::Prefix,
            Implies | MagicWand => OperatorFixity::InfixRight,
            Lt | Le | Gt | Ge | PermLt | PermLe | PermGt | PermGe => {
                OperatorFixity::InfixNonAssociative
            }
            _ => OperatorFixity::InfixLeft,
        }
    }
}
impl Method {
    /// Source deep-collection of labels in the body; handles retain statement identity.
    pub fn labels(&self) -> Result<Vec<LabelDeclaration>, super::utility::nodes::TraversalError> {
        use super::utility::nodes::{self, Node};
        fn collect(node: &Node) -> Result<Vec<LabelDeclaration>, nodes::TraversalError> {
            let mut children = Vec::new();
            for child in nodes::subnodes(node)? {
                children.extend(collect(&child)?);
            }
            let mut result = match node {
                Node::Stmt(stmt) => match stmt.kind() {
                    super::statement::StmtKind::Label(label) => vec![label.clone()],
                    _ => vec![],
                },
                Node::LabelDecl(label) => vec![label.clone()],
                _ => vec![],
            };
            result.extend(children);
            Ok(result)
        }
        match &self.body {
            Some(body) => collect(&Node::Stmt(body.clone())),
            None => Ok(vec![]),
        }
    }
    pub fn scoped_declarations(
        &self,
    ) -> Result<Vec<Declaration>, super::utility::nodes::TraversalError> {
        let mut result: Vec<_> = self
            .formal_args
            .iter()
            .chain(&self.formal_returns)
            .cloned()
            .map(Declaration::Local)
            .collect();
        result.extend(self.labels()?.into_iter().map(Declaration::Label));
        Ok(result)
    }
    /// The source's absent-body helper is `inhale false`, not an empty body.
    pub fn body_or_assume_false(&self) -> Stmt {
        self.body.clone().unwrap_or_else(|| {
            let false_exp = Exp::new(super::expression::ExpKind::FalseLit, Metadata::default());
            Stmt::new(
                super::statement::StmtKind::Seqn {
                    statements: vec![Stmt::new(
                        super::statement::StmtKind::Inhale(false_exp),
                        Metadata::default(),
                    )],
                    declarations: Vec::new(),
                },
                Metadata::default(),
            )
        })
    }
}
impl Function {
    pub fn result(&self) -> Exp {
        Exp::new(
            super::expression::ExpKind::Result(self.typ.clone()),
            Metadata::default(),
        )
    }
}

impl Program {
    /// Source lazy groundTypeInstances uses the default recursion threshold of one.
    /// Failed analysis is retried on the next access, as for a throwing lazy val.
    pub fn ground_type_instances(
        &self,
    ) -> Result<
        std::collections::HashSet<Type>,
        super::utility::domain_instances::DomainInstanceError,
    > {
        let mut cache = self
            .0
            .ground_type_instances
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if let Some(value) = cache.as_ref() {
            return Ok(value.clone());
        }
        let value = super::utility::domain_instances::find_necessary_type_instances(self, 1)?;
        *cache = Some(value.clone());
        Ok(value)
    }
    /// Source deepCollect is evaluated bottom-up but returned parent-before-child;
    /// distinct retains the first structurally equal canonical wand.
    pub fn magic_wand_structures(
        &self,
    ) -> Result<Vec<Exp>, super::utility::expressions::MagicWandError> {
        use super::utility::expressions::MagicWandError;
        use super::utility::nodes::{self, Node};
        // Failures are not cached: like a throwing Scala lazy val, a later
        // access retries. Recover a poisoned guard rather than caching failure.
        let mut cache = self
            .0
            .magic_wand_structures
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if let Some(structures) = cache.as_ref() {
            return Ok(structures.clone());
        }
        fn collect(node: &Node, program: &Program) -> Result<Vec<Exp>, MagicWandError> {
            let mut descendants = Vec::new();
            for child in nodes::subnodes(node)? {
                descendants.extend(collect(&child, program)?);
            }
            let mut result = Vec::new();
            if let Node::Exp(wand) = node {
                if matches!(wand.kind(), super::expression::ExpKind::MagicWand(..)) {
                    result.push(wand.magic_wand_structure(program, false)?);
                }
            }
            result.extend(descendants);
            Ok(result)
        }
        let mut result = Vec::new();
        for wand in collect(&Node::Program(self.clone()), self)? {
            if !result.contains(&wand) {
                result.push(wand);
            }
        }
        *cache = Some(result.clone());
        Ok(result)
    }
}

#[cfg(test)]
mod member_identity_tests {
    use super::*;
    #[test]
    fn handles_share_clones_and_freshen_copies_without_mutating_original() {
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: Metadata::default(),
        });
        let mut changed = field.clone();
        assert!(field.same_node(&changed));
        changed.name = "g".into();
        assert!(!field.same_node(&changed));
        assert_eq!(field.name, "f");
        let copied = field.copy_with(|_| {});
        assert_eq!(field, copied);
        assert!(!field.same_node(&copied));
        let axiom = DomainAxiom::new(DomainAxiomKind::Anonymous {
            exp: Exp::new(
                super::super::expression::ExpKind::TrueLit,
                Metadata::default(),
            ),
            domain_name: "D".into(),
            meta: Metadata::default(),
        });
        let same = axiom.clone();
        assert!(axiom.same_node(&same));
        let copied = axiom.copy_with(|_| {});
        assert_eq!(axiom, copied);
        assert!(!axiom.same_node(&copied));
    }
}
