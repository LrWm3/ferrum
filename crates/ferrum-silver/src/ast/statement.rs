//! Silver statements and statement scope.
//!
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/Statement.scala
//!
//! Status: partial. Statement variants and structural equality are implemented;
//! consistency checks, scope traversal, CFG and pretty-printing await collaborators.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::ast::Metadata;
use super::expression::{Exp, ExpKind, FieldAccess, LocalVar, PredicateAccess};
use super::program::{Declaration, Field, LabelDeclaration, LocalVarDecl};
use std::any::Any;
use std::fmt::Debug;
use std::sync::{Arc, OnceLock};

pub trait ExtensionStmt: Debug + Send + Sync {
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
    ) -> Result<
        Option<Vec<super::program::Declaration>>,
        crate::verifier::verification_result::DiagnosticError,
    > {
        Err(crate::verifier::verification_result::DiagnosticError::Unsupported("extension scope"))
    }

    fn metadata(&self) -> &Metadata;
    fn with_metadata(&self, metadata: Metadata) -> ExtensionStmtHandle;
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
    fn equals(&self, other: &dyn ExtensionStmt) -> bool;
    /// Rebuild direct expression children for error back-transformation.
    /// Extensions with additional rewritable node fields must report unsupported.
    fn map_expressions(
        &self,
        _map: &dyn Fn(&Exp) -> Result<Exp, crate::verifier::verification_result::DiagnosticError>,
    ) -> Result<ExtensionStmtHandle, crate::verifier::verification_result::DiagnosticError> {
        Err(
            crate::verifier::verification_result::DiagnosticError::Unsupported(
                "extension statement reconstruction",
            ),
        )
    }
    fn subnodes(
        &self,
    ) -> Result<Vec<super::utility::nodes::Node>, super::utility::nodes::TraversalError> {
        Err(super::utility::nodes::TraversalError::Extension(
            "statement subnodes",
        ))
    }
    fn declarations_in_parent_scope(&self) -> Vec<Declaration> {
        Vec::new()
    }
}
#[derive(Clone, Debug)]
pub struct ExtensionStmtHandle(pub Arc<dyn ExtensionStmt>);
impl PartialEq for ExtensionStmtHandle {
    fn eq(&self, other: &Self) -> bool {
        self.0.equals(other.0.as_ref())
    }
}
impl Eq for ExtensionStmtHandle {}

#[derive(Clone, Debug)]
pub struct PredicateAccessPredicateNode {
    pub location: PredicateAccess,
    pub permission: Option<Exp>,
    pub meta: Metadata,
    implicit_full_permission: OnceLock<Exp>,
}
#[derive(Clone, Debug)]
pub struct PredicateAccessPredicate(pub Arc<PredicateAccessPredicateNode>);
impl PredicateAccessPredicate {
    pub fn new(location: PredicateAccess, permission: Option<Exp>, meta: Metadata) -> Self {
        Self(Arc::new(PredicateAccessPredicateNode {
            location,
            permission,
            meta,
            implicit_full_permission: OnceLock::new(),
        }))
    }
    pub fn permission_or_full(&self) -> Exp {
        self.permission.clone().unwrap_or_else(|| {
            self.0
                .implicit_full_permission
                .get_or_init(|| {
                    Exp::new(
                        ExpKind::FullPerm,
                        Metadata {
                            position: self.meta.position.clone(),
                            ..Metadata::default()
                        },
                    )
                })
                .clone()
        })
    }
    pub fn same_node(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}
impl std::ops::Deref for PredicateAccessPredicate {
    type Target = PredicateAccessPredicateNode;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl PartialEq for PredicateAccessPredicate {
    fn eq(&self, other: &Self) -> bool {
        self.location == other.location && self.permission == other.permission
    }
}
impl Eq for PredicateAccessPredicate {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResourceAccess {
    Field(FieldAccess),
    Predicate(PredicateAccess),
    MagicWand(Exp),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StmtKind {
    NewStmt {
        lhs: LocalVar,
        fields: Vec<Field>,
    },
    LocalVarAssign {
        lhs: LocalVar,
        rhs: Exp,
    },
    FieldAssign {
        lhs: FieldAccess,
        rhs: Exp,
    },
    MethodCall {
        method_name: String,
        args: Vec<Exp>,
        targets: Vec<LocalVar>,
    },
    Exhale(Exp),
    Inhale(Exp),
    Assert(Exp),
    Assume(Exp),
    Fold(PredicateAccessPredicate),
    Unfold(PredicateAccessPredicate),
    Package {
        wand: Exp,
        proof_script: Stmt,
    },
    Apply(Exp),
    Seqn {
        statements: Vec<Stmt>,
        declarations: Vec<Declaration>,
    },
    If {
        condition: Exp,
        then_branch: Stmt,
        else_branch: Stmt,
    },
    While {
        condition: Exp,
        invariants: Vec<Exp>,
        body: Stmt,
    },
    Label(LabelDeclaration),
    Goto(String),
    LocalVarDeclStmt(LocalVarDecl),
    Quasihavoc {
        guard: Option<Exp>,
        resource: ResourceAccess,
    },
    Quasihavocall {
        variables: Vec<LocalVarDecl>,
        guard: Option<Exp>,
        resource: ResourceAccess,
    },
    Extension(ExtensionStmtHandle),
}
#[derive(Clone, Debug)]
pub struct StmtNode {
    pub kind: StmtKind,
    pub meta: Metadata,
}
#[derive(Clone, Debug)]
pub struct Stmt(pub Arc<StmtNode>);
impl PartialEq for Stmt {
    fn eq(&self, other: &Self) -> bool {
        self.0.kind == other.0.kind
    }
}
impl Eq for Stmt {}
impl Stmt {
    pub fn new(kind: StmtKind, meta: Metadata) -> Self {
        let meta = match &kind {
            StmtKind::Label(label) => label.meta.clone(),
            StmtKind::Extension(extension) => extension.0.metadata().clone(),
            _ => meta,
        };
        Self(Arc::new(StmtNode { kind, meta }))
    }
    pub fn kind(&self) -> &StmtKind {
        &self.0.kind
    }
    pub fn metadata(&self) -> &Metadata {
        &self.0.meta
    }
    pub fn same_node(&self, other: &Self) -> bool {
        match (self.kind(), other.kind()) {
            (StmtKind::Label(a), StmtKind::Label(b)) => a.same_node(b),
            (StmtKind::Extension(a), StmtKind::Extension(b)) => Arc::ptr_eq(&a.0, &b.0),
            _ => Arc::ptr_eq(&self.0, &other.0),
        }
    }
    pub fn scoped_declarations(&self) -> Vec<Declaration> {
        match self.kind() {
            StmtKind::Seqn {
                statements,
                declarations,
            } => {
                let mut result = declarations.clone();
                for s in statements {
                    if let StmtKind::Extension(e) = s.kind() {
                        result.extend(e.0.declarations_in_parent_scope());
                    }
                }
                result
            }
            StmtKind::Quasihavocall { variables, .. } => {
                variables.iter().cloned().map(Declaration::Local).collect()
            }
            _ => Vec::new(),
        }
    }
}
