//! Ordered Silver AST child dispatch.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Nodes.scala
//! Status: partial. Subnode dispatch, member references and a preorder typed-product mapper
//! are implemented; generic strategy integration and extension declaration hooks remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::expression::{
    Exp, ExpKind, ExpressionTypeError, FieldAccess, LocalVar, PredicateAccess, Trigger,
};
use crate::ast::program::{
    AnyLocalVarDecl, DomainAxiom, DomainFunc, LabelDeclaration, LocalVarDecl, Member, Program,
    UnnamedLocalVarDecl,
};
use crate::ast::statement::{PredicateAccessPredicate, ResourceAccess, Stmt, StmtKind};
use crate::ast::r#type::Type;

/// Owned views of source nodes. Typed access and trigger handles retain identity.
#[derive(Clone, Debug)]
pub enum Node {
    Program(Program),
    Member(Member),
    DomainFunc(DomainFunc),
    DomainAxiom(DomainAxiom),
    LocalDecl(LocalVarDecl),
    LabelDecl(LabelDeclaration),
    UnnamedLocalDecl(UnnamedLocalVarDecl),
    Exp(Exp),
    LocalVar(LocalVar),
    FieldAccess(FieldAccess),
    PredicateAccess(PredicateAccess),
    PredicateAccessPredicate(PredicateAccessPredicate),
    Trigger(Trigger),
    Stmt(Stmt),
    Type(Type),
}
impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        use Node::*;
        match (self, other) {
            (Program(a), Program(b)) => a == b,
            (Member(a), Member(b)) => a == b,
            (DomainFunc(a), DomainFunc(b)) => a == b,
            (DomainAxiom(a), DomainAxiom(b)) => a == b,
            (LocalDecl(a), LocalDecl(b)) => a == b,
            (LabelDecl(a), LabelDecl(b)) => a == b,
            (LabelDecl(a), Stmt(b)) | (Stmt(b), LabelDecl(a)) => {
                matches!(b.kind(), StmtKind::Label(label) if a == label)
            }
            (UnnamedLocalDecl(a), UnnamedLocalDecl(b)) => a == b,
            (Exp(a), Exp(b)) => a == b,
            (LocalVar(a), LocalVar(b)) => a == b,
            (FieldAccess(a), FieldAccess(b)) => a == b,
            (PredicateAccess(a), PredicateAccess(b)) => a == b,
            (PredicateAccessPredicate(a), PredicateAccessPredicate(b)) => a == b,
            (Trigger(a), Trigger(b)) => a == b,
            (Stmt(a), Stmt(b)) => a == b,
            (Type(a), Type(b)) => a == b,
            (Exp(e), FieldAccess(a)) | (FieldAccess(a), Exp(e)) => {
                matches!(e.kind(), ExpKind::FieldAccess(b) if a == b)
            }
            (Exp(e), PredicateAccess(a)) | (PredicateAccess(a), Exp(e)) => {
                matches!(e.kind(), ExpKind::PredicateAccess(b) if a == b)
            }
            (Exp(e), LocalVar(a)) | (LocalVar(a), Exp(e)) => {
                matches!(e.kind(), ExpKind::LocalVar(b) if a == b)
            }
            (Exp(e), PredicateAccessPredicate(a)) | (PredicateAccessPredicate(a), Exp(e)) => {
                matches!(e.kind(), ExpKind::PredicateAccessPredicate(b) if a == b)
            }
            _ => false,
        }
    }
}
impl Eq for Node {}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraversalError {
    ExpressionType(ExpressionTypeError),
    Extension(&'static str),
}
impl Node {
    /// Identity is available for handle-backed nodes. Other source-node families
    /// still need identity-bearing representations, reported as `None`.
    pub fn same_node(&self, other: &Self) -> Option<bool> {
        use Node::*;
        match (self, other) {
            (Program(a), Program(b)) => Some(a.same_node(b)),
            (
                Member(crate::ast::program::Member::Domain(a)),
                Member(crate::ast::program::Member::Domain(b)),
            ) => Some(a.same_node(b)),
            (
                Member(crate::ast::program::Member::Field(a)),
                Member(crate::ast::program::Member::Field(b)),
            ) => Some(a.same_node(b)),
            (
                Member(crate::ast::program::Member::Function(a)),
                Member(crate::ast::program::Member::Function(b)),
            ) => Some(a.same_node(b)),
            (
                Member(crate::ast::program::Member::Predicate(a)),
                Member(crate::ast::program::Member::Predicate(b)),
            ) => Some(a.same_node(b)),
            (
                Member(crate::ast::program::Member::Method(a)),
                Member(crate::ast::program::Member::Method(b)),
            ) => Some(a.same_node(b)),
            (
                Member(crate::ast::program::Member::Extension(a)),
                Member(crate::ast::program::Member::Extension(b)),
            ) => Some(std::sync::Arc::ptr_eq(&a.0, &b.0)),
            (Member(_), Member(_)) => Some(false),
            (DomainFunc(a), DomainFunc(b)) => Some(a.same_node(b)),
            (DomainAxiom(a), DomainAxiom(b)) => Some(a.same_node(b)),
            (Exp(a), Exp(b)) => Some(a.same_node(b)),
            (Stmt(a), Stmt(b)) => Some(a.same_node(b)),
            (LocalDecl(a), LocalDecl(b)) => Some(a.same_node(b)),
            (LabelDecl(a), LabelDecl(b)) => Some(a.same_node(b)),
            (LabelDecl(a), Stmt(b)) | (Stmt(b), LabelDecl(a)) => {
                Some(matches!(b.kind(), StmtKind::Label(label) if a.same_node(label)))
            }
            (UnnamedLocalDecl(a), UnnamedLocalDecl(b)) => Some(a.same_node(b)),
            (LocalVar(a), LocalVar(b)) => Some(a.same_node(b)),
            (FieldAccess(a), FieldAccess(b)) => Some(a.same_node(b)),
            (PredicateAccess(a), PredicateAccess(b)) => Some(a.same_node(b)),
            (PredicateAccessPredicate(a), PredicateAccessPredicate(b)) => Some(a.same_node(b)),
            (Trigger(a), Trigger(b)) => Some(a.same_node(b)),
            (Type(a), Type(b)) => Some(a.same_node(b)),
            (Exp(e), FieldAccess(a)) | (FieldAccess(a), Exp(e)) => {
                Some(matches!(e.kind(), ExpKind::FieldAccess(b) if a.same_node(b)))
            }
            (Exp(e), PredicateAccess(a)) | (PredicateAccess(a), Exp(e)) => {
                Some(matches!(e.kind(), ExpKind::PredicateAccess(b) if a.same_node(b)))
            }
            (Exp(e), LocalVar(a)) | (LocalVar(a), Exp(e)) => {
                Some(matches!(e.kind(), ExpKind::LocalVar(b) if a.same_node(b)))
            }
            (Exp(e), PredicateAccessPredicate(a)) | (PredicateAccessPredicate(a), Exp(e)) => {
                Some(matches!(e.kind(), ExpKind::PredicateAccessPredicate(b) if a.same_node(b)))
            }
            _ => None,
        }
    }
    /// Type of a Typed node; Type nodes themselves are not Typed.
    pub fn typ(&self) -> Result<Option<Type>, TraversalError> {
        Ok(match self {
            Node::Member(crate::ast::program::Member::Field(f)) => Some(f.typ.clone()),
            Node::Member(crate::ast::program::Member::Function(f)) => Some(f.typ.clone()),
            Node::DomainFunc(f) => Some(f.typ.clone()),
            Node::LocalDecl(d) => Some(d.typ.clone()),
            Node::UnnamedLocalDecl(d) => Some(d.typ.clone()),
            Node::LocalVar(v) => Some(v.typ.clone()),
            Node::FieldAccess(a) => Some(a.field.typ.clone()),
            Node::PredicateAccess(_) | Node::PredicateAccessPredicate(_) => Some(Type::Bool),
            Node::Exp(e) => Some(e.typ()?),
            _ => None,
        })
    }
}
impl From<ExpressionTypeError> for TraversalError {
    fn from(e: ExpressionTypeError) -> Self {
        Self::ExpressionType(e)
    }
}
fn exps(xs: &[Exp]) -> Vec<Node> {
    xs.iter().cloned().map(Node::Exp).collect()
}
fn decls(xs: &[LocalVarDecl]) -> Vec<Node> {
    xs.iter().cloned().map(Node::LocalDecl).collect()
}
fn resource(r: &ResourceAccess) -> Node {
    match r {
        ResourceAccess::Field(x) => Node::FieldAccess(x.clone()),
        ResourceAccess::Predicate(x) => Node::PredicateAccess(x.clone()),
        ResourceAccess::MagicWand(x) => Node::Exp(x.clone()),
    }
}

pub fn subnodes(node: &Node) -> Result<Vec<Node>, TraversalError> {
    use Node::*;
    let mut out = match node {
        Program(p) => p.members().into_iter().map(Member).collect(),
        Member(m) => match m {
            crate::ast::program::Member::Domain(d) => d
                .functions
                .iter()
                .cloned()
                .map(DomainFunc)
                .chain(d.axioms.iter().cloned().map(DomainAxiom))
                .chain(
                    d.type_vars
                        .iter()
                        .cloned()
                        .map(|v| Type(crate::ast::r#type::Type::Var(v))),
                )
                .collect(),
            crate::ast::program::Member::Field(_) => vec![],
            crate::ast::program::Member::Function(f) => {
                let mut v = decls(&f.formal_args);
                v.extend(exps(&f.pres));
                v.extend(exps(&f.posts));
                v.extend(f.body.iter().cloned().map(Exp));
                v
            }
            crate::ast::program::Member::Predicate(p) => {
                let mut v = decls(&p.formal_args);
                v.extend(p.body.iter().cloned().map(Exp));
                v
            }
            crate::ast::program::Member::Method(m) => {
                let mut v = decls(&m.formal_args);
                v.extend(decls(&m.formal_returns));
                v.extend(exps(&m.pres));
                v.extend(exps(&m.posts));
                v.extend(m.body.iter().cloned().map(Stmt));
                v
            }
            crate::ast::program::Member::Extension(e) => e.0.subnodes()?,
        },
        DomainFunc(f) => f
            .formal_args
            .iter()
            .map(|a| match a {
                AnyLocalVarDecl::Named(d) => LocalDecl(d.clone()),
                AnyLocalVarDecl::Unnamed(d) => UnnamedLocalDecl(d.clone()),
            })
            .collect(),
        DomainAxiom(a) => vec![Exp(a.exp().clone())],
        LocalDecl(_) | UnnamedLocalDecl(_) | LocalVar(_) | Type(_) => vec![],
        LabelDecl(label) => exps(&label.invariants),
        FieldAccess(a) => vec![Exp(a.receiver.clone())],
        PredicateAccess(a) => exps(&a.args),
        PredicateAccessPredicate(a) => {
            let mut v = vec![PredicateAccess(a.location.clone())];
            v.extend(a.permission.iter().cloned().map(Exp));
            v
        }
        Trigger(t) => exps(&t.exps),
        Stmt(s) => match s.kind() {
            StmtKind::NewStmt { lhs, fields } => std::iter::once(LocalVar(lhs.clone()))
                .chain(
                    fields
                        .iter()
                        .cloned()
                        .map(|f| Member(crate::ast::program::Member::Field(f))),
                )
                .collect(),
            StmtKind::LocalVarAssign { lhs, rhs } => vec![LocalVar(lhs.clone()), Exp(rhs.clone())],
            StmtKind::FieldAssign { lhs, rhs } => vec![FieldAccess(lhs.clone()), Exp(rhs.clone())],
            StmtKind::Fold(p) | StmtKind::Unfold(p) => vec![PredicateAccessPredicate(p.clone())],
            StmtKind::Package { wand, proof_script } => {
                vec![Exp(wand.clone()), Stmt(proof_script.clone())]
            }
            StmtKind::Apply(e)
            | StmtKind::Inhale(e)
            | StmtKind::Exhale(e)
            | StmtKind::Assert(e)
            | StmtKind::Assume(e) => vec![Exp(e.clone())],
            StmtKind::MethodCall { args, targets, .. } => exps(args)
                .into_iter()
                .chain(targets.iter().cloned().map(LocalVar))
                .collect(),
            StmtKind::Seqn {
                statements,
                declarations,
            } => statements
                .iter()
                .cloned()
                .map(Stmt)
                .chain(declarations.iter().filter_map(|d| match d {
                    crate::ast::program::Declaration::Local(l) => Some(LocalDecl(l.clone())),
                    _ => None,
                }))
                .collect(),
            StmtKind::While {
                condition,
                invariants,
                body,
            } => std::iter::once(Exp(condition.clone()))
                .chain(exps(invariants))
                .chain(std::iter::once(Stmt(body.clone())))
                .collect(),
            StmtKind::If {
                condition,
                then_branch,
                else_branch,
            } => vec![
                Exp(condition.clone()),
                Stmt(then_branch.clone()),
                Stmt(else_branch.clone()),
            ],
            StmtKind::Label(label) => exps(&label.invariants),
            StmtKind::Goto(_) => vec![],
            StmtKind::LocalVarDeclStmt(d) => vec![LocalDecl(d.clone())],
            StmtKind::Quasihavoc { guard, resource: r } => guard
                .iter()
                .cloned()
                .map(Exp)
                .chain(std::iter::once(resource(r)))
                .collect(),
            StmtKind::Quasihavocall {
                variables,
                guard,
                resource: r,
            } => decls(variables)
                .into_iter()
                .chain(guard.iter().cloned().map(Exp))
                .chain(std::iter::once(resource(r)))
                .collect(),
            StmtKind::Extension(e) => e.0.subnodes()?,
        },
        Exp(e) => expression_subnodes(e)?,
    };
    if let Some(t) = node.typ()? {
        out.push(Type(t));
    }
    Ok(out)
}

fn expression_subnodes(e: &Exp) -> Result<Vec<Node>, TraversalError> {
    use ExpKind::*;
    use Node::{Exp as E, Type as T};
    Ok(match e.kind() {
        Add(a, b)
        | Sub(a, b)
        | Mul(a, b)
        | Div(a, b)
        | Mod(a, b)
        | LtCmp(a, b)
        | LeCmp(a, b)
        | GtCmp(a, b)
        | GeCmp(a, b)
        | EqCmp(a, b)
        | NeCmp(a, b)
        | Or(a, b)
        | And(a, b)
        | Implies(a, b)
        | MagicWand(a, b)
        | InhaleExhaleExp(a, b)
        | FractionalPerm(a, b)
        | PermDiv(a, b)
        | PermPermDiv(a, b)
        | PermAdd(a, b)
        | PermSub(a, b)
        | PermMul(a, b)
        | IntPermMul(a, b)
        | DebugPermMin(a, b)
        | PermLtCmp(a, b)
        | PermLeCmp(a, b)
        | PermGtCmp(a, b)
        | PermGeCmp(a, b)
        | Unfolding(a, b)
        | Applying(a, b)
        | Asserting(a, b)
        | RangeSeq(a, b)
        | SeqAppend(a, b)
        | SeqIndex(a, b)
        | SeqTake(a, b)
        | SeqDrop(a, b)
        | SeqContains(a, b)
        | AnySetUnion(a, b)
        | AnySetIntersection(a, b)
        | AnySetSubset(a, b)
        | AnySetMinus(a, b)
        | AnySetContains(a, b)
        | Maplet(a, b)
        | MapLookup(a, b)
        | MapContains(a, b) => vec![E(a.clone()), E(b.clone())],
        Minus(a)
        | Not(a)
        | CurrentPerm(a)
        | PermMinus(a)
        | Old(a)
        | SeqLength(a)
        | AnySetCardinality(a)
        | MapCardinality(a)
        | MapDomain(a)
        | MapRange(a)
        | LabelledOld(a, _)
        | DebugLabelledOld(a, _) => vec![E(a.clone())],
        CondExp(a, b, c) | SeqUpdate(a, b, c) | MapUpdate(a, b, c) => {
            vec![E(a.clone()), E(b.clone()), E(c.clone())]
        }
        IntLit(_)
        | TrueLit
        | FalseLit
        | NullLit
        | RefLit(_)
        | BackendValueLit(..)
        | WildcardPerm
        | FullPerm
        | NoPerm
        | EpsilonPerm
        | LocalVar(_)
        | Result(_)
        | LocalVarWithVersion(..) => vec![],
        // Unlike PredicateAccessPredicate's earlier dedicated source case,
        // FieldAccessPredicate reaches AccessPredicate(loc, perm), whose `perm`
        // supplies a FullPerm when the optional syntax is absent.
        FieldAccessPredicate(a, _) => vec![
            Node::FieldAccess(a.clone()),
            E(e.permission_or_full()
                .expect("field access predicate has permission")),
        ],
        PredicateAccessPredicate(a) => std::iter::once(Node::PredicateAccess(a.location.clone()))
            .chain(a.permission.iter().cloned().map(E))
            .collect(),
        FieldAccess(a) => vec![E(a.receiver.clone())],
        PredicateAccess(a) => exps(&a.args),
        FuncApp(_, args)
        | BackendFuncApp(_, args)
        | ExplicitSeq(args)
        | ExplicitSet(args)
        | ExplicitMultiset(args)
        | ExplicitMap(args) => exps(args),
        DomainFuncApp(_, args, m) => {
            let mut v = exps(args);
            v.extend(
                m.keys()
                    .cloned()
                    .map(|x| T(crate::ast::r#type::Type::Var(x))),
            );
            v.extend(m.values().cloned().map(T));
            v
        }
        Let(d, a, b) => vec![Node::LocalDecl(d.clone()), E(a.clone()), E(b.clone())],
        Forall(ds, ts, b) | Exists(ds, ts, b) => decls(ds)
            .into_iter()
            .chain(ts.iter().cloned().map(Node::Trigger))
            .chain(std::iter::once(E(b.clone())))
            .collect(),
        ForPerm(ds, r, b) => decls(ds)
            .into_iter()
            .chain([E(r.clone()), E(b.clone())])
            .collect(),
        EmptySeq(t) | EmptySet(t) | EmptyMultiset(t) => vec![T(t.clone())],
        EmptyMap(a, b) => vec![T(a.clone()), T(b.clone())],
        Extension(e) => e.0.subnodes()?,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferencedMemberError {
    Traversal(TraversalError),
    Missing(crate::ast::program::MissingMember),
    InvalidUnfoldingAccess,
}
impl From<TraversalError> for ReferencedMemberError {
    fn from(error: TraversalError) -> Self {
        Self::Traversal(error)
    }
}
impl From<crate::ast::program::MissingMember> for ReferencedMemberError {
    fn from(error: crate::ast::program::MissingMember) -> Self {
        Self::Missing(error)
    }
}

/// Nodes which refer to methods, functions, or folded/unfolded predicates,
/// including duplicates and the root itself.
pub fn member_referencing_nodes(root: &Node) -> Result<Vec<Node>, TraversalError> {
    let mut result = Vec::new();
    super::visitor::visit(root, &subnodes, &mut |node| {
        let references = match node {
            Node::Stmt(s) => matches!(
                s.kind(),
                StmtKind::MethodCall { .. } | StmtKind::Fold(_) | StmtKind::Unfold(_)
            ),
            Node::Exp(e) => matches!(e.kind(), ExpKind::FuncApp(..) | ExpKind::Unfolding(..)),
            _ => false,
        };
        if references {
            result.push(node.clone());
        }
    })?;
    Ok(result)
}

pub fn referenced_members(
    root: &Node,
    program: &Program,
) -> Result<Vec<Member>, ReferencedMemberError> {
    let mut result = Vec::new();
    for node in member_referencing_nodes(root)? {
        let member = match node {
            Node::Stmt(s) => match s.kind() {
                StmtKind::MethodCall { method_name, .. } => {
                    Member::Method(program.find_method(method_name)?.clone())
                }
                StmtKind::Fold(p) | StmtKind::Unfold(p) => {
                    Member::Predicate(program.find_predicate(&p.location.predicate_name)?.clone())
                }
                _ => unreachable!("member_referencing_nodes selects only member references"),
            },
            Node::Exp(e) => match e.kind() {
                ExpKind::FuncApp(name, _) => Member::Function(program.find_function(name)?.clone()),
                ExpKind::Unfolding(access, _) => match access.kind() {
                    ExpKind::PredicateAccessPredicate(p) => Member::Predicate(
                        program.find_predicate(&p.location.predicate_name)?.clone(),
                    ),
                    _ => return Err(ReferencedMemberError::InvalidUnfoldingAccess),
                },
                _ => unreachable!("member_referencing_nodes selects only member references"),
            },
            _ => unreachable!("member_referencing_nodes selects only member references"),
        };
        if !result.contains(&member) {
            result.push(member);
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ast::Metadata;
    use crate::ast::expression::{ExpKind, FieldAccess};
    use crate::ast::program::Field;
    use crate::ast::r#type::Type;

    #[test]
    fn predicate_permission_is_cached_across_expression_views_but_omitted_from_subnodes() {
        use crate::ast::expression::PredicateAccess;
        use crate::ast::statement::PredicateAccessPredicate;
        let access = PredicateAccess::new(vec![], "p".into(), Metadata::default());
        let pred = PredicateAccessPredicate::new(access, None, Metadata::default());
        let a = Exp::new(
            ExpKind::PredicateAccessPredicate(pred.clone()),
            Metadata::default(),
        );
        let b = Exp::new(ExpKind::PredicateAccessPredicate(pred), Metadata::default());
        assert!(
            a.permission_or_full()
                .unwrap()
                .same_node(&b.permission_or_full().unwrap())
        );
        let children = subnodes(&Node::Exp(a)).unwrap();
        assert_eq!(children.len(), 2); // access plus the predicate's Bool type
        assert!(matches!(children[0], Node::PredicateAccess(_)));
        assert!(matches!(children[1], Node::Type(Type::Bool)));
    }

    #[test]
    fn field_predicate_traverses_stable_default_full_permission() {
        let receiver = Exp::new(ExpKind::NullLit, Metadata::default());
        let access = FieldAccess::new(
            receiver,
            Field::new(crate::ast::program::FieldData {
                name: "f".into(),
                typ: Type::Int,
                meta: Metadata::default(),
            }),
            Metadata::default(),
        );
        let predicate = Exp::new(
            ExpKind::FieldAccessPredicate(access, None),
            Metadata::default(),
        );
        let first = subnodes(&Node::Exp(predicate.clone())).unwrap();
        let second = subnodes(&Node::Exp(predicate)).unwrap();
        match (&first[1], &second[1]) {
            (Node::Exp(a), Node::Exp(b)) => {
                assert!(matches!(a.kind(), ExpKind::FullPerm));
                assert!(a.same_node(b));
            }
            _ => panic!("expected default permission expression"),
        }
    }
}

/// Errors from expression-only reconstruction of a general Silver node.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NodeReplacementError {
    Expression(super::rewriter::strategy::ExpressionReplacementError),
    Statement(super::statements::StatementReplacementError),
    InvalidTypedNode(&'static str),
    Extension(&'static str),
}
impl From<super::rewriter::strategy::ExpressionReplacementError> for NodeReplacementError {
    fn from(e: super::rewriter::strategy::ExpressionReplacementError) -> Self {
        Self::Expression(e)
    }
}
impl From<super::statements::StatementReplacementError> for NodeReplacementError {
    fn from(e: super::statements::StatementReplacementError) -> Self {
        Self::Statement(e)
    }
}
/// Simultaneous expression-key replacement throughout built-in program nodes. This
/// does not replace declarations/types themselves; extension reconstruction is fallible.
pub fn replace_expressions(
    root: &Node,
    replacements: &[(Exp, Exp)],
) -> Result<Node, NodeReplacementError> {
    use super::rewriter::strategy::replace_expressions as replace;
    use crate::ast::program::{DomainAxiom, DomainAxiomKind, Member, Program};
    fn axiom(
        a: &DomainAxiom,
        replacements: &[(Exp, Exp)],
    ) -> Result<DomainAxiom, NodeReplacementError> {
        let original = a.exp();
        let changed = replace(original, replacements)?;
        if changed == *original {
            return Ok(a.clone());
        }
        Ok(a.copy_with(|kind| match kind {
            DomainAxiomKind::Named { exp, .. } | DomainAxiomKind::Anonymous { exp, .. } => {
                *exp = changed
            }
        }))
    }
    fn member(m: &Member, replacements: &[(Exp, Exp)]) -> Result<Member, NodeReplacementError> {
        let exp = |e: &Exp| replace(e, replacements).map_err(NodeReplacementError::from);
        let exps = |es: &[Exp]| es.iter().map(exp).collect::<Result<Vec<_>, _>>();
        Ok(match m {
            Member::Domain(d) => {
                let axioms = d
                    .axioms
                    .iter()
                    .map(|a| axiom(a, replacements))
                    .collect::<Result<Vec<_>, _>>()?;
                Member::Domain(if axioms == d.axioms {
                    d.clone()
                } else {
                    d.copy_with(|d| d.axioms = axioms)
                })
            }
            Member::Field(f) => Member::Field(f.clone()),
            Member::Function(f) => {
                let pres = exps(&f.pres)?;
                let posts = exps(&f.posts)?;
                let body = f.body.as_ref().map(exp).transpose()?;
                Member::Function(if pres == f.pres && posts == f.posts && body == f.body {
                    f.clone()
                } else {
                    f.copy_with(|f| {
                        f.pres = pres;
                        f.posts = posts;
                        f.body = body;
                    })
                })
            }
            Member::Predicate(p) => {
                let body = p.body.as_ref().map(exp).transpose()?;
                Member::Predicate(if body == p.body {
                    p.clone()
                } else {
                    p.copy_with(|p| p.body = body)
                })
            }
            Member::Method(m) => {
                let pres = exps(&m.pres)?;
                let posts = exps(&m.posts)?;
                let body = m
                    .body
                    .as_ref()
                    .map(|s| super::statements::replace_expressions(s, replacements))
                    .transpose()?;
                Member::Method(if pres == m.pres && posts == m.posts && body == m.body {
                    m.clone()
                } else {
                    m.copy_with(|m| {
                        m.pres = pres;
                        m.posts = posts;
                        m.body = body;
                    })
                })
            }
            Member::Extension(_) => {
                return Err(NodeReplacementError::Extension("member reconstruction"));
            }
        })
    }
    if replacements.is_empty() {
        return Ok(root.clone());
    }
    Ok(match root {
        Node::Program(p) => {
            let domains = p
                .domains
                .iter()
                .map(|v| member(&Member::Domain(v.clone()), replacements))
                .map(|v| match v? {
                    Member::Domain(v) => Ok(v),
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, NodeReplacementError>>()?;
            let functions = p
                .functions
                .iter()
                .map(|v| member(&Member::Function(v.clone()), replacements))
                .map(|v| match v? {
                    Member::Function(v) => Ok(v),
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, NodeReplacementError>>()?;
            let predicates = p
                .predicates
                .iter()
                .map(|v| member(&Member::Predicate(v.clone()), replacements))
                .map(|v| match v? {
                    Member::Predicate(v) => Ok(v),
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, NodeReplacementError>>()?;
            let methods = p
                .methods
                .iter()
                .map(|v| member(&Member::Method(v.clone()), replacements))
                .map(|v| match v? {
                    Member::Method(v) => Ok(v),
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, NodeReplacementError>>()?;
            if !p.extensions.is_empty() {
                return Err(NodeReplacementError::Extension(
                    "program extension reconstruction",
                ));
            }
            if domains == p.domains
                && functions == p.functions
                && predicates == p.predicates
                && methods == p.methods
            {
                Node::Program(p.clone())
            } else {
                Node::Program(Program::new(
                    domains,
                    p.fields.clone(),
                    functions,
                    predicates,
                    methods,
                    p.extensions.clone(),
                    p.meta.clone(),
                ))
            }
        }
        Node::Member(m) => Node::Member(member(m, replacements)?),
        Node::DomainAxiom(a) => Node::DomainAxiom(axiom(a, replacements)?),
        Node::Exp(e) => Node::Exp(replace(e, replacements)?),
        Node::Stmt(s) => Node::Stmt(super::statements::replace_expressions(s, replacements)?),
        Node::LocalVar(v) => {
            let e = Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone());
            let e = replace(&e, replacements)?;
            if let ExpKind::LocalVar(v) = e.kind() {
                Node::LocalVar(v.clone())
            } else {
                return Err(NodeReplacementError::InvalidTypedNode("LocalVar"));
            }
        }
        Node::FieldAccess(v) => {
            let e = Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone());
            let e = replace(&e, replacements)?;
            if let ExpKind::FieldAccess(v) = e.kind() {
                Node::FieldAccess(v.clone())
            } else {
                return Err(NodeReplacementError::InvalidTypedNode("FieldAccess"));
            }
        }
        Node::PredicateAccess(v) => {
            let e = Exp::new(ExpKind::PredicateAccess(v.clone()), v.meta.clone());
            let e = replace(&e, replacements)?;
            if let ExpKind::PredicateAccess(v) = e.kind() {
                Node::PredicateAccess(v.clone())
            } else {
                return Err(NodeReplacementError::InvalidTypedNode("PredicateAccess"));
            }
        }
        Node::PredicateAccessPredicate(v) => {
            let e = Exp::new(ExpKind::PredicateAccessPredicate(v.clone()), v.meta.clone());
            let e = replace(&e, replacements)?;
            if let ExpKind::PredicateAccessPredicate(v) = e.kind() {
                Node::PredicateAccessPredicate(v.clone())
            } else {
                return Err(NodeReplacementError::InvalidTypedNode(
                    "PredicateAccessPredicate",
                ));
            }
        }
        Node::Trigger(t) => {
            let exps = t
                .exps
                .iter()
                .map(|e| replace(e, replacements))
                .collect::<Result<Vec<_>, _>>()?;
            Node::Trigger(if exps == t.exps {
                t.clone()
            } else {
                Trigger::new(exps, t.meta.clone())
            })
        }
        Node::LabelDecl(label) => {
            let invariants = label
                .invariants
                .iter()
                .map(|e| replace(e, replacements))
                .collect::<Result<Vec<_>, _>>()?;
            Node::LabelDecl(if invariants == label.invariants {
                label.clone()
            } else {
                label.copy_with(|data| data.invariants = invariants)
            })
        }
        Node::DomainFunc(_) | Node::LocalDecl(_) | Node::UnnamedLocalDecl(_) | Node::Type(_) => {
            root.clone()
        }
    })
}

/// Maps each expression root in program/source order, delegating expression recursion to the caller.
pub fn map_expression_roots<
    E: From<NodeReplacementError> + From<super::statements::StatementReplacementError>,
>(
    root: &Node,
    replace: &dyn Fn(&Exp) -> Result<Exp, E>,
) -> Result<Node, E> {
    map_expression_roots_with_extensions(root, replace, &|_, _| {
        Err(super::statements::StatementReplacementError::Extension.into())
    })
}

pub fn map_expression_roots_with_extensions<
    E: From<NodeReplacementError> + From<super::statements::StatementReplacementError>,
>(
    root: &Node,
    replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    extension: &dyn Fn(
        &crate::ast::statement::ExtensionStmtHandle,
        &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<crate::ast::statement::ExtensionStmtHandle, E>,
) -> Result<Node, E> {
    use crate::ast::program::{DomainAxiom, DomainAxiomKind, Member, Program};
    fn axiom<E: From<NodeReplacementError>>(
        a: &DomainAxiom,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
    ) -> Result<DomainAxiom, E> {
        let original = a.exp();
        let changed = replace(original)?;
        if changed == *original {
            return Ok(a.clone());
        }
        Ok(a.copy_with(|kind| match kind {
            DomainAxiomKind::Named { exp, .. } | DomainAxiomKind::Anonymous { exp, .. } => {
                *exp = changed
            }
        }))
    }
    fn member<
        E: From<NodeReplacementError> + From<super::statements::StatementReplacementError>,
    >(
        m: &Member,
        replace: &dyn Fn(&Exp) -> Result<Exp, E>,
        extension: &dyn Fn(
            &crate::ast::statement::ExtensionStmtHandle,
            &dyn Fn(&Exp) -> Result<Exp, E>,
        ) -> Result<crate::ast::statement::ExtensionStmtHandle, E>,
    ) -> Result<Member, E> {
        let exp = |e: &Exp| replace(e);
        let exps = |es: &[Exp]| es.iter().map(exp).collect::<Result<Vec<_>, _>>();
        Ok(match m {
            Member::Domain(d) => {
                let axioms = d
                    .axioms
                    .iter()
                    .map(|a| axiom(a, replace))
                    .collect::<Result<Vec<_>, _>>()?;
                Member::Domain(if axioms == d.axioms {
                    d.clone()
                } else {
                    d.copy_with(|d| d.axioms = axioms)
                })
            }
            Member::Field(f) => Member::Field(f.clone()),
            Member::Function(f) => {
                let pres = exps(&f.pres)?;
                let posts = exps(&f.posts)?;
                let body = f.body.as_ref().map(exp).transpose()?;
                Member::Function(if pres == f.pres && posts == f.posts && body == f.body {
                    f.clone()
                } else {
                    f.copy_with(|f| {
                        f.pres = pres;
                        f.posts = posts;
                        f.body = body;
                    })
                })
            }
            Member::Predicate(p) => {
                let body = p.body.as_ref().map(exp).transpose()?;
                Member::Predicate(if body == p.body {
                    p.clone()
                } else {
                    p.copy_with(|p| p.body = body)
                })
            }
            Member::Method(m) => {
                let pres = exps(&m.pres)?;
                let posts = exps(&m.posts)?;
                let body = m
                    .body
                    .as_ref()
                    .map(|s| {
                        super::statements::map_expression_roots_with_extensions(
                            s, replace, extension,
                        )
                    })
                    .transpose()?;
                Member::Method(if pres == m.pres && posts == m.posts && body == m.body {
                    m.clone()
                } else {
                    m.copy_with(|m| {
                        m.pres = pres;
                        m.posts = posts;
                        m.body = body;
                    })
                })
            }
            Member::Extension(_) => {
                return Err(NodeReplacementError::Extension("member reconstruction").into());
            }
        })
    }
    Ok(match root {
        Node::Program(p) => {
            let domains = p
                .domains
                .iter()
                .map(|v| member(&Member::Domain(v.clone()), replace, extension))
                .map(|v| match v? {
                    Member::Domain(v) => Ok(v),
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, E>>()?;
            let functions = p
                .functions
                .iter()
                .map(|v| member(&Member::Function(v.clone()), replace, extension))
                .map(|v| match v? {
                    Member::Function(v) => Ok(v),
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, E>>()?;
            let predicates = p
                .predicates
                .iter()
                .map(|v| member(&Member::Predicate(v.clone()), replace, extension))
                .map(|v| match v? {
                    Member::Predicate(v) => Ok(v),
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, E>>()?;
            let methods = p
                .methods
                .iter()
                .map(|v| member(&Member::Method(v.clone()), replace, extension))
                .map(|v| match v? {
                    Member::Method(v) => Ok(v),
                    _ => unreachable!(),
                })
                .collect::<Result<Vec<_>, E>>()?;
            if !p.extensions.is_empty() {
                return Err(
                    NodeReplacementError::Extension("program extension reconstruction").into(),
                );
            }
            if domains == p.domains
                && functions == p.functions
                && predicates == p.predicates
                && methods == p.methods
            {
                Node::Program(p.clone())
            } else {
                Node::Program(Program::new(
                    domains,
                    p.fields.clone(),
                    functions,
                    predicates,
                    methods,
                    p.extensions.clone(),
                    p.meta.clone(),
                ))
            }
        }
        Node::Member(m) => Node::Member(member(m, replace, extension)?),
        Node::DomainAxiom(a) => Node::DomainAxiom(axiom(a, replace)?),
        Node::Exp(e) => Node::Exp(replace(e)?),
        Node::Stmt(s) => Node::Stmt(super::statements::map_expression_roots_with_extensions(
            s, replace, extension,
        )?),
        Node::LocalVar(v) => {
            let e = Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone());
            let e = replace(&e)?;
            if let ExpKind::LocalVar(v) = e.kind() {
                Node::LocalVar(v.clone())
            } else {
                return Err(NodeReplacementError::InvalidTypedNode("LocalVar").into());
            }
        }
        Node::FieldAccess(v) => {
            let e = Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone());
            let e = replace(&e)?;
            if let ExpKind::FieldAccess(v) = e.kind() {
                Node::FieldAccess(v.clone())
            } else {
                return Err(NodeReplacementError::InvalidTypedNode("FieldAccess").into());
            }
        }
        Node::PredicateAccess(v) => {
            let e = Exp::new(ExpKind::PredicateAccess(v.clone()), v.meta.clone());
            let e = replace(&e)?;
            if let ExpKind::PredicateAccess(v) = e.kind() {
                Node::PredicateAccess(v.clone())
            } else {
                return Err(NodeReplacementError::InvalidTypedNode("PredicateAccess").into());
            }
        }
        Node::PredicateAccessPredicate(v) => {
            let e = Exp::new(ExpKind::PredicateAccessPredicate(v.clone()), v.meta.clone());
            let e = replace(&e)?;
            if let ExpKind::PredicateAccessPredicate(v) = e.kind() {
                Node::PredicateAccessPredicate(v.clone())
            } else {
                return Err(
                    NodeReplacementError::InvalidTypedNode("PredicateAccessPredicate").into(),
                );
            }
        }
        Node::Trigger(t) => {
            let exps = t
                .exps
                .iter()
                .map(|e| replace(e))
                .collect::<Result<Vec<_>, _>>()?;
            Node::Trigger(if exps == t.exps {
                t.clone()
            } else {
                Trigger::new(exps, t.meta.clone())
            })
        }
        Node::LabelDecl(label) => {
            let invariants = label
                .invariants
                .iter()
                .map(replace)
                .collect::<Result<Vec<_>, _>>()?;
            Node::LabelDecl(if invariants == label.invariants {
                label.clone()
            } else {
                label.copy_with(|data| data.invariants = invariants)
            })
        }
        Node::DomainFunc(_) | Node::LocalDecl(_) | Node::UnnamedLocalDecl(_) | Node::Type(_) => {
            root.clone()
        }
    })
}

/// Apply one preorder rewrite/reconstruction pass over supported node products.
/// Typed product fields are recursively rewritten. Replacements must fit their typed
/// product slots; extension hooks and unsupported declarations fail explicitly. Map
/// iteration order follows the host map, and strategy contexts/modes are separate.
pub fn map_node_tree(
    node: &Node,
    rule: &dyn Fn(&Node) -> Result<Node, crate::verifier::verification_result::DiagnosticError>,
) -> Result<Node, crate::verifier::verification_result::DiagnosticError> {
    map_node_tree_impl(node, rule, true, false, false, false)
}

/// Visit source checkTransitively product fields, which exclude maps.
pub fn visit_check_products(
    node: &Node,
    rule: &dyn Fn(&Node) -> Result<Node, crate::verifier::verification_result::DiagnosticError>,
) -> Result<Node, crate::verifier::verification_result::DiagnosticError> {
    map_node_tree_impl(node, rule, false, false, false, false)
}
/// Bottom-up typed product rewriting. Forced mode also traverses the extra return
/// types of function applications, as needed by ADT type encoding. It rebuilds
/// parents so extra-list changes survive structural equality; narrowed child slots
/// reject incompatible replacements. Extension reconstruction hooks remain fallible.
pub fn map_node_tree_bottom_up(
    node: &Node,
    rule: &dyn Fn(&Node) -> Result<Node, crate::verifier::verification_result::DiagnosticError>,
    force_copy: bool,
) -> Result<Node, crate::verifier::verification_result::DiagnosticError> {
    map_node_tree_impl(node, rule, true, true, force_copy, false)
}
/// Reconstruct a node while substituting type variables in type values, preserving
/// declaration and substitution-map keys. Extra application return types are rebuilt.
pub fn substitute_node_types(
    node: &Node,
    substitution: &crate::ast::r#type::TypeSubstitution,
) -> Result<Node, crate::verifier::verification_result::DiagnosticError> {
    map_node_tree_impl(
        node,
        &|node| match node {
            Node::Type(crate::ast::r#type::Type::Var(v)) => {
                Ok(Node::Type(substitution.get(v).cloned().unwrap_or_else(
                    || crate::ast::r#type::Type::Var(v.clone()),
                )))
            }
            _ => Ok(node.clone()),
        },
        true,
        true,
        true,
        true,
    )
}
/// DomainInstances.substitute additionally reconstructs domain applications from
/// their resolved declaration and resets error transformations on applications and
/// local-variable occurrences, as the source constructors do.
pub fn substitute_domain_node_types(
    node: &Node,
    substitution: &crate::ast::r#type::TypeSubstitution,
    program: &crate::ast::program::Program,
) -> Result<Node, crate::verifier::verification_result::DiagnosticError> {
    use crate::ast::{
        ast::Metadata,
        expression::{Exp, ExpExtra, ExpKind, LocalVar},
        r#type::Type,
    };
    use crate::verifier::verification_result::DiagnosticError;
    map_node_tree_impl(
        node,
        &|node| match node {
            Node::Type(Type::Var(v)) => Ok(Node::Type(
                substitution
                    .get(v)
                    .cloned()
                    .unwrap_or_else(|| Type::Var(v.clone())),
            )),
            Node::LocalVar(v) => Ok(Node::LocalVar(LocalVar::new(
                v.name.clone(),
                v.typ.clone(),
                Metadata {
                    position: v.meta.position.clone(),
                    info: v.meta.info.clone(),
                    error_trafo: Default::default(),
                },
            ))),
            Node::Exp(e) => {
                if let ExpKind::DomainFuncApp(name, args, map) = e.kind() {
                    let func = program
                        .find_domain_function_optionally(name)
                        .ok_or(DiagnosticError::InvalidNode("domain function declaration"))?;
                    Ok(Node::Exp(Exp::with_extra(
                        ExpKind::DomainFuncApp(name.clone(), args.clone(), map.clone()),
                        Metadata {
                            position: e.metadata().position.clone(),
                            info: e.metadata().info.clone(),
                            error_trafo: Default::default(),
                        },
                        ExpExtra {
                            typ: Some(func.typ.substitute(map)),
                            domain_name: Some(func.domain_name.clone()),
                            interpretation: None,
                        },
                    )))
                } else {
                    Ok(node.clone())
                }
            }
            _ => Ok(node.clone()),
        },
        true,
        true,
        true,
        true,
    )
}
fn map_node_tree_impl(
    node: &Node,
    rule: &dyn Fn(&Node) -> Result<Node, crate::verifier::verification_result::DiagnosticError>,
    visit_maps: bool,
    bottom_up: bool,
    force_copy: bool,
    preserve_type_keys: bool,
) -> Result<Node, crate::verifier::verification_result::DiagnosticError> {
    use crate::ast::{
        expression::{Exp, ExpKind, FieldAccess, PredicateAccess, Trigger},
        program::{LocalVarDecl, Member},
        statement::{Stmt, StmtKind},
        utility::statements,
    };
    use crate::verifier::verification_result::DiagnosticError;
    struct Walker<'a> {
        rule: &'a dyn Fn(&Node) -> Result<Node, DiagnosticError>,
        visit_maps: bool,
        bottom_up: bool,
        force_copy: bool,
        preserve_type_keys: bool,
    }
    impl Walker<'_> {
        fn typ(
            &self,
            v: &crate::ast::r#type::Type,
        ) -> Result<crate::ast::r#type::Type, DiagnosticError> {
            let value = self.typ_inner(v)?;
            if self.bottom_up {
                match (self.rule)(&Node::Type(value))? {
                    Node::Type(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("type replacement")),
                }
            } else {
                Ok(value)
            }
        }
        fn unnamed(
            &self,
            v: &crate::ast::program::UnnamedLocalVarDecl,
        ) -> Result<crate::ast::program::UnnamedLocalVarDecl, DiagnosticError> {
            let value = self.unnamed_inner(v)?;
            if self.bottom_up {
                match (self.rule)(&Node::UnnamedLocalDecl(value))? {
                    Node::UnnamedLocalDecl(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode(
                        "unnamed declaration replacement",
                    )),
                }
            } else {
                Ok(value)
            }
        }
        fn local(&self, v: &LocalVarDecl) -> Result<LocalVarDecl, DiagnosticError> {
            let value = self.local_inner(v)?;
            if self.bottom_up {
                match (self.rule)(&Node::LocalDecl(value))? {
                    Node::LocalDecl(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode(
                        "local declaration replacement",
                    )),
                }
            } else {
                Ok(value)
            }
        }
        fn trigger(&self, v: &Trigger) -> Result<Trigger, DiagnosticError> {
            let value = self.trigger_inner(v)?;
            if self.bottom_up {
                match (self.rule)(&Node::Trigger(value))? {
                    Node::Trigger(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("trigger replacement")),
                }
            } else {
                Ok(value)
            }
        }
        fn exp(&self, v: &Exp) -> Result<Exp, DiagnosticError> {
            let mut value = self.exp_inner(v)?;
            if self.force_copy {
                let mut extra = value.0.extra.clone();
                if matches!(
                    value.kind(),
                    ExpKind::FuncApp(..) | ExpKind::DomainFuncApp(..)
                ) {
                    if let Some(t) = &extra.typ {
                        extra.typ = Some(self.typ(t)?);
                    }
                }
                value = Exp::with_extra(value.kind().clone(), value.metadata().clone(), extra);
            }
            if self.bottom_up {
                let view = match value.kind() {
                    ExpKind::LocalVar(v) => Node::LocalVar(v.clone()),
                    ExpKind::FieldAccess(v) => Node::FieldAccess(v.clone()),
                    ExpKind::PredicateAccess(v) => Node::PredicateAccess(v.clone()),
                    ExpKind::PredicateAccessPredicate(v) => {
                        Node::PredicateAccessPredicate(v.clone())
                    }
                    _ => Node::Exp(value),
                };
                self.as_exp((self.rule)(&view)?)
            } else {
                Ok(value)
            }
        }
        fn domain_func(
            &self,
            v: &crate::ast::program::DomainFunc,
        ) -> Result<crate::ast::program::DomainFunc, DiagnosticError> {
            let value = self.domain_func_inner(v)?;
            if self.bottom_up {
                match (self.rule)(&Node::DomainFunc(value))? {
                    Node::DomainFunc(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("domain function replacement")),
                }
            } else {
                Ok(value)
            }
        }
        fn axiom(
            &self,
            v: &crate::ast::program::DomainAxiom,
        ) -> Result<crate::ast::program::DomainAxiom, DiagnosticError> {
            let value = self.axiom_inner(v)?;
            if self.bottom_up {
                match (self.rule)(&Node::DomainAxiom(value))? {
                    Node::DomainAxiom(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("axiom replacement")),
                }
            } else {
                Ok(value)
            }
        }
        fn member(&self, v: &Member) -> Result<Member, DiagnosticError> {
            let value = self.member_inner(v)?;
            if self.bottom_up {
                match (self.rule)(&Node::Member(value))? {
                    Node::Member(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("member replacement")),
                }
            } else {
                Ok(value)
            }
        }
        fn program(
            &self,
            v: &crate::ast::program::Program,
        ) -> Result<crate::ast::program::Program, DiagnosticError> {
            let value = self.program_inner(v)?;
            if self.bottom_up {
                match (self.rule)(&Node::Program(value))? {
                    Node::Program(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("program replacement")),
                }
            } else {
                Ok(value)
            }
        }

        fn pre(&self, node: &Node) -> Result<Node, DiagnosticError> {
            if self.bottom_up {
                Ok(node.clone())
            } else {
                (self.rule)(node)
            }
        }
        fn typ_inner(
            &self,
            original: &crate::ast::r#type::Type,
        ) -> Result<crate::ast::r#type::Type, DiagnosticError> {
            use crate::ast::r#type::{DomainType, Type};
            let Node::Type(current) = self.pre(&Node::Type(original.clone()))? else {
                return Err(DiagnosticError::InvalidNode("type replacement"));
            };
            let rebuilt = match &current {
                Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => {
                    let child = self.typ(t)?;
                    if !self.force_copy && child == **t {
                        return Ok(current);
                    }
                    match &current {
                        Type::Seq(_) => Type::Seq(std::sync::Arc::new(child)),
                        Type::Set(_) => Type::Set(std::sync::Arc::new(child)),
                        _ => Type::Multiset(std::sync::Arc::new(child)),
                    }
                }
                Type::Map(pair) => {
                    let key = self.typ(&pair.0)?;
                    let value = self.typ(&pair.1)?;
                    if !self.force_copy && key == pair.0 && value == pair.1 {
                        return Ok(current);
                    }
                    Type::map(key, value)
                }
                Type::Domain(domain) => {
                    if !self.visit_maps {
                        return Ok(current);
                    }
                    let mut mappings = std::collections::HashMap::new();
                    for (var, value) in &domain.partial_type_vars {
                        let var = if self.preserve_type_keys {
                            var.clone()
                        } else {
                            let Type::Var(var) = self.typ(&Type::Var(var.clone()))? else {
                                return Err(DiagnosticError::InvalidNode(
                                    "domain type variable replacement",
                                ));
                            };
                            var
                        };
                        mappings.insert(var, self.typ(value)?);
                    }
                    if !self.force_copy && mappings == domain.partial_type_vars {
                        return Ok(current);
                    }
                    Type::Domain(DomainType::new(
                        domain.domain_name.clone(),
                        mappings,
                        domain.type_parameters.clone(),
                    ))
                }
                Type::Var(var) if self.force_copy => {
                    Type::Var(crate::ast::r#type::TypeVar::new(var.name.clone()))
                }
                Type::Backend(backend) if self.force_copy => {
                    Type::Backend(crate::ast::r#type::BackendType::new(
                        backend.viper_name.clone(),
                        backend.interpretations.clone(),
                    ))
                }
                Type::Extension(extension) => {
                    if !self.visit_maps {
                        for child in extension.check_product_nodes()? {
                            self.pass(&child)?;
                        }
                        return Ok(current);
                    }
                    let mapped = extension.map_types(&|t| self.typ(t))?;
                    if !self.force_copy && extension.equals(mapped.as_ref()) {
                        return Ok(current);
                    }
                    Type::Extension(mapped)
                }
                _ => return Ok(current),
            };
            Ok(rebuilt)
        }
        fn type_var(
            &self,
            var: &crate::ast::r#type::TypeVar,
        ) -> Result<crate::ast::r#type::TypeVar, DiagnosticError> {
            match self.typ(&crate::ast::r#type::Type::Var(var.clone()))? {
                crate::ast::r#type::Type::Var(v) => Ok(v),
                _ => Err(DiagnosticError::InvalidNode("type variable replacement")),
            }
        }
        fn unnamed_inner(
            &self,
            v: &crate::ast::program::UnnamedLocalVarDecl,
        ) -> Result<crate::ast::program::UnnamedLocalVarDecl, DiagnosticError> {
            let Node::UnnamedLocalDecl(v) = self.pre(&Node::UnnamedLocalDecl(v.clone()))? else {
                return Err(DiagnosticError::InvalidNode(
                    "unnamed declaration replacement",
                ));
            };
            let typ = self.typ(&v.typ)?;
            Ok(if !self.force_copy && typ == v.typ {
                v
            } else {
                v.copy_with(|data| data.typ = typ)
            })
        }
        fn as_exp(&self, n: Node) -> Result<Exp, DiagnosticError> {
            Ok(match n {
                Node::Exp(e) => e,
                Node::LocalVar(v) => Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone()),
                Node::FieldAccess(v) => Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone()),
                Node::PredicateAccess(v) => {
                    Exp::new(ExpKind::PredicateAccess(v.clone()), v.meta.clone())
                }
                Node::PredicateAccessPredicate(v) => {
                    Exp::new(ExpKind::PredicateAccessPredicate(v.clone()), v.meta.clone())
                }
                _ => return Err(DiagnosticError::InvalidNode("expression backlink")),
            })
        }
        fn local_inner(&self, v: &LocalVarDecl) -> Result<LocalVarDecl, DiagnosticError> {
            let Node::LocalDecl(v) = self.pre(&Node::LocalDecl(v.clone()))? else {
                return Err(DiagnosticError::InvalidNode("local declaration backlink"));
            };
            let typ = self.typ(&v.typ)?;
            Ok(if !self.force_copy && typ == v.typ {
                v
            } else {
                LocalVarDecl::new(v.name.clone(), typ, v.meta.clone())
            })
        }
        fn trigger_inner(&self, t: &Trigger) -> Result<Trigger, DiagnosticError> {
            let Node::Trigger(current) = self.pre(&Node::Trigger(t.clone()))? else {
                return Err(DiagnosticError::InvalidNode("trigger replacement"));
            };
            let t = &current;
            let exps = t
                .exps
                .iter()
                .map(|v| self.exp(v))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(if !self.force_copy && exps == t.exps {
                t.clone()
            } else {
                Trigger::new(exps, t.meta.clone())
            })
        }
        fn field(&self, f: &FieldAccess) -> Result<FieldAccess, DiagnosticError> {
            let original = Exp::new(ExpKind::FieldAccess(f.clone()), f.meta.clone());
            let mapped = self.exp(&original)?;
            match mapped.kind() {
                ExpKind::FieldAccess(v) => Ok(v.clone()),
                _ => Err(DiagnosticError::InvalidNode("field access backlink")),
            }
        }
        fn predicate(&self, p: &PredicateAccess) -> Result<PredicateAccess, DiagnosticError> {
            let original = Exp::new(ExpKind::PredicateAccess(p.clone()), p.meta.clone());
            let mapped = self.exp(&original)?;
            match mapped.kind() {
                ExpKind::PredicateAccess(v) => Ok(v.clone()),
                _ => Err(DiagnosticError::InvalidNode("predicate access backlink")),
            }
        }
        fn exp_inner(&self, e: &Exp) -> Result<Exp, DiagnosticError> {
            let view = match e.kind() {
                ExpKind::LocalVar(v) => Node::LocalVar(v.clone()),
                ExpKind::FieldAccess(v) => Node::FieldAccess(v.clone()),
                ExpKind::PredicateAccess(v) => Node::PredicateAccess(v.clone()),
                ExpKind::PredicateAccessPredicate(v) => Node::PredicateAccessPredicate(v.clone()),
                _ => Node::Exp(e.clone()),
            };
            let current = self.as_exp(self.pre(&view)?)?;
            let special = match current.kind() {
                ExpKind::LocalVar(v) => {
                    let typ = self.typ(&v.typ)?;
                    if !self.force_copy && typ == v.typ {
                        return Ok(current);
                    }
                    Some(ExpKind::LocalVar(crate::ast::expression::LocalVar::new(
                        v.name.clone(),
                        typ,
                        v.meta.clone(),
                    )))
                }
                ExpKind::Result(t) => {
                    let typ = self.typ(t)?;
                    if !self.force_copy && typ == *t {
                        return Ok(current);
                    }
                    Some(ExpKind::Result(typ))
                }
                ExpKind::LocalVarWithVersion(name, t) => {
                    let typ = self.typ(t)?;
                    if !self.force_copy && typ == *t {
                        return Ok(current);
                    }
                    Some(ExpKind::LocalVarWithVersion(name.clone(), typ))
                }
                ExpKind::BackendValueLit(value, t) => {
                    let typ = self.typ(t)?;
                    if !self.force_copy && typ == *t {
                        return Ok(current);
                    }
                    Some(ExpKind::BackendValueLit(value.clone(), typ))
                }
                ExpKind::EmptySeq(t) | ExpKind::EmptySet(t) | ExpKind::EmptyMultiset(t) => {
                    let typ = self.typ(t)?;
                    if !self.force_copy && typ == *t {
                        return Ok(current);
                    }
                    Some(match current.kind() {
                        ExpKind::EmptySeq(_) => ExpKind::EmptySeq(typ),
                        ExpKind::EmptySet(_) => ExpKind::EmptySet(typ),
                        _ => ExpKind::EmptyMultiset(typ),
                    })
                }
                ExpKind::EmptyMap(k, v) => {
                    let nk = self.typ(k)?;
                    let nv = self.typ(v)?;
                    if !self.force_copy && nk == *k && nv == *v {
                        return Ok(current);
                    }
                    Some(ExpKind::EmptyMap(nk, nv))
                }
                ExpKind::DomainFuncApp(name, args, substitutions) => {
                    let args2 = args
                        .iter()
                        .map(|v| self.exp(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let mut substitutions2 = std::collections::HashMap::new();
                    if self.visit_maps {
                        for (k, v) in substitutions {
                            substitutions2.insert(
                                if self.preserve_type_keys {
                                    k.clone()
                                } else {
                                    self.type_var(k)?
                                },
                                self.typ(v)?,
                            );
                        }
                    } else {
                        substitutions2 = substitutions.clone();
                    }
                    if !self.force_copy && args2 == *args && substitutions2 == *substitutions {
                        return Ok(current);
                    }
                    Some(ExpKind::DomainFuncApp(name.clone(), args2, substitutions2))
                }
                ExpKind::FieldAccess(f) => {
                    let receiver = self.exp(&f.receiver)?;
                    let member = match self.member(&Member::Field(f.field.clone()))? {
                        Member::Field(field) => field,
                        _ => {
                            return Err(DiagnosticError::InvalidNode("field declaration backlink"));
                        }
                    };
                    if !self.force_copy && receiver == f.receiver && member == f.field {
                        return Ok(current);
                    }
                    Some(ExpKind::FieldAccess(FieldAccess::new(
                        receiver,
                        member,
                        f.meta.clone(),
                    )))
                }
                ExpKind::Let(v, value, body) => {
                    let nv = self.local(v)?;
                    let value2 = self.exp(value)?;
                    let body2 = self.exp(body)?;
                    if !self.force_copy && nv == *v && value2 == *value && body2 == *body {
                        return Ok(current);
                    }
                    Some(ExpKind::Let(nv, value2, body2))
                }
                ExpKind::Forall(vars, triggers, body) | ExpKind::Exists(vars, triggers, body) => {
                    let nv = vars
                        .iter()
                        .map(|v| self.local(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let nt = triggers
                        .iter()
                        .map(|v| self.trigger(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let nb = self.exp(body)?;
                    if !self.force_copy && nv == *vars && nt == *triggers && nb == *body {
                        return Ok(current);
                    }
                    Some(if matches!(current.kind(), ExpKind::Forall(..)) {
                        ExpKind::Forall(nv, nt, nb)
                    } else {
                        ExpKind::Exists(nv, nt, nb)
                    })
                }
                ExpKind::ForPerm(vars, resource, body) => {
                    let nv = vars
                        .iter()
                        .map(|v| self.local(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let nr = self.exp(resource)?;
                    let nb = self.exp(body)?;
                    if !self.force_copy && nv == *vars && nr == *resource && nb == *body {
                        return Ok(current);
                    }
                    Some(ExpKind::ForPerm(nv, nr, nb))
                }
                _ => None,
            };
            if let Some(kind) = special {
                return Ok(Exp::with_extra(
                    kind,
                    current.metadata().clone(),
                    current.0.extra.clone(),
                ));
            }
            if !self.visit_maps {
                if let ExpKind::Extension(extension) = current.kind() {
                    for child in extension.0.check_product_nodes()? {
                        self.pass(&child)?;
                    }
                    return Ok(current);
                }
            }
            if self.force_copy {
                current.map_expression_children_by_identity(
                    &mut |v| self.exp(v),
                    &mut |extension| extension.0.map_expressions(&|e| self.exp(e)),
                    &mut |v| self.field(v),
                    &mut |v| self.predicate(v),
                    &mut |v| self.trigger(v),
                )
            } else {
                current.map_expression_children(
                    &mut |v| self.exp(v),
                    &mut |extension| extension.0.map_expressions(&|e| self.exp(e)),
                    &mut |v| self.field(v),
                    &mut |v| self.predicate(v),
                    &mut |v| self.trigger(v),
                )
            }
        }
        fn stmt(&self, s: &Stmt) -> Result<Stmt, DiagnosticError> {
            statements::map_statement_tree_with_post(
                s,
                &|e| self.exp(e),
                &|n| self.pre(n),
                &|n| self.pass(n),
                &|ext, map| {
                    if self.visit_maps {
                        ext.0.map_expressions(map)
                    } else {
                        for child in ext.0.check_product_nodes()? {
                            self.pass(&child)?;
                        }
                        Ok(ext.clone())
                    }
                },
                if self.bottom_up {
                    Some(self.rule)
                } else {
                    None
                },
                self.force_copy,
            )
        }
        fn domain_func_inner(
            &self,
            f: &crate::ast::program::DomainFunc,
        ) -> Result<crate::ast::program::DomainFunc, DiagnosticError> {
            use crate::ast::program::AnyLocalVarDecl;
            let Node::DomainFunc(f) = self.pre(&Node::DomainFunc(f.clone()))? else {
                return Err(DiagnosticError::InvalidNode("domain function backlink"));
            };
            let args = f
                .formal_args
                .iter()
                .map(|a| -> Result<AnyLocalVarDecl, DiagnosticError> {
                    match a {
                        AnyLocalVarDecl::Named(v) => Ok(AnyLocalVarDecl::Named(self.local(v)?)),
                        AnyLocalVarDecl::Unnamed(v) => {
                            Ok(AnyLocalVarDecl::Unnamed(self.unnamed(v)?))
                        }
                    }
                })
                .collect::<Result<Vec<_>, _>>()?;
            let typ = self.typ(&f.typ)?;
            Ok(
                if !self.force_copy && args == f.formal_args && typ == f.typ {
                    f
                } else {
                    f.copy_with(|d| {
                        d.formal_args = args;
                        d.typ = typ;
                    })
                },
            )
        }
        fn axiom_inner(
            &self,
            a: &crate::ast::program::DomainAxiom,
        ) -> Result<crate::ast::program::DomainAxiom, DiagnosticError> {
            use crate::ast::program::DomainAxiomKind;
            let Node::DomainAxiom(a) = self.pre(&Node::DomainAxiom(a.clone()))? else {
                return Err(DiagnosticError::InvalidNode("domain axiom backlink"));
            };
            let changed = self.exp(a.exp())?;
            Ok(if !self.force_copy && changed == *a.exp() {
                a
            } else {
                a.copy_with(|kind| match kind {
                    DomainAxiomKind::Named { exp, .. } | DomainAxiomKind::Anonymous { exp, .. } => {
                        *exp = changed
                    }
                })
            })
        }
        fn member_inner(&self, m: &Member) -> Result<Member, DiagnosticError> {
            let Node::Member(m) = self.pre(&Node::Member(m.clone()))? else {
                return Err(DiagnosticError::InvalidNode("member backlink"));
            };
            Ok(match m {
                Member::Domain(d) => {
                    let funcs = d
                        .functions
                        .iter()
                        .map(|v| self.domain_func(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let axioms = d
                        .axioms
                        .iter()
                        .map(|v| self.axiom(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let type_vars = d
                        .type_vars
                        .iter()
                        .map(|v| self.type_var(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    Member::Domain(
                        if !self.force_copy
                            && funcs == d.functions
                            && axioms == d.axioms
                            && type_vars == d.type_vars
                        {
                            d
                        } else {
                            d.copy_with(|v| {
                                v.functions = funcs;
                                v.axioms = axioms;
                                v.type_vars = type_vars;
                            })
                        },
                    )
                }
                Member::Field(f) => {
                    let typ = self.typ(&f.typ)?;
                    Member::Field(if !self.force_copy && typ == f.typ {
                        f
                    } else {
                        f.copy_with(|v| v.typ = typ)
                    })
                }
                Member::Function(f) => {
                    let args = f
                        .formal_args
                        .iter()
                        .map(|v| self.local(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let typ = self.typ(&f.typ)?;
                    let pres = f
                        .pres
                        .iter()
                        .map(|v| self.exp(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let posts = f
                        .posts
                        .iter()
                        .map(|v| self.exp(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let body = f.body.as_ref().map(|v| self.exp(v)).transpose()?;
                    Member::Function(
                        if !self.force_copy
                            && args == f.formal_args
                            && typ == f.typ
                            && pres == f.pres
                            && posts == f.posts
                            && body == f.body
                        {
                            f
                        } else {
                            f.copy_with(|v| {
                                v.formal_args = args;
                                v.typ = typ;
                                v.pres = pres;
                                v.posts = posts;
                                v.body = body;
                            })
                        },
                    )
                }
                Member::Predicate(p) => {
                    let args = p
                        .formal_args
                        .iter()
                        .map(|v| self.local(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let body = p.body.as_ref().map(|v| self.exp(v)).transpose()?;
                    Member::Predicate(
                        if !self.force_copy && args == p.formal_args && body == p.body {
                            p
                        } else {
                            p.copy_with(|v| {
                                v.formal_args = args;
                                v.body = body;
                            })
                        },
                    )
                }
                Member::Method(m) => {
                    let args = m
                        .formal_args
                        .iter()
                        .map(|v| self.local(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let returns = m
                        .formal_returns
                        .iter()
                        .map(|v| self.local(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let pres = m
                        .pres
                        .iter()
                        .map(|v| self.exp(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let posts = m
                        .posts
                        .iter()
                        .map(|v| self.exp(v))
                        .collect::<Result<Vec<_>, _>>()?;
                    let body = m.body.as_ref().map(|v| self.stmt(v)).transpose()?;
                    Member::Method(
                        if !self.force_copy
                            && args == m.formal_args
                            && returns == m.formal_returns
                            && pres == m.pres
                            && posts == m.posts
                            && body == m.body
                        {
                            m
                        } else {
                            m.copy_with(|v| {
                                v.formal_args = args;
                                v.formal_returns = returns;
                                v.pres = pres;
                                v.posts = posts;
                                v.body = body;
                            })
                        },
                    )
                }
                Member::Extension(v) => {
                    if !self.visit_maps {
                        for child in v.0.check_product_nodes()? {
                            self.pass(&child)?;
                        }
                        return Ok(Member::Extension(v));
                    }
                    let rebuilt = v.0.map_nodes(&|n| self.pass(n))?;
                    Member::Extension(if !self.force_copy && rebuilt == v {
                        v
                    } else {
                        rebuilt
                    })
                }
            })
        }
        fn program_inner(
            &self,
            p: &crate::ast::program::Program,
        ) -> Result<crate::ast::program::Program, DiagnosticError> {
            let Node::Program(p) = self.pre(&Node::Program(p.clone()))? else {
                return Err(DiagnosticError::InvalidNode("program backlink"));
            };
            let domains = p
                .domains
                .iter()
                .map(|v| match self.member(&Member::Domain(v.clone()))? {
                    Member::Domain(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("domain slot")),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let fields = p
                .fields
                .iter()
                .map(|v| match self.member(&Member::Field(v.clone()))? {
                    Member::Field(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("field slot")),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let functions = p
                .functions
                .iter()
                .map(|v| match self.member(&Member::Function(v.clone()))? {
                    Member::Function(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("function slot")),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let predicates = p
                .predicates
                .iter()
                .map(|v| match self.member(&Member::Predicate(v.clone()))? {
                    Member::Predicate(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("predicate slot")),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let methods = p
                .methods
                .iter()
                .map(|v| match self.member(&Member::Method(v.clone()))? {
                    Member::Method(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("method slot")),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let extensions = p
                .extensions
                .iter()
                .map(|v| match self.member(&Member::Extension(v.clone()))? {
                    Member::Extension(v) => Ok(v),
                    _ => Err(DiagnosticError::InvalidNode("extension member slot")),
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(
                if !self.force_copy
                    && domains == p.domains
                    && fields == p.fields
                    && functions == p.functions
                    && predicates == p.predicates
                    && methods == p.methods
                    && extensions == p.extensions
                {
                    p
                } else {
                    p.copy_with(|v| {
                        v.domains = domains;
                        v.fields = fields;
                        v.functions = functions;
                        v.predicates = predicates;
                        v.methods = methods;
                        v.extensions = extensions;
                    })
                },
            )
        }
        fn pass(&self, node: &Node) -> Result<Node, DiagnosticError> {
            Ok(match node {
                Node::Exp(e) => Node::Exp(self.exp(e)?),
                Node::LocalVar(v) => {
                    match self
                        .exp(&Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone()))?
                        .kind()
                    {
                        ExpKind::LocalVar(v) => Node::LocalVar(v.clone()),
                        _ => return Err(DiagnosticError::InvalidNode("local variable backlink")),
                    }
                }
                Node::FieldAccess(v) => Node::FieldAccess(self.field(v)?),
                Node::PredicateAccess(v) => Node::PredicateAccess(self.predicate(v)?),
                Node::PredicateAccessPredicate(v) => match self
                    .exp(&Exp::new(
                        ExpKind::PredicateAccessPredicate(v.clone()),
                        v.meta.clone(),
                    ))?
                    .kind()
                {
                    ExpKind::PredicateAccessPredicate(v) => {
                        Node::PredicateAccessPredicate(v.clone())
                    }
                    _ => {
                        return Err(DiagnosticError::InvalidNode(
                            "predicate permission backlink",
                        ));
                    }
                },
                Node::Stmt(s) => Node::Stmt(self.stmt(s)?),
                Node::LabelDecl(label) => {
                    let view = Stmt::new(StmtKind::Label(label.clone()), label.meta.clone());
                    let result = self.stmt(&view)?;
                    match result.kind() {
                        StmtKind::Label(v) => Node::LabelDecl(v.clone()),
                        _ => return Err(DiagnosticError::InvalidNode("label backlink")),
                    }
                }
                Node::LocalDecl(v) => Node::LocalDecl(self.local(v)?),
                Node::UnnamedLocalDecl(v) => Node::UnnamedLocalDecl(self.unnamed(v)?),
                Node::Program(p) => Node::Program(self.program(p)?),
                Node::Member(m) => Node::Member(self.member(m)?),
                Node::DomainFunc(f) => Node::DomainFunc(self.domain_func(f)?),
                Node::DomainAxiom(a) => Node::DomainAxiom(self.axiom(a)?),
                Node::Trigger(t) => Node::Trigger(self.trigger(t)?),
                Node::Type(t) => Node::Type(self.typ(t)?),
            })
        }
    }
    Walker {
        rule,
        visit_maps,
        bottom_up,
        force_copy,
        preserve_type_keys,
    }
    .pass(node)
}

#[cfg(test)]
mod reconstruction_tests {
    use super::*;
    use crate::ast::{ast::Metadata, program::Function, r#type::Type};
    #[test]
    fn consistency_products_skip_extension_substitution_maps() {
        use crate::ast::r#type::TypeVar;
        use crate::plugin::standard::adt::adt_ast_extension::AdtType;
        use std::cell::Cell;
        use std::collections::HashMap;
        let variable = TypeVar::new("T");
        let ty = AdtType::new("D", HashMap::from([(variable, Type::Int)]), vec![]).as_type();
        let seen = Cell::new(0);
        visit_check_products(&Node::Type(ty.clone()), &|node| {
            if matches!(node, Node::Type(Type::Int)) {
                seen.set(seen.get() + 1);
            }
            Ok(node.clone())
        })
        .unwrap();
        assert_eq!(seen.get(), 0);
        map_node_tree(&Node::Type(ty), &|node| {
            if matches!(node, Node::Type(Type::Int)) {
                seen.set(seen.get() + 1);
            }
            Ok(node.clone())
        })
        .unwrap();
        assert_eq!(seen.get(), 1);
    }
    #[test]
    fn bottom_up_rebuilds_extra_type_through_statement() {
        use crate::ast::{
            expression::ExpExtra,
            statement::{Stmt, StmtKind},
        };
        let meta = Metadata::default();
        let app = Exp::with_extra(
            ExpKind::FuncApp("f".into(), vec![]),
            meta.clone(),
            ExpExtra {
                typ: Some(Type::Int),
                ..Default::default()
            },
        );
        let expression = Exp::new(ExpKind::Not(app), meta.clone());
        let statement = Stmt::new(StmtKind::Assert(expression), meta);
        let result = map_node_tree_bottom_up(
            &Node::Stmt(statement),
            &|n| {
                Ok(if matches!(n, Node::Type(Type::Int)) {
                    Node::Type(Type::Bool)
                } else {
                    n.clone()
                })
            },
            true,
        )
        .unwrap();
        let Node::Stmt(stmt) = result else {
            panic!("statement")
        };
        let StmtKind::Assert(expression) = stmt.kind() else {
            panic!("assert")
        };
        let ExpKind::Not(app) = expression.kind() else {
            panic!("not")
        };
        assert!(matches!(app.0.extra.typ, Some(Type::Bool)));
    }
    #[test]
    fn bottom_up_force_preserves_extra_type_through_program_member() {
        use crate::ast::{
            expression::ExpExtra,
            program::{FunctionData, Program},
        };
        let meta = Metadata::default();
        let app = Exp::with_extra(
            ExpKind::FuncApp("g".into(), vec![]),
            meta.clone(),
            ExpExtra {
                typ: Some(Type::Int),
                ..Default::default()
            },
        );
        let function = Function::new(FunctionData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(app),
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![function], vec![], vec![], vec![], meta);
        let Node::Program(result) = map_node_tree_bottom_up(
            &Node::Program(program),
            &|n| {
                Ok(if matches!(n, Node::Type(Type::Int)) {
                    Node::Type(Type::Bool)
                } else {
                    n.clone()
                })
            },
            true,
        )
        .unwrap() else {
            panic!("program")
        };
        assert!(matches!(
            result.functions[0].body.as_ref().unwrap().0.extra.typ,
            Some(Type::Bool)
        ));
    }
    #[test]
    fn forced_type_reconstruction_copies_case_class_identity() {
        use crate::ast::r#type::TypeVar;
        let variable = TypeVar::new("T");
        let Node::Type(Type::Var(result)) = map_node_tree_bottom_up(
            &Node::Type(Type::Var(variable.clone())),
            &|n| Ok(n.clone()),
            true,
        )
        .unwrap() else {
            panic!("type variable")
        };
        assert_eq!(variable, result);
        assert!(!variable.same_node(&result));
    }
    #[test]
    fn bottom_up_visits_children_before_statement() {
        use crate::ast::statement::{Stmt, StmtKind};
        let meta = Metadata::default();
        let stmt = Stmt::new(
            StmtKind::Assert(Exp::new(ExpKind::TrueLit, meta.clone())),
            meta,
        );
        let order = std::cell::RefCell::new(Vec::new());
        map_node_tree_bottom_up(
            &Node::Stmt(stmt),
            &|node| {
                match node {
                    Node::Exp(_) => order.borrow_mut().push("expression"),
                    Node::Stmt(_) => order.borrow_mut().push("statement"),
                    _ => {}
                }
                Ok(node.clone())
            },
            false,
        )
        .unwrap();
        assert_eq!(*order.borrow(), vec!["expression", "statement"]);
    }
    #[test]
    fn shared_node_mapper_rewrites_nested_type_product_fields() {
        use crate::ast::{
            program::{Field, FieldData, Member},
            r#type::Type,
        };
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Seq(std::sync::Arc::new(Type::Int)),
            meta: Metadata::default(),
        });
        let mapped = map_node_tree(&Node::Member(Member::Field(field.clone())), &|node| {
            Ok(if matches!(node, Node::Type(Type::Int)) {
                Node::Type(Type::Bool)
            } else {
                node.clone()
            })
        })
        .unwrap();
        let Node::Member(Member::Field(result)) = mapped else {
            panic!("field")
        };
        assert!(matches!(&result.typ, Type::Seq(t) if **t == Type::Bool));
        assert!(!result.same_node(&field));
    }
    #[test]
    fn label_statement_and_declaration_are_same_source_node() {
        use crate::ast::{
            ast::Metadata,
            program::{LabelDeclaration, LabelDeclarationData},
            statement::{Stmt, StmtKind},
        };
        let meta = Metadata::default();
        let label = LabelDeclaration::new(LabelDeclarationData {
            name: "L".into(),
            invariants: vec![],
            meta: meta.clone(),
        });
        let statement = Stmt::new(StmtKind::Label(label.clone()), meta);
        assert_eq!(
            Node::LabelDecl(label.clone()).same_node(&Node::Stmt(statement.clone())),
            Some(true)
        );
        let second_view = Stmt::new(StmtKind::Label(label), Metadata::default());
        assert!(statement.same_node(&second_view));
    }
    #[test]
    fn maps_each_statement_expression_occurrence() {
        use crate::ast::{
            ast::Metadata,
            statement::{Stmt, StmtKind},
        };
        let m = Metadata::default();
        let yes = Exp::new(ExpKind::TrueLit, m.clone());
        let root = Node::Stmt(Stmt::new(
            StmtKind::Seqn {
                statements: vec![
                    Stmt::new(StmtKind::Assert(yes.clone()), m.clone()),
                    Stmt::new(StmtKind::Assert(yes), m.clone()),
                ],
                declarations: vec![],
            },
            m,
        ));
        let count = std::cell::Cell::new(0);
        let result = map_expression_roots::<NodeReplacementError>(&root, &|e| {
            count.set(count.get() + 1);
            Ok(if count.get() == 1 {
                Exp::new(ExpKind::FalseLit, e.metadata().clone())
            } else {
                e.clone()
            })
        })
        .unwrap();
        assert_eq!(count.get(), 2);
        let Node::Stmt(s) = result else {
            panic!("stmt")
        };
        assert!(
            matches!(s.kind(), StmtKind::Seqn { statements, .. } if matches!(statements[0].kind(), StmtKind::Assert(e) if matches!(e.kind(), ExpKind::FalseLit)) && matches!(statements[1].kind(), StmtKind::Assert(e) if matches!(e.kind(), ExpKind::TrueLit)))
        );
    }
    #[test]
    fn program_replacement_preserves_or_freshens_identity_with_structure() {
        let m = Metadata::default();
        let yes = Exp::new(ExpKind::TrueLit, m.clone());
        let no = Exp::new(ExpKind::FalseLit, m.clone());
        let f = Function::new(crate::ast::program::FunctionData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(yes.clone()),
            meta: m.clone(),
        });
        let p = Program::new(vec![], vec![], vec![f], vec![], vec![], vec![], m);
        let Node::Program(unchanged) =
            replace_expressions(&Node::Program(p.clone()), &[(no.clone(), yes.clone())]).unwrap()
        else {
            panic!("program")
        };
        assert!(p.same_node(&unchanged));
        let Node::Program(changed) =
            replace_expressions(&Node::Program(p.clone()), &[(yes, no.clone())]).unwrap()
        else {
            panic!("program")
        };
        assert!(!p.same_node(&changed));
        assert_eq!(changed.functions[0].body, Some(no));
    }
}
