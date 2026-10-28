//! Ordered Silver AST child dispatch.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Nodes.scala
//! Status: partial. Subnode dispatch, extension hooks and member references are implemented;
//! product children and complete metadata-preserving reconstruction remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::expression::{
    Exp, ExpKind, ExpressionTypeError, FieldAccess, LocalVar, PredicateAccess, Trigger,
};
use crate::ast::program::{
    AnyLocalVarDecl, DomainAxiom, DomainFunc, LocalVarDecl, Member, Program, UnnamedLocalVarDecl,
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
            (UnnamedLocalDecl(a), UnnamedLocalDecl(b)) => Some(a.same_node(b)),
            (LocalVar(a), LocalVar(b)) => Some(a.same_node(b)),
            (FieldAccess(a), FieldAccess(b)) => Some(a.same_node(b)),
            (PredicateAccess(a), PredicateAccess(b)) => Some(a.same_node(b)),
            (PredicateAccessPredicate(a), PredicateAccessPredicate(b)) => Some(a.same_node(b)),
            (Trigger(a), Trigger(b)) => Some(a.same_node(b)),
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
            StmtKind::Label { invariants, .. } => exps(invariants),
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
        Node::DomainFunc(_) | Node::LocalDecl(_) | Node::UnnamedLocalDecl(_) | Node::Type(_) => {
            root.clone()
        }
    })
}

#[cfg(test)]
mod reconstruction_tests {
    use super::*;
    use crate::ast::{ast::Metadata, program::Function, r#type::Type};
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
