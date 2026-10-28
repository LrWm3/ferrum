//! Port plan: Check local and context-dependent Silver AST consistency.
//!
//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Consistency.scala
//!
//! Purpose:
//! Check local and context-dependent Silver AST consistency.
//!
//! Planned Rust structure:
//! Consistency diagnostics accumulator and legacy function-precondition flag;
//! identifier/assignability/purity and contract helpers, wildcard, trigger, forperm, backend
//! type, recursion and wand context checks; Context and InsideWandStatus.
//!
//! Behavior to preserve:
//! Preserve diagnostics order and positions, parser keyword restrictions and assignability
//! subtype rules. Legacy flag controls wildcard restrictions in function preconditions.
//! Validate trigger coverage, forperm direct resource arguments, wand proof scripts and
//! old[lhs] location, backend interpretation consistency, and recursion via function
//! preconditions. Existing extension-expression exception in noPermissions and mutable message
//! accumulator remain explicit.
//!
//! Integration:
//! ast::{ast,expression,statement,program,type},
//! ast::utility::{expressions,functions,viper_strategy}, parser keywords and verifier errors.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, ordering, explicit ownership, errors and
//! replacement of Scala reflection; interfaces remain provisional.
//!
//! Open decisions:
//! Reconcile per-run message/config ownership and extension rules with frontend and plugin
//! callers, preserving source diagnostics.
//!
//! Status: partial; identifier/type helpers, core traversal checks, contract diagnostics,
//! trigger coverage, wildcard, forperm and precondition-cycle checks are implemented.
//! Context-dependent wand checks are implemented; node-specific checks remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use std::collections::HashSet;

/// The parser's basic keyword set, excluding plugin extensions.
pub fn reserved_names() -> HashSet<String> {
    [
        "Bool",
        "Int",
        "Map",
        "Multiset",
        "Rational",
        "Ref",
        "Seq",
        "Set",
        "acc",
        "apply",
        "applying",
        "assert",
        "asserting",
        "assume",
        "axiom",
        "define",
        "domain",
        "else",
        "elseif",
        "ensures",
        "epsilon",
        "exhale",
        "exists",
        "false",
        "field",
        "fold",
        "forall",
        "forperm",
        "function",
        "goto",
        "if",
        "import",
        "in",
        "inhale",
        "interpretation",
        "intersection",
        "invariant",
        "label",
        "let",
        "lhs",
        "method",
        "new",
        "none",
        "null",
        "old",
        "package",
        "perm",
        "predicate",
        "quasihavoc",
        "quasihavocall",
        "range",
        "requires",
        "result",
        "returns",
        "setminus",
        "subset",
        "true",
        "unfold",
        "unfolding",
        "union",
        "unique",
        "var",
        "while",
        "wildcard",
        "write",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect()
}

pub fn valid_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '$' || c == '_')
        && chars.all(|c| c.is_ascii_alphanumeric() || matches!(c, '$' | '_' | '\'' | '@'))
}

use super::nodes::{Node, TraversalError, subnodes};
use crate::ast::{
    expression::{Exp, ExpKind},
    program::Program,
    r#type::Type,
};
use crate::verifier::verification_result::{FrontendError, FrontendErrorKind};

pub fn valid_user_defined_identifier(name: &str) -> bool {
    valid_identifier(name) && !reserved_names().contains(name)
}
pub fn same_length<A, B>(a: &[A], b: &[B]) -> bool {
    a.len() == b.len()
}
pub fn is_assignable(a: &Type, b: &Type) -> bool {
    a.is_subtype(b)
}
pub fn are_assignable(a: &[Type], b: &[Type]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(a, b)| is_assignable(a, b))
}
pub fn no_duplicates<T: Eq>(items: &[T]) -> bool {
    items
        .iter()
        .enumerate()
        .all(|(i, x)| !items[..i].contains(x))
}
fn exists(root: &Node, predicate: &impl Fn(&Node) -> bool) -> Result<bool, TraversalError> {
    if predicate(root) {
        return Ok(true);
    }
    for child in subnodes(root)? {
        if exists(&child, predicate)? {
            return Ok(true);
        }
    }
    Ok(false)
}
pub fn no_old(n: &Node) -> Result<bool, TraversalError> {
    Ok(!exists(
        n,
        &|n| matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::Old(_))),
    )?)
}
pub fn no_labelled_old(n: &Node) -> Result<bool, TraversalError> {
    Ok(!exists(
        n,
        &|n| matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::LabelledOld(_,label) if label != "lhs")),
    )?)
}
pub fn no_result(n: &Node) -> Result<bool, TraversalError> {
    Ok(!exists(
        n,
        &|n| matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::Result(_))),
    )?)
}
pub fn no_perm(n: &Node) -> Result<bool, TraversalError> {
    Ok(!exists(
        n,
        &|n| matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::CurrentPerm(_))),
    )?)
}
pub fn no_for_perm(n: &Node) -> Result<bool, TraversalError> {
    Ok(!exists(
        n,
        &|n| matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::ForPerm(..))),
    )?)
}
pub fn no_location_accesses(n: &Node) -> Result<bool, TraversalError> {
    Ok(!exists(n, &|n| {
        matches!(n, Node::FieldAccess(_) | Node::PredicateAccess(_))
            || matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::FieldAccess(_) | ExpKind::PredicateAccess(_)))
    })?)
}
pub fn no_asserting(n: &Node) -> Result<bool, TraversalError> {
    Ok(!exists(
        n,
        &|n| matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::Asserting(..))),
    )?)
}
pub fn no_ghost_operations(n: &Node) -> Result<bool, TraversalError> {
    Ok(!exists(
        n,
        &|n| matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::Unfolding(..) | ExpKind::Applying(..)) && !e.is_pure()),
    )?)
}
/// Source extension-root exception is checked after traversal.
pub fn no_permissions(root: &Node) -> Result<bool, TraversalError> {
    fn walk(node: &Node, parent: Option<&Node>) -> Result<bool, TraversalError> {
        let parent_unfolding =
            matches!(parent,Some(Node::Exp(e)) if matches!(e.kind(),ExpKind::Unfolding(..)));
        let parent_applying =
            matches!(parent,Some(Node::Exp(e)) if matches!(e.kind(),ExpKind::Applying(..)));
        if matches!(node,Node::Exp(e) if matches!(e.kind(),ExpKind::FieldAccessPredicate(..)))
            || (matches!(node,Node::Exp(e) if matches!(e.kind(),ExpKind::PredicateAccessPredicate(_)))
                || matches!(node, Node::PredicateAccessPredicate(_)))
                && !parent_unfolding
            || matches!(node,Node::Exp(e) if matches!(e.kind(),ExpKind::MagicWand(..)))
                && !parent_applying
        {
            return Ok(true);
        }
        for child in subnodes(node)? {
            if walk(&child, Some(node))? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    let found = walk(root, None)?;
    if matches!(root,Node::Exp(e) if matches!(e.kind(),ExpKind::Extension(_))) {
        Ok(true)
    } else {
        Ok(!found)
    }
}
pub fn check_backend_types(program: &Program, backend: &str) -> Vec<FrontendError> {
    let mut result = Vec::new();
    for domain in &program.domains {
        if domain
            .interpretations
            .as_ref()
            .is_some_and(|i| !i.contains_key(backend))
        {
            result.insert(
                0,
                FrontendError::new(
                    FrontendErrorKind::ConsistencyError(format!(
                        "Domain {} has no interpretation for backend {}.",
                        domain.name, backend
                    )),
                    domain.meta.position.clone(),
                ),
            );
        }
    }
    result
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConsistencyCheckError<E> {
    Traversal(TraversalError),
    Type(crate::ast::expression::ExpressionTypeError),
    Render(E),
}
impl<E> From<TraversalError> for ConsistencyCheckError<E> {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
impl<E> From<crate::ast::expression::ExpressionTypeError> for ConsistencyCheckError<E> {
    fn from(e: crate::ast::expression::ExpressionTypeError) -> Self {
        Self::Type(e)
    }
}
fn diagnostic(e: &Exp, message: String) -> FrontendError {
    FrontendError::new(
        FrontendErrorKind::ConsistencyError(message),
        e.metadata().position.clone(),
    )
}
pub fn check_pure<E>(
    e: &Exp,
    render: &impl Fn(&Exp) -> Result<String, E>,
) -> Result<Vec<FrontendError>, ConsistencyCheckError<E>> {
    if e.is_pure() {
        Ok(Vec::new())
    } else {
        Ok(vec![diagnostic(
            e,
            format!(
                "{} is non pure and appears where only pure expressions are allowed.",
                render(e).map_err(ConsistencyCheckError::Render)?
            ),
        )])
    }
}
pub fn check_function_body<E>(
    e: &Exp,
    render: &impl Fn(&Exp) -> Result<String, E>,
) -> Result<Vec<FrontendError>, ConsistencyCheckError<E>> {
    let node = Node::Exp(e.clone());
    let mut out = Vec::new();
    if !no_old(&node)? {
        out.push(diagnostic(
            e,
            "Old expressions are not allowed in functions bodies.".into(),
        ));
    }
    if !no_result(&node)? {
        out.push(diagnostic(
            e,
            "Result expressions are not allowed in functions bodies.".into(),
        ));
    }
    if !no_for_perm(&node)? {
        out.push(diagnostic(
            e,
            "Function bodies are not allowed to contain forperm expressions".into(),
        ));
    }
    if !no_perm(&node)? {
        out.push(diagnostic(
            e,
            "Function bodies are not allowed to contain perm expressions".into(),
        ));
    }
    out.extend(check_pure(e, render)?);
    Ok(out)
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContractKind {
    Precondition,
    NonPost,
    Postcondition,
}
pub fn check_contract<E>(
    e: &Exp,
    kind: ContractKind,
    render: &impl Fn(&Exp) -> Result<String, E>,
    render_type: &impl Fn(&Type) -> Result<String, E>,
) -> Result<Vec<FrontendError>, ConsistencyCheckError<E>> {
    let mut out = Vec::new();
    let typ = e.typ()?;
    if !typ.is_subtype(&Type::Bool) {
        let label = match kind {
            ContractKind::Precondition => "Precondition",
            ContractKind::NonPost => "Contract",
            ContractKind::Postcondition => "Postcondition",
        };
        out.push(diagnostic(
            e,
            format!(
                "{label} {}: {} must be boolean.",
                render(e).map_err(ConsistencyCheckError::Render)?,
                render_type(&typ).map_err(ConsistencyCheckError::Render)?
            ),
        ));
    }
    let node = Node::Exp(e.clone());
    if kind == ContractKind::Precondition && !no_old(&node)? {
        out.push(diagnostic(
            e,
            "Old expressions are not allowed in preconditions.".into(),
        ));
    }
    if kind != ContractKind::NonPost && !no_labelled_old(&node)? {
        out.push(diagnostic(
            e,
            if kind == ContractKind::Precondition {
                "Labelled-old expressions are not allowed in preconditions."
            } else {
                "Labelled-old expressions are not allowed in postconditions."
            }
            .into(),
        ));
    }
    if kind != ContractKind::Postcondition && !no_result(&node)? {
        out.push(diagnostic(
            e,
            "Result variables are only allowed in postconditions of functions.".into(),
        ));
    }
    Ok(out)
}

/// Local variables in trigger expressions, respecting source let's conditional RHS use.
fn contained_variables_excluding_let(
    root: &Node,
) -> Result<Vec<crate::ast::expression::LocalVar>, TraversalError> {
    fn add(out: &mut Vec<crate::ast::expression::LocalVar>, v: crate::ast::expression::LocalVar) {
        if !out.contains(&v) {
            out.push(v);
        }
    }
    fn walk(root: &Node) -> Result<Vec<crate::ast::expression::LocalVar>, TraversalError> {
        if let Node::Exp(e) = root {
            if let ExpKind::Let(var, value, body) = e.kind() {
                let mut vars = walk(&Node::Exp(body.clone()))?;
                let local = var.local_var();
                let used = vars.contains(&local);
                vars.retain(|v| v != &local);
                if used {
                    for v in walk(&Node::Exp(value.clone()))? {
                        add(&mut vars, v);
                    }
                }
                return Ok(vars);
            }
        }
        let mut out = Vec::new();
        match root {
            Node::LocalVar(v) => add(&mut out, v.clone()),
            Node::Exp(e) => {
                if let ExpKind::LocalVar(v) = e.kind() {
                    add(&mut out, v.clone());
                }
            }
            _ => {}
        }
        for child in subnodes(root)? {
            for v in walk(&child)? {
                add(&mut out, v);
            }
        }
        Ok(out)
    }
    walk(root)
}
pub fn check_all_vars_mentioned_in_triggers<E>(
    variables: &[crate::ast::program::LocalVarDecl],
    triggers: &[crate::ast::expression::Trigger],
    render: &impl Fn(&Exp) -> Result<String, E>,
) -> Result<Vec<FrontendError>, ConsistencyCheckError<E>> {
    let mut vars_in_triggers = Vec::new();
    for trigger in triggers {
        vars_in_triggers.push(contained_variables_excluding_let(&Node::Trigger(
            trigger.clone(),
        ))?);
    }
    let mut result = Vec::new();
    for variable in variables {
        for present in &vars_in_triggers {
            if !present.iter().any(|v| v.name == variable.name) {
                result.push(FrontendError::new(
                    FrontendErrorKind::ConsistencyError(format!(
                        "Variable {} is not mentioned in one or more triggers.",
                        variable.name
                    )),
                    variable.meta.position.clone(),
                ));
            }
        }
    }
    for trigger in triggers {
        for exp in &trigger.exps {
            let mut found = false;
            for var in variables {
                let sought = Node::LocalVar(var.local_var());
                if exists(&Node::Exp(exp.clone()), &|n| n == &sought)? {
                    found = true;
                    break;
                }
            }
            if !found {
                result.push(diagnostic(
                    exp,
                    format!(
                        "Trigger expression {} does not contain any quantified variable.",
                        render(exp).map_err(ConsistencyCheckError::Render)?
                    ),
                ));
            }
        }
    }
    Ok(result)
}

pub fn check_no_perm_forperm_except_inhale_exhale(
    e: &Exp,
) -> Result<Vec<FrontendError>, TraversalError> {
    fn collect(n: &Node, perms: &mut Vec<Exp>, pairs: &mut Vec<Exp>) -> Result<(), TraversalError> {
        if let Node::Exp(e) = n {
            match e.kind() {
                ExpKind::CurrentPerm(_) | ExpKind::ForPerm(..) => perms.push(e.clone()),
                ExpKind::InhaleExhaleExp(..) => pairs.push(e.clone()),
                _ => {}
            }
        }
        for child in subnodes(n)? {
            collect(&child, perms, pairs)?;
        }
        Ok(())
    }
    let mut perms = Vec::new();
    let mut pairs = Vec::new();
    collect(&Node::Exp(e.clone()), &mut perms, &mut pairs)?;
    let mut result = Vec::new();
    for perm in perms {
        let mut inside = false;
        for pair in &pairs {
            if exists(&Node::Exp(pair.clone()), &|n| n == &Node::Exp(perm.clone()))? {
                inside = true;
                break;
            }
        }
        if !inside {
            result.push(diagnostic(&perm,"Perm and forperm in this context are only allowed if nested under inhale-exhale assertions.".into()));
        }
    }
    Ok(result)
}

pub fn check_no_args_reassigned<E>(
    args: &[crate::ast::program::LocalVarDecl],
    body: &crate::ast::statement::Stmt,
    render: &impl Fn(&Node) -> Result<String, E>,
) -> Result<Vec<FrontendError>, ConsistencyCheckError<E>> {
    use crate::ast::statement::StmtKind;
    fn gather(
        node: &Node,
        out: &mut Vec<crate::ast::statement::Stmt>,
    ) -> Result<(), TraversalError> {
        if let Node::Stmt(s) = node {
            out.push(s.clone());
        }
        for child in subnodes(node)? {
            gather(&child, out)?;
        }
        Ok(())
    }
    let mut statements = Vec::new();
    gather(&Node::Stmt(body.clone()), &mut statements)?;
    let arg_vars: Vec<_> = args.iter().map(|v| v.local_var()).collect();
    let mut result = Vec::new();
    for kind in 0..3 {
        for stmt in &statements {
            let targets: Vec<_> = match (kind, stmt.kind()) {
                (0, StmtKind::LocalVarAssign { lhs, .. }) => vec![lhs],
                (1, StmtKind::MethodCall { targets, .. }) => targets.iter().collect(),
                (2, StmtKind::NewStmt { lhs, .. }) => vec![lhs],
                _ => Vec::new(),
            };
            for target in targets {
                if arg_vars.contains(target) {
                    let message = format!(
                        "{} is a reassignment of formal argument {}.",
                        render(&Node::Stmt(stmt.clone())).map_err(ConsistencyCheckError::Render)?,
                        render(&Node::LocalVar(target.clone()))
                            .map_err(ConsistencyCheckError::Render)?
                    );
                    result.push(FrontendError::new(
                        FrontendErrorKind::ConsistencyError(message),
                        stmt.metadata().position.clone(),
                    ));
                }
            }
        }
    }
    Ok(result)
}

pub fn check_wildcard_usage(
    root: &Node,
    in_function: bool,
    respect_function_pre_perm_amounts: bool,
) -> Result<Vec<FrontendError>, TraversalError> {
    if !respect_function_pre_perm_amounts && in_function {
        return Ok(Vec::new());
    }
    fn check_permission(
        permission: &Exp,
        out: &mut Vec<FrontendError>,
    ) -> Result<(), TraversalError> {
        if !matches!(permission.kind(), ExpKind::WildcardPerm)
            && exists(
                &Node::Exp(permission.clone()),
                &|n| matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::WildcardPerm)),
            )?
        {
            out.push(diagnostic(permission,"Wildcard occurs inside compound expression (should only occur directly in an accessibility predicate).".into()));
        }
        Ok(())
    }
    fn walk(node: &Node, out: &mut Vec<FrontendError>) -> Result<(), TraversalError> {
        match node {
            Node::Exp(e) => match e.kind() {
                ExpKind::FieldAccessPredicate(_, Some(p)) => check_permission(p, out)?,
                ExpKind::PredicateAccessPredicate(p) => {
                    if let Some(p) = &p.permission {
                        check_permission(p, out)?
                    }
                }
                _ => {}
            },
            Node::PredicateAccessPredicate(p) => {
                if let Some(p) = &p.permission {
                    check_permission(p, out)?
                }
            }
            _ => {}
        }
        for child in subnodes(node)? {
            walk(&child, out)?;
        }
        Ok(())
    }
    let mut out = Vec::new();
    walk(root, &mut out)?;
    Ok(out)
}

#[cfg(test)]
mod consistency_tests {
    use super::*;
    use crate::ast::{ast::Metadata, expression::LocalVar, program::LocalVarDecl};
    #[test]
    fn lhs_labelled_old_is_allowed_and_trigger_binder_is_checked() {
        let m = Metadata::default();
        let v = LocalVar::new("x".into(), Type::Int, m.clone());
        let var = Exp::new(ExpKind::LocalVar(v.clone()), m.clone());
        let lhs = Exp::new(ExpKind::LabelledOld(var.clone(), "lhs".into()), m.clone());
        let other = Exp::new(ExpKind::LabelledOld(var.clone(), "label".into()), m.clone());
        assert!(no_labelled_old(&Node::Exp(lhs)).unwrap());
        assert!(!no_labelled_old(&Node::Exp(other)).unwrap());
        let t = crate::ast::expression::Trigger::new(vec![var], m.clone());
        let decl = LocalVarDecl::new("x".into(), Type::Int, m);
        let result =
            check_all_vars_mentioned_in_triggers(&[decl], &[t], &|_| Ok::<_, ()>("x".into()))
                .unwrap();
        assert!(result.is_empty());
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ForPermCheckError {
    Traversal(TraversalError),
    Wand(super::expressions::MagicWandError),
    InvalidResource,
    NotForPerm,
}
impl From<TraversalError> for ForPermCheckError {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
impl From<super::expressions::MagicWandError> for ForPermCheckError {
    fn from(e: super::expressions::MagicWandError) -> Self {
        Self::Wand(e)
    }
}
pub fn one_ref_param(
    p: &crate::ast::expression::PredicateAccess,
) -> Result<bool, crate::ast::expression::ExpressionTypeError> {
    Ok(p.args.len() == 1 && p.args[0].typ()? == Type::Ref)
}
/// Source onlyDirectUse is false if the sought variable occurs anywhere under a
/// non-variable argument; callers separately permit direct variable arguments.
pub fn only_direct_use(
    v: &crate::ast::expression::LocalVar,
    e: &Exp,
) -> Result<bool, TraversalError> {
    fn walk(v: &crate::ast::expression::LocalVar, n: &Node) -> Result<bool, TraversalError> {
        if matches!(n,Node::LocalVar(x) if x == v)
            || matches!(n,Node::Exp(e) if matches!(e.kind(),ExpKind::LocalVar(x) if x == v))
        {
            return Ok(false);
        }
        for child in subnodes(n)? {
            if matches!(
                child,
                Node::Exp(_)
                    | Node::LocalVar(_)
                    | Node::FieldAccess(_)
                    | Node::PredicateAccess(_)
                    | Node::PredicateAccessPredicate(_)
            ) && !walk(v, &child)?
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
    walk(v, &Node::Exp(e.clone()))
}
pub fn all_variables_used(
    vars: &[crate::ast::program::LocalVarDecl],
    args: &[Exp],
) -> Result<bool, TraversalError> {
    for v in vars {
        let sought = Node::LocalVar(v.local_var());
        let mut found = false;
        for e in args {
            if exists(&Node::Exp(e.clone()), &|n| n == &sought)? {
                found = true;
                break;
            }
        }
        if !found {
            return Ok(false);
        }
    }
    Ok(true)
}
pub fn check_for_perm_arguments(
    forperm: &Exp,
    program: &Program,
) -> Result<Vec<FrontendError>, ForPermCheckError> {
    let ExpKind::ForPerm(vars, resource, _) = forperm.kind() else {
        return Err(ForPermCheckError::NotForPerm);
    };
    let args = match resource.kind() {
        ExpKind::FieldAccess(f) => vec![f.receiver.clone()],
        ExpKind::PredicateAccess(p) => p.args.clone(),
        ExpKind::MagicWand(..) => resource.magic_wand_subexpressions(program)?,
        _ => return Err(ForPermCheckError::InvalidResource),
    };
    let mut out = Vec::new();
    if !all_variables_used(vars, &args)? {
        out.push(diagnostic(
            forperm,
            "All quantified variables need to be used in a resource".into(),
        ));
    }
    for v in vars {
        for arg in &args {
            if !matches!(arg.kind(), ExpKind::LocalVar(_)) && !only_direct_use(&v.local_var(), arg)?
            {
                out.push(diagnostic(
                    arg,
                    "Quantified arguments can only be used directly".into(),
                ));
            }
        }
    }
    Ok(out)
}

pub fn check_no_function_recurses_via_preconditions(
    program: &Program,
) -> Result<Vec<FrontendError>, super::functions::FunctionAnalysisError> {
    let cycles = super::functions::find_function_cycles_via_preconditions(program)?;
    let mut result = Vec::new();
    for (name, cycle) in cycles {
        let mut message = format!("Function {name} recurses via its precondition");
        if !cycle.is_empty() {
            message.push_str(&format!(
                ": the cycle contains the function(s) {}",
                cycle.into_iter().collect::<Vec<_>>().join(", ")
            ));
        }
        let function = program.find_function_optionally(&name).ok_or_else(|| {
            super::functions::FunctionAnalysisError::MissingFunction(name.clone())
        })?;
        result.push(FrontendError::new(
            FrontendErrorKind::ConsistencyError(message),
            function.meta.position.clone(),
        ));
    }
    Ok(result)
}

pub fn is_forbidden_in_trigger(e: &Exp) -> bool {
    use ExpKind::*;
    match e.kind() {
        Extension(v) => v.0.is_forbidden_in_trigger(),
        Add(..) | Sub(..) | Mul(..) | Div(..) | Mod(..) | LtCmp(..) | LeCmp(..) | GtCmp(..)
        | GeCmp(..) | EqCmp(..) | NeCmp(..) | Minus(..) | Not(..) | Or(..) | And(..)
        | Implies(..) | CondExp(..) | FractionalPerm(..) | PermDiv(..) | PermPermDiv(..)
        | PermMinus(..) | PermAdd(..) | PermSub(..) | PermMul(..) | IntPermMul(..)
        | DebugPermMin(..) | PermLtCmp(..) | PermLeCmp(..) | PermGtCmp(..) | PermGeCmp(..) => true,
        _ => false,
    }
}
fn possible_trigger(e: &Exp) -> bool {
    use ExpKind::*;
    matches!(
        e.kind(),
        FuncApp(..)
            | DomainFuncApp(..)
            | FieldAccess(..)
            | PredicateAccess(..)
            | EmptySeq(..)
            | ExplicitSeq(..)
            | RangeSeq(..)
            | SeqAppend(..)
            | SeqIndex(..)
            | SeqTake(..)
            | SeqDrop(..)
            | SeqContains(..)
            | SeqUpdate(..)
            | SeqLength(..)
            | EmptySet(..)
            | ExplicitSet(..)
            | EmptyMultiset(..)
            | ExplicitMultiset(..)
            | AnySetUnion(..)
            | AnySetIntersection(..)
            | AnySetSubset(..)
            | AnySetMinus(..)
            | AnySetContains(..)
            | AnySetCardinality(..)
            | EmptyMap(..)
            | ExplicitMap(..)
            | Maplet(..)
            | MapUpdate(..)
            | MapLookup(..)
            | MapContains(..)
            | MapCardinality(..)
            | MapDomain(..)
            | MapRange(..)
    )
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TriggerCheckError {
    Traversal(TraversalError),
    Wand(super::expressions::MagicWandError),
}
impl From<TraversalError> for TriggerCheckError {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
impl From<super::expressions::MagicWandError> for TriggerCheckError {
    fn from(e: super::expressions::MagicWandError) -> Self {
        Self::Wand(e)
    }
}
pub fn valid_trigger(e: &Exp, program: &Program) -> Result<bool, TriggerCheckError> {
    match e.kind() {
        ExpKind::Old(inner) | ExpKind::LabelledOld(inner, _) => valid_trigger(inner, program),
        ExpKind::Extension(extension) => Ok(extension.0.is_valid_trigger()),
        ExpKind::MagicWand(..) => {
            for hole in e.magic_wand_subexpressions(program)? {
                if exists(
                    &Node::Exp(hole),
                    &|n| matches!(n,Node::Exp(e) if is_forbidden_in_trigger(e)),
                )? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ if possible_trigger(e) => Ok(!exists(
            &Node::Exp(e.clone()),
            &|n| matches!(n,Node::Exp(e) if is_forbidden_in_trigger(e)),
        )?),
        _ => Ok(false),
    }
}
pub fn check_triggers<E>(
    trigger: &crate::ast::expression::Trigger,
    program: &Program,
    render: &impl Fn(&crate::ast::expression::Trigger) -> Result<String, E>,
) -> Result<Vec<FrontendError>, TriggerDiagnosticError<E>> {
    let mut out = Vec::new();
    for exp in &trigger.exps {
        if !valid_trigger(exp, program).map_err(TriggerDiagnosticError::Check)? {
            out.push(FrontendError::new(
                FrontendErrorKind::ConsistencyError(format!(
                    "{} is not a valid Trigger",
                    render(trigger).map_err(TriggerDiagnosticError::Render)?
                )),
                trigger.meta.position.clone(),
            ));
        }
    }
    Ok(out)
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TriggerDiagnosticError<E> {
    Check(TriggerCheckError),
    Render(E),
}

#[cfg(test)]
mod trigger_validity_tests {
    use super::*;
    use crate::ast::{ast::Metadata, expression::ExpExtra};
    #[test]
    fn function_trigger_rejects_arithmetic_and_old_unwraps() {
        let m = Metadata::default();
        let one = Exp::new(ExpKind::IntLit(1.into()), m.clone());
        let plus = Exp::new(ExpKind::Add(one.clone(), one), m.clone());
        let call = Exp::with_extra(
            ExpKind::FuncApp("f".into(), vec![plus]),
            m.clone(),
            ExpExtra {
                typ: Some(Type::Int),
                ..ExpExtra::default()
            },
        );
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], m.clone());
        assert!(!valid_trigger(&call, &program).unwrap());
        let old = Exp::new(ExpKind::Old(call), m);
        assert!(!valid_trigger(&old, &program).unwrap());
    }
}

/// Errors representing source preconditions or unsupported extension traversal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContextConsistencyError {
    Traversal(TraversalError),
    InvalidProofScript,
    NonLocalProofDeclaration,
}
impl From<TraversalError> for ContextConsistencyError {
    fn from(value: TraversalError) -> Self {
        Self::Traversal(value)
    }
}

/// Context-dependent wand, wildcard and domain-reference checks in source preorder.
pub fn check_context_dependent_consistency(
    root: &Node,
    program: &Program,
) -> Result<Vec<FrontendError>, ContextConsistencyError> {
    use crate::ast::{position::Position, program::Declaration, statement::StmtKind};
    fn report(out: &mut Vec<FrontendError>, message: String, position: Position) {
        out.push(FrontendError::new(
            FrontendErrorKind::ConsistencyError(message),
            position,
        ));
    }
    fn old(
        n: &Node,
        right: bool,
        out: &mut Vec<FrontendError>,
    ) -> Result<(), ContextConsistencyError> {
        if let Node::Exp(e) = n {
            if let ExpKind::MagicWand(l, r) = e.kind() {
                old(&Node::Exp(l.clone()), false, out)?;
                old(&Node::Exp(r.clone()), true, out)?;
                return Ok(());
            }
            if matches!(e.kind(), ExpKind::LabelledOld(_, label) if label == "lhs") && !right {
                report(out, "Wands may use the old[lhs]-expression on the rhs and in their proof script only.".into(), e.metadata().position.clone());
                return Ok(());
            }
        }
        for child in subnodes(n)? {
            old(&child, right, out)?;
        }
        Ok(())
    }
    fn script(
        n: &Node,
        locals: &[String],
        out: &mut Vec<FrontendError>,
    ) -> Result<(), ContextConsistencyError> {
        if let Node::Stmt(s) = n {
            let msg = match s.kind() {
                StmtKind::FieldAssign { .. } => {
                    Some("Field assignments are not allowed in magic wand proof scripts.")
                }
                StmtKind::NewStmt { .. } => {
                    Some("New statements statements are not allowed in magic wand proof scripts.")
                }
                StmtKind::While { .. } => {
                    Some("While statements are not allowed in magic wand proof scripts.")
                }
                StmtKind::LocalVarAssign { lhs, .. } if !locals.contains(&lhs.name) => Some(
                    "Can only assign to local variables that were declared inside the proof script.",
                ),
                StmtKind::Package { .. } => return Ok(()),
                _ => None,
            };
            if let Some(message) = msg {
                report(out, message.into(), s.metadata().position.clone());
                return Ok(());
            }
        }
        for child in subnodes(n)? {
            script(&child, locals, out)?;
        }
        Ok(())
    }
    fn walk(
        n: &Node,
        p: &Program,
        inside: bool,
        access: bool,
        out: &mut Vec<FrontendError>,
    ) -> Result<(), ContextConsistencyError> {
        let mut next_inside = inside;
        let mut next_access = access;
        match n {
            Node::Stmt(s) => if let StmtKind::Package { proof_script, .. } = s.kind() {
                let StmtKind::Seqn { declarations, .. } = proof_script.kind() else { return Err(ContextConsistencyError::InvalidProofScript) };
                let mut locals = Vec::new();
                for d in declarations { match d { Declaration::Local(v) => locals.push(v.name.clone()), _ => return Err(ContextConsistencyError::NonLocalProofDeclaration) } }
                script(&Node::Stmt(proof_script.clone()), &locals, out)?;
                next_inside = true;
            },
            Node::Exp(e) => match e.kind() {
                ExpKind::MagicWand(lhs, rhs) => {
                    old(&Node::Exp(lhs.clone()), false, out)?;
                    old(&Node::Exp(rhs.clone()), true, out)?;
                    if !no_ghost_operations(n)? { report(out, "Ghost operations may not occur inside of wands.".into(), e.metadata().position.clone()); }
                    next_inside = true;
                }
                ExpKind::LabelledOld(_, label) if label == "lhs" && !inside => report(out, "Labelled old expressions with \"lhs\" label may only occur inside wands and their proof scripts.".into(), e.metadata().position.clone()),
                ExpKind::FieldAccessPredicate(..) | ExpKind::PredicateAccessPredicate(_) => next_access = true,
                ExpKind::WildcardPerm if !access => report(out, "\"wildcard\" can only be used in accessibility predicates".into(), e.metadata().position.clone()),
                _ => {}
            },
            Node::PredicateAccessPredicate(_) => next_access = true,
            Node::Type(Type::Domain(t)) => match p.find_domain_optionally(&t.domain_name) {
                None => report(out, format!("DomainType references non-existent domain {}.", t.domain_name), Position::NoPosition),
                Some(d) if d.interpretations.is_some() => report(out, format!("DomainType {} references domain with interpretation; must use BackendType instead.", t.domain_name), Position::NoPosition),
                _ => {}
            },
            Node::Type(Type::Backend(t)) => match p.find_domain_optionally(&t.viper_name) {
                None => report(out, format!("BackendType references non-existent domain {}.", t.viper_name), Position::NoPosition),
                Some(d) if d.interpretations.is_none() => report(out, format!("BackendType {} references domain without interpretation; must use DomainType instead.", t.viper_name), Position::NoPosition),
                Some(d) if d.interpretations.as_ref() != Some(&t.interpretations) => report(out, format!("BackendType {} has different interpretations than the domain it references.", t.viper_name), Position::NoPosition),
                _ => {}
            },
            _ => {}
        }
        for child in subnodes(n)? {
            walk(&child, p, next_inside, next_access, out)?;
        }
        Ok(())
    }
    let mut out = Vec::new();
    walk(root, program, false, false, &mut out)?;
    Ok(out)
}

#[cfg(test)]
mod context_consistency_tests {
    use super::*;
    use crate::ast::ast::Metadata;
    #[test]
    fn old_lhs_is_allowed_only_in_wand_rhs() {
        let m = Metadata::default();
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], m.clone());
        let lhs_old = Exp::new(
            ExpKind::LabelledOld(Exp::new(ExpKind::TrueLit, m.clone()), "lhs".into()),
            m.clone(),
        );
        let wand = Exp::new(ExpKind::MagicWand(lhs_old.clone(), lhs_old), m);
        let errors = check_context_dependent_consistency(&Node::Exp(wand), &program).unwrap();
        assert_eq!(errors.len(), 1);
        assert!(
            matches!(&errors[0].kind, FrontendErrorKind::ConsistencyError(s) if s.starts_with("Wands may use"))
        );
    }
}
