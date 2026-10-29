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
    let cycles = super::functions::find_ordered_function_cycles_via_preconditions(program)?;
    let mut result = Vec::new();
    for (name, cycle) in cycles {
        let mut message = format!("Function {name} recurses via its precondition");
        if !cycle.is_empty() {
            message.push_str(&format!(
                ": the cycle contains the function(s) {}",
                cycle.join(", ")
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
        ExpKind::Extension(extension) => Ok(extension.0.is_valid_trigger()?),
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

/// Failures encountered while checking scoped declarations and uses.
#[derive(Debug)]
pub enum IdentifierCheckError {
    Traversal(TraversalError),
    Type(crate::ast::expression::ExpressionTypeError),
    TypePrinter(crate::ast::pretty::pretty_printer::PrintError),
    UnsupportedExtension,
    Extension(crate::verifier::verification_result::DiagnosticError),
}
impl From<TraversalError> for IdentifierCheckError {
    fn from(value: TraversalError) -> Self {
        Self::Traversal(value)
    }
}

#[derive(Debug)]
struct MemberDeclaration(crate::ast::program::ExtensionMemberHandle);
impl crate::ast::program::ExtensionDeclaration for MemberDeclaration {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn name(&self) -> &str {
        self.0.0.name()
    }
    fn equals(&self, other: &dyn crate::ast::program::ExtensionDeclaration) -> bool {
        other
            .as_any()
            .downcast_ref::<Self>()
            .is_some_and(|other| self.0 == other.0)
    }
    fn metadata(
        &self,
    ) -> Result<&crate::ast::ast::Metadata, crate::verifier::verification_result::DiagnosticError>
    {
        self.0.0.metadata()
    }
}
fn scope_declarations(
    n: &Node,
) -> Result<Option<Vec<crate::ast::program::Declaration>>, IdentifierCheckError> {
    use crate::ast::{
        program::{AnyLocalVarDecl, Declaration, DomainAxiomKind, Member},
        statement::StmtKind,
    };
    Ok(match n {
        Node::Program(p) => {
            let mut ds: Vec<Declaration> = p
                .domains
                .iter()
                .cloned()
                .map(Declaration::Domain)
                .chain(p.fields.iter().cloned().map(Declaration::Field))
                .chain(p.functions.iter().cloned().map(Declaration::Function))
                .chain(p.predicates.iter().cloned().map(Declaration::Predicate))
                .chain(p.methods.iter().cloned().map(Declaration::Method))
                .collect();
            ds.extend(p.extensions.iter().cloned().map(|v| {
                Declaration::Extension(crate::ast::program::ExtensionDeclarationHandle(
                    std::sync::Arc::new(MemberDeclaration(v)),
                ))
            }));
            for d in &p.domains {
                ds.extend(
                    d.axioms
                        .iter()
                        .filter(|a| matches!(a.kind(), DomainAxiomKind::Named { .. }))
                        .cloned()
                        .map(Declaration::NamedDomainAxiom),
                );
                ds.extend(d.functions.iter().cloned().map(Declaration::DomainFunc));
            }
            Some(ds)
        }
        Node::Member(m) => Some(match m {
            Member::Domain(_) | Member::Field(_) => vec![],
            Member::Function(f) => f
                .formal_args
                .iter()
                .cloned()
                .map(Declaration::Local)
                .collect(),
            Member::Predicate(p) => p
                .formal_args
                .iter()
                .cloned()
                .map(Declaration::Local)
                .collect(),
            Member::Method(m) => m.scoped_declarations()?,
            Member::Extension(v) => {
                v.0.scope_declarations()
                    .map_err(IdentifierCheckError::Extension)?
            }
        }),
        Node::DomainFunc(f) => Some(
            f.formal_args
                .iter()
                .filter_map(|v| match v {
                    AnyLocalVarDecl::Named(v) => Some(Declaration::Local(v.clone())),
                    _ => None,
                })
                .collect(),
        ),
        Node::DomainAxiom(_) => Some(vec![]),
        Node::Stmt(s) => match s.kind() {
            StmtKind::Seqn { .. } => Some(s.scoped_declarations()),
            StmtKind::Extension(v) => {
                v.0.scope_declarations()
                    .map_err(IdentifierCheckError::Extension)?
            }
            StmtKind::Quasihavocall { variables, .. } => {
                Some(variables.iter().cloned().map(Declaration::Local).collect())
            }
            _ => None,
        },
        Node::Exp(e) => match e.kind() {
            ExpKind::Extension(v) => {
                v.0.scope_declarations()
                    .map_err(IdentifierCheckError::Extension)?
            }
            ExpKind::Let(v, ..) => Some(vec![Declaration::Local(v.clone())]),
            ExpKind::Forall(v, ..) | ExpKind::Exists(v, ..) | ExpKind::ForPerm(v, ..) => {
                Some(v.iter().cloned().map(Declaration::Local).collect())
            }
            _ => None,
        },
        Node::Type(Type::Extension(v)) => v
            .scope_declarations()
            .map_err(IdentifierCheckError::Extension)?,
        _ => None,
    })
}

/// The source Scope.transitiveScopedDecls order, including duplicate declarations.
/// Unknown extension traversal or scope membership is reported rather than skipped.
pub fn transitive_scoped_declarations(
    program: &Program,
) -> Result<Vec<crate::ast::program::Declaration>, IdentifierCheckError> {
    fn descend(
        root: &Node,
        current: &Node,
        output: &mut Vec<crate::ast::program::Declaration>,
    ) -> Result<(), IdentifierCheckError> {
        if current != root {
            if let Some(declarations) = scope_declarations(current)? {
                output.extend(declarations);
                for child in subnodes(current)? {
                    descend(current, &child, output)?;
                }
                return Ok(());
            }
        }
        for child in subnodes(current)? {
            descend(root, &child, output)?;
        }
        Ok(())
    }
    let root = Node::Program(program.clone());
    let mut result = scope_declarations(&root)?.expect("program is a scope");
    for child in subnodes(&root)? {
        descend(&root, &child, &mut result)?;
    }
    Ok(result)
}

/// Names in the same order as `transitive_scoped_declarations`.
pub fn transitive_scoped_names(program: &Program) -> Result<Vec<String>, IdentifierCheckError> {
    use crate::ast::program::{Declaration, DomainAxiomKind};
    transitive_scoped_declarations(program)?
        .into_iter()
        .map(|d| {
            Ok(match d {
                Declaration::Local(v) => v.name.clone(),
                Declaration::Field(v) => v.name.clone(),
                Declaration::Predicate(v) => v.name.clone(),
                Declaration::Method(v) => v.name.clone(),
                Declaration::Function(v) => v.name.clone(),
                Declaration::Domain(v) => v.name.clone(),
                Declaration::DomainFunc(v) => v.name.clone(),
                Declaration::Label(v) => v.name.clone(),
                Declaration::Extension(v) => v.0.name().to_owned(),
                Declaration::NamedDomainAxiom(v) => match v.kind() {
                    DomainAxiomKind::Named { name, .. } => name.clone(),
                    _ => return Err(IdentifierCheckError::UnsupportedExtension),
                },
            })
        })
        .collect()
}

/// Source Program.checkIdentifiers: scope shadowing, duplicates, and typed uses.
pub fn check_identifiers(program: &Program) -> Result<Vec<FrontendError>, IdentifierCheckError> {
    use crate::ast::{
        position::Position,
        program::{Declaration, DomainAxiomKind},
        statement::StmtKind,
    };
    use std::collections::HashMap;
    #[derive(Clone)]
    struct Entry {
        name: String,
        class: &'static str,
        typ: Option<Type>,
        pos: Position,
    }
    fn entry(d: &Declaration) -> Result<Entry, IdentifierCheckError> {
        Ok(match d {
            Declaration::Local(v) => Entry {
                name: v.name.clone(),
                class: "LocalVarDecl",
                typ: Some(v.typ.clone()),
                pos: v.meta.position.clone(),
            },
            Declaration::Label(v) => Entry {
                name: v.name.clone(),
                class: "Label",
                typ: None,
                pos: v.meta.position.clone(),
            },
            Declaration::Field(v) => Entry {
                name: v.name.clone(),
                class: "Field",
                typ: Some(v.typ.clone()),
                pos: v.meta.position.clone(),
            },
            Declaration::Function(v) => Entry {
                name: v.name.clone(),
                class: "Function",
                typ: Some(v.typ.clone()),
                pos: v.meta.position.clone(),
            },
            Declaration::Method(v) => Entry {
                name: v.name.clone(),
                class: "Method",
                typ: None,
                pos: v.meta.position.clone(),
            },
            Declaration::Predicate(v) => Entry {
                name: v.name.clone(),
                class: "Predicate",
                typ: None,
                pos: v.meta.position.clone(),
            },
            Declaration::Domain(v) => Entry {
                name: v.name.clone(),
                class: "Domain",
                typ: None,
                pos: v.meta.position.clone(),
            },
            Declaration::DomainFunc(v) => Entry {
                name: v.name.clone(),
                class: "DomainFunc",
                typ: Some(v.typ.clone()),
                pos: v.meta.position.clone(),
            },
            Declaration::NamedDomainAxiom(v) => match v.kind() {
                DomainAxiomKind::Named { name, meta, .. } => Entry {
                    name: name.clone(),
                    class: "NamedDomainAxiom",
                    typ: None,
                    pos: meta.position.clone(),
                },
                _ => return Err(IdentifierCheckError::UnsupportedExtension),
            },
            Declaration::Extension(v) => Entry {
                name: v.0.name().to_owned(),
                class: "__extension__",
                typ: None,
                pos: v
                    .0
                    .metadata()
                    .map_err(IdentifierCheckError::Extension)?
                    .position
                    .clone(),
            },
        })
    }
    fn issue(out: &mut Vec<FrontendError>, pos: &Position, message: String) {
        out.push(FrontendError::new(
            FrontendErrorKind::ConsistencyError(message),
            pos.clone(),
        ));
    }
    fn type_string(t: &Type) -> Result<String, IdentifierCheckError> {
        crate::ast::pretty::pretty_printer::show_type(t).map_err(IdentifierCheckError::TypePrinter)
    }
    fn check_scope(
        root: &Node,
        outer: &HashMap<String, Entry>,
        out: &mut Vec<FrontendError>,
    ) -> Result<(), IdentifierCheckError> {
        let ds = scope_declarations(root)?.expect("scope caller");
        let mut own = HashMap::new();
        for d in ds {
            let e = entry(&d)?;
            if !valid_user_defined_identifier(&e.name) {
                issue(
                    out,
                    &e.pos,
                    format!("{} is not a valid identifier.", e.name),
                );
            }
            if own.contains_key(&e.name) {
                issue(
                    out,
                    &e.pos,
                    format!("Duplicate identifier `{}` found.", e.name),
                );
            } else {
                own.insert(e.name.clone(), e);
            }
        }
        let mut context = outer.clone();
        context.extend(own);
        fn walk(
            n: &Node,
            root: &Node,
            scope: &HashMap<String, Entry>,
            out: &mut Vec<FrontendError>,
        ) -> Result<(), IdentifierCheckError> {
            if n != root && scope_declarations(n)?.is_some() {
                return if matches!(n, Node::DomainFunc(_)) {
                    check_scope(n, &HashMap::new(), out)
                } else {
                    check_scope(n, scope, out)
                };
            }
            let name_check = |name: &str,
                              expected: &str,
                              pos: &Position,
                              out: &mut Vec<FrontendError>|
             -> Result<(), IdentifierCheckError> {
                match scope.get(name) {
                    Some(d) if d.class == "__extension__" => {
                        return Err(IdentifierCheckError::UnsupportedExtension);
                    }
                    Some(d) if d.class == expected => {}
                    Some(d) => issue(
                        out,
                        pos,
                        format!(
                            "No matching identifier {name} found of type {expected}, instead found of type {}.",
                            d.class
                        ),
                    ),
                    None => issue(
                        out,
                        pos,
                        format!("No matching identifier {name} found of type {expected}."),
                    ),
                }
                Ok(())
            };
            let local = |v: &crate::ast::expression::LocalVar,
                         out: &mut Vec<FrontendError>|
             -> Result<(), IdentifierCheckError> {
                match scope.get(&v.name) {
                    Some(d) if d.class == "LocalVarDecl" && d.typ.as_ref() == Some(&v.typ) => {}
                    Some(d) if d.class == "LocalVarDecl" => issue(
                        out,
                        &v.meta.position,
                        format!(
                            "No matching local variable {} found with type {}, instead found {}.",
                            v.name,
                            type_string(&v.typ)?,
                            type_string(d.typ.as_ref().expect("local type"))?
                        ),
                    ),
                    Some(d) if d.class == "__extension__" => {
                        return Err(IdentifierCheckError::UnsupportedExtension);
                    }
                    Some(d) => issue(
                        out,
                        &v.meta.position,
                        format!(
                            "No matching local variable {} found with type {}, instead found other identifier of type {}.",
                            v.name,
                            type_string(&v.typ)?,
                            d.class
                        ),
                    ),
                    None => issue(
                        out,
                        &v.meta.position,
                        format!("Local variable {} not found.", v.name),
                    ),
                };
                Ok(())
            };
            match n {
                Node::LocalVar(v) => local(v, out)?,
                Node::FieldAccess(v) => name_check(&v.field.name, "Field", &v.meta.position, out)?,
                Node::PredicateAccess(v) => {
                    name_check(&v.predicate_name, "Predicate", &v.meta.position, out)?
                }
                Node::Stmt(s) => match s.kind() {
                    StmtKind::MethodCall { method_name, .. } => {
                        name_check(method_name, "Method", &s.metadata().position, out)?
                    }
                    StmtKind::Goto(name) => name_check(name, "Label", &s.metadata().position, out)?,
                    _ => {}
                },
                Node::Exp(e) => match e.kind() {
                    ExpKind::LocalVar(v) => local(v, out)?,
                    ExpKind::FieldAccess(v) => {
                        name_check(&v.field.name, "Field", &v.meta.position, out)?
                    }
                    ExpKind::PredicateAccess(v) => {
                        name_check(&v.predicate_name, "Predicate", &v.meta.position, out)?
                    }
                    ExpKind::FuncApp(name, _) => {
                        name_check(name, "Function", &e.metadata().position, out)?
                    }
                    ExpKind::DomainFuncApp(name, ..) => {
                        name_check(name, "DomainFunc", &e.metadata().position, out)?
                    }
                    ExpKind::LabelledOld(_, name) if name != "lhs" => {
                        name_check(name, "Label", &e.metadata().position, out)?
                    }
                    _ => {}
                },
                _ => {}
            }
            for child in subnodes(n)? {
                walk(&child, root, scope, out)?;
            }
            Ok(())
        }
        walk(root, root, &context, out)
    }
    let mut out = Vec::new();
    check_scope(&Node::Program(program.clone()), &HashMap::new(), &mut out)?;
    Ok(out)
}

#[cfg(test)]
mod identifier_scope_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        expression::LocalVar,
        program::{LocalVarDecl, Method, MethodData},
        statement::{Stmt, StmtKind},
    };
    #[test]
    fn scope_reports_duplicate_formals_and_unbound_use() {
        let m = Metadata::default();
        let formal = LocalVarDecl::new("x".into(), Type::Bool, m.clone());
        let missing = Exp::new(
            ExpKind::LocalVar(LocalVar::new("y".into(), Type::Bool, m.clone())),
            m.clone(),
        );
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![Stmt::new(StmtKind::Assert(missing), m.clone())],
                declarations: vec![],
            },
            m.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![formal.clone(), formal],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: m.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], m);
        let errors = check_identifiers(&program).unwrap();
        assert_eq!(errors.len(), 2);
        assert!(
            matches!(&errors[0].kind, FrontendErrorKind::ConsistencyError(s) if s == "Duplicate identifier `x` found.")
        );
        assert!(
            matches!(&errors[1].kind, FrontendErrorKind::ConsistencyError(s) if s == "Local variable y not found.")
        );
    }
}

#[derive(Debug)]
pub enum ProgramUseCheckError<E> {
    Traversal(TraversalError),
    Type(crate::ast::expression::ExpressionTypeError),
    Render(E),
    MissingDomainName,
    InvalidPredicateAccess,
}
impl<E> From<TraversalError> for ProgramUseCheckError<E> {
    fn from(value: TraversalError) -> Self {
        Self::Traversal(value)
    }
}
/// The five Program.check use/arity/type and abstract-predicate checks, in source phase order.
/// The caller supplies source-compatible node and sequence renderers for diagnostic text.
pub fn check_program_uses<E>(
    p: &Program,
    render: &impl Fn(&Node) -> Result<String, E>,
    render_seq: &impl Fn(&[Node]) -> Result<String, E>,
) -> Result<Vec<FrontendError>, ProgramUseCheckError<E>> {
    use crate::ast::{program::AnyLocalVarDecl, statement::StmtKind};
    fn nodes<E>(root: &Node) -> Result<Vec<Node>, ProgramUseCheckError<E>> {
        fn go<E>(n: &Node, out: &mut Vec<Node>) -> Result<(), ProgramUseCheckError<E>> {
            out.push(n.clone());
            for child in subnodes(n)? {
                go(&child, out)?;
            }
            Ok(())
        }
        let mut out = Vec::new();
        go(root, &mut out)?;
        Ok(out)
    }
    fn assign_exps<E>(xs: &[Exp], targets: &[Type]) -> Result<bool, ProgramUseCheckError<E>> {
        if xs.len() != targets.len() {
            return Ok(false);
        }
        for (e, target) in xs.iter().zip(targets) {
            if !e
                .typ()
                .map_err(ProgramUseCheckError::Type)?
                .is_subtype(target)
            {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn decl_nodes(xs: &[crate::ast::program::LocalVarDecl]) -> Vec<Node> {
        xs.iter().cloned().map(Node::LocalDecl).collect()
    }
    fn exp_nodes(xs: &[Exp]) -> Vec<Node> {
        xs.iter().cloned().map(Node::Exp).collect()
    }
    fn emit(out: &mut Vec<FrontendError>, message: String, pos: &crate::ast::position::Position) {
        out.push(FrontendError::new(
            FrontendErrorKind::ConsistencyError(message),
            pos.clone(),
        ));
    }
    let mut result = Vec::new();
    for m in &p.methods {
        if let Some(body) = &m.body {
            for n in nodes::<E>(&Node::Stmt(body.clone()))? {
                if let Node::Stmt(s) = n {
                    if let StmtKind::MethodCall {
                        method_name,
                        args,
                        targets,
                    } = s.kind()
                    {
                        if let Some(def) = p.find_method_optionally(method_name) {
                            let returns: Vec<_> =
                                def.formal_returns.iter().map(|v| v.typ.clone()).collect();
                            let target_types: Vec<_> =
                                targets.iter().map(|v| v.typ.clone()).collect();
                            if !are_assignable(&returns, &target_types) {
                                let a = render_seq(&decl_nodes(&def.formal_returns))
                                    .map_err(ProgramUseCheckError::Render)?;
                                let b = render_seq(
                                    &targets
                                        .iter()
                                        .cloned()
                                        .map(Node::LocalVar)
                                        .collect::<Vec<_>>(),
                                )
                                .map_err(ProgramUseCheckError::Render)?;
                                emit(
                                    &mut result,
                                    format!(
                                        "Formal returns {a} of method {method_name} are not assignable to targets {b}."
                                    ),
                                    &s.metadata().position,
                                );
                            }
                            let formal: Vec<_> =
                                def.formal_args.iter().map(|v| v.typ.clone()).collect();
                            if !assign_exps(args, &formal)? {
                                let a = render_seq(&exp_nodes(args))
                                    .map_err(ProgramUseCheckError::Render)?;
                                let b = render_seq(&decl_nodes(&def.formal_args))
                                    .map_err(ProgramUseCheckError::Render)?;
                                emit(
                                    &mut result,
                                    format!(
                                        "Arguments {a} are not assignable to formal arguments {b} of method {method_name}"
                                    ),
                                    &s.metadata().position,
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    let all = nodes::<E>(&Node::Program(p.clone()))?;
    for n in &all {
        if let Node::Exp(e) = n {
            if let ExpKind::FuncApp(name, args) = e.kind() {
                if let Some(def) = p.find_function_optionally(name) {
                    let formal: Vec<_> = def.formal_args.iter().map(|v| v.typ.clone()).collect();
                    if !assign_exps(args, &formal)? {
                        let a = render_seq(&decl_nodes(&def.formal_args))
                            .map_err(ProgramUseCheckError::Render)?;
                        let b =
                            render_seq(&exp_nodes(args)).map_err(ProgramUseCheckError::Render)?;
                        emit(
                            &mut result,
                            format!(
                                "Function {name} with formal arguments {a} cannot be applied to provided arguments {b}."
                            ),
                            &e.metadata().position,
                        );
                    }
                    let typ = e.typ().map_err(ProgramUseCheckError::Type)?;
                    if typ != def.typ {
                        let a = render(&Node::Type(typ)).map_err(ProgramUseCheckError::Render)?;
                        let b = render(&Node::Type(def.typ.clone()))
                            .map_err(ProgramUseCheckError::Render)?;
                        emit(
                            &mut result,
                            format!(
                                "No matching function {name} found of return type {a}, instead found with return type {b}."
                            ),
                            &e.metadata().position,
                        );
                    }
                }
            }
        }
    }
    let all = nodes::<E>(&Node::Program(p.clone()))?;
    for n in &all {
        if let Node::Exp(e) = n {
            if let ExpKind::DomainFuncApp(name, args, subst) = e.kind() {
                if let Some(def) = p.find_domain_function_optionally(name) {
                    let formal: Vec<_> = def
                        .formal_args
                        .iter()
                        .map(|v| v.typ().substitute(subst))
                        .collect();
                    if !assign_exps(args, &formal)? {
                        let a: Vec<_> = def
                            .formal_args
                            .iter()
                            .map(|v| match v {
                                AnyLocalVarDecl::Named(v) => Node::LocalDecl(v.clone()),
                                AnyLocalVarDecl::Unnamed(v) => Node::UnnamedLocalDecl(v.clone()),
                            })
                            .collect();
                        let a = render_seq(&a).map_err(ProgramUseCheckError::Render)?;
                        let b =
                            render_seq(&exp_nodes(args)).map_err(ProgramUseCheckError::Render)?;
                        emit(
                            &mut result,
                            format!(
                                "Domain function {name} with formal arguments {a} cannot be applied to provided arguments {b}."
                            ),
                            &e.metadata().position,
                        );
                    }
                    let typ = e.typ().map_err(ProgramUseCheckError::Type)?;
                    if typ != def.typ.substitute(subst) {
                        let a = render(&Node::Type(typ)).map_err(ProgramUseCheckError::Render)?;
                        let b = render(&Node::Type(def.typ.clone()))
                            .map_err(ProgramUseCheckError::Render)?;
                        emit(
                            &mut result,
                            format!(
                                "No matching domain function {name} found of return type {a}, instead found with return type {b}."
                            ),
                            &e.metadata().position,
                        );
                    }
                    let domain =
                        e.0.extra
                            .domain_name
                            .as_ref()
                            .ok_or(ProgramUseCheckError::MissingDomainName)?;
                    if domain != &def.domain_name {
                        emit(
                            &mut result,
                            format!(
                                "No matching domain function {name} found in domain {domain}, instead found in domain {}.",
                                def.domain_name
                            ),
                            &e.metadata().position,
                        );
                    }
                } else {
                    emit(
                        &mut result,
                        format!("No domain function named {name} found in the program."),
                        &e.metadata().position,
                    );
                }
            }
        }
    }
    let all = nodes::<E>(&Node::Program(p.clone()))?;
    for n in &all {
        let access = match n {
            Node::PredicateAccess(v) => Some(v),
            Node::Exp(e) => {
                if let ExpKind::PredicateAccess(v) = e.kind() {
                    Some(v)
                } else {
                    None
                }
            }
            _ => None,
        };
        if let Some(access) = access {
            if let Some(def) = p.find_predicate_optionally(&access.predicate_name) {
                let formal: Vec<_> = def.formal_args.iter().map(|v| v.typ.clone()).collect();
                if !assign_exps(&access.args, &formal)? {
                    let a = render_seq(&decl_nodes(&def.formal_args))
                        .map_err(ProgramUseCheckError::Render)?;
                    let b = render_seq(&exp_nodes(&access.args))
                        .map_err(ProgramUseCheckError::Render)?;
                    emit(
                        &mut result,
                        format!(
                            "Predicate {} with formal arguments {a} cannot be used with provided arguments {b}.",
                            access.predicate_name
                        ),
                        &access.meta.position,
                    );
                }
            }
        }
    }
    for root in p
        .predicates
        .iter()
        .cloned()
        .map(crate::ast::program::Member::Predicate)
        .chain(
            p.functions
                .iter()
                .cloned()
                .map(crate::ast::program::Member::Function),
        )
        .chain(
            p.methods
                .iter()
                .cloned()
                .map(crate::ast::program::Member::Method),
        )
    {
        for n in nodes::<E>(&Node::Member(root))? {
            let (access, pos) = match &n {
                Node::Stmt(s) => match s.kind() {
                    StmtKind::Fold(a) | StmtKind::Unfold(a) => (
                        Some(a.location.clone()),
                        Some(s.metadata().position.clone()),
                    ),
                    _ => (None, None),
                },
                Node::Exp(e) => match e.kind() {
                    ExpKind::Unfolding(a, _) => match a.kind() {
                        ExpKind::PredicateAccessPredicate(a) => (
                            Some(a.location.clone()),
                            Some(e.metadata().position.clone()),
                        ),
                        _ => return Err(ProgramUseCheckError::InvalidPredicateAccess),
                    },
                    _ => (None, None),
                },
                _ => (None, None),
            };
            if let (Some(access), Some(pos)) = (access, pos) {
                if p.find_predicate_optionally(&access.predicate_name)
                    .is_some_and(|d| d.body.is_none())
                {
                    let text = render(&Node::PredicateAccess(access.clone()))
                        .map_err(ProgramUseCheckError::Render)?;
                    emit(
                        &mut result,
                        format!(
                            "Cannot unfold {text} because {}  is abstract.",
                            access.predicate_name
                        ),
                        &pos,
                    );
                }
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
mod program_use_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        expression::LocalVar,
        program::{LocalVarDecl, Method, MethodData},
        statement::{Stmt, StmtKind},
    };
    #[test]
    fn method_returns_are_checked_before_arguments() {
        let m = Metadata::default();
        let arg = LocalVarDecl::new("a".into(), Type::Int, m.clone());
        let ret = LocalVarDecl::new("r".into(), Type::Int, m.clone());
        let callee = Method::new(MethodData {
            name: "callee".into(),
            formal_args: vec![arg],
            formal_returns: vec![ret],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: m.clone(),
        });
        let call = Stmt::new(
            StmtKind::MethodCall {
                method_name: "callee".into(),
                args: vec![Exp::new(ExpKind::FalseLit, m.clone())],
                targets: vec![LocalVar::new("b".into(), Type::Bool, m.clone())],
            },
            m.clone(),
        );
        let caller = Method::new(MethodData {
            name: "caller".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(Stmt::new(
                StmtKind::Seqn {
                    statements: vec![call],
                    declarations: vec![],
                },
                m.clone(),
            )),
            meta: m.clone(),
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![caller, callee],
            vec![],
            m,
        );
        let errors = check_program_uses(
            &program,
            &|_| -> Result<String, ()> { Ok("node".into()) },
            &|_| -> Result<String, ()> { Ok("nodes".into()) },
        )
        .unwrap();
        assert_eq!(errors.len(), 2);
        assert!(
            matches!(&errors[0].kind, FrontendErrorKind::ConsistencyError(s) if s.starts_with("Formal returns"))
        );
        assert!(
            matches!(&errors[1].kind, FrontendErrorKind::ConsistencyError(s) if s.starts_with("Arguments"))
        );
    }
}

#[derive(Debug)]
pub enum ProgramConsistencyError<E> {
    Context(ContextConsistencyError),
    FunctionAnalysis(super::functions::FunctionAnalysisError),
    Uses(ProgramUseCheckError<E>),
    Identifiers(IdentifierCheckError),
}
/// Program's own consistency checks, in upstream order; this does not recursively
/// invoke node-local checks and therefore is not a transitive consistency result.
pub fn check_program<E>(
    program: &Program,
    render: &impl Fn(&Node) -> Result<String, E>,
    render_seq: &impl Fn(&[Node]) -> Result<String, E>,
) -> Result<Vec<FrontendError>, ProgramConsistencyError<E>> {
    let mut result = check_context_dependent_consistency(&Node::Program(program.clone()), program)
        .map_err(ProgramConsistencyError::Context)?;
    result.extend(
        check_no_function_recurses_via_preconditions(program)
            .map_err(ProgramConsistencyError::FunctionAnalysis)?,
    );
    result.extend(
        check_program_uses(program, render, render_seq).map_err(ProgramConsistencyError::Uses)?,
    );
    result.extend(check_identifiers(program).map_err(ProgramConsistencyError::Identifiers)?);
    Ok(result)
}

#[derive(Debug)]
pub enum NodeConsistencyError<E> {
    Program(ProgramConsistencyError<E>),
    Helper(ConsistencyCheckError<E>),
    Traversal(TraversalError),
    Type(crate::ast::expression::ExpressionTypeError),
    Render(E),
    Unsupported(&'static str),
    Extension(crate::verifier::verification_result::DiagnosticError),
}
impl<E> From<TraversalError> for NodeConsistencyError<E> {
    fn from(value: TraversalError) -> Self {
        Self::Traversal(value)
    }
}
impl<E> From<crate::ast::expression::ExpressionTypeError> for NodeConsistencyError<E> {
    fn from(value: crate::ast::expression::ExpressionTypeError) -> Self {
        Self::Type(value)
    }
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ConsistencyOptions {
    pub respect_function_pre_perm_amounts: bool,
}

/// Local source `Node.check` dispatch. Unported families explicitly fail.
pub fn check_node<E>(
    node: &Node,
    program: &Program,
    render: &impl Fn(&Node) -> Result<String, E>,
    render_seq: &impl Fn(&[Node]) -> Result<String, E>,
) -> Result<Vec<FrontendError>, NodeConsistencyError<E>> {
    check_node_with_options(
        node,
        program,
        render,
        render_seq,
        ConsistencyOptions::default(),
    )
}

pub fn check_node_with_options<E>(
    node: &Node,
    program: &Program,
    render: &impl Fn(&Node) -> Result<String, E>,
    render_seq: &impl Fn(&[Node]) -> Result<String, E>,
    options: ConsistencyOptions,
) -> Result<Vec<FrontendError>, NodeConsistencyError<E>> {
    use crate::ast::{program::Member, statement::StmtKind};
    fn add(out: &mut Vec<FrontendError>, message: String, pos: &crate::ast::position::Position) {
        out.push(FrontendError::new(
            FrontendErrorKind::ConsistencyError(message),
            pos.clone(),
        ));
    }
    let render_exp = |e: &Exp| render(&Node::Exp(e.clone()));
    let render_type = |t: &Type| render(&Node::Type(t.clone()));
    let mut out = Vec::new();
    match node {
        Node::Program(p) => {
            return check_program(p, render, render_seq).map_err(NodeConsistencyError::Program);
        }
        Node::Type(Type::Extension(v)) => {
            out.extend(v.check().map_err(NodeConsistencyError::Extension)?)
        }
        Node::Type(_) | Node::Trigger(_) | Node::LocalDecl(_) | Node::UnnamedLocalDecl(_) => {}
        Node::DomainFunc(f) => {
            if f.unique && !f.formal_args.is_empty() {
                add(
                    &mut out,
                    "Only constants, i.e. nullary domain functions can be unique.".into(),
                    &f.meta.position,
                );
            }
        }
        Node::DomainAxiom(a) => {
            let e = a.exp();
            let n = Node::Exp(e.clone());
            for (bad, text) in [
                (
                    !no_result(&n)?,
                    "Axioms can never contain result variables.",
                ),
                (!no_old(&n)?, "Axioms can never contain old expressions."),
                (
                    !no_location_accesses(&n)?,
                    "Axioms can never contain location accesses.",
                ),
                (
                    !no_asserting(&n)?,
                    "Axioms can never contain asserting expressions.",
                ),
            ] {
                if bad {
                    out.push(diagnostic(e, text.into()));
                }
            }
            if !e.typ()?.is_subtype(&Type::Bool) {
                out.push(diagnostic(e, "Axioms must be of Bool type".into()));
            }
            out.extend(check_pure(e, &render_exp).map_err(NodeConsistencyError::Helper)?);
        }
        Node::Member(Member::Domain(d)) => {
            if !d.type_vars.is_empty() && d.interpretations.is_some() {
                add(
                    &mut out,
                    "Interpreted domains cannot have type arguments.".into(),
                    &d.meta.position,
                );
            }
        }
        Node::Member(Member::Field(f)) => {
            if !f.typ.is_concrete() {
                add(
                    &mut out,
                    format!(
                        "Type of field {} must be concrete, but found {}.",
                        f.name,
                        render_type(&f.typ).map_err(NodeConsistencyError::Render)?
                    ),
                    &f.meta.position,
                );
            }
        }
        Node::Member(Member::Method(m)) => {
            for e in &m.pres {
                out.extend(
                    check_contract(e, ContractKind::Precondition, &render_exp, &render_type)
                        .map_err(NodeConsistencyError::Helper)?,
                );
            }
            for e in &m.posts {
                out.extend(
                    check_contract(e, ContractKind::Postcondition, &render_exp, &render_type)
                        .map_err(NodeConsistencyError::Helper)?,
                );
            }
            for e in &m.posts {
                if !no_result(&Node::Exp(e.clone()))? {
                    out.push(diagnostic(
                        e,
                        "Method postconditions must have no result variables.".into(),
                    ));
                }
            }
            if let Some(body) = &m.body {
                out.extend(
                    check_no_args_reassigned(&m.formal_args, body, render)
                        .map_err(NodeConsistencyError::Helper)?,
                );
            }
            if m.formal_args
                .iter()
                .chain(&m.formal_returns)
                .any(|v| !v.typ.is_concrete())
            {
                add(
                    &mut out,
                    "Formal args and returns must have concrete types.".into(),
                    &m.meta.position,
                );
            }
            for e in m.pres.iter().chain(&m.posts) {
                out.extend(check_no_perm_forperm_except_inhale_exhale(e)?);
            }
            fn vars(
                n: &Node,
                out: &mut Vec<crate::ast::expression::LocalVar>,
            ) -> Result<(), TraversalError> {
                if let Node::LocalVar(v) = n {
                    out.push(v.clone());
                }
                if let Node::Exp(e) = n {
                    if let ExpKind::LocalVar(v) = e.kind() {
                        out.push(v.clone());
                    }
                }
                for c in subnodes(n)? {
                    vars(&c, out)?;
                }
                Ok(())
            }
            let mut used = Vec::new();
            for e in &m.pres {
                vars(&Node::Exp(e.clone()), &mut used)?;
            }
            for ret in &m.formal_returns {
                for v in &used {
                    if v.name == ret.name && v.typ == ret.typ {
                        add(
                            &mut out,
                            format!(
                                "Return variable {} cannot be accessed in precondition.",
                                v.name
                            ),
                            &v.meta.position,
                        );
                    }
                }
            }
            for e in m.pres.iter().chain(&m.posts) {
                out.extend(check_wildcard_usage(&Node::Exp(e.clone()), false, false)?);
            }
            if let Some(body) = &m.body {
                out.extend(check_wildcard_usage(
                    &Node::Stmt(body.clone()),
                    false,
                    false,
                )?);
            }
        }
        Node::Member(Member::Predicate(predicate)) => {
            if let Some(body) = &predicate.body {
                out.extend(
                    check_contract(body, ContractKind::NonPost, &render_exp, &render_type)
                        .map_err(NodeConsistencyError::Helper)?,
                );
                out.extend(check_wildcard_usage(
                    &Node::Exp(body.clone()),
                    false,
                    options.respect_function_pre_perm_amounts,
                )?);
                let n = Node::Exp(body.clone());
                if !no_old(&n)? {
                    out.push(diagnostic(
                        body,
                        "Predicates must not contain old expressions.".into(),
                    ));
                }
                if !no_perm(&n)? || !no_for_perm(&n)? {
                    out.push(diagnostic(
                        body,
                        "perm and forperm expressions are not allowed in predicate bodies".into(),
                    ));
                }
                let wands = std::cell::RefCell::new(Vec::new());
                super::nodes::map_node_tree(&n, &|node| {
                    if let Node::Exp(e) = node {
                        if matches!(e.kind(), ExpKind::MagicWand(..)) {
                            wands.borrow_mut().push(e.clone());
                        }
                    }
                    Ok(node.clone())
                })
                .map_err(NodeConsistencyError::Extension)?;
                for wand in wands.into_inner() {
                    out.push(diagnostic(
                        &wand,
                        "Magic wands are not supported in predicates.".into(),
                    ));
                }
            }
        }
        Node::Member(Member::Function(function)) => {
            for post in &function.posts {
                if !no_old(&Node::Exp(post.clone()))? {
                    out.push(diagnostic(
                        post,
                        "Function post-conditions must not have old expressions.".into(),
                    ));
                }
            }
            for e in function.pres.iter().chain(&function.posts) {
                out.extend(check_no_perm_forperm_except_inhale_exhale(e)?);
            }
            for e in function
                .pres
                .iter()
                .chain(&function.posts)
                .chain(function.body.iter())
            {
                out.extend(check_wildcard_usage(
                    &Node::Exp(e.clone()),
                    true,
                    options.respect_function_pre_perm_amounts,
                )?);
            }
            if let Some(body) = &function.body {
                if !body.typ()?.is_subtype(&function.typ) {
                    add(
                        &mut out,
                        "Type of function body must match function type.".into(),
                        &function.meta.position,
                    );
                }
            }
            for post in &function.posts {
                let n = Node::Exp(post.clone());
                if !no_perm(&n)? || !no_for_perm(&n)? {
                    out.push(diagnostic(
                        post,
                        "perm and forperm expressions are not allowed in function postconditions"
                            .into(),
                    ));
                }
            }
            for pre in &function.pres {
                out.extend(
                    check_contract(pre, ContractKind::Precondition, &render_exp, &render_type)
                        .map_err(NodeConsistencyError::Helper)?,
                );
            }
            for post in &function.posts {
                out.extend(
                    check_contract(post, ContractKind::Postcondition, &render_exp, &render_type)
                        .map_err(NodeConsistencyError::Helper)?,
                );
            }
            for post in &function.posts {
                if !no_permissions(&Node::Exp(post.clone()))? {
                    out.push(diagnostic(
                        post,
                        "Function post-conditions must not contain permissions.".into(),
                    ));
                }
            }
            if let Some(body) = &function.body {
                out.extend(
                    check_function_body(body, &render_exp).map_err(NodeConsistencyError::Helper)?,
                );
            }
            if !no_duplicates(&function.formal_args) {
                add(
                    &mut out,
                    "There must be no duplicates in formal args.".into(),
                    &function.meta.position,
                );
            }
            for pre in &function.pres {
                let wands = std::cell::RefCell::new(Vec::new());
                super::nodes::map_node_tree(&Node::Exp(pre.clone()), &|node| {
                    if let Node::Exp(e) = node {
                        if matches!(e.kind(), ExpKind::MagicWand(..)) {
                            wands.borrow_mut().push(e.clone());
                        }
                    }
                    Ok(node.clone())
                })
                .map_err(NodeConsistencyError::Extension)?;
                for wand in wands.into_inner() {
                    out.push(diagnostic(
                        &wand,
                        "Magic wands are not supported in function's preconditions.".into(),
                    ));
                }
            }
        }
        Node::Member(Member::Extension(v)) => {
            out.extend(v.0.check().map_err(NodeConsistencyError::Extension)?)
        }
        Node::LocalVar(v) => {
            if !valid_user_defined_identifier(&v.name) {
                add(
                    &mut out,
                    "Local var name must be valid identifier.".into(),
                    &v.meta.position,
                );
            }
        }
        Node::FieldAccess(_) => {}
        Node::PredicateAccess(v) => {
            for e in &v.args {
                out.extend(check_pure(e, &render_exp).map_err(NodeConsistencyError::Helper)?);
            }
        }
        Node::PredicateAccessPredicate(v) => {
            let permission = v.permission_or_full();
            let typ = permission.typ()?;
            if !typ.is_subtype(&Type::Perm) {
                out.push(diagnostic(&permission, format!("Permission amount parameter of access predicate must be of Perm type, but found {}", render_type(&typ).map_err(NodeConsistencyError::Render)?)));
            }
        }
        Node::LabelDecl(label) => {
            let view = crate::ast::statement::Stmt::new(
                StmtKind::Label(label.clone()),
                label.meta.clone(),
            );
            return check_node_with_options(
                &Node::Stmt(view),
                program,
                render,
                render_seq,
                options,
            );
        }
        Node::Stmt(s) => {
            let n = Node::Stmt(s.clone());
            let no_result_message =
                "Result variables are only allowed in postconditions of functions.";
            match s.kind() {
                StmtKind::Seqn { .. } | StmtKind::Goto(_) | StmtKind::LocalVarDeclStmt(_) => {}
                StmtKind::Assert(e)
                | StmtKind::Inhale(e)
                | StmtKind::Exhale(e)
                | StmtKind::Assume(e) => {
                    if !matches!(s.kind(), StmtKind::Assume(_)) && !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                    let typ = e.typ()?;
                    if !typ.is_subtype(&Type::Bool) {
                        let action = match s.kind() {
                            StmtKind::Assert(_) => "assert",
                            StmtKind::Inhale(_) => "inhale",
                            StmtKind::Exhale(_) => "exhale",
                            _ => "assume",
                        };
                        out.push(diagnostic(
                            e,
                            format!(
                                "Assertion to {action} must be of type Bool, but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                StmtKind::Label(label) => {
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                    for e in &label.invariants {
                        let typ = e.typ()?;
                        if !typ.is_subtype(&Type::Bool) {
                            out.push(diagnostic(
                                e,
                                format!(
                                    "Label invariants must be of type Bool, but found {}",
                                    render_type(&typ).map_err(NodeConsistencyError::Render)?
                                ),
                            ));
                        }
                    }
                }
                StmtKind::If { condition, .. } => {
                    out.extend(
                        check_pure(condition, &render_exp).map_err(NodeConsistencyError::Helper)?,
                    );
                    let typ = condition.typ()?;
                    if !typ.is_subtype(&Type::Bool) {
                        out.push(diagnostic(
                            condition,
                            format!(
                                "If condition must be of type Bool, but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                }
                StmtKind::NewStmt { lhs, .. } => {
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                    if !Type::Ref.is_subtype(&lhs.typ) {
                        add(
                            &mut out,
                            format!(
                                "Left-hand side of New statement must be Ref type, but found {}",
                                render_type(&lhs.typ).map_err(NodeConsistencyError::Render)?
                            ),
                            &lhs.meta.position,
                        );
                    }
                }
                StmtKind::LocalVarAssign { lhs, rhs } => {
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                    out.extend(check_pure(rhs, &render_exp).map_err(NodeConsistencyError::Helper)?);
                    if !rhs.typ()?.is_subtype(&lhs.typ) {
                        add(
                            &mut out,
                            format!(
                                "Right-hand side {} is not assignable to left-hand side {}.",
                                render_exp(rhs).map_err(NodeConsistencyError::Render)?,
                                render(&Node::LocalVar(lhs.clone()))
                                    .map_err(NodeConsistencyError::Render)?
                            ),
                            &lhs.meta.position,
                        );
                    }
                }
                StmtKind::FieldAssign { lhs, rhs } => {
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                    out.extend(check_pure(rhs, &render_exp).map_err(NodeConsistencyError::Helper)?);
                    if !rhs.typ()?.is_subtype(&lhs.field.typ) {
                        add(
                            &mut out,
                            format!(
                                "Right-hand side {} is not assignable to left-hand side {}.",
                                render_exp(rhs).map_err(NodeConsistencyError::Render)?,
                                render(&Node::FieldAccess(lhs.clone()))
                                    .map_err(NodeConsistencyError::Render)?
                            ),
                            &lhs.meta.position,
                        );
                    }
                }
                StmtKind::MethodCall { args, targets, .. } => {
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                    if !no_duplicates(targets) {
                        add(
                            &mut out,
                            "Targets are not allowed to have duplicates".into(),
                            &s.metadata().position,
                        );
                    }
                    for e in args {
                        out.extend(
                            check_pure(e, &render_exp).map_err(NodeConsistencyError::Helper)?,
                        );
                    }
                }
                StmtKind::While {
                    condition,
                    invariants,
                    ..
                } => {
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                    out.extend(
                        check_pure(condition, &render_exp).map_err(NodeConsistencyError::Helper)?,
                    );
                    for e in invariants {
                        out.extend(
                            check_contract(e, ContractKind::NonPost, &render_exp, &render_type)
                                .map_err(NodeConsistencyError::Helper)?,
                        );
                    }
                    let typ = condition.typ()?;
                    if !typ.is_subtype(&Type::Bool) {
                        out.push(diagnostic(
                            condition,
                            format!(
                                "While loop condition must be of type Bool, but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    for e in invariants {
                        out.extend(check_no_perm_forperm_except_inhale_exhale(e)?);
                    }
                }
                StmtKind::Package { wand, .. } | StmtKind::Apply(wand) => {
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                    let typ = wand.typ()?;
                    if !typ.is_subtype(&Type::Wand) {
                        out.push(diagnostic(
                            wand,
                            format!(
                                "Expected wand but found {} ({})",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?,
                                render_exp(wand).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                StmtKind::Quasihavoc { guard, resource }
                | StmtKind::Quasihavocall {
                    guard, resource, ..
                } => {
                    use crate::ast::statement::ResourceAccess;
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                    if let Some(guard) = guard {
                        if !guard.typ()?.is_subtype(&Type::Bool) {
                            let resource = match resource {
                                ResourceAccess::Field(v) => {
                                    Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone())
                                }
                                ResourceAccess::Predicate(v) => {
                                    Exp::new(ExpKind::PredicateAccess(v.clone()), v.meta.clone())
                                }
                                ResourceAccess::MagicWand(v) => v.clone(),
                            };
                            let name = if matches!(s.kind(), StmtKind::Quasihavoc { .. }) {
                                "quasihavoc"
                            } else {
                                "quasihavocall"
                            };
                            out.push(diagnostic(&resource, format!("Left side of {name} implication must be of type Bool, but found {}", render_type(&resource.typ()?).map_err(NodeConsistencyError::Render)?)));
                        }
                    }
                }
                StmtKind::Fold(_) | StmtKind::Unfold(_) => {
                    if !no_result(&n)? {
                        add(&mut out, no_result_message.into(), &s.metadata().position);
                    }
                }
                StmtKind::Extension(v) => {
                    out.extend(v.0.check().map_err(NodeConsistencyError::Extension)?)
                }
            }
        }
        Node::Exp(e) => {
            use ExpKind::*;
            match e.kind() {
                IntLit(_) | TrueLit | FalseLit | NullLit | RefLit(_) | BackendValueLit(..)
                | WildcardPerm | FullPerm | NoPerm | EpsilonPerm | Result(_) | FieldAccess(_)
                | Add(..) | Sub(..) | Mul(..) | Div(..) | Mod(..) | LtCmp(..) | LeCmp(..)
                | GtCmp(..) | GeCmp(..) | Minus(..) | And(..) | PermMinus(..) | PermAdd(..)
                | PermSub(..) | PermMul(..) | IntPermMul(..) | DebugPermMin(..) | PermLtCmp(..)
                | PermLeCmp(..) | PermGtCmp(..) | PermGeCmp(..) | CurrentPerm(_)
                | MagicWand(..) => {}
                LocalVar(v) => {
                    if !valid_user_defined_identifier(&v.name) {
                        add(
                            &mut out,
                            "Local var name must be valid identifier.".into(),
                            &v.meta.position,
                        );
                    }
                }
                LocalVarWithVersion(name, _) => {
                    if !valid_user_defined_identifier(name) {
                        out.push(diagnostic(
                            e,
                            "Local var name must be valid identifier.".into(),
                        ));
                    }
                }
                EmptySeq(_) | EmptySet(_) | EmptyMultiset(_) | EmptyMap(..) | Maplet(..) => {}
                ExplicitSeq(elems) | ExplicitSet(elems) | ExplicitMultiset(elems) => {
                    let Some(first) = elems.first() else {
                        return Err(NodeConsistencyError::Type(
                            crate::ast::expression::ExpressionTypeError::EmptyCollection,
                        ));
                    };
                    let mut same = true;
                    for item in &elems[1..] {
                        if item.typ()? != first.typ()? {
                            same = false;
                            break;
                        }
                    }
                    if !same {
                        let collection = match e.kind() {
                            ExplicitSeq(_) => "sequence",
                            ExplicitSet(_) => "set",
                            _ => "multiset",
                        };
                        out.push(diagnostic(
                            first,
                            format!("All elements of {collection} must have same type."),
                        ));
                    }
                    for item in elems {
                        out.extend(
                            check_pure(item, &render_exp).map_err(NodeConsistencyError::Helper)?,
                        );
                    }
                }
                RangeSeq(low, high) => {
                    let low_type = low.typ()?;
                    if !low_type.is_subtype(&Type::Int) {
                        out.push(diagnostic(low, format!("First parameter of range-sequence expression must be Int, but found {}", render_type(&low_type).map_err(NodeConsistencyError::Render)?)));
                    }
                    let high_type = high.typ()?;
                    if !high_type.is_subtype(&Type::Int) {
                        out.push(diagnostic(high, format!("Second parameter of range-sequence expression must be Int, but found {}", render_type(&high_type).map_err(NodeConsistencyError::Render)?)));
                    }
                }
                SeqAppend(left, right) => {
                    let rt = right.typ()?;
                    let lt = left.typ()?;
                    if rt != lt {
                        out.push(diagnostic(left, format!("Left and right sequence types of sequence-append expression must match, but found {} and {}.", render_type(&lt).map_err(NodeConsistencyError::Render)?, render_type(&rt).map_err(NodeConsistencyError::Render)?)));
                    }
                }
                SeqIndex(seq, index) | SeqTake(seq, index) | SeqDrop(seq, index) => {
                    let typ = seq.typ()?;
                    if !matches!(typ, Type::Seq(_)) {
                        out.push(diagnostic(
                            seq,
                            format!(
                                "Expected sequence type but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    let typ = index.typ()?;
                    if !typ.is_subtype(&Type::Int) {
                        let operation = match e.kind() {
                            SeqIndex(..) => "access",
                            SeqTake(..) => "take",
                            _ => "drop",
                        };
                        out.push(diagnostic(index, format!("Second parameter of sequence-{operation} expression must be Int, but found {}", render_type(&typ).map_err(NodeConsistencyError::Render)?)));
                    }
                }
                SeqLength(seq) => {
                    let typ = seq.typ()?;
                    if !matches!(typ, Type::Seq(_)) {
                        out.push(diagnostic(
                            seq,
                            format!(
                                "Expected sequence type but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                SeqContains(elem, seq) | SeqUpdate(seq, _, elem) => {
                    let typ = seq.typ()?;
                    if !matches!(typ, Type::Seq(_)) {
                        out.push(diagnostic(
                            seq,
                            format!(
                                "Expected sequence type but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    if let SeqUpdate(_, index, _) = e.kind() {
                        let typ = index.typ()?;
                        if !typ.is_subtype(&Type::Int) {
                            out.push(diagnostic(index, format!("Second parameter of sequence-update expression must be of Int type, but found {}", render_type(&typ).map_err(NodeConsistencyError::Render)?)));
                        }
                    }
                    let Type::Seq(element_type) = typ else {
                        return Err(NodeConsistencyError::Type(
                            crate::ast::expression::ExpressionTypeError::ExpectedSequence,
                        ));
                    };
                    let actual = elem.typ()?;
                    if !actual.is_subtype(&element_type) {
                        out.push(diagnostic(
                            elem,
                            format!(
                                "Expected type {} but found {}",
                                render_type(&element_type).map_err(NodeConsistencyError::Render)?,
                                render_type(&actual).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    if matches!(e.kind(), SeqUpdate(..)) {
                        out.extend(
                            check_pure(elem, &render_exp).map_err(NodeConsistencyError::Helper)?,
                        );
                    }
                }
                AnySetUnion(left, right)
                | AnySetIntersection(left, right)
                | AnySetSubset(left, right)
                | AnySetMinus(left, right) => {
                    let lt = left.typ()?;
                    let rt = right.typ()?;
                    if lt != rt {
                        out.push(diagnostic(
                            left,
                            "Left and right operand types must match".into(),
                        ));
                    }
                    if !matches!(lt, Type::Set(_) | Type::Multiset(_)) {
                        out.push(diagnostic(
                            left,
                            format!(
                                "Expected SetType or MultisetType, but found {}",
                                render_type(&lt).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                AnySetContains(elem, set) => {
                    let st = set.typ()?;
                    let compatible = match &st {
                        Type::Set(t) | Type::Multiset(t) => elem.typ()?.is_subtype(t),
                        _ => false,
                    };
                    if !compatible {
                        out.push(diagnostic(
                            elem,
                            format!(
                                "Set type {} and element type {} must be compatible.",
                                render_type(&st).map_err(NodeConsistencyError::Render)?,
                                render_type(&elem.typ()?).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                AnySetCardinality(set) => {
                    let typ = set.typ()?;
                    if !matches!(typ, Type::Set(_) | Type::Multiset(_)) {
                        out.push(diagnostic(
                            set,
                            format!(
                                "Set type expected SetType or MultisetType, but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                ExplicitMap(elems) => {
                    let pairs: Vec<_> = elems
                        .iter()
                        .filter_map(|item| {
                            if let Maplet(k, v) = item.kind() {
                                Some((k, v))
                            } else {
                                None
                            }
                        })
                        .collect();
                    let Some((first_key, first_value)) = pairs.first() else {
                        return Err(NodeConsistencyError::Type(
                            crate::ast::expression::ExpressionTypeError::EmptyCollection,
                        ));
                    };
                    if pairs.len() != elems.len() {
                        out.push(diagnostic(
                            e,
                            "All elements of a map must be key-value pairs.".into(),
                        ));
                    }
                    let mut same_keys = true;
                    for (k, _) in &pairs[1..] {
                        if k.typ()? != first_key.typ()? {
                            same_keys = false;
                            break;
                        }
                    }
                    if !same_keys {
                        out.push(diagnostic(
                            first_key,
                            "All keys within the map must have same type.".into(),
                        ));
                    }
                    let mut same_values = true;
                    for (_, v) in &pairs[1..] {
                        if v.typ()? != first_value.typ()? {
                            same_values = false;
                            break;
                        }
                    }
                    if !same_values {
                        out.push(diagnostic(
                            first_value,
                            "All values within the map must have same type.".into(),
                        ));
                    }
                    for item in elems {
                        out.extend(
                            check_pure(item, &render_exp).map_err(NodeConsistencyError::Helper)?,
                        );
                    }
                }
                MapUpdate(base, key, value) => {
                    out.extend(
                        check_pure(value, &render_exp).map_err(NodeConsistencyError::Helper)?,
                    );
                    match base.typ()? {
                        Type::Map(pair) => {
                            let kt = key.typ()?;
                            if !kt.is_subtype(&pair.0) {
                                out.push(diagnostic(
                                    key,
                                    format!(
                                        "Expected the key to be of type {}, but found {}",
                                        render_type(&pair.0)
                                            .map_err(NodeConsistencyError::Render)?,
                                        render_type(&kt).map_err(NodeConsistencyError::Render)?
                                    ),
                                ));
                            }
                            let vt = value.typ()?;
                            if !vt.is_subtype(&pair.1) {
                                out.push(diagnostic(
                                    value,
                                    format!(
                                        "Expected the value to be of type {}, but found {}",
                                        render_type(&pair.1)
                                            .map_err(NodeConsistencyError::Render)?,
                                        render_type(&vt).map_err(NodeConsistencyError::Render)?
                                    ),
                                ));
                            }
                        }
                        t => out.push(diagnostic(
                            base,
                            format!(
                                "Expected map type but found {}",
                                render_type(&t).map_err(NodeConsistencyError::Render)?
                            ),
                        )),
                    }
                }
                MapLookup(base, key) | MapContains(key, base) => match base.typ()? {
                    Type::Map(pair) => {
                        let typ = key.typ()?;
                        if !typ.is_subtype(&pair.0) {
                            out.push(diagnostic(
                                key,
                                format!(
                                    "Expected the key to be of type {}, but found {}",
                                    render_type(&pair.0).map_err(NodeConsistencyError::Render)?,
                                    render_type(&typ).map_err(NodeConsistencyError::Render)?
                                ),
                            ));
                        }
                    }
                    t => out.push(diagnostic(
                        base,
                        format!(
                            "Expected map type but found {}",
                            render_type(&t).map_err(NodeConsistencyError::Render)?
                        ),
                    )),
                },
                MapCardinality(base) | MapDomain(base) | MapRange(base) => {
                    let typ = base.typ()?;
                    if !matches!(typ, Type::Map(_)) {
                        out.push(diagnostic(
                            base,
                            format!(
                                "Expected map type but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                CondExp(cond, thn, els) => {
                    let typ = cond.typ()?;
                    if !typ.is_subtype(&Type::Bool) {
                        out.push(diagnostic(
                            cond,
                            format!(
                                "Condition must be of Bool type, but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    out.extend(
                        check_pure(cond, &render_exp).map_err(NodeConsistencyError::Helper)?,
                    );
                    let a = thn.typ()?;
                    let b = els.typ()?;
                    if a != b {
                        out.push(diagnostic(thn, format!("Second and third parameter types of conditional expression must match, but found {} and {}", render_type(&a).map_err(NodeConsistencyError::Render)?, render_type(&b).map_err(NodeConsistencyError::Render)?)));
                    }
                }
                Unfolding(_, body) | Asserting(_, body) => {
                    out.extend(check_pure(body, &render_exp).map_err(NodeConsistencyError::Helper)?)
                }
                Applying(wand, body) => {
                    let typ = wand.typ()?;
                    if !typ.is_subtype(&Type::Wand) {
                        out.push(diagnostic(
                            wand,
                            format!(
                                "Expected wand but found {} ({})",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?,
                                render_exp(wand).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    out.extend(
                        check_pure(body, &render_exp).map_err(NodeConsistencyError::Helper)?,
                    );
                }
                Let(var, value, _) => {
                    let typ = value.typ()?;
                    if !typ.is_subtype(&var.typ) {
                        out.push(diagnostic(value, format!("Let-bound variable {} is of type {}, but bound expression is of type {}", var.name, render_type(&var.typ).map_err(NodeConsistencyError::Render)?, render_type(&typ).map_err(NodeConsistencyError::Render)?)));
                    }
                    if !value.is_pure() {
                        out.push(diagnostic(
                            value,
                            format!(
                                "Let expression '{}' is not pure",
                                render_exp(value).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                FractionalPerm(left, right) | PermDiv(left, right) | PermPermDiv(left, right) => {
                    let lt = left.typ()?;
                    let rt = right.typ()?;
                    let (expected_left, expected_right, left_msg, right_msg) = match e.kind() {
                        FractionalPerm(..) => (
                            Type::Int,
                            Type::Int,
                            "Numerator type of fractional permission must be Int, but found",
                            "Denominator type of fractional permission must be Int, but found",
                        ),
                        PermDiv(..) => (
                            Type::Perm,
                            Type::Int,
                            "First parameter of permission division expression must be Perm, but found",
                            "Second parameter of permission division expression must be Int, but found",
                        ),
                        _ => (
                            Type::Perm,
                            Type::Perm,
                            "First parameter of permission division expression must be Perm, but found",
                            "Second parameter of permission-permission division expression must be Perm, but found",
                        ),
                    };
                    if lt != expected_left {
                        out.push(diagnostic(
                            left,
                            format!(
                                "{left_msg} {}",
                                render_type(&lt).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    if rt != expected_right {
                        out.push(diagnostic(
                            right,
                            format!(
                                "{right_msg} {}",
                                render_type(&rt).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                Forall(vars, triggers, body) => {
                    let typ = body.typ()?;
                    if !typ.is_subtype(&Type::Bool) {
                        out.push(diagnostic(
                            body,
                            format!(
                                "Body of universal quantifier must be of Bool type, but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    if vars.is_empty() {
                        out.push(diagnostic(
                            e,
                            "Quantifier must have at least one quantified variable.".into(),
                        ));
                    }
                    out.extend(
                        check_all_vars_mentioned_in_triggers(vars, triggers, &render_exp)
                            .map_err(NodeConsistencyError::Helper)?,
                    );
                    if let Some((_, condition, _)) =
                        super::quantified_permissions::quantified_permission_assertion(e)
                    {
                        if exists(
                            &Node::Exp(condition.clone()),
                            &|n| matches!(n, Node::Exp(e) if matches!(e.kind(), Forall(..))),
                        )? && !condition.is_pure()
                        {
                            out.push(diagnostic(
                                &condition,
                                "Nested quantifiers are not allowed for quantified permissions."
                                    .into(),
                            ));
                        }
                    }
                    fn outside_unfolding(
                        n: &Node,
                        inside: bool,
                    ) -> std::result::Result<bool, NodeConsistencyError<()>> {
                        let inside = inside
                            || matches!(n, Node::Exp(e) if matches!(e.kind(), Unfolding(..)));
                        let mut found = !inside
                            && (matches!(n, Node::Exp(e) if matches!(e.kind(), FieldAccessPredicate(..) | PredicateAccessPredicate(_)))
                                || matches!(n, Node::PredicateAccessPredicate(_)));
                        for child in subnodes(n)? {
                            found |= outside_unfolding(&child, inside)?;
                        }
                        Ok(found)
                    }
                    match outside_unfolding(&Node::Exp(body.clone()), false) {
                        Ok(true) if !matches!(body.kind(), Implies(..) | FieldAccessPredicate(..) | PredicateAccessPredicate(_)) => out.push(diagnostic(body, "Quantified permissions must have an implication as expression, with the access predicate in its right-hand side.".into())),
                        Ok(_) => {},
                        Err(NodeConsistencyError::Traversal(e)) => return Err(NodeConsistencyError::Traversal(e)),
                        Err(_) => return Err(NodeConsistencyError::Unsupported("extension quantified-permission context")),
                    }
                }
                Exists(vars, triggers, body) => {
                    out.extend(
                        check_pure(body, &render_exp).map_err(NodeConsistencyError::Helper)?,
                    );
                    let typ = body.typ()?;
                    if !typ.is_subtype(&Type::Bool) {
                        out.push(diagnostic(
                            body,
                            format!(
                                "Body of existential quantifier must be of Bool type, but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    if vars.is_empty() {
                        out.push(diagnostic(
                            e,
                            "Quantifier must have at least one quantified variable.".into(),
                        ));
                    }
                    out.extend(
                        check_all_vars_mentioned_in_triggers(vars, triggers, &render_exp)
                            .map_err(NodeConsistencyError::Helper)?,
                    );
                }
                ForPerm(_, _, body) => {
                    let typ = body.typ()?;
                    if !typ.is_subtype(&Type::Bool) {
                        out.push(diagnostic(
                            body,
                            format!(
                                "Body of forperm quantifier must be of Bool type, but found {}",
                                render_type(&typ).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                    out.extend(
                        check_pure(body, &render_exp).map_err(NodeConsistencyError::Helper)?,
                    );
                    if !no_perm(&Node::Exp(body.clone()))? {
                        out.push(diagnostic(body, "Body of forperm quantifier is not allowed to contain perm expressions.".into()));
                    }
                    if !no_for_perm(&Node::Exp(body.clone()))? {
                        out.push(diagnostic(body, "Body of forperm quantifier is not allowed to contain nested forperm expressions.".into()));
                    }
                }
                FieldAccessPredicate(_, permission) => {
                    let permission = permission.clone().unwrap_or_else(|| {
                        Exp::new(
                            FullPerm,
                            crate::ast::ast::Metadata {
                                position: e.metadata().position.clone(),
                                ..Default::default()
                            },
                        )
                    });
                    let typ = permission.typ()?;
                    if !typ.is_subtype(&Type::Perm) {
                        out.push(diagnostic(&permission, format!("Permission amount parameter of access predicate must be of Perm type, but found {}", render_type(&typ).map_err(NodeConsistencyError::Render)?)));
                    }
                }
                PredicateAccessPredicate(v) => {
                    let permission = v.permission_or_full();
                    let typ = permission.typ()?;
                    if !typ.is_subtype(&Type::Perm) {
                        out.push(diagnostic(&permission, format!("Permission amount parameter of access predicate must be of Perm type, but found {}", render_type(&typ).map_err(NodeConsistencyError::Render)?)));
                    }
                }
                InhaleExhaleExp(first, second) => {
                    let first_typ = first.typ()?;
                    if !first_typ.is_subtype(&Type::Bool) {
                        out.push(diagnostic(first, format!("First parameter to inhale-exhale assertion must be of Bool type, but found {}", render_type(&first_typ).map_err(NodeConsistencyError::Render)?)));
                    }
                    let second_typ = second.typ()?;
                    if !second_typ.is_subtype(&Type::Bool) {
                        out.push(diagnostic(second, format!("Second parameter to inhale-exhale assertion must be of Bool type, but found {}", render_type(&second_typ).map_err(NodeConsistencyError::Render)?)));
                    }
                }
                PredicateAccess(v) => {
                    for arg in &v.args {
                        out.extend(
                            check_pure(arg, &render_exp).map_err(NodeConsistencyError::Helper)?,
                        );
                    }
                }
                FuncApp(_, args) | DomainFuncApp(_, args, _) | BackendFuncApp(_, args) => {
                    for arg in args {
                        out.extend(
                            check_pure(arg, &render_exp).map_err(NodeConsistencyError::Helper)?,
                        );
                    }
                }
                Not(inner) | Old(inner) | LabelledOld(inner, _) | DebugLabelledOld(inner, _) => out
                    .extend(check_pure(inner, &render_exp).map_err(NodeConsistencyError::Helper)?),
                Or(a, b) => {
                    out.extend(check_pure(a, &render_exp).map_err(NodeConsistencyError::Helper)?);
                    out.extend(check_pure(b, &render_exp).map_err(NodeConsistencyError::Helper)?);
                }
                Implies(a, _) => {
                    out.extend(check_pure(a, &render_exp).map_err(NodeConsistencyError::Helper)?)
                }
                EqCmp(a, b) | NeCmp(a, b) => {
                    out.extend(check_pure(a, &render_exp).map_err(NodeConsistencyError::Helper)?);
                    out.extend(check_pure(b, &render_exp).map_err(NodeConsistencyError::Helper)?);
                    let ta = a.typ()?;
                    let tb = b.typ()?;
                    if ta != tb {
                        out.push(diagnostic(
                            a,
                            format!(
                                "expected the same type, but got {} and {}",
                                render_type(&ta).map_err(NodeConsistencyError::Render)?,
                                render_type(&tb).map_err(NodeConsistencyError::Render)?
                            ),
                        ));
                    }
                }
                Extension(v) => out.extend(v.0.check().map_err(NodeConsistencyError::Extension)?),
            }
        }
    }
    Ok(out)
}

#[derive(Debug)]
pub enum TransitiveConsistencyError<E> {
    Node(NodeConsistencyError<E>),
    Reconstruction(crate::verifier::verification_result::DiagnosticError),
}
/// Source checkTransitively product traversal. A node family without a complete
/// local check returns Unsupported; partial checks never become a success result.
pub fn check_transitively<E>(
    program: &Program,
    render: &impl Fn(&Node) -> Result<String, E>,
    render_seq: &impl Fn(&[Node]) -> Result<String, E>,
) -> Result<Vec<FrontendError>, TransitiveConsistencyError<E>> {
    check_transitively_with_options(program, render, render_seq, ConsistencyOptions::default())
}

pub fn check_transitively_with_options<E>(
    program: &Program,
    render: &impl Fn(&Node) -> Result<String, E>,
    render_seq: &impl Fn(&[Node]) -> Result<String, E>,
    options: ConsistencyOptions,
) -> Result<Vec<FrontendError>, TransitiveConsistencyError<E>> {
    let errors = std::cell::RefCell::new(Vec::new());
    let failure = std::cell::RefCell::new(None);
    let result = super::nodes::visit_check_products(&Node::Program(program.clone()), &|node| {
        match check_node_with_options(node, program, render, render_seq, options) {
            Ok(mut found) => {
                errors.borrow_mut().append(&mut found);
                Ok(node.clone())
            }
            Err(err) => {
                *failure.borrow_mut() = Some(err);
                Err(
                    crate::verifier::verification_result::DiagnosticError::Unsupported(
                        "node consistency check",
                    ),
                )
            }
        }
    });
    if let Some(error) = failure.into_inner() {
        return Err(TransitiveConsistencyError::Node(error));
    }
    result.map_err(TransitiveConsistencyError::Reconstruction)?;
    Ok(errors.into_inner())
}

#[cfg(test)]
mod transitive_consistency_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        program::{Method, MethodData},
        statement::{Stmt, StmtKind},
    };
    #[derive(Debug)]
    struct UnknownExtension {
        meta: Metadata,
    }
    impl crate::ast::expression::ExtensionExp for UnknownExtension {
        fn metadata(&self) -> &Metadata {
            &self.meta
        }
        fn with_metadata(&self, meta: Metadata) -> crate::ast::expression::ExtensionExpHandle {
            crate::ast::expression::ExtensionExpHandle(std::sync::Arc::new(Self { meta }))
        }
        fn as_any(&self) -> &dyn std::any::Any {
            self
        }
        fn equals(&self, other: &dyn crate::ast::expression::ExtensionExp) -> bool {
            other.as_any().is::<Self>()
        }
        fn typ(&self) -> Type {
            Type::Bool
        }
        fn is_pure(&self) -> bool {
            true
        }
        fn scope_declarations(
            &self,
        ) -> Result<
            Option<Vec<crate::ast::program::Declaration>>,
            crate::verifier::verification_result::DiagnosticError,
        > {
            Ok(None)
        }
        fn subnodes(&self) -> Result<Vec<Node>, TraversalError> {
            Ok(vec![])
        }
    }
    #[test]
    fn sequence_length_expression_is_checked_transitively() {
        let m = Metadata::default();
        let length = Exp::new(
            ExpKind::SeqLength(Exp::new(ExpKind::EmptySeq(Type::Int), m.clone())),
            m.clone(),
        );
        let assertion = Exp::new(
            ExpKind::EqCmp(length, Exp::new(ExpKind::IntLit(0.into()), m.clone())),
            m.clone(),
        );
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![Stmt::new(StmtKind::Assert(assertion), m.clone())],
                declarations: vec![],
            },
            m.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: m.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], m);
        let renderer = |_: &Node| -> Result<String, ()> { Ok("node".into()) };
        let seq = |_: &[Node]| -> Result<String, ()> { Ok("nodes".into()) };
        assert!(
            check_transitively(&program, &renderer, &seq)
                .unwrap()
                .is_empty()
        );
    }
    #[test]
    fn pure_function_and_predicate_pass_local_checks() {
        use crate::ast::program::{Function, FunctionData, Predicate, PredicateData};
        let m = Metadata::default();
        let function = Function::new(FunctionData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Int,
            pres: vec![],
            posts: vec![],
            body: Some(Exp::new(ExpKind::IntLit(1.into()), m.clone())),
            meta: m.clone(),
        });
        let predicate = Predicate::new(PredicateData {
            name: "p".into(),
            formal_args: vec![],
            body: Some(Exp::new(ExpKind::TrueLit, m.clone())),
            meta: m.clone(),
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![function],
            vec![predicate],
            vec![],
            vec![],
            m,
        );
        let renderer = |_: &Node| -> Result<String, ()> { Ok("node".into()) };
        let seq = |_: &[Node]| -> Result<String, ()> { Ok("nodes".into()) };
        assert!(
            check_transitively(&program, &renderer, &seq)
                .unwrap()
                .is_empty()
        );
    }
    #[test]
    fn simple_method_is_checked() {
        let m = Metadata::default();
        let yes = Exp::new(ExpKind::TrueLit, m.clone());
        let mk_program = |body| {
            let method = Method::new(MethodData {
                name: "m".into(),
                formal_args: vec![],
                formal_returns: vec![],
                pres: vec![],
                posts: vec![],
                body: Some(body),
                meta: m.clone(),
            });
            Program::new(
                vec![],
                vec![],
                vec![],
                vec![],
                vec![method],
                vec![],
                m.clone(),
            )
        };
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![Stmt::new(StmtKind::Assert(yes.clone()), m.clone())],
                declarations: vec![],
            },
            m.clone(),
        );
        let renderer = |_: &Node| -> Result<String, ()> { Ok("node".into()) };
        let seq = |_: &[Node]| -> Result<String, ()> { Ok("nodes".into()) };
        assert!(
            check_transitively(&mk_program(body), &renderer, &seq)
                .unwrap()
                .is_empty()
        );
        let unknown = Exp::new(
            ExpKind::Extension(crate::ast::expression::ExtensionExpHandle(
                std::sync::Arc::new(UnknownExtension { meta: m.clone() }),
            )),
            m.clone(),
        );
        let body = Stmt::new(
            StmtKind::Seqn {
                statements: vec![Stmt::new(StmtKind::Assert(unknown), m.clone())],
                declarations: vec![],
            },
            m.clone(),
        );
        assert!(matches!(
            check_transitively(&mk_program(body), &renderer, &seq),
            Err(TransitiveConsistencyError::Node(
                NodeConsistencyError::Extension(_)
            ))
        ));
    }
}

#[cfg(test)]
mod scoped_name_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        program::{Function, FunctionData, LocalVarDecl},
    };
    #[test]
    fn transitive_names_include_nested_scopes_after_program_declarations() {
        let meta = Metadata::default();
        let arg = LocalVarDecl::new("x".into(), Type::Int, meta.clone());
        let bound = LocalVarDecl::new("y".into(), Type::Int, meta.clone());
        let body = Exp::new(
            ExpKind::Forall(
                vec![bound],
                vec![],
                Exp::new(ExpKind::TrueLit, meta.clone()),
            ),
            meta.clone(),
        );
        let function = Function::new(FunctionData {
            name: "f".into(),
            formal_args: vec![arg],
            typ: Type::Bool,
            pres: vec![],
            posts: vec![],
            body: Some(body),
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![function], vec![], vec![], vec![], meta);
        assert_eq!(
            transitive_scoped_names(&program).unwrap(),
            vec!["f", "x", "y"]
        );
    }
}
