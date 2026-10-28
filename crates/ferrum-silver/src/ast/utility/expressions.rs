//! Expression projections and queries.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Expressions.scala
//! Status: partial. Purity, conjuncts, fragments, free variables and built-in
//! inhale/exhale projection and heap-dependency queries are implemented; other queries remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use super::nodes::Node;
use crate::ast::expression::{Exp, ExpKind, FieldAccess, PredicateAccess, Trigger};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UnsupportedExtensionProjection;

/// Bottom-up projection of inhale/exhale expressions, retaining the selected
/// expression's metadata. Extensions require their own reconstruction hook.
pub fn when_inhaling(e: &Exp) -> Result<Exp, UnsupportedExtensionProjection> {
    project(e, true)
}
pub fn when_exhaling(e: &Exp) -> Result<Exp, UnsupportedExtensionProjection> {
    project(e, false)
}

fn project(e: &Exp, inhale: bool) -> Result<Exp, UnsupportedExtensionProjection> {
    let rebuilt = e.map_expression_children(
        &mut |child| project(child, inhale),
        &mut |_| Err(UnsupportedExtensionProjection),
        &mut |field| {
            let receiver = project(&field.receiver, inhale)?;
            Ok(if receiver == field.receiver {
                field.clone()
            } else {
                FieldAccess::new(receiver, field.field.clone(), field.meta.clone())
            })
        },
        &mut |pred| {
            let args = pred
                .args
                .iter()
                .map(|child| project(child, inhale))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(if args.iter().zip(&pred.args).all(|(a, b)| a == b) {
                pred.clone()
            } else {
                PredicateAccess::new(args, pred.predicate_name.clone(), pred.meta.clone())
            })
        },
        &mut |trigger| {
            let exps = trigger
                .exps
                .iter()
                .map(|child| project(child, inhale))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(if exps.iter().zip(&trigger.exps).all(|(a, b)| a == b) {
                trigger.clone()
            } else {
                Trigger::new(exps, trigger.meta.clone())
            })
        },
    )?;
    Ok(match rebuilt.kind() {
        ExpKind::InhaleExhaleExp(in_exp, ex_exp) => {
            if inhale {
                in_exp.clone()
            } else {
                ex_exp.clone()
            }
        }
        _ => rebuilt,
    })
}

/// Free abstract local variables, deduplicated by source structural equality.
/// `ignore` may include LocalVar, Result and LocalVarWithVersion expressions.
/// The returned vector represents the source set; its order is not a source guarantee.
pub fn free_variables(e: &Exp, ignore: &[Exp]) -> Result<Vec<Exp>, super::nodes::TraversalError> {
    fn visit(
        node: &super::nodes::Node,
        ignore: &[Exp],
        out: &mut Vec<Exp>,
    ) -> Result<(), super::nodes::TraversalError> {
        use super::nodes::Node;
        if let Node::LocalVar(v) = node {
            let variable = Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone());
            if !ignore.contains(&variable) && !out.contains(&variable) {
                out.push(variable);
            }
            return Ok(());
        }
        if let Node::Exp(e) = node {
            match e.kind() {
                ExpKind::Let(binding, value, body) => {
                    visit(&Node::Exp(value.clone()), ignore, out)?;
                    let mut inner = ignore.to_vec();
                    inner.push(Exp::new(
                        ExpKind::LocalVar(binding.local_var()),
                        binding.meta.clone(),
                    ));
                    visit(&Node::Exp(body.clone()), &inner, out)?;
                    return Ok(());
                }
                ExpKind::Forall(bindings, _, body) | ExpKind::Exists(bindings, _, body) => {
                    let mut inner = ignore.to_vec();
                    inner.extend(
                        bindings
                            .iter()
                            .map(|v| Exp::new(ExpKind::LocalVar(v.local_var()), v.meta.clone())),
                    );
                    visit(&Node::Exp(body.clone()), &inner, out)?;
                    return Ok(());
                }
                ExpKind::ForPerm(bindings, resource, body) => {
                    let mut inner = ignore.to_vec();
                    inner.extend(
                        bindings
                            .iter()
                            .map(|v| Exp::new(ExpKind::LocalVar(v.local_var()), v.meta.clone())),
                    );
                    visit(&Node::Exp(resource.clone()), &inner, out)?;
                    visit(&Node::Exp(body.clone()), &inner, out)?;
                    return Ok(());
                }
                ExpKind::LocalVar(_) | ExpKind::Result(_) | ExpKind::LocalVarWithVersion(..) => {
                    if !ignore.contains(e) && !out.contains(e) {
                        out.push(e.clone());
                    }
                    return Ok(());
                }
                _ => {}
            }
        }
        for child in super::nodes::subnodes(node)? {
            visit(&child, ignore, out)?;
        }
        Ok(())
    }
    let mut result = Vec::new();
    visit(&super::nodes::Node::Exp(e.clone()), ignore, &mut result)?;
    Ok(result)
}

pub fn as_pure_fragment(e: &Exp) -> Option<Exp> {
    fragment(e, true)
}
pub fn as_access_fragment(e: &Exp) -> Option<Exp> {
    fragment(e, false)
}

fn fragment(e: &Exp, pure: bool) -> Option<Exp> {
    use ExpKind::*;
    let rebuild = |kind| Exp::with_extra(kind, e.metadata().clone(), e.0.extra.clone());
    match e.kind() {
        FieldAccessPredicate(..) | PredicateAccessPredicate(..) | MagicWand(..) => {
            (!pure).then(|| e.clone())
        }
        InhaleExhaleExp(a, b) => Some(rebuild(InhaleExhaleExp(
            fragment(a, pure)?,
            fragment(b, pure)?,
        ))),
        Implies(a, b) => fragment(b, pure).map(|x| rebuild(Implies(a.clone(), x))),
        And(a, b) => match (fragment(a, pure), fragment(b, pure)) {
            (Some(x), Some(y)) => Some(rebuild(And(x, y))),
            (Some(x), None) | (None, Some(x)) => Some(x),
            (None, None) => None,
        },
        CondExp(c, a, b) => match (fragment(a, pure), fragment(b, pure)) {
            (Some(x), Some(y)) => Some(rebuild(CondExp(c.clone(), x, y))),
            (Some(x), None) => Some(rebuild(Implies(c.clone(), x))),
            (None, Some(y)) => Some(rebuild(Implies(
                Exp::new(Not(c.clone()), c.metadata().clone()),
                y,
            ))),
            (None, None) => None,
        },
        Unfolding(a, b) => fragment(b, pure).map(|x| rebuild(Unfolding(a.clone(), x))),
        Applying(a, b) => fragment(b, pure).map(|x| rebuild(Applying(a.clone(), x))),
        Asserting(a, b) => fragment(b, pure).map(|x| rebuild(Asserting(a.clone(), x))),
        Let(d, a, b) => fragment(b, pure).map(|x| rebuild(Let(d.clone(), a.clone(), x))),
        Forall(ds, ts, b) => fragment(b, pure).map(|x| rebuild(Forall(ds.clone(), ts.clone(), x))),
        Exists(ds, ts, b) => fragment(b, pure).map(|x| rebuild(Exists(ds.clone(), ts.clone(), x))),
        Extension(x) => (x.0.is_pure() == pure).then(|| e.clone()),
        Add(..)
        | Sub(..)
        | Mul(..)
        | Div(..)
        | Mod(..)
        | LtCmp(..)
        | LeCmp(..)
        | GtCmp(..)
        | GeCmp(..)
        | EqCmp(..)
        | NeCmp(..)
        | IntLit(..)
        | Minus(..)
        | Or(..)
        | Not(..)
        | TrueLit
        | FalseLit
        | NullLit
        | RefLit(..)
        | BackendValueLit(..)
        | WildcardPerm
        | FullPerm
        | NoPerm
        | EpsilonPerm
        | FractionalPerm(..)
        | PermDiv(..)
        | PermPermDiv(..)
        | CurrentPerm(..)
        | PermMinus(..)
        | PermAdd(..)
        | PermSub(..)
        | PermMul(..)
        | IntPermMul(..)
        | DebugPermMin(..)
        | PermLtCmp(..)
        | PermLeCmp(..)
        | PermGtCmp(..)
        | PermGeCmp(..)
        | FuncApp(..)
        | DomainFuncApp(..)
        | BackendFuncApp(..)
        | FieldAccess(..)
        | PredicateAccess(..)
        | Old(..)
        | LabelledOld(..)
        | DebugLabelledOld(..)
        | ForPerm(..)
        | LocalVar(..)
        | Result(..)
        | LocalVarWithVersion(..)
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
        | MapRange(..) => pure.then(|| e.clone()),
    }
}

/// Failures at boundaries that upstream expresses as exceptions or plugin hooks.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MagicWandError {
    NotMagicWand,
    Traversal(super::nodes::TraversalError),
    Type(crate::ast::expression::ExpressionTypeError),
    MissingMember(crate::ast::program::MissingMember),
    UnsupportedTypePrinter,
    UnsupportedExtensionReconstruction,
    InvalidReconstructedAccess,
}
impl From<super::nodes::TraversalError> for MagicWandError {
    fn from(e: super::nodes::TraversalError) -> Self {
        Self::Traversal(e)
    }
}
impl From<crate::ast::expression::ExpressionTypeError> for MagicWandError {
    fn from(e: crate::ast::expression::ExpressionTypeError) -> Self {
        Self::Type(e)
    }
}
impl From<crate::ast::program::MissingMember> for MagicWandError {
    fn from(e: crate::ast::program::MissingMember) -> Self {
        Self::MissingMember(e)
    }
}

/// Source `Type.toString`, from FastPrettyPrinter.showType.
fn wand_type_name(t: &crate::ast::r#type::Type) -> Result<String, MagicWandError> {
    use crate::ast::r#type::Type;
    Ok(match t {
        Type::Int => "Int".into(),
        Type::Bool => "Bool".into(),
        Type::Ref => "Ref".into(),
        Type::Perm => "Perm".into(),
        Type::InternalType => "InternalType".into(),
        Type::Wand => "$WandType".into(),
        Type::Seq(t) => format!("Seq[{}]", wand_type_name(t)?),
        Type::Set(t) => format!("Set[{}]", wand_type_name(t)?),
        Type::Multiset(t) => format!("Multiset[{}]", wand_type_name(t)?),
        Type::Map(pair) => format!(
            "Map[{},{}]",
            wand_type_name(&pair.0)?,
            wand_type_name(&pair.1)?
        ),
        Type::Var(v) => v.name.clone(),
        Type::Backend(b) => b.viper_name.clone(),
        Type::Domain(d) => {
            let args = d
                .type_parameters
                .iter()
                .map(|p| {
                    wand_type_name(d.partial_type_vars.get(p).unwrap_or(&Type::Var(p.clone())))
                })
                .collect::<Result<Vec<_>, _>>()?;
            if args.is_empty() {
                d.domain_name.clone()
            } else {
                format!("{}[{}]", d.domain_name, args.join(", "))
            }
        }
        Type::Extension(e) => e
            .pretty_print()
            .map_err(|_| MagicWandError::UnsupportedTypePrinter)?,
    })
}

/// Convert the typed expression-node views produced by Nodes.subnodes back into
/// expression handles without losing their underlying identity or metadata.
fn expression_view(node: &super::nodes::Node) -> Option<Exp> {
    use super::nodes::Node;
    Some(match node {
        Node::Exp(e) => e.clone(),
        Node::LocalVar(v) => Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone()),
        Node::FieldAccess(a) => Exp::new(ExpKind::FieldAccess(a.clone()), a.meta.clone()),
        Node::PredicateAccess(a) => Exp::new(ExpKind::PredicateAccess(a.clone()), a.meta.clone()),
        Node::PredicateAccessPredicate(a) => {
            Exp::new(ExpKind::PredicateAccessPredicate(a.clone()), a.meta.clone())
        }
        _ => return None,
    })
}

fn direct_subexpressions(e: &Exp) -> Result<Vec<Exp>, MagicWandError> {
    Ok(super::nodes::subnodes(&super::nodes::Node::Exp(e.clone()))?
        .iter()
        .filter_map(expression_view)
        .collect())
}

fn top_level_heap_dependent(
    e: &Exp,
    p: &crate::ast::program::Program,
) -> Result<bool, MagicWandError> {
    Ok(match e.kind() {
        ExpKind::FieldAccessPredicate(..)
        | ExpKind::PredicateAccessPredicate(..)
        | ExpKind::MagicWand(..)
        | ExpKind::FieldAccess(..)
        | ExpKind::PredicateAccess(..) => true,
        ExpKind::FuncApp(name, _) => {
            let function = p.find_function(name)?;
            let mut result = false;
            for pre in &function.pres {
                if wand_is_heap_dependent(pre, p)? {
                    result = true;
                    break;
                }
            }
            result
        }
        _ => false,
    })
}
fn wand_is_heap_dependent(
    e: &Exp,
    p: &crate::ast::program::Program,
) -> Result<bool, MagicWandError> {
    fn go(
        node: &super::nodes::Node,
        p: &crate::ast::program::Program,
    ) -> Result<bool, MagicWandError> {
        if let Some(e) = expression_view(node) {
            if top_level_heap_dependent(&e, p)? {
                return Ok(true);
            }
        }
        for child in super::nodes::subnodes(node)? {
            if go(&child, p)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    go(&super::nodes::Node::Exp(e.clone()), p)
}
fn wand_depends_on_current_heap(
    e: &Exp,
    p: &crate::ast::program::Program,
    current: bool,
) -> Result<bool, MagicWandError> {
    match e.kind() {
        ExpKind::LabelledOld(child, label) if label == "lhs" => {
            return wand_depends_on_current_heap(child, p, true);
        }
        ExpKind::Old(child)
        | ExpKind::LabelledOld(child, _)
        | ExpKind::DebugLabelledOld(child, _) => {
            return wand_depends_on_current_heap(child, p, false);
        }
        _ => {}
    }
    if current && top_level_heap_dependent(e, p)? {
        return Ok(true);
    }
    for child in direct_subexpressions(e)? {
        if wand_depends_on_current_heap(&child, p, current)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Ordered fixed-state holes selected by MagicWand.subexpressionsToEvaluate.
pub fn magic_wand_subexpressions(
    e: &Exp,
    p: &crate::ast::program::Program,
) -> Result<Vec<Exp>, MagicWandError> {
    if !matches!(e.kind(), ExpKind::MagicWand(..)) {
        return Err(MagicWandError::NotMagicWand);
    }
    fn contains_bound(
        root: &Exp,
        bound: &[crate::ast::expression::LocalVar],
    ) -> Result<bool, MagicWandError> {
        for v in bound {
            let target = super::nodes::Node::LocalVar(v.clone());
            if super::visitor::exists_defined(
                &super::nodes::Node::Exp(root.clone()),
                &super::nodes::subnodes,
                &mut |n| n == &target,
            )? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    fn go(
        node: &super::nodes::Node,
        p: &crate::ast::program::Program,
        bound: &[crate::ast::expression::LocalVar],
        out: &mut Vec<Exp>,
    ) -> Result<(), MagicWandError> {
        if let Some(e) = expression_view(node) {
            match e.kind() {
                ExpKind::Let(v, value, body) => {
                    go(&super::nodes::Node::Exp(value.clone()), p, bound, out)?;
                    let mut next = bound.to_vec();
                    let local = v.local_var();
                    if !next.contains(&local) {
                        next.push(local);
                    }
                    go(&super::nodes::Node::Exp(body.clone()), p, &next, out)?;
                    return Ok(());
                }
                ExpKind::Forall(vars, _, body) | ExpKind::Exists(vars, _, body) => {
                    let mut next = bound.to_vec();
                    for v in vars {
                        let local = v.local_var();
                        if !next.contains(&local) {
                            next.push(local);
                        }
                    }
                    go(&super::nodes::Node::Exp(body.clone()), p, &next, out)?;
                    return Ok(());
                }
                ExpKind::ForPerm(vars, resource, body) => {
                    let mut next = bound.to_vec();
                    for v in vars {
                        let local = v.local_var();
                        if !next.contains(&local) {
                            next.push(local);
                        }
                    }
                    go(&super::nodes::Node::Exp(resource.clone()), p, &next, out)?;
                    go(&super::nodes::Node::Exp(body.clone()), p, &next, out)?;
                    return Ok(());
                }
                _ => {}
            }
            if !wand_depends_on_current_heap(&e, p, true)? && !contains_bound(&e, bound)? {
                out.push(e);
                return Ok(());
            }
        }
        for child in super::nodes::subnodes(node)? {
            go(&child, p, bound, out)?;
        }
        Ok(())
    }
    let mut result = Vec::new();
    go(&super::nodes::Node::Exp(e.clone()), p, &[], &mut result)?;
    Ok(result)
}

/// Canonical source MagicWand structure. Holes are determined before the
/// top-down substitution; binder contexts follow the source rewriter.
pub fn magic_wand_structure(
    e: &Exp,
    p: &crate::ast::program::Program,
    unique_names: bool,
) -> Result<Exp, MagicWandError> {
    use crate::ast::expression::{ExtensionExpHandle, LocalVar};
    use crate::ast::program::LocalVarDecl;
    use std::cell::Cell;
    use std::collections::HashMap;
    let holes = magic_wand_subexpressions(e, p)?;
    let unique = Cell::new(-1_i32);
    fn extend(bindings: &HashMap<String, usize>, vars: &[LocalVarDecl]) -> HashMap<String, usize> {
        let mut next = bindings.clone();
        let mut count = bindings.len();
        for v in vars {
            count += 1;
            next.insert(v.name.clone(), count);
        }
        next
    }
    fn rename(
        vars: &[LocalVarDecl],
        bindings: &HashMap<String, usize>,
    ) -> Result<Vec<LocalVarDecl>, MagicWandError> {
        vars.iter()
            .map(|v| {
                Ok(LocalVarDecl::new(
                    format!("{}_{}", wand_type_name(&v.typ)?, bindings[&v.name]),
                    v.typ.clone(),
                    v.meta.clone(),
                ))
            })
            .collect()
    }
    fn transform(
        e: &Exp,
        holes: &[Exp],
        bindings: &HashMap<String, usize>,
        unique: &Cell<i32>,
        unique_names: bool,
    ) -> Result<Exp, MagicWandError> {
        if holes.contains(e) {
            let typ = e.typ()?;
            let mut name = wand_type_name(&typ)?;
            if unique_names {
                let i = unique.get() + 1;
                unique.set(i);
                name.push_str(&i.to_string());
            }
            return Ok(Exp::new(
                ExpKind::LocalVar(LocalVar::new(name, typ, Default::default())),
                Default::default(),
            ));
        }
        let mut context = bindings.clone();
        let rewritten = match e.kind() {
            ExpKind::Forall(vars, triggers, body) => {
                context = extend(bindings, vars);
                Exp::with_extra(
                    ExpKind::Forall(rename(vars, &context)?, triggers.clone(), body.clone()),
                    e.metadata().clone(),
                    e.0.extra.clone(),
                )
            }
            ExpKind::Exists(vars, triggers, body) => {
                context = extend(bindings, vars);
                Exp::with_extra(
                    ExpKind::Exists(rename(vars, &context)?, triggers.clone(), body.clone()),
                    e.metadata().clone(),
                    e.0.extra.clone(),
                )
            }
            ExpKind::ForPerm(vars, resource, body) => {
                context = extend(bindings, vars);
                Exp::with_extra(
                    ExpKind::ForPerm(rename(vars, &context)?, resource.clone(), body.clone()),
                    e.metadata().clone(),
                    e.0.extra.clone(),
                )
            }
            ExpKind::Let(var, value, body) => {
                context = extend(bindings, std::slice::from_ref(var));
                let new_var = rename(std::slice::from_ref(var), &context)?.remove(0);
                Exp::with_extra(
                    ExpKind::Let(new_var, value.clone(), body.clone()),
                    e.metadata().clone(),
                    e.0.extra.clone(),
                )
            }
            ExpKind::LocalVar(v) => match bindings.get(&v.name) {
                Some(index) => Exp::new(
                    ExpKind::LocalVar(LocalVar::new(
                        format!("{}_{}", wand_type_name(&v.typ)?, index),
                        v.typ.clone(),
                        v.meta.clone(),
                    )),
                    e.metadata().clone(),
                ),
                None => e.clone(),
            },
            _ => e.clone(),
        };
        let mut exp_map = |child: &Exp| transform(child, holes, &context, unique, unique_names);
        let mut extension =
            |_: &ExtensionExpHandle| Err(MagicWandError::UnsupportedExtensionReconstruction);
        let mut field = |child: &FieldAccess| {
            let exp = Exp::new(ExpKind::FieldAccess(child.clone()), child.meta.clone());
            match transform(&exp, holes, &context, unique, unique_names)?.kind() {
                ExpKind::FieldAccess(result) => Ok(result.clone()),
                _ => Err(MagicWandError::InvalidReconstructedAccess),
            }
        };
        let mut predicate = |child: &PredicateAccess| {
            let exp = Exp::new(ExpKind::PredicateAccess(child.clone()), child.meta.clone());
            match transform(&exp, holes, &context, unique, unique_names)?.kind() {
                ExpKind::PredicateAccess(result) => Ok(result.clone()),
                _ => Err(MagicWandError::InvalidReconstructedAccess),
            }
        };
        let mut trigger = |child: &Trigger| {
            let exps = child
                .exps
                .iter()
                .map(|x| transform(x, holes, &context, unique, unique_names))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(if exps == child.exps {
                child.clone()
            } else {
                Trigger::new(exps, child.meta.clone())
            })
        };
        rewritten.map_expression_children(
            &mut exp_map,
            &mut extension,
            &mut field,
            &mut predicate,
            &mut trigger,
        )
    }
    transform(e, &holes, &HashMap::new(), &unique, unique_names)
}

/// Failure of source well-definedness analysis, including unresolved function references.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WellDefinednessError {
    Traversal(super::nodes::TraversalError),
    MissingFunction(String),
}
/// Source `Expressions.isKnownWellDefined`. Only direct expression children are
/// followed; trigger and declaration nodes are not implicitly traversed.
pub fn is_known_well_defined(
    e: &Exp,
    program: Option<&crate::ast::program::Program>,
) -> Result<bool, WellDefinednessError> {
    use super::nodes::{Node, subnodes};
    use crate::ast::expression::ExpKind;
    match e.kind() {
        ExpKind::FieldAccessPredicate(loc, permission) => {
            if !is_known_well_defined(&loc.receiver, program)? {
                return Ok(false);
            }
            return match permission {
                Some(p) => is_known_well_defined(p, program),
                None => Ok(true),
            };
        }
        ExpKind::FieldAccess(_)
        | ExpKind::Unfolding(..)
        | ExpKind::Applying(..)
        | ExpKind::Asserting(..)
        | ExpKind::SeqIndex(..)
        | ExpKind::MapLookup(..)
        | ExpKind::Div(..)
        | ExpKind::Mod(..) => return Ok(false),
        ExpKind::FuncApp(name, args) => {
            let Some(program) = program else {
                return Ok(false);
            };
            let function = program
                .find_function_optionally(name)
                .ok_or_else(|| WellDefinednessError::MissingFunction(name.clone()))?;
            if !function.pres.is_empty() {
                return Ok(false);
            }
            for arg in args {
                if !is_known_well_defined(arg, Some(program))? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        _ => {}
    }
    for node in subnodes(&Node::Exp(e.clone())).map_err(WellDefinednessError::Traversal)? {
        let exp = match node {
            Node::Exp(e) => Some(e),
            Node::LocalVar(v) => Some(Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone())),
            Node::FieldAccess(v) => Some(Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone())),
            Node::PredicateAccess(v) => Some(Exp::new(
                ExpKind::PredicateAccess(v.clone()),
                v.meta.clone(),
            )),
            Node::PredicateAccessPredicate(v) => Some(Exp::new(
                ExpKind::PredicateAccessPredicate(v.clone()),
                v.meta.clone(),
            )),
            _ => None,
        };
        if let Some(exp) = exp {
            if !is_known_well_defined(&exp, program)? {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HeapDependencyError {
    Traversal(super::nodes::TraversalError),
    MissingFunction(crate::ast::program::MissingMember),
    RecursiveFunctionPreconditions(String),
}
impl From<super::nodes::TraversalError> for HeapDependencyError {
    fn from(value: super::nodes::TraversalError) -> Self {
        Self::Traversal(value)
    }
}
/// Direct expression children in source `Expressions.subExps` order.
pub fn sub_expressions(e: &Exp) -> Result<Vec<Exp>, super::nodes::TraversalError> {
    Ok(super::nodes::subnodes(&Node::Exp(e.clone()))?
        .into_iter()
        .filter_map(|n| match n {
            Node::Exp(e) => Some(e),
            Node::LocalVar(v) => Some(Exp::new(ExpKind::LocalVar(v.clone()), v.meta.clone())),
            Node::FieldAccess(v) => Some(Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone())),
            Node::PredicateAccess(v) => Some(Exp::new(
                ExpKind::PredicateAccess(v.clone()),
                v.meta.clone(),
            )),
            Node::PredicateAccessPredicate(v) => Some(Exp::new(
                ExpKind::PredicateAccessPredicate(v.clone()),
                v.meta.clone(),
            )),
            _ => None,
        })
        .collect())
}
fn top_heap(
    e: &Exp,
    p: &crate::ast::program::Program,
    active: &mut Vec<String>,
) -> Result<bool, HeapDependencyError> {
    Ok(match e.kind() {
        ExpKind::FieldAccessPredicate(..)
        | ExpKind::PredicateAccessPredicate(..)
        | ExpKind::FieldAccess(..)
        | ExpKind::PredicateAccess(..)
        | ExpKind::MagicWand(..) => true,
        ExpKind::FuncApp(name, _) => {
            let f = p
                .find_function(name)
                .map_err(HeapDependencyError::MissingFunction)?;
            if active.contains(name) {
                return Err(HeapDependencyError::RecursiveFunctionPreconditions(
                    name.clone(),
                ));
            }
            active.push(name.clone());
            let mut found = false;
            for pre in &f.pres {
                if heap(pre, p, active)? {
                    found = true;
                    break;
                }
            }
            active.pop();
            found
        }
        _ => false,
    })
}
fn heap(
    e: &Exp,
    p: &crate::ast::program::Program,
    active: &mut Vec<String>,
) -> Result<bool, HeapDependencyError> {
    fn walk(
        n: &Node,
        p: &crate::ast::program::Program,
        active: &mut Vec<String>,
    ) -> Result<bool, HeapDependencyError> {
        let e = match n {
            Node::Exp(e) => Some(e.clone()),
            Node::FieldAccess(v) => Some(Exp::new(ExpKind::FieldAccess(v.clone()), v.meta.clone())),
            Node::PredicateAccess(v) => Some(Exp::new(
                ExpKind::PredicateAccess(v.clone()),
                v.meta.clone(),
            )),
            Node::PredicateAccessPredicate(v) => Some(Exp::new(
                ExpKind::PredicateAccessPredicate(v.clone()),
                v.meta.clone(),
            )),
            _ => None,
        };
        if let Some(e) = e {
            if top_heap(&e, p, active)? {
                return Ok(true);
            }
        }
        for child in super::nodes::subnodes(n)? {
            if walk(&child, p, active)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    walk(&Node::Exp(e.clone()), p, active)
}
pub fn is_top_level_heap_dependent(
    e: &Exp,
    p: &crate::ast::program::Program,
) -> Result<bool, HeapDependencyError> {
    top_heap(e, p, &mut Vec::new())
}
pub fn is_heap_dependent(
    e: &Exp,
    p: &crate::ast::program::Program,
) -> Result<bool, HeapDependencyError> {
    heap(e, p, &mut Vec::new())
}
/// Old states are ignored unless magic-wand lhs states are treated as current.
pub fn depends_on_current_heap(
    e: &Exp,
    p: &crate::ast::program::Program,
    treat_wand_states_as_current: bool,
) -> Result<bool, HeapDependencyError> {
    fn walk(
        e: &Exp,
        p: &crate::ast::program::Program,
        current: bool,
        wand_current: bool,
        active: &mut Vec<String>,
    ) -> Result<bool, HeapDependencyError> {
        match e.kind() {
            ExpKind::LabelledOld(inner, label) if label == "lhs" => {
                return if wand_current {
                    walk(inner, p, true, wand_current, active)
                } else {
                    Ok(false)
                };
            }
            ExpKind::Old(inner)
            | ExpKind::LabelledOld(inner, _)
            | ExpKind::DebugLabelledOld(inner, _) => {
                return if wand_current {
                    walk(inner, p, false, wand_current, active)
                } else {
                    Ok(false)
                };
            }
            _ => {}
        }
        if current && top_heap(e, p, active)? {
            return Ok(true);
        }
        for child in sub_expressions(e)? {
            if walk(&child, p, current, wand_current, active)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    walk(e, p, true, treat_wand_states_as_current, &mut Vec::new())
}
pub fn could_be_heap_dependent(
    f: &crate::ast::program::Function,
    p: &crate::ast::program::Program,
) -> Result<bool, HeapDependencyError> {
    for pre in &f.pres {
        if is_heap_dependent(pre, p)? {
            return Ok(true);
        }
    }
    Ok(false)
}
pub fn contains_permission_introspection(e: &Exp) -> Result<bool, super::nodes::TraversalError> {
    fn walk(n: &Node) -> Result<bool, super::nodes::TraversalError> {
        if matches!(n, Node::Exp(e) if matches!(e.kind(), ExpKind::CurrentPerm(..) | ExpKind::ForPerm(..)))
        {
            return Ok(true);
        }
        for child in super::nodes::subnodes(n)? {
            if walk(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    walk(&Node::Exp(e.clone()))
}

#[cfg(test)]
mod heap_dependency_tests {
    use super::*;
    use crate::ast::{
        ast::Metadata,
        expression::LocalVar,
        program::{Field, FieldData, Program},
        r#type::Type,
    };
    #[test]
    fn unused_let_value_does_not_add_variables() {
        let m = Metadata::default();
        let decl = crate::ast::program::LocalVarDecl::new("x".into(), Type::Int, m.clone());
        let y = Exp::new(
            ExpKind::LocalVar(LocalVar::new("y".into(), Type::Int, m.clone())),
            m.clone(),
        );
        let body = Exp::new(ExpKind::IntLit(1.into()), m.clone());
        let root = Exp::new(ExpKind::Let(decl, y, body), m);
        assert!(
            contained_variables_excluding_let(&Node::Exp(root))
                .unwrap()
                .is_empty()
        );
    }
    #[test]
    fn wand_lhs_can_reenter_current_state_beneath_old() {
        let m = Metadata::default();
        let p = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], m.clone());
        let receiver = Exp::new(
            ExpKind::LocalVar(LocalVar::new("r".into(), Type::Ref, m.clone())),
            m.clone(),
        );
        let access = FieldAccess::new(
            receiver,
            Field::new(FieldData {
                name: "f".into(),
                typ: Type::Int,
                meta: m.clone(),
            }),
            m.clone(),
        );
        let field = Exp::new(ExpKind::FieldAccess(access), m.clone());
        let lhs = Exp::new(ExpKind::LabelledOld(field, "lhs".into()), m.clone());
        let old = Exp::new(ExpKind::Old(lhs), m);
        assert!(!depends_on_current_heap(&old, &p, false).unwrap());
        assert!(depends_on_current_heap(&old, &p, true).unwrap());
    }
}

/// Variables actually used after accounting for unused and shadowed let bindings.
pub fn contained_variables_excluding_let(
    root: &Node,
) -> Result<Vec<crate::ast::expression::LocalVar>, super::nodes::TraversalError> {
    use crate::ast::expression::LocalVar;
    fn append_distinct(out: &mut Vec<LocalVar>, values: impl IntoIterator<Item = LocalVar>) {
        for value in values {
            if !out.contains(&value) {
                out.push(value);
            }
        }
    }
    fn visit(n: &Node) -> Result<Vec<LocalVar>, super::nodes::TraversalError> {
        let mut out = Vec::new();
        if let Node::Exp(e) = n {
            if let ExpKind::Let(var, value, body) = e.kind() {
                let bound = var.local_var();
                let mut used = visit(&Node::Exp(body.clone()))?;
                let bound_used = used.contains(&bound);
                used.retain(|v| v != &bound);
                if bound_used {
                    append_distinct(&mut used, visit(&Node::Exp(value.clone()))?);
                }
                return Ok(used);
            }
            if let ExpKind::LocalVar(var) = e.kind() {
                out.push(var.clone());
            }
        } else if let Node::LocalVar(var) = n {
            out.push(var.clone());
        }
        for child in super::nodes::subnodes(n)? {
            append_distinct(&mut out, visit(&child)?);
        }
        Ok(out)
    }
    visit(root)
}

/// Remove resource assertions from boolean guards using the source innermost rules.
pub fn as_boolean_exp(
    e: &Exp,
) -> Result<Exp, super::rewriter::strategy::ExpressionReplacementError> {
    use super::rewriter::strategy::ExpressionReplacementError as Error;
    let m = e.metadata().clone();
    match e.kind() {
        ExpKind::FieldAccessPredicate(..)
        | ExpKind::PredicateAccessPredicate(..)
        | ExpKind::MagicWand(..) => return Ok(Exp::new(ExpKind::TrueLit, Default::default())),
        ExpKind::Forall(vars, triggers, body) => {
            return Ok(Exp::new(
                ExpKind::Forall(vars.clone(), triggers.clone(), as_boolean_exp(body)?),
                m,
            ));
        }
        ExpKind::Unfolding(_, body) | ExpKind::Applying(_, body) => return as_boolean_exp(body),
        ExpKind::Asserting(assertion, body) => {
            return Ok(Exp::new(
                ExpKind::Asserting(as_boolean_exp(assertion)?, as_boolean_exp(body)?),
                m,
            ));
        }
        _ => {}
    }
    e.map_expression_children(
        &mut as_boolean_exp,
        &mut |_| Err(Error::Extension),
        &mut |field| {
            let receiver = as_boolean_exp(&field.receiver)?;
            Ok(if receiver == field.receiver {
                field.clone()
            } else {
                FieldAccess::new(receiver, field.field.clone(), field.meta.clone())
            })
        },
        &mut |predicate| {
            let args = predicate
                .args
                .iter()
                .map(as_boolean_exp)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(if args == predicate.args {
                predicate.clone()
            } else {
                PredicateAccess::new(
                    args,
                    predicate.predicate_name.clone(),
                    predicate.meta.clone(),
                )
            })
        },
        &mut |trigger| {
            let exps = trigger
                .exps
                .iter()
                .map(as_boolean_exp)
                .collect::<Result<Vec<_>, _>>()?;
            Ok(if exps == trigger.exps {
                trigger.clone()
            } else {
                Trigger::new(exps, trigger.meta.clone())
            })
        },
    )
}
fn positioned(position: &crate::ast::position::Position) -> crate::ast::ast::Metadata {
    crate::ast::ast::Metadata {
        position: position.clone(),
        ..Default::default()
    }
}
fn conjunction_at(exps: &[Exp], position: &crate::ast::position::Position) -> Option<Exp> {
    let (first, tail) = exps.split_first()?;
    Some(tail.iter().fold(first.clone(), |a, b| {
        Exp::new(ExpKind::And(a, b.clone()), positioned(position))
    }))
}
pub fn reduce_cond_exp_proof_obligations(
    cond: &Exp,
    cond_conditions: &[Exp],
    then_conditions: &[Exp],
    else_conditions: &[Exp],
    position: &crate::ast::position::Position,
) -> Vec<Exp> {
    let mut result = cond_conditions.to_vec();
    if !then_conditions.is_empty() || !else_conditions.is_empty() {
        let yes = || Exp::new(ExpKind::TrueLit, positioned(position));
        let then = conjunction_at(then_conditions, position).unwrap_or_else(yes);
        let otherwise = conjunction_at(else_conditions, position).unwrap_or_else(yes);
        result.push(Exp::new(
            ExpKind::CondExp(cond.clone(), then, otherwise),
            positioned(position),
        ));
    }
    result
}
pub fn reduce_lazy_binary_proof_obligations(
    guard: &Exp,
    left_conditions: &[Exp],
    right_conditions: &[Exp],
    position: &crate::ast::position::Position,
) -> Vec<Exp> {
    let mut result = left_conditions.to_vec();
    if let Some(right) = conjunction_at(right_conditions, position) {
        result.push(Exp::new(
            ExpKind::Implies(guard.clone(), right),
            positioned(position),
        ));
    }
    result
}
pub fn reduce_implies_proof_obligations(
    left: &Exp,
    left_conditions: &[Exp],
    right_conditions: &[Exp],
    position: &crate::ast::position::Position,
) -> Vec<Exp> {
    reduce_lazy_binary_proof_obligations(left, left_conditions, right_conditions, position)
}
pub fn reduce_and_proof_obligations(
    left: &Exp,
    left_conditions: &[Exp],
    right_conditions: &[Exp],
    position: &crate::ast::position::Position,
) -> Result<Vec<Exp>, super::rewriter::strategy::ExpressionReplacementError> {
    Ok(reduce_lazy_binary_proof_obligations(
        &as_boolean_exp(left)?,
        left_conditions,
        right_conditions,
        position,
    ))
}
pub fn reduce_or_proof_obligations(
    left: &Exp,
    left_conditions: &[Exp],
    right_conditions: &[Exp],
    position: &crate::ast::position::Position,
) -> Vec<Exp> {
    reduce_lazy_binary_proof_obligations(
        &Exp::new(ExpKind::Not(left.clone()), positioned(position)),
        left_conditions,
        right_conditions,
        position,
    )
}

#[cfg(test)]
mod proof_obligation_reduction_tests {
    use super::*;
    use crate::ast::{ast::Metadata, position::Position};
    #[test]
    fn lazy_and_guard_removes_resource_before_guarding_right_obligation() {
        let m = Metadata::default();
        let yes = Exp::new(ExpKind::TrueLit, m.clone());
        let wand = Exp::new(ExpKind::MagicWand(yes.clone(), yes.clone()), m);
        let result =
            reduce_and_proof_obligations(&wand, &[], &[yes], &Position::Virtual("p".into()))
                .unwrap();
        assert!(
            matches!(result[0].kind(), ExpKind::Implies(guard, _) if matches!(guard.kind(), ExpKind::TrueLit))
        );
        assert_eq!(result[0].metadata().position, Position::Virtual("p".into()));
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofObligationError {
    Traversal(super::nodes::TraversalError),
    MissingFunction(crate::ast::program::MissingMember),
    BooleanProjection(super::rewriter::strategy::ExpressionReplacementError),
    Position(crate::verifier::verification_result::DiagnosticError),
    UnexpectedChildren,
}
impl From<super::nodes::TraversalError> for ProofObligationError {
    fn from(value: super::nodes::TraversalError) -> Self {
        Self::Traversal(value)
    }
}
/// Compute source proof obligations in postorder, guarding lazy child obligations.
pub fn proof_obligations(
    e: &Exp,
    program: &crate::ast::program::Program,
) -> Result<Vec<Exp>, ProofObligationError> {
    use crate::ast::position::Position;
    fn visit(n: &Node, p: &crate::ast::program::Program) -> Result<Vec<Exp>, ProofObligationError> {
        let mut child_conditions = Vec::new();
        for child in super::nodes::subnodes(n)? {
            child_conditions.push(visit(&child, p)?);
        }
        let position = if matches!(n, Node::Type(_)) {
            Position::NoPosition
        } else {
            crate::verifier::verification_error::node_position(n)
                .map_err(ProofObligationError::Position)?
        };
        let meta = || positioned(&position);
        let node_exp = expression_view(n);
        let mut own = Vec::new();
        if let Some(e) = &node_exp {
            match e.kind() {
                ExpKind::FieldAccess(field) => {
                    let null = Exp::new(ExpKind::NullLit, meta());
                    own.push(Exp::new(
                        ExpKind::NeCmp(field.receiver.clone(), null),
                        meta(),
                    ));
                    let wildcard = Exp::new(ExpKind::WildcardPerm, meta());
                    own.push(Exp::new(
                        ExpKind::FieldAccessPredicate(field.clone(), Some(wildcard)),
                        meta(),
                    ));
                }
                ExpKind::FuncApp(name, _) => own.extend(
                    p.find_function(name)
                        .map_err(ProofObligationError::MissingFunction)?
                        .pres
                        .clone(),
                ),
                ExpKind::Div(_, divisor) | ExpKind::Mod(_, divisor) => own.push(Exp::new(
                    ExpKind::NeCmp(divisor.clone(), Exp::new(ExpKind::IntLit(0.into()), meta())),
                    meta(),
                )),
                ExpKind::SeqIndex(sequence, index) => {
                    own.push(Exp::new(
                        ExpKind::GeCmp(index.clone(), Exp::new(ExpKind::IntLit(0.into()), meta())),
                        meta(),
                    ));
                    own.push(Exp::new(
                        ExpKind::LtCmp(
                            index.clone(),
                            Exp::new(ExpKind::SeqLength(sequence.clone()), meta()),
                        ),
                        meta(),
                    ));
                }
                ExpKind::MapLookup(map, key) => own.push(Exp::new(
                    ExpKind::MapContains(key.clone(), map.clone()),
                    meta(),
                )),
                ExpKind::Unfolding(pred, _)
                | ExpKind::Applying(pred, _)
                | ExpKind::Asserting(pred, _) => own.push(pred.clone()),
                _ => {}
            }
        }
        let mut nontrivial = child_conditions.clone();
        for conditions in &mut nontrivial {
            conditions.retain(|e| !matches!(e.kind(), ExpKind::TrueLit));
        }
        let final_children = match node_exp.as_ref().map(|e| e.kind()) {
            Some(ExpKind::And(left, _)) => {
                if nontrivial.len() != 3 || !nontrivial[2].is_empty() {
                    return Err(ProofObligationError::UnexpectedChildren);
                }
                reduce_and_proof_obligations(left, &nontrivial[0], &nontrivial[1], &position)
                    .map_err(ProofObligationError::BooleanProjection)?
            }
            Some(ExpKind::Implies(left, _)) => {
                if nontrivial.len() != 3 || !nontrivial[2].is_empty() {
                    return Err(ProofObligationError::UnexpectedChildren);
                }
                reduce_implies_proof_obligations(left, &nontrivial[0], &nontrivial[1], &position)
            }
            Some(ExpKind::Or(left, _)) => {
                if nontrivial.len() != 3 || !nontrivial[2].is_empty() {
                    return Err(ProofObligationError::UnexpectedChildren);
                }
                reduce_or_proof_obligations(left, &nontrivial[0], &nontrivial[1], &position)
            }
            Some(ExpKind::CondExp(cond, _, _)) => {
                if nontrivial.len() != 4 || !nontrivial[3].is_empty() {
                    return Err(ProofObligationError::UnexpectedChildren);
                }
                reduce_cond_exp_proof_obligations(
                    cond,
                    &nontrivial[0],
                    &nontrivial[1],
                    &nontrivial[2],
                    &position,
                )
            }
            _ => child_conditions.into_iter().flatten().collect(),
        };
        let mut result = final_children;
        result.extend(own);
        Ok(result)
    }
    visit(&Node::Exp(e.clone()), program)
}

#[cfg(test)]
mod proof_obligations_tests {
    use super::*;
    use crate::ast::{ast::Metadata, program::Program};
    #[test]
    fn guards_division_obligations_in_lazy_conjunction() {
        let m = Metadata::default();
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], m.clone());
        let one = Exp::new(ExpKind::IntLit(1.into()), m.clone());
        let divisor = Exp::new(ExpKind::IntLit(2.into()), m.clone());
        let division = Exp::new(ExpKind::Div(one.clone(), divisor), m.clone());
        let comparison = Exp::new(ExpKind::EqCmp(division, one), m.clone());
        let guard = Exp::new(ExpKind::FalseLit, m.clone());
        let expr = Exp::new(ExpKind::And(guard.clone(), comparison), m);
        let conditions = proof_obligations(&expr, &program).unwrap();
        assert_eq!(conditions.len(), 1);
        assert!(
            matches!(conditions[0].kind(), ExpKind::Implies(left, right) if left == &guard && matches!(right.kind(), ExpKind::NeCmp(..)))
        );
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstantiateError {
    ArityMismatch,
    NotAbstractLocalVariable,
    Sanitizer(crate::utility::sanitizer::SanitizeError),
}
/// Instantiate declared locals, preserving source capture avoidance and supplied scope.
pub fn instantiate_variables(
    expression: &Exp,
    variables: &[crate::ast::program::LocalVarDecl],
    values: &[Exp],
    scope: &std::collections::HashSet<String>,
) -> Result<Exp, InstantiateError> {
    if variables.len() != values.len() {
        return Err(InstantiateError::ArityMismatch);
    }
    let replacements = variables
        .iter()
        .zip(values)
        .map(|(v, e)| (v.name.clone(), e.clone()))
        .collect();
    crate::utility::sanitizer::replace_free_variables_in_expression(
        expression,
        replacements,
        scope.clone(),
    )
    .map_err(InstantiateError::Sanitizer)
}
/// Source overload accepting AbstractLocalVar expression nodes and an empty scope.
pub fn instantiate_abstract_variables(
    expression: &Exp,
    variables: &[Exp],
    values: &[Exp],
) -> Result<Exp, InstantiateError> {
    if variables.len() != values.len() {
        return Err(InstantiateError::ArityMismatch);
    }
    let mut replacements = std::collections::HashMap::new();
    for (var, value) in variables.iter().zip(values) {
        let name = match var.kind() {
            ExpKind::LocalVar(v) => v.name.clone(),
            ExpKind::LocalVarWithVersion(name, _) => name.clone(),
            ExpKind::Result(_) => "result".into(),
            _ => return Err(InstantiateError::NotAbstractLocalVariable),
        };
        replacements.insert(name, value.clone());
    }
    crate::utility::sanitizer::replace_free_variables_in_expression(
        expression,
        replacements,
        Default::default(),
    )
    .map_err(InstantiateError::Sanitizer)
}
