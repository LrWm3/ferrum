//! Expression projections and queries.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/Expressions.scala
//! Status: partial. Purity, conjuncts, fragments, free variables and built-in
//! inhale/exhale projection are implemented; other queries remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

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
                if is_heap_dependent(pre, p)? {
                    result = true;
                    break;
                }
            }
            result
        }
        _ => false,
    })
}
fn is_heap_dependent(e: &Exp, p: &crate::ast::program::Program) -> Result<bool, MagicWandError> {
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
fn depends_on_current_heap(
    e: &Exp,
    p: &crate::ast::program::Program,
    current: bool,
) -> Result<bool, MagicWandError> {
    match e.kind() {
        ExpKind::LabelledOld(child, label) if label == "lhs" => {
            return depends_on_current_heap(child, p, true);
        }
        ExpKind::Old(child)
        | ExpKind::LabelledOld(child, _)
        | ExpKind::DebugLabelledOld(child, _) => return depends_on_current_heap(child, p, false),
        _ => {}
    }
    if current && top_level_heap_dependent(e, p)? {
        return Ok(true);
    }
    for child in direct_subexpressions(e)? {
        if depends_on_current_heap(&child, p, current)? {
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
            if !depends_on_current_heap(&e, p, true)? && !contains_bound(&e, bound)? {
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
