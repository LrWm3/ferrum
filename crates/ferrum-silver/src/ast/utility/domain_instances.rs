//! Domain type instance analysis.
//! Upstream: https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/ast/utility/DomainInstances.scala
//! Status: partial; ground collection, thresholded coordinate closure, axiom-call
//! unification, type substitution and instance-member filtering are implemented.
//! Extension types and unsupported reconstruction paths return explicit errors.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use crate::ast::{
    expression::ExpKind,
    program::{Domain, Program},
    r#type::{DomainType, Type, TypeVar},
    utility::nodes::{Node, TraversalError, subnodes},
};
use std::collections::{HashMap, HashSet};
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DomainInstanceError {
    Traversal(TraversalError),
    MissingDomainName,
    MissingDomain(String),
    MissingExpressionType,
    ExtensionType,
    MissingTypeArgument(String),
    NonGroundCoordinate(Type),
    MissingInflation(TypeVar),
    Reconstruction(crate::verifier::verification_result::DiagnosticError),
}
impl From<TraversalError> for DomainInstanceError {
    fn from(e: TraversalError) -> Self {
        Self::Traversal(e)
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GroundTypeInstance {
    TypeInstance {
        domain: Domain,
        arguments: Vec<GroundTypeInstance>,
    },
    AtomicTypeInstance(Type),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DomainParameter {
    pub domain: Domain,
    pub variable: TypeVar,
}
impl DomainParameter {
    pub fn new(domain: Domain, variable: TypeVar) -> Self {
        assert!(domain.type_vars.contains(&variable));
        Self { domain, variable }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DomainParameterDependency {
    pub domain_parameter: DomainParameter,
    pub depth: i32,
}
pub fn get_ftv_depths(t: &Type) -> Result<HashMap<TypeVar, i32>, DomainInstanceError> {
    let mut result = HashMap::new();
    match t {
        Type::Var(v) => {
            result.insert(v.clone(), 0);
        }
        Type::Domain(d) => {
            for child in d.type_vars_map().into_values() {
                for (var, depth) in get_ftv_depths(&child)? {
                    result.insert(var, depth.wrapping_add(1));
                }
            }
        }
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => {
            for (var, depth) in get_ftv_depths(t)? {
                result.insert(var, depth.wrapping_add(1));
            }
        }
        Type::Map(pair) => {
            for child in [&pair.0, &pair.1] {
                for (var, depth) in get_ftv_depths(child)? {
                    let depth = depth.wrapping_add(1);
                    result
                        .entry(var)
                        .and_modify(|old: &mut i32| *old = (*old).max(depth))
                        .or_insert(depth);
                }
            }
        }
        Type::Extension(_) => return Err(DomainInstanceError::ExtensionType),
        _ => {}
    }
    Ok(result)
}
pub fn down1_types(t: &Type) -> Result<HashSet<Type>, DomainInstanceError> {
    Ok(match t {
        Type::Domain(d) => d.type_vars_map().into_values().collect(),
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => {
            [t.as_ref().clone()].into_iter().collect()
        }
        Type::Map(pair) => [pair.0.clone(), pair.1.clone()].into_iter().collect(),
        Type::Extension(_) => return Err(DomainInstanceError::ExtensionType),
        _ => HashSet::new(),
    })
}
pub fn down_closure(t: &Type) -> Result<HashSet<Type>, DomainInstanceError> {
    let mut result = HashSet::from([t.clone()]);
    for child in down1_types(t)? {
        result.extend(down_closure(&child)?);
    }
    Ok(result)
}
/// Source filters only the root; descendants use downClosure even when non-ground.
pub fn down_closure_ground(t: &Type) -> Result<HashSet<Type>, DomainInstanceError> {
    let mut result = HashSet::new();
    if t.is_concrete() {
        result.insert(t.clone());
    }
    for child in down1_types(t)? {
        result.extend(down_closure(&child)?);
    }
    Ok(result)
}
pub fn get_tvs(t: &Type) -> Result<HashSet<TypeVar>, DomainInstanceError> {
    Ok(match t {
        Type::Var(v) => HashSet::from([v.clone()]),
        Type::Domain(d) => {
            let mut result: HashSet<_> = d
                .type_parameters
                .iter()
                .filter(|v| !d.partial_type_vars.contains_key(*v))
                .cloned()
                .collect();
            for child in d.partial_type_vars.values() {
                result.extend(get_tvs(child)?);
            }
            result
        }
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => get_tvs(t)?,
        Type::Map(pair) => {
            let mut result = get_tvs(&pair.0)?;
            result.extend(get_tvs(&pair.1)?);
            result
        }
        Type::Extension(_) => return Err(DomainInstanceError::ExtensionType),
        _ => HashSet::new(),
    })
}
pub fn collect_ground_types(
    root: &Node,
    program: &Program,
) -> Result<HashSet<Type>, DomainInstanceError> {
    fn walk(n: &Node, p: &Program, out: &mut HashSet<Type>) -> Result<(), DomainInstanceError> {
        match n {
            Node::Type(t) if t.is_concrete() => {
                out.insert(t.clone());
            }
            Node::Exp(e) => {
                if let ExpKind::DomainFuncApp(_, _, map) = e.kind() {
                    if map.values().all(Type::is_concrete) {
                        let name =
                            e.0.extra
                                .domain_name
                                .as_ref()
                                .ok_or(DomainInstanceError::MissingDomainName)?;
                        let domain = p
                            .find_domain_optionally(name)
                            .ok_or_else(|| DomainInstanceError::MissingDomain(name.clone()))?;
                        out.insert(Type::Domain(DomainType::new(
                            name.clone(),
                            map.clone(),
                            domain.type_vars.clone(),
                        )));
                    }
                }
            }
            _ => {}
        }
        for child in subnodes(n)? {
            walk(&child, p, out)?;
        }
        Ok(())
    }
    let mut out = HashSet::new();
    walk(root, program, &mut out)?;
    Ok(out)
}
/// Source shallow collection of types and domain-function applications.
pub fn collect_domain_types(
    root: &Node,
    program: &Program,
) -> Result<HashSet<Type>, DomainInstanceError> {
    fn walk(n: &Node, p: &Program, out: &mut HashSet<Type>) -> Result<(), DomainInstanceError> {
        if let Node::Type(t) = n {
            out.extend(down_closure(t)?);
            return Ok(());
        }
        if let Node::Exp(e) = n {
            if let ExpKind::DomainFuncApp(_, args, map) = e.kind() {
                let name =
                    e.0.extra
                        .domain_name
                        .as_ref()
                        .ok_or(DomainInstanceError::MissingDomainName)?;
                let domain = p
                    .find_domain_optionally(name)
                    .ok_or_else(|| DomainInstanceError::MissingDomain(name.clone()))?;
                let mappings = domain
                    .type_vars
                    .iter()
                    .map(|v| (v.clone(), map.get(v).cloned().unwrap_or(Type::Int)))
                    .collect();
                out.insert(Type::Domain(DomainType::new(
                    name.clone(),
                    mappings,
                    domain.type_vars.clone(),
                )));
                out.insert(e.typ().map_err(TraversalError::from)?);
                for arg in args {
                    walk(&Node::Exp(arg.clone()), p, out)?;
                }
                for t in map.values() {
                    walk(&Node::Type(t.clone()), p, out)?;
                }
                return Ok(());
            }
        }
        for child in subnodes(n)? {
            walk(&child, p, out)?;
        }
        Ok(())
    }
    let mut result = HashSet::new();
    walk(root, program, &mut result)?;
    Ok(result)
}

fn unify(pattern: &Type, ground: &Type, subst: &mut HashMap<TypeVar, Type>) -> bool {
    match (pattern, ground) {
        (Type::Var(v), t) => match subst.get(v) {
            Some(old) => old == t,
            None => {
                subst.insert(v.clone(), t.clone());
                true
            }
        },
        (Type::Seq(a), Type::Seq(b))
        | (Type::Set(a), Type::Set(b))
        | (Type::Multiset(a), Type::Multiset(b)) => unify(a, b, subst),
        (Type::Map(a), Type::Map(b)) => unify(&a.0, &b.0, subst) && unify(&a.1, &b.1, subst),
        (Type::Domain(a), Type::Domain(b)) if a.domain_name == b.domain_name => {
            let x = a.type_arguments();
            let y = b.type_arguments();
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(a, b)| unify(a, b, subst))
        }
        _ => pattern == ground,
    }
}

/// Upstream thresholded type-coordinate expansion and axiom-call unification.
pub fn find_necessary_type_instances(
    p: &Program,
    threshold: i32,
) -> Result<HashSet<Type>, DomainInstanceError> {
    use std::collections::VecDeque;
    type App = (String, String, HashMap<TypeVar, Type>);
    fn apps(n: &Node, out: &mut Vec<App>) -> Result<(), DomainInstanceError> {
        if let Node::Exp(e) = n {
            if let ExpKind::DomainFuncApp(name, _, map) = e.kind() {
                out.push((
                    name.clone(),
                    e.0.extra
                        .domain_name
                        .clone()
                        .ok_or(DomainInstanceError::MissingDomainName)?,
                    map.clone(),
                ));
            }
        }
        for c in subnodes(n)? {
            apps(&c, out)?;
        }
        Ok(())
    }
    let mut axiom_apps = Vec::new();
    for domain in &p.domains {
        for axiom in &domain.axioms {
            let mut found = Vec::new();
            apps(&Node::Exp(axiom.exp().clone()), &mut found)?;
            let name = match axiom.kind() {
                crate::ast::program::DomainAxiomKind::Named { domain_name, .. }
                | crate::ast::program::DomainAxiomKind::Anonymous { domain_name, .. } => {
                    domain_name
                }
            };
            let owner = p
                .find_domain_optionally(name)
                .ok_or_else(|| DomainInstanceError::MissingDomain(name.clone()))?;
            for app in found {
                axiom_apps.push((app, owner));
            }
        }
    }
    let mut all_apps = Vec::new();
    apps(&Node::Program(p.clone()), &mut all_apps)?;
    let mut initial = HashSet::new();
    for typ in collect_ground_types(&Node::Program(p.clone()), p)? {
        initial.extend(down_closure_ground(&typ)?);
    }
    for (name, called_domain, ground_map) in all_apps
        .iter()
        .filter(|(_, _, m)| m.values().all(Type::is_concrete))
    {
        let called = p
            .find_domain_optionally(called_domain)
            .ok_or_else(|| DomainInstanceError::MissingDomain(called_domain.clone()))?;
        for ((pattern_name, _, pattern_map), axiom_domain) in &axiom_apps {
            if name != pattern_name {
                continue;
            }
            let mut subst = HashMap::new();
            let mut matched = true;
            for tv in &called.type_vars {
                let left = pattern_map
                    .get(tv)
                    .ok_or_else(|| DomainInstanceError::MissingTypeArgument(tv.name.clone()))?;
                let right = ground_map
                    .get(tv)
                    .ok_or_else(|| DomainInstanceError::MissingTypeArgument(tv.name.clone()))?;
                if !unify(left, right, &mut subst) {
                    matched = false;
                    break;
                }
            }
            if matched {
                let map = axiom_domain
                    .type_vars
                    .iter()
                    .map(|v| (v.clone(), subst.get(v).cloned().unwrap_or(Type::Int)))
                    .collect();
                initial.extend(down_closure_ground(&Type::Domain(DomainType::new(
                    axiom_domain.name.clone(),
                    map,
                    axiom_domain.type_vars.clone(),
                )))?);
            }
        }
    }
    let mut done = HashSet::new();
    let mut todo = VecDeque::new();
    let mut luggage: HashMap<Type, HashMap<TypeVar, i32>> = HashMap::new();
    for t in &initial {
        if !t.is_concrete() {
            return Err(DomainInstanceError::NonGroundCoordinate(t.clone()));
        }
        luggage.entry(t.clone()).or_insert_with(|| match t {
            Type::Domain(d) => d.type_parameters.iter().cloned().map(|v| (v, 0)).collect(),
            _ => HashMap::new(),
        });
    }
    fn enqueue(
        t: Type,
        done: &mut HashSet<Type>,
        todo: &mut VecDeque<Type>,
    ) -> Result<(), DomainInstanceError> {
        if !t.is_concrete() {
            return Err(DomainInstanceError::NonGroundCoordinate(t));
        }
        if done.insert(t.clone()) {
            for c in down1_types(&t)? {
                enqueue(c, done, todo)?;
            }
            todo.push_back(t);
        }
        Ok(())
    }
    for t in initial {
        enqueue(t, &mut done, &mut todo)?;
    }
    while let Some(t) = todo.pop_front() {
        let Some(inflation) = luggage.get(&t).cloned() else {
            return Err(DomainInstanceError::NonGroundCoordinate(t));
        };
        let Type::Domain(d) = t else { continue };
        let domain = p
            .find_domain_optionally(&d.domain_name)
            .ok_or_else(|| DomainInstanceError::MissingDomain(d.domain_name.clone()))?;
        let candidates = collect_domain_types(
            &Node::Member(crate::ast::program::Member::Domain(domain.clone())),
            p,
        )?;
        let mut pending = HashSet::new();
        for template in candidates {
            let next = template.substitute(&d.type_vars_map());
            if done.contains(&next) {
                continue;
            }
            if !next.is_concrete() {
                return Err(DomainInstanceError::NonGroundCoordinate(next));
            }
            let mut depths = HashMap::new();
            if let Type::Domain(dt) = &template {
                for (tv, value) in dt.type_vars_map() {
                    let mut maximum = 0;
                    for (free, depth) in get_ftv_depths(&value)? {
                        maximum = maximum.max(
                            depth.wrapping_add(
                                *inflation
                                    .get(&free)
                                    .ok_or(DomainInstanceError::MissingInflation(free))?,
                            ),
                        );
                    }
                    depths.insert(tv, maximum);
                }
            }
            if depths.values().all(|depth| *depth <= threshold) {
                let target = luggage.entry(next.clone()).or_default();
                for (v, depth) in depths {
                    let old = target.get(&v).copied().unwrap_or(0);
                    target.insert(v, depth.wrapping_add(old));
                }
                pending.insert(next);
            }
        }
        for next in pending {
            enqueue(next, &mut done, &mut todo)?;
        }
    }
    Ok(done)
}

/// Instantiate and filter domain members against the source ground-instance set.
pub fn get_instance_members(
    program: &Program,
    instance: &DomainType,
    ground: &HashSet<Type>,
) -> Result<
    (
        Vec<crate::ast::program::DomainFunc>,
        Vec<crate::ast::program::DomainAxiom>,
    ),
    DomainInstanceError,
> {
    use crate::ast::utility::nodes::substitute_domain_node_types;
    let domain = program
        .find_domain_optionally(&instance.domain_name)
        .ok_or_else(|| DomainInstanceError::MissingDomain(instance.domain_name.clone()))?;
    let substitution = instance.type_vars_map();
    let mut functions = Vec::new();
    for f in &domain.functions {
        let n = substitute_domain_node_types(&Node::DomainFunc(f.clone()), &substitution, program)
            .map_err(DomainInstanceError::Reconstruction)?;
        if !collect_ground_types(&n, program)?.is_subset(ground) {
            continue;
        }
        let Node::DomainFunc(f) = n else {
            return Err(DomainInstanceError::Reconstruction(
                crate::verifier::verification_result::DiagnosticError::InvalidNode(
                    "domain function",
                ),
            ));
        };
        if !functions.contains(&f) {
            functions.push(f);
        }
    }
    let mut axioms = Vec::new();
    for a in &domain.axioms {
        let n = substitute_domain_node_types(&Node::DomainAxiom(a.clone()), &substitution, program)
            .map_err(DomainInstanceError::Reconstruction)?;
        if !collect_ground_types(&n, program)?.is_subset(ground) {
            continue;
        }
        let Node::DomainAxiom(a) = n else {
            return Err(DomainInstanceError::Reconstruction(
                crate::verifier::verification_result::DiagnosticError::InvalidNode("domain axiom"),
            ));
        };
        if !axioms.contains(&a) {
            axioms.push(a);
        }
    }
    Ok((functions, axioms))
}

pub fn get_domain_type_instances(domain: &Domain) -> Result<HashSet<Type>, DomainInstanceError> {
    fn walk(node: &Node, out: &mut HashSet<Type>) -> Result<(), DomainInstanceError> {
        if let Node::Type(t) = node {
            out.insert(t.clone());
        }
        for child in subnodes(node)? {
            walk(&child, out)?;
        }
        Ok(())
    }
    let mut out = HashSet::new();
    walk(
        &Node::Member(crate::ast::program::Member::Domain(domain.clone())),
        &mut out,
    )?;
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn closure_expands_generic_signature_and_substitution_preserves_keys() {
        use crate::ast::{
            ast::Metadata,
            program::{
                AnyLocalVarDecl, DomainData, DomainFunc, DomainFuncData, LocalVarDecl, Method,
                MethodData,
            },
            utility::nodes::substitute_node_types,
        };
        use std::sync::Arc;
        let meta = Metadata::default();
        let tv = TypeVar::new("T");
        let seq_t = Type::Seq(Arc::new(Type::Var(tv.clone())));
        let function = DomainFunc::new(DomainFuncData {
            name: "f".into(),
            formal_args: vec![AnyLocalVarDecl::Named(LocalVarDecl::new(
                "x".into(),
                seq_t.clone(),
                meta.clone(),
            ))],
            typ: Type::Var(tv.clone()),
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![function.clone()],
            axioms: vec![],
            type_vars: vec![tv.clone()],
            interpretations: None,
            meta: meta.clone(),
        });
        let instance =
            Type::Domain(domain.domain_type([(tv.clone(), Type::Int)].into_iter().collect()));
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new(
                "d".into(),
                instance.clone(),
                meta.clone(),
            )],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![domain],
            vec![],
            vec![],
            vec![],
            vec![method],
            vec![],
            meta,
        );
        let closure = find_necessary_type_instances(&program, 1).unwrap();
        assert!(closure.contains(&instance));
        assert!(closure.contains(&Type::Seq(Arc::new(Type::Int))));
        let (functions, _) = get_instance_members(
            &program,
            match &instance {
                Type::Domain(d) => d,
                _ => unreachable!(),
            },
            &closure,
        )
        .unwrap();
        assert_eq!(functions.len(), 1);
        let mapped = substitute_node_types(
            &Node::DomainFunc(function),
            &[(tv, Type::Int)].into_iter().collect(),
        )
        .unwrap();
        let Node::DomainFunc(mapped) = mapped else {
            panic!("domain function")
        };
        assert_eq!(mapped.typ, Type::Int);
        assert_eq!(mapped.formal_args[0].typ(), &Type::Seq(Arc::new(Type::Int)));
    }
    #[test]
    fn axiom_domain_instance_is_discovered_by_generic_call_unification() {
        use crate::ast::{
            ast::Metadata,
            expression::{Exp, ExpExtra},
            program::{
                DomainAxiom, DomainAxiomKind, DomainData, DomainFunc, DomainFuncData, Method,
                MethodData,
            },
        };
        let meta = Metadata::default();
        let t = TypeVar::new("T");
        let u = TypeVar::new("U");
        let v = TypeVar::new("V");
        let app = |typ: Type| {
            Exp::with_extra(
                ExpKind::DomainFuncApp(
                    "f".into(),
                    vec![],
                    [(t.clone(), typ)].into_iter().collect(),
                ),
                meta.clone(),
                ExpExtra {
                    typ: Some(Type::Bool),
                    domain_name: Some("A".into()),
                    ..Default::default()
                },
            )
        };
        let func = DomainFunc::new(DomainFuncData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Bool,
            unique: false,
            interpretation: None,
            domain_name: "A".into(),
            meta: meta.clone(),
        });
        let a = Domain::new(DomainData {
            name: "A".into(),
            functions: vec![func],
            axioms: vec![],
            type_vars: vec![t.clone()],
            interpretations: None,
            meta: meta.clone(),
        });
        let axiom = DomainAxiom::new(DomainAxiomKind::Anonymous {
            exp: app(Type::Var(u.clone())),
            domain_name: "B".into(),
            meta: meta.clone(),
        });
        let b = Domain::new(DomainData {
            name: "B".into(),
            functions: vec![],
            axioms: vec![axiom],
            type_vars: vec![u.clone(), v.clone()],
            interpretations: None,
            meta: meta.clone(),
        });
        let expected =
            Type::Domain(b.domain_type([(u, Type::Int), (v, Type::Int)].into_iter().collect()));
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![app(Type::Int)],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![a, b],
            vec![],
            vec![],
            vec![],
            vec![method],
            vec![],
            meta,
        );
        let closure = find_necessary_type_instances(&program, 1).unwrap();
        assert!(closure.contains(&expected));
        let Type::Domain(instance) = expected else {
            unreachable!()
        };
        let (_, axioms) = get_instance_members(&program, &instance, &closure).unwrap();
        assert_eq!(axioms.len(), 1);
        let ExpKind::DomainFuncApp(_, _, map) = axioms[0].exp().kind() else {
            panic!("domain application")
        };
        assert_eq!(map.get(&t), Some(&Type::Int));
    }
    #[test]
    fn domain_substitution_preserves_unchanged_identity_and_rebuilds_source_matches() {
        use crate::ast::{
            ast::Metadata,
            expression::{Exp, LocalVar},
            program::{DomainAxiom, DomainAxiomKind, DomainFunc, DomainFuncData},
            utility::nodes::substitute_domain_node_types,
        };
        use std::sync::Arc;
        let meta = Metadata::default();
        let function = DomainFunc::new(DomainFuncData {
            name: "f".into(),
            formal_args: vec![],
            typ: Type::Int,
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let generic = function.copy_with(|f| f.typ = Type::Seq(Arc::new(Type::Int)));
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], meta.clone());
        let Node::DomainFunc(unchanged) = substitute_domain_node_types(
            &Node::DomainFunc(function.clone()),
            &HashMap::new(),
            &program,
        )
        .unwrap() else {
            panic!("function")
        };
        assert!(function.same_node(&unchanged));
        let Node::DomainFunc(rebuilt) = substitute_domain_node_types(
            &Node::DomainFunc(generic.clone()),
            &HashMap::new(),
            &program,
        )
        .unwrap() else {
            panic!("function")
        };
        assert!(!generic.same_node(&rebuilt));
        let truth = Exp::new(ExpKind::TrueLit, meta.clone());
        let axiom = DomainAxiom::new(DomainAxiomKind::Anonymous {
            exp: truth.clone(),
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let Node::DomainAxiom(same) = substitute_domain_node_types(
            &Node::DomainAxiom(axiom.clone()),
            &HashMap::new(),
            &program,
        )
        .unwrap() else {
            panic!("axiom")
        };
        assert!(axiom.same_node(&same));
        assert!(truth.same_node(same.exp()));
        let local = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Int, meta.clone())),
            meta.clone(),
        );
        let equality = Exp::new(ExpKind::EqCmp(local.clone(), truth.clone()), meta.clone());
        let Node::Exp(result) =
            substitute_domain_node_types(&Node::Exp(equality.clone()), &HashMap::new(), &program)
                .unwrap()
        else {
            panic!("expression")
        };
        let ExpKind::EqCmp(new_local, new_truth) = result.kind() else {
            panic!("equality")
        };
        assert!(!equality.same_node(&result));
        assert!(!local.same_node(new_local));
        assert!(truth.same_node(new_truth));
    }
    #[test]
    fn domain_substitution_completes_partial_type_maps() {
        use crate::ast::{ast::Metadata, utility::nodes::substitute_domain_node_types};
        let t = TypeVar::new("T");
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            Metadata::default(),
        );
        let typ = Type::Domain(DomainType::new("D", HashMap::new(), vec![t.clone()]));
        let Node::Type(Type::Domain(mapped)) = substitute_domain_node_types(
            &Node::Type(typ),
            &[(t.clone(), Type::Int)].into_iter().collect(),
            &program,
        )
        .unwrap() else {
            panic!("domain")
        };
        assert_eq!(mapped.partial_type_vars.get(&t), Some(&Type::Int));
    }
    #[test]
    fn substitution_recomputes_domain_application_return_from_declaration() {
        use crate::ast::{
            ast::Metadata,
            expression::{Exp, ExpExtra, LocalVar},
            program::{AnyLocalVarDecl, DomainData, DomainFunc, DomainFuncData, LocalVarDecl},
            utility::nodes::substitute_domain_node_types,
        };
        let meta = Metadata::default();
        let t = TypeVar::new("T");
        let u = TypeVar::new("U");
        let function = DomainFunc::new(DomainFuncData {
            name: "f".into(),
            formal_args: vec![AnyLocalVarDecl::Named(LocalVarDecl::new(
                "x".into(),
                Type::Var(t.clone()),
                meta.clone(),
            ))],
            typ: Type::Var(t.clone()),
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![function],
            axioms: vec![],
            type_vars: vec![t.clone()],
            interpretations: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![domain],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            meta.clone(),
        );
        let arg = Exp::new(
            ExpKind::LocalVar(LocalVar::new("x".into(), Type::Int, meta.clone())),
            meta.clone(),
        );
        let app = Exp::with_extra(
            ExpKind::DomainFuncApp(
                "f".into(),
                vec![arg.clone()],
                [(t.clone(), Type::Var(u.clone()))].into_iter().collect(),
            ),
            meta,
            ExpExtra {
                typ: Some(Type::Bool),
                domain_name: Some("wrong".into()),
                ..Default::default()
            },
        );
        let node = substitute_domain_node_types(
            &Node::Exp(app),
            &[(u, Type::Int)].into_iter().collect(),
            &program,
        )
        .unwrap();
        let Node::Exp(app) = node else {
            panic!("domain application")
        };
        let ExpKind::DomainFuncApp(_, args, map) = app.kind() else {
            panic!("domain application")
        };
        assert!(!arg.same_node(&args[0]));
        assert_eq!(map.get(&t), Some(&Type::Int));
        assert_eq!(app.0.extra.typ, Some(Type::Int));
        assert_eq!(app.0.extra.domain_name.as_deref(), Some("D"));
    }
    #[test]
    fn unification_checks_nested_arguments_and_repeated_variables() {
        use std::sync::Arc;
        let variable = TypeVar::new("T");
        let pattern = Type::map(
            Type::Var(variable.clone()),
            Type::Seq(Arc::new(Type::Var(variable.clone()))),
        );
        let matching = Type::map(Type::Int, Type::Seq(Arc::new(Type::Int)));
        let mismatched = Type::map(Type::Int, Type::Seq(Arc::new(Type::Bool)));
        let mut substitution = HashMap::new();
        assert!(unify(&pattern, &matching, &mut substitution));
        assert_eq!(substitution.get(&variable), Some(&Type::Int));
        assert!(!unify(&pattern, &mismatched, &mut HashMap::new()));
    }
    #[test]
    fn recursive_domain_inflation_obeys_source_threshold() {
        use crate::ast::{
            ast::Metadata,
            program::{DomainData, DomainFunc, DomainFuncData, LocalVarDecl, Method, MethodData},
        };
        use std::sync::Arc;
        let meta = Metadata::default();
        let tv = TypeVar::new("T");
        let sequence = Type::Seq(Arc::new(Type::Var(tv.clone())));
        let next = Type::Domain(DomainType::new(
            "D",
            [(tv.clone(), sequence)].into_iter().collect(),
            vec![tv.clone()],
        ));
        let function = DomainFunc::new(DomainFuncData {
            name: "f".into(),
            formal_args: vec![],
            typ: next,
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![function],
            axioms: vec![],
            type_vars: vec![tv.clone()],
            interpretations: None,
            meta: meta.clone(),
        });
        let make = |t| Type::Domain(domain.domain_type([(tv.clone(), t)].into_iter().collect()));
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new("d".into(), make(Type::Int), meta.clone())],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![domain.clone()],
            vec![],
            vec![],
            vec![],
            vec![method],
            vec![],
            meta,
        );
        let closure = find_necessary_type_instances(&program, 1).unwrap();
        let seq = Type::Seq(Arc::new(Type::Int));
        assert!(closure.contains(&make(seq.clone())));
        assert!(!closure.contains(&make(Type::Seq(Arc::new(seq)))));
    }
    #[test]
    fn ground_closure_keeps_nonground_descendants_as_upstream() {
        let variable = Type::Var(TypeVar::new("T"));
        let seq = Type::Seq(std::sync::Arc::new(variable.clone()));
        let closure = down_closure_ground(&seq).unwrap();
        assert!(!closure.contains(&seq));
        assert!(closure.contains(&variable));
    }
}
