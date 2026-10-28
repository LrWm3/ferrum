//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/plugin/standard/adt/encoding/AdtEncoder.scala
//!
//! Purpose:
//! Encode ADTs into Silver domains, functions and axioms before backend verification.
//!
//! Planned Rust structure:
//! Port AdtEncoder encode, tagMapping, constructor/destructor/discriminator conversion, ADT-type
//! conversion and axiom generators for injectivity, tag, exclusivity, contains, transitivity and
//! well-foundedness.
//!
//! Behavior to preserve:
//! Assign constructor tags by sorted name. Bottom-up replace declarations and applications, then
//! rewrite all ADT types, then add contains transitivity domain when derived. Generate
//! constructor/destructor/tag functions and axioms with source triggers; optional well-founded
//! domains require termination enabled, an existing well-founded-order declaration domain and
//! absence of the ADT-specific well-founded domain. Traverse nested ADT
//! constructor types with visited-set guard for decreases axioms; derive contains excluding
//! blocklisted fields and build concrete-type transitive closure. Preserve order, metadata, type
//! maps and actual trigger generation, including exclusivity’s last destructor-call list.
//!
//! Integration:
//! plugin::standard::adt::{adt_plugin,adt_ast_extension,encoding::adt_name_manager};
//! ast domain/type/expression rewriter, termination and ADT resources.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for ordering, typed maps, metadata and explicit reconstruction.
//!
//! Open decisions:
//! Reconcile exclusivity trigger accumulation and unordered closure enumeration against upstream
//! tests before any correction.
//!
//! Status: partial; whole-program lowering and all source axiom families are implemented.
//! Scoped-name collection and typed plugin lifecycle are wired; source parsing and
//! pre-resolution remain pending. Unsupported extension reconstruction fails explicitly.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2022 ETH Zurich.

use super::adt_name_manager::AdtNameManager;
use crate::ast::ast::Metadata;
use crate::ast::expression::{Exp, ExpExtra, ExpKind, Trigger};
use crate::ast::program::{
    AnyLocalVarDecl, Domain, DomainAxiom, DomainAxiomKind, DomainData, DomainFunc, DomainFuncData,
    LocalVarDecl, Program,
};
use crate::ast::r#type::{DomainType, Type, TypeSubstitution, TypeVar};
use crate::plugin::standard::adt::adt_ast_extension::{
    Adt, AdtConstructor, AdtConstructorApp, AdtDestructorApp, AdtDiscriminatorApp, AdtType,
};
use crate::verifier::verification_result::DiagnosticError;
use std::collections::{HashMap, HashSet};

/// Generates the ordinary domain representation and lowers typed ADT programs.
pub struct AdtEncoder {
    pub names: AdtNameManager,
    tags: HashMap<String, HashMap<String, i32>>,
}

impl AdtEncoder {
    pub fn new(program: Program, scoped_names: impl IntoIterator<Item = String>) -> Self {
        let mut tags = HashMap::new();
        for member in &program.extensions {
            if let Some(adt) = member.0.as_any().downcast_ref::<Adt>() {
                let mut names: Vec<_> = adt.constructors.iter().map(|c| c.name.clone()).collect();
                names.sort();
                tags.insert(
                    adt.name.clone(),
                    names
                        .into_iter()
                        .enumerate()
                        .map(|(i, n)| (n, i as i32))
                        .collect(),
                );
            }
        }
        Self {
            names: AdtNameManager::new(program, scoped_names),
            tags,
        }
    }

    /// Perform the source's declaration/application pass, ADT-type pass, and
    /// optional contains-transitivity pass in that order. Unsupported extension
    /// product reconstruction and unresolved expression types are reported.
    pub fn encode(&mut self, termination_active: bool) -> Result<Program, DiagnosticError> {
        use crate::ast::utility::nodes::{Node, map_node_tree_bottom_up};
        use std::cell::RefCell;
        let source = self.names.program.clone();
        let contains_derived = source.extensions.iter().any(|m| {
            m.0.as_any().downcast_ref::<Adt>().is_some_and(|a| {
                a.deriving_info
                    .contains_key(self.names.contains_function_name())
            })
        });
        let encoder = RefCell::new(self);
        let first = map_node_tree_bottom_up(
            &Node::Program(source.clone()),
            &|node| {
                match node {
                    Node::Exp(e) => {
                        if let ExpKind::Extension(extension) = e.kind() {
                            if let Some(app) =
                                extension.0.as_any().downcast_ref::<AdtConstructorApp>()
                            {
                                return Ok(Node::Exp(encoder.borrow().encode_constructor_app(app)));
                            }
                            if let Some(app) =
                                extension.0.as_any().downcast_ref::<AdtDestructorApp>()
                            {
                                return Ok(Node::Exp(
                                    encoder.borrow_mut().encode_destructor_app(app),
                                ));
                            }
                            if let Some(app) =
                                extension.0.as_any().downcast_ref::<AdtDiscriminatorApp>()
                            {
                                return Ok(Node::Exp(
                                    encoder.borrow_mut().encode_discriminator_app(app)?,
                                ));
                            }
                        }
                    }
                    Node::Program(program) => {
                        let mut domains = program.domains.clone();
                        let mut extensions = Vec::new();
                        for member in &program.extensions {
                            if let Some(adt) = member.0.as_any().downcast_ref::<Adt>() {
                                let encoder = &mut *encoder.borrow_mut();
                                let wf = termination_active
                                    && source.domains.iter().any(|d| {
                                        d.name
                                            == encoder
                                                .names
                                                .well_founded_order_declaration_domain_name()
                                    })
                                    && !source.domains.iter().any(|d| {
                                        d.name == encoder.names.well_founded_domain_name(&adt.name)
                                    });
                                domains.extend(encoder.encode_adt_as_domains(adt, wf)?);
                            } else {
                                extensions.push(member.clone());
                            }
                        }
                        return Ok(Node::Program(program.copy_with(|p| {
                            p.domains = domains;
                            p.extensions = extensions;
                        })));
                    }
                    _ => {}
                }
                Ok(node.clone())
            },
            false,
        )?;
        let pairs: RefCell<HashSet<(Type, Type)>> = RefCell::new(HashSet::new());
        let second = map_node_tree_bottom_up(
            &first,
            &|node| {
                match node {
                    Node::Type(Type::Extension(extension)) => {
                        if let Some(adt) = extension.as_any().downcast_ref::<AdtType>() {
                            return Ok(Node::Type(encode_adt_type(adt)));
                        }
                    }
                    Node::Exp(e) if contains_derived => {
                        if let ExpKind::DomainFuncApp(name, args, _) = e.kind() {
                            if name == encoder.borrow().names.contains_function_name()
                                && e.0.extra.domain_name.as_deref()
                                    == Some(encoder.borrow().names.contains_domain_name())
                            {
                                if args.len() != 2 {
                                    return Err(DiagnosticError::InvalidNode(
                                        "contains application arity",
                                    ));
                                }
                                let left = args[0].typ().map_err(|_| {
                                    DiagnosticError::InvalidNode("contains argument type")
                                })?;
                                let right = args[1].typ().map_err(|_| {
                                    DiagnosticError::InvalidNode("contains argument type")
                                })?;
                                if left.is_concrete() && right.is_concrete() {
                                    pairs.borrow_mut().insert((left, right));
                                }
                            }
                        }
                    }
                    _ => {}
                }
                Ok(node.clone())
            },
            true,
        )?;
        let Node::Program(mut result) = second else {
            return Err(DiagnosticError::InvalidNode("ADT encoded program"));
        };
        if contains_derived {
            let transitivity = encoder
                .borrow_mut()
                .contains_transitivity_domain(pairs.into_inner());
            result = result.copy_with(|p| p.domains.push(transitivity));
        }
        Ok(result)
    }

    /// Lower the three source application forms; children are supplied as already
    /// rewritten expressions by the whole-program traversal.
    pub fn encode_constructor_app(&self, app: &AdtConstructorApp) -> Exp {
        domain_app(
            &app.name,
            app.args.clone(),
            app.type_vars.clone(),
            app.typ.clone(),
            &app.adt_name,
            &app.meta,
        )
    }

    pub fn encode_destructor_app(&mut self, app: &AdtDestructorApp) -> Exp {
        let name = self.names.destructor_name(&app.adt_name, &app.name);
        domain_app(
            &name,
            vec![app.receiver.clone()],
            app.type_vars.clone(),
            app.typ.clone(),
            &app.adt_name,
            &app.meta,
        )
    }

    pub fn encode_discriminator_app(
        &mut self,
        app: &AdtDiscriminatorApp,
    ) -> Result<Exp, DiagnosticError> {
        let value = *self
            .tags
            .get(&app.adt_name)
            .and_then(|tags| tags.get(&app.name))
            .ok_or(DiagnosticError::InvalidNode(
                "ADT discriminator constructor",
            ))?;
        let name = self.names.tag_name(&app.adt_name);
        let tag = domain_app(
            &name,
            vec![app.receiver.clone()],
            app.type_vars.clone(),
            Type::Int,
            &app.adt_name,
            &app.meta,
        );
        Ok(exp(
            ExpKind::EqCmp(tag, exp(ExpKind::IntLit(value.into()), &app.meta)),
            &app.meta,
        ))
    }

    /// Encode the declaration and, when requested, its separate well-founded-order domain.
    pub fn encode_adt_as_domains(
        &mut self,
        adt: &Adt,
        well_founded: bool,
    ) -> Result<Vec<Domain>, DiagnosticError> {
        let domain = self.encode_adt_as_domain(adt, false)?;
        if !well_founded {
            return Ok(vec![domain]);
        }
        let domain_type = Type::Domain(DomainType::new(
            adt.name.clone(),
            default_types(adt),
            adt.type_vars.clone(),
        ));
        let wf_name = self.names.well_founded_domain_name(&adt.name);
        let order = self.names.well_founded_order_declaration_domain_name();
        let mut axioms = Vec::new();
        for constructor in &adt.constructors {
            let vars = constructor_vars(constructor);
            let mut quantifiers = Vec::new();
            for (index, declaration) in constructor.formal_args.iter().enumerate() {
                let nested = self.nested_adt_values(constructor, declaration, &HashSet::new())?;
                for (mut qvars, value, smaller) in nested {
                    qvars.extend(
                        constructor
                            .formal_args
                            .iter()
                            .enumerate()
                            .filter(|(j, _)| *j != index)
                            .map(|(_, v)| v.clone()),
                    );
                    let mut args = vars.clone();
                    args[index] = value;
                    let app = domain_app(
                        &constructor.name,
                        args,
                        default_types(adt),
                        encode_adt_type(&constructor.typ),
                        &adt.name,
                        &constructor.meta,
                    );
                    let mut types = TypeSubstitution::new();
                    types.insert(TypeVar::new("T"), encode_adt_type(&constructor.typ));
                    let decreases = domain_app(
                        self.names.decreases_function_name(),
                        vec![smaller, app.clone()],
                        types,
                        Type::Bool,
                        order,
                        &constructor.meta,
                    );
                    quantifiers.insert(
                        0,
                        quantified(qvars, vec![app], decreases, &constructor.meta),
                    );
                }
            }
            let default_meta = Metadata::default();
            let body = quantifiers
                .into_iter()
                .fold(exp(ExpKind::TrueLit, &default_meta), |a, b| {
                    exp(ExpKind::And(a, b), &default_meta)
                });
            axioms.push(axiom(body, &wf_name, &constructor.meta));
        }
        let default_meta = Metadata::default();
        let vars: Vec<_> = ["v1", "v2", "v3"]
            .into_iter()
            .map(|name| LocalVarDecl::new(name.into(), domain_type.clone(), default_meta.clone()))
            .collect();
        let vals: Vec<_> = vars
            .iter()
            .map(|v| exp(ExpKind::LocalVar(v.local_var()), &default_meta))
            .collect();
        let mut types = TypeSubstitution::new();
        types.insert(TypeVar::new("T"), domain_type.clone());
        let decrease = |a: Exp, b: Exp| {
            domain_app(
                self.names.decreases_function_name(),
                vec![a, b],
                types.clone(),
                Type::Bool,
                order,
                &adt.meta,
            )
        };
        let d12 = decrease(vals[0].clone(), vals[1].clone());
        let d23 = decrease(vals[1].clone(), vals[2].clone());
        let d13 = decrease(vals[0].clone(), vals[2].clone());
        let body = exp(
            ExpKind::Implies(exp(ExpKind::And(d12.clone(), d23.clone()), &adt.meta), d13),
            &adt.meta,
        );
        axioms.push(axiom(
            quantified(vars, vec![d12, d23], body, &default_meta),
            &wf_name,
            &adt.meta,
        ));
        let x = LocalVarDecl::new("x".into(), domain_type, default_meta.clone());
        let bounded = domain_app(
            self.names.bounded_function_name(),
            vec![exp(ExpKind::LocalVar(x.local_var()), &default_meta)],
            types,
            Type::Bool,
            order,
            &adt.meta,
        );
        axioms.push(axiom(
            quantified(vec![x], vec![bounded.clone()], bounded, &adt.meta),
            &wf_name,
            &adt.meta,
        ));
        let well_founded_domain = Domain::new(DomainData {
            name: wf_name,
            functions: vec![],
            axioms,
            type_vars: adt.type_vars.clone(),
            interpretations: None,
            meta: adt.meta.clone(),
        });
        Ok(vec![domain, well_founded_domain])
    }

    fn nested_adt_values(
        &self,
        outer: &AdtConstructor,
        current: &LocalVarDecl,
        visited: &HashSet<Type>,
    ) -> Result<Vec<(Vec<LocalVarDecl>, Exp, Exp)>, DiagnosticError> {
        let Type::Extension(extension) = &current.typ else {
            return Ok(vec![]);
        };
        let Some(current_adt) = extension.as_any().downcast_ref::<AdtType>() else {
            return Ok(vec![]);
        };
        if current.typ == outer.typ.clone().as_type() {
            let renamed = LocalVarDecl::new(
                format!("{}_{}", current.name, visited.len()),
                current.typ.clone(),
                current.meta.clone(),
            );
            let value = exp(ExpKind::LocalVar(renamed.local_var()), &renamed.meta);
            return Ok(vec![(vec![renamed], value.clone(), value)]);
        }
        if visited.contains(&current.typ) {
            return Ok(vec![]);
        }
        let adt = self
            .names
            .program
            .extensions
            .iter()
            .find_map(|m| {
                m.0.as_any()
                    .downcast_ref::<Adt>()
                    .filter(|a| a.name == current_adt.adt_name)
            })
            .ok_or(DiagnosticError::InvalidNode("nested ADT declaration"))?;
        let mut next_visited = visited.clone();
        next_visited.insert(current.typ.clone());
        let mut result = Vec::new();
        for constructor in &adt.constructors {
            let args: Vec<_> = constructor
                .formal_args
                .iter()
                .map(|arg| {
                    LocalVarDecl::new(
                        format!("{}_{}", arg.name, visited.len()),
                        arg.typ.clone(),
                        arg.meta.clone(),
                    )
                })
                .collect();
            for (index, arg) in constructor.formal_args.iter().enumerate() {
                for (mut qvars, value, smaller) in
                    self.nested_adt_values(outer, arg, &next_visited)?
                {
                    // Scala's sequence diff removes one structurally equal declaration.
                    let mut remaining = args.clone();
                    if let Some(i) = remaining.iter().position(|v| *v == args[index]) {
                        remaining.remove(i);
                    }
                    qvars.extend(remaining);
                    let mut arguments: Vec<_> = args
                        .iter()
                        .map(|v| exp(ExpKind::LocalVar(v.local_var()), &v.meta))
                        .collect();
                    arguments[index] = value;
                    let app = domain_app(
                        &constructor.name,
                        arguments,
                        constructor.typ.type_vars_map(),
                        encode_adt_type(&constructor.typ),
                        &outer.adt_name,
                        &outer.meta,
                    );
                    result.push((qvars, app, smaller));
                }
            }
        }
        Ok(result)
    }

    /// Construct the source contains-transitivity domain from the concrete argument
    /// type pairs collected from all `ContainsDomain.contains` applications.
    pub fn contains_transitivity_domain(
        &mut self,
        pairs: impl IntoIterator<Item = (Type, Type)>,
    ) -> Domain {
        let mut closure: HashSet<(Type, Type)> = pairs
            .into_iter()
            .filter(|(a, b)| a.is_concrete() && b.is_concrete())
            .collect();
        loop {
            let additions: Vec<_> = closure
                .iter()
                .flat_map(|(a, b)| {
                    closure
                        .iter()
                        .filter_map(move |(c, d)| (b == c).then(|| (a.clone(), d.clone())))
                })
                .collect();
            let size = closure.len();
            closure.extend(additions);
            if closure.len() == size {
                break;
            }
        }
        let triples: HashSet<_> = closure
            .iter()
            .flat_map(|(a, b)| {
                closure
                    .iter()
                    .filter_map(move |(c, d)| (b == c).then(|| (a.clone(), b.clone(), d.clone())))
            })
            .collect();
        let name = self.names.contains_transitivity_domain();
        let meta = Metadata::default();
        let mut axioms = Vec::new();
        for (a, b, c) in triples {
            let vars = vec![
                LocalVarDecl::new("a".into(), a.clone(), meta.clone()),
                LocalVarDecl::new("b".into(), b.clone(), meta.clone()),
                LocalVarDecl::new("c".into(), c.clone(), meta.clone()),
            ];
            let values: Vec<_> = vars
                .iter()
                .map(|v| exp(ExpKind::LocalVar(v.local_var()), &meta))
                .collect();
            let contains = |left: Exp, right: Exp, left_type: Type, right_type: Type| {
                let mut types = TypeSubstitution::new();
                types.insert(TypeVar::new("A"), left_type);
                types.insert(TypeVar::new("B"), right_type);
                domain_app(
                    self.names.contains_function_name(),
                    vec![left, right],
                    types,
                    Type::Bool,
                    self.names.contains_domain_name(),
                    &meta,
                )
            };
            let ab = contains(values[0].clone(), values[1].clone(), a.clone(), b.clone());
            let bc = contains(values[1].clone(), values[2].clone(), b, c.clone());
            let ac = contains(values[0].clone(), values[2].clone(), a, c);
            let body = exp(
                ExpKind::Implies(exp(ExpKind::And(ab.clone(), bc.clone()), &meta), ac),
                &meta,
            );
            axioms.push(axiom(
                quantified(vars, vec![ab, bc], body, &meta),
                &name,
                &meta,
            ));
        }
        Domain::new(DomainData {
            name,
            functions: vec![],
            axioms,
            type_vars: vec![],
            interpretations: None,
            meta,
        })
    }

    pub fn encode_adt_as_domain(
        &mut self,
        adt: &Adt,
        generate_well_foundedness: bool,
    ) -> Result<Domain, DiagnosticError> {
        if generate_well_foundedness {
            return Err(DiagnosticError::Unsupported("ADT well-foundedness axioms"));
        }
        let ty = Type::Domain(DomainType::new(
            adt.name.clone(),
            default_types(adt),
            adt.type_vars.clone(),
        ));
        let mut functions = Vec::new();
        let mut axioms = Vec::new();
        for c in &adt.constructors {
            if c.adt_name != adt.name {
                return Err(DiagnosticError::InvalidNode("ADT constructor owner"));
            }
            functions.push(function(
                &c.name,
                c.formal_args
                    .iter()
                    .cloned()
                    .map(AnyLocalVarDecl::Named)
                    .collect(),
                encode_adt_type(&c.typ),
                &adt.name,
                &c.meta,
            ));
        }
        for c in &adt.constructors {
            for arg in &c.formal_args {
                let name = self.names.destructor_name(&adt.name, &arg.name);
                functions.push(function(
                    &name,
                    vec![AnyLocalVarDecl::Named(LocalVarDecl::new(
                        "t".into(),
                        ty.clone(),
                        c.meta.clone(),
                    ))],
                    direct_adt_type(&arg.typ),
                    &adt.name,
                    &c.meta,
                ));
            }
        }
        let tag_name = self.names.tag_name(&adt.name);
        functions.push(function(
            &tag_name,
            vec![AnyLocalVarDecl::Named(LocalVarDecl::new(
                "t".into(),
                ty.clone(),
                adt.meta.clone(),
            ))],
            Type::Int,
            &adt.name,
            &adt.meta,
        ));
        for c in &adt.constructors {
            let vars = constructor_vars(c);
            let app = domain_app(
                &c.name,
                vars.clone(),
                default_types(adt),
                encode_adt_type(&c.typ),
                &adt.name,
                &c.meta,
            );
            for (arg, var) in c.formal_args.iter().zip(vars.iter()) {
                let destructor = self.names.destructor_name(&adt.name, &arg.name);
                let right = domain_app(
                    &destructor,
                    vec![app.clone()],
                    default_types(adt),
                    direct_adt_type(&arg.typ),
                    &adt.name,
                    &c.meta,
                );
                let eq = exp(ExpKind::EqCmp(var.clone(), right), &c.meta);
                let forall = quantified(c.formal_args.clone(), vec![app.clone()], eq, &c.meta);
                axioms.push(axiom(forall, &adt.name, &c.meta));
            }
        }
        for c in &adt.constructors {
            let vars = constructor_vars(c);
            let app = domain_app(
                &c.name,
                vars,
                default_types(adt),
                encode_adt_type(&c.typ),
                &adt.name,
                &c.meta,
            );
            let tag = domain_app(
                &tag_name,
                vec![app.clone()],
                default_types(adt),
                Type::Int,
                &adt.name,
                &c.meta,
            );
            let value = *self
                .tags
                .get(&adt.name)
                .and_then(|m| m.get(&c.name))
                .ok_or(DiagnosticError::InvalidNode("ADT constructor tag"))?;
            let eq = exp(
                ExpKind::EqCmp(tag, exp(ExpKind::IntLit(value.into()), &c.meta)),
                &c.meta,
            );
            let body = if c.formal_args.is_empty() {
                eq
            } else {
                quantified(c.formal_args.clone(), vec![app], eq, &c.meta)
            };
            axioms.push(axiom(body, &adt.name, &c.meta));
        }
        let local = LocalVarDecl::new("t".into(), ty.clone(), adt.meta.clone());
        let t = exp(ExpKind::LocalVar(local.local_var()), &adt.meta);
        let tag = domain_app(
            &tag_name,
            vec![t.clone()],
            default_types(adt),
            Type::Int,
            &adt.name,
            &adt.meta,
        );
        let mut body = exp(ExpKind::FalseLit, &adt.meta);
        let mut last_destructors = Vec::new();
        for c in &adt.constructors {
            let mut destructors = Vec::new();
            for arg in &c.formal_args {
                let name = self.names.destructor_name(&adt.name, &arg.name);
                destructors.push(domain_app(
                    &name,
                    vec![t.clone()],
                    default_types(adt),
                    arg.typ.clone(),
                    &adt.name,
                    &adt.meta,
                ));
            }
            let app = domain_app(
                &c.name,
                destructors.clone(),
                default_types(adt),
                c.typ.clone().as_type(),
                &adt.name,
                &adt.meta,
            );
            body = exp(
                ExpKind::Or(body, exp(ExpKind::EqCmp(t.clone(), app), &adt.meta)),
                &adt.meta,
            );
            last_destructors = destructors;
        }
        let triggers = std::iter::once(tag)
            .chain(last_destructors)
            .map(|e| Trigger::new(vec![e], adt.meta.clone()))
            .collect();
        axioms.push(axiom(
            exp(ExpKind::Forall(vec![local], triggers, body), &adt.meta),
            &adt.name,
            &adt.meta,
        ));
        if let Some((_, blocklist)) = adt.deriving_info.get(self.names.contains_function_name()) {
            for c in &adt.constructors {
                if c.formal_args.is_empty() {
                    continue;
                }
                let vars = constructor_vars(c);
                let app = domain_app(
                    &c.name,
                    vars.clone(),
                    default_types(adt),
                    encode_adt_type(&c.typ),
                    &adt.name,
                    &c.meta,
                );
                let mut body = exp(ExpKind::TrueLit, &c.meta);
                for (arg, var) in c.formal_args.iter().zip(vars) {
                    if blocklist.contains(&arg.name) {
                        continue;
                    }
                    let mut types = TypeSubstitution::new();
                    types.insert(TypeVar::new("A"), direct_adt_type(&arg.typ));
                    types.insert(TypeVar::new("B"), encode_adt_type(&c.typ));
                    let contains = domain_app(
                        self.names.contains_function_name(),
                        vec![var, app.clone()],
                        types,
                        Type::Bool,
                        self.names.contains_domain_name(),
                        &c.meta,
                    );
                    body = exp(ExpKind::And(body, contains), &c.meta);
                }
                axioms.push(axiom(
                    quantified(c.formal_args.clone(), vec![app], body, &c.meta),
                    &adt.name,
                    &c.meta,
                ));
            }
        }
        Ok(Domain::new(DomainData {
            name: adt.name.clone(),
            functions,
            axioms,
            type_vars: adt.type_vars.clone(),
            interpretations: None,
            meta: adt.meta.clone(),
        }))
    }
}

fn default_types(adt: &Adt) -> TypeSubstitution {
    adt.type_vars
        .iter()
        .map(|v| (v.clone(), Type::Var(v.clone())))
        .collect()
}
fn encode_adt_type(t: &AdtType) -> Type {
    Type::Domain(DomainType::new(
        t.adt_name.clone(),
        t.partial_type_vars.clone(),
        t.type_parameters.clone(),
    ))
}
fn direct_adt_type(t: &Type) -> Type {
    if let Type::Extension(e) = t {
        if let Some(a) = e.as_any().downcast_ref::<AdtType>() {
            return encode_adt_type(a);
        }
    }
    t.clone()
}
fn exp(kind: ExpKind, meta: &Metadata) -> Exp {
    Exp::new(kind, meta.clone())
}
fn domain_app(
    name: &str,
    args: Vec<Exp>,
    types: TypeSubstitution,
    typ: Type,
    domain: &str,
    meta: &Metadata,
) -> Exp {
    Exp::with_extra(
        ExpKind::DomainFuncApp(name.into(), args, types),
        meta.clone(),
        ExpExtra {
            typ: Some(typ),
            domain_name: Some(domain.into()),
            interpretation: None,
        },
    )
}
fn function(
    name: &str,
    formal_args: Vec<AnyLocalVarDecl>,
    typ: Type,
    domain: &str,
    meta: &Metadata,
) -> DomainFunc {
    DomainFunc::new(DomainFuncData {
        name: name.into(),
        formal_args,
        typ,
        unique: false,
        interpretation: None,
        domain_name: domain.into(),
        meta: meta.clone(),
    })
}
fn axiom(body: Exp, domain: &str, meta: &Metadata) -> DomainAxiom {
    DomainAxiom::new(DomainAxiomKind::Anonymous {
        exp: body,
        domain_name: domain.into(),
        meta: meta.clone(),
    })
}
fn constructor_vars(c: &AdtConstructor) -> Vec<Exp> {
    c.formal_args
        .iter()
        .map(|a| {
            exp(
                ExpKind::LocalVar(crate::ast::expression::LocalVar::new(
                    a.name.clone(),
                    direct_adt_type(&a.typ),
                    c.meta.clone(),
                )),
                &c.meta,
            )
        })
        .collect()
}
fn quantified(vars: Vec<LocalVarDecl>, trigger: Vec<Exp>, body: Exp, meta: &Metadata) -> Exp {
    exp(
        ExpKind::Forall(vars, vec![Trigger::new(trigger, meta.clone())], body),
        meta,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::program::ExtensionMemberHandle;
    use std::sync::Arc;

    #[test]
    fn whole_program_lowers_adt_application_and_return_type() {
        let meta = Metadata::default();
        let constructor = Arc::new(AdtConstructor::new(
            "Tree",
            vec![],
            "Leaf",
            vec![],
            meta.clone(),
        ));
        let adt = Adt {
            name: "Tree".into(),
            constructors: vec![constructor.clone()],
            type_vars: vec![],
            deriving_info: HashMap::new(),
            meta: meta.clone(),
        };
        let app =
            AdtConstructorApp::new(&constructor, vec![], TypeSubstitution::new(), meta.clone())
                .expression();
        let function = crate::ast::program::Function::new(crate::ast::program::FunctionData {
            name: "leaf".into(),
            formal_args: vec![],
            typ: constructor.typ.clone().as_type(),
            pres: vec![],
            posts: vec![],
            body: Some(app),
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![],
            vec![],
            vec![function],
            vec![],
            vec![],
            vec![ExtensionMemberHandle(Arc::new(adt))],
            meta,
        );
        let result = AdtEncoder::new(program, Vec::<String>::new())
            .encode(false)
            .unwrap();
        assert!(result.extensions.is_empty());
        assert_eq!(result.domains[0].name, "Tree");
        assert!(matches!(&result.functions[0].typ, Type::Domain(d) if d.domain_name == "Tree"));
        let body = result.functions[0].body.as_ref().unwrap();
        assert!(matches!(body.kind(), ExpKind::DomainFuncApp(name, _, _) if name == "Leaf"));
        assert!(matches!(body.typ().unwrap(), Type::Domain(d) if d.domain_name == "Tree"));
    }

    #[test]
    fn well_founded_domain_contains_recursive_constructor_decrease() {
        let meta = Metadata::default();
        let list_type = AdtType::new("List", TypeSubstitution::new(), vec![]).as_type();
        let nil = Arc::new(AdtConstructor::new(
            "List",
            vec![],
            "Nil",
            vec![],
            meta.clone(),
        ));
        let cons = Arc::new(AdtConstructor::new(
            "List",
            vec![],
            "Cons",
            vec![LocalVarDecl::new("tail".into(), list_type, meta.clone())],
            meta.clone(),
        ));
        let adt = Adt {
            name: "List".into(),
            constructors: vec![nil, cons],
            type_vars: vec![],
            deriving_info: HashMap::new(),
            meta: meta.clone(),
        };
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![ExtensionMemberHandle(Arc::new(adt.clone()))],
            meta,
        );
        let domains = AdtEncoder::new(program, Vec::<String>::new())
            .encode_adt_as_domains(&adt, true)
            .unwrap();
        assert_eq!(domains.len(), 2);
        assert_eq!(domains[1].name, "ListWellFoundedOrder");
        assert_eq!(domains[1].axioms.len(), 4);
        let DomainAxiomKind::Anonymous { exp, .. } = domains[1].axioms[1].kind() else {
            panic!()
        };
        assert!(
            matches!(exp.kind(), ExpKind::And(_, q) if matches!(q.kind(), ExpKind::Forall(vars, _, body) if vars[0].name == "tail_0" && matches!(body.kind(), ExpKind::DomainFuncApp(name, _, _) if name == "decreasing")))
        );
    }

    #[test]
    fn contains_transitivity_uses_reachable_concrete_types() {
        let meta = Metadata::default();
        let program = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], meta);
        let domain = AdtEncoder::new(program, Vec::<String>::new())
            .contains_transitivity_domain(vec![(Type::Int, Type::Bool), (Type::Bool, Type::Ref)]);
        assert_eq!(domain.name, "ContainsTransitivityDomain");
        assert_eq!(domain.axioms.len(), 1);
        let DomainAxiomKind::Anonymous { exp, .. } = domain.axioms[0].kind() else {
            panic!()
        };
        let ExpKind::Forall(vars, triggers, body) = exp.kind() else {
            panic!()
        };
        assert_eq!(
            vars.iter().map(|v| v.typ.clone()).collect::<Vec<_>>(),
            vec![Type::Int, Type::Bool, Type::Ref]
        );
        assert_eq!(triggers[0].exps.len(), 2);
        assert!(matches!(body.kind(), ExpKind::Implies(_, _)));
    }

    #[test]
    fn domain_uses_sorted_tags_and_last_constructor_destructor_triggers() {
        let meta = Metadata::default();
        let constructors = vec![
            Arc::new(AdtConstructor::new(
                "Tree",
                vec![],
                "Z",
                vec![LocalVarDecl::new("z".into(), Type::Int, meta.clone())],
                meta.clone(),
            )),
            Arc::new(AdtConstructor::new(
                "Tree",
                vec![],
                "A",
                vec![LocalVarDecl::new("a".into(), Type::Int, meta.clone())],
                meta.clone(),
            )),
        ];
        let adt = Adt {
            name: "Tree".into(),
            constructors,
            type_vars: vec![],
            deriving_info: HashMap::new(),
            meta: meta.clone(),
        };
        let program = Program::new(
            vec![],
            vec![],
            vec![],
            vec![],
            vec![],
            vec![ExtensionMemberHandle(Arc::new(adt.clone()))],
            meta,
        );
        let domain = AdtEncoder::new(program, Vec::<String>::new())
            .encode_adt_as_domain(&adt, false)
            .unwrap();
        assert_eq!(
            domain
                .functions
                .iter()
                .map(|f| f.name.as_str())
                .collect::<Vec<_>>(),
            vec!["Z", "A", "get_Tree_z", "get_Tree_a", "Tree_tag"]
        );
        assert_eq!(domain.axioms.len(), 5);
        let DomainAxiomKind::Anonymous { exp, .. } = domain.axioms[2].kind() else {
            panic!()
        };
        let ExpKind::Forall(_, _, eq) = exp.kind() else {
            panic!()
        };
        assert!(
            matches!(eq.kind(), ExpKind::EqCmp(_, n) if matches!(n.kind(), ExpKind::IntLit(i) if *i == 1.into()))
        );
        let DomainAxiomKind::Anonymous { exp, .. } = domain.axioms[4].kind() else {
            panic!()
        };
        let ExpKind::Forall(_, triggers, _) = exp.kind() else {
            panic!()
        };
        assert_eq!(triggers.len(), 2);
        assert!(
            matches!(triggers[1].exps[0].kind(), ExpKind::DomainFuncApp(name, _, _) if name == "get_Tree_a")
        );
    }
}
