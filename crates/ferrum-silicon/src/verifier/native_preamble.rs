//! Ferrum native verifier domain contributor assembly, as described in PLAN.md.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/Domains.scala
//! Status: partial; source ground closure drives a staged general domain and collection
//! preamble. Unsupported expression, type and precondition paths return explicit errors;
//! verifier admission and broader source compatibility are still under validation.
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::interfaces::decider::prover::ProverLike;
use crate::state::symbol_converter::{DefaultSymbolConverter, SymbolConversionError};
use crate::state::terms::TermFactory;
use crate::supporters::domains::{DefaultDomainsContributor, DomainCollectionError};
use ferrum_silver::ast::{
    program::Program,
    r#type::Type,
    utility::{
        domain_instances::{DomainInstanceError, collect_ground_types},
        nodes::Node,
    },
};

#[derive(Debug)]
pub enum NativePreambleError<E> {
    Unsupported(&'static str),
    GroundTypes(DomainInstanceError),
    Symbol(SymbolConversionError),
    Domain(DomainCollectionError),
    Translation(String),
    Sink(E),
}
/// Collected source-order declarations and uniqueness assumptions for later emission.
#[derive(Default)]
pub struct NativePreambleData {
    domains: DefaultDomainsContributor,
}
impl NativePreambleData {
    /// Ground sorts in the same order as the contributor declarations.
    pub fn sorts(&self) -> impl Iterator<Item = &crate::state::terms::Sort> {
        self.domains.sorts.iter()
    }
    pub fn declare_sorts<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn declare_symbols<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit_axioms<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)?;
        self.domains
            .emit_uniqueness(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.domains
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.domains
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)?;
        self.domains
            .emit_uniqueness(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
}
/// Analyze the safely supported subset before emitting anything. Source uses the
/// ground-type fixed point; without generic domains/collections/axioms its domain
/// instances are exactly the concrete domain types appearing in the program.
pub fn analyze(
    program: &Program,
    converter: &DefaultSymbolConverter,
) -> Result<NativePreambleData, NativePreambleError<std::convert::Infallible>> {
    analyze_domain_slice(
        program, converter, None, false, false, false, false, false, false,
    )
}
/// Analyze and translate the supported non-generic user-domain axioms.
pub fn analyze_with_axioms(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
) -> Result<NativePreambleData, NativePreambleError<std::convert::Infallible>> {
    analyze_domain_slice(
        program,
        converter,
        Some(factory),
        false,
        false,
        false,
        false,
        false,
        false,
    )
}
/// Analyze non-generic axioms and simple generic domains instantiated with
/// atomic types. Generic axioms and recursive generic signatures remain errors.
pub fn analyze_simple_generics(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
) -> Result<NativePreambleData, NativePreambleError<std::convert::Infallible>> {
    analyze_domain_slice(
        program,
        converter,
        Some(factory),
        true,
        false,
        false,
        false,
        false,
        false,
    )
}
/// User-domain analysis when a separate sequence contributor supplies all ground Seq sorts.
pub fn analyze_with_sequences(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
) -> Result<NativePreambleData, NativePreambleError<std::convert::Infallible>> {
    analyze_domain_slice(
        program,
        converter,
        Some(factory),
        true,
        true,
        false,
        false,
        false,
        false,
    )
}
/// User-domain analysis when separate sequence and set contributors supply sorts.
pub fn analyze_with_sequences_and_sets(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
) -> Result<NativePreambleData, NativePreambleError<std::convert::Infallible>> {
    analyze_domain_slice(
        program,
        converter,
        Some(factory),
        true,
        true,
        true,
        false,
        false,
        false,
    )
}
/// User-domain analysis when sequence, set and map contributors supply their sorts.
pub fn analyze_with_maps(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
) -> Result<NativePreambleData, NativePreambleError<std::convert::Infallible>> {
    analyze_domain_slice(
        program,
        converter,
        Some(factory),
        true,
        true,
        true,
        true,
        false,
        false,
    )
}
/// User-domain analysis when all four collection contributors supply their sorts.
pub fn analyze_with_multisets(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
) -> Result<NativePreambleData, NativePreambleError<std::convert::Infallible>> {
    analyze_domain_slice(
        program,
        converter,
        Some(factory),
        true,
        true,
        true,
        true,
        true,
        false,
    )
}
/// Restricted generic axioms: atomic type instances, no foreign-domain calls,
/// collection types or heap-dependent functions.
pub fn analyze_generic_axioms(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
) -> Result<NativePreambleData, NativePreambleError<std::convert::Infallible>> {
    analyze_domain_slice(
        program,
        converter,
        Some(factory),
        true,
        false,
        false,
        false,
        false,
        true,
    )
}
fn validate_generic_axiom(
    node: &Node,
    domain_name: &str,
) -> Result<(), NativePreambleError<std::convert::Infallible>> {
    use ferrum_silver::ast::{expression::ExpKind, utility::nodes::subnodes};
    match node {
        Node::Type(typ)
            if matches!(
                typ,
                Type::Seq(_) | Type::Set(_) | Type::Multiset(_) | Type::Map(_) | Type::Extension(_)
            ) =>
        {
            return Err(NativePreambleError::Unsupported(
                "generic axiom collection type",
            ));
        }
        Node::Type(Type::Domain(domain)) if domain.domain_name != domain_name => {
            return Err(NativePreambleError::Unsupported(
                "generic axiom foreign domain type",
            ));
        }
        Node::Type(Type::Domain(domain))
            if domain.type_arguments().iter().any(|typ| {
                !matches!(
                    typ,
                    Type::Var(_) | Type::Int | Type::Bool | Type::Ref | Type::Perm
                )
            }) =>
        {
            return Err(NativePreambleError::Unsupported(
                "generic axiom nested domain argument",
            ));
        }
        Node::Exp(e) => match e.kind() {
            ExpKind::FuncApp(..) | ExpKind::BackendFuncApp(..) => {
                return Err(NativePreambleError::Unsupported(
                    "generic axiom function call",
                ));
            }
            ExpKind::DomainFuncApp(..) if e.0.extra.domain_name.as_deref() != Some(domain_name) => {
                return Err(NativePreambleError::Unsupported(
                    "generic axiom foreign domain function",
                ));
            }
            _ => {}
        },
        _ => {}
    }
    for child in subnodes(node).map_err(|e| NativePreambleError::Translation(format!("{e:?}")))? {
        validate_generic_axiom(&child, domain_name)?;
    }
    Ok(())
}
fn analyze_domain_slice(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: Option<&TermFactory>,
    allow_simple_generics: bool,
    allow_sequences: bool,
    allow_sets: bool,
    allow_maps: bool,
    allow_multisets: bool,
    allow_generic_axioms: bool,
) -> Result<NativePreambleData, NativePreambleError<std::convert::Infallible>> {
    for domain in &program.domains {
        if !domain.type_vars.is_empty() {
            if !allow_simple_generics || (!allow_generic_axioms && !domain.axioms.is_empty()) {
                return Err(NativePreambleError::Unsupported(
                    "generic domain instantiation or axioms",
                ));
            }
            if allow_generic_axioms {
                for axiom in &domain.axioms {
                    validate_generic_axiom(&Node::Exp(axiom.exp().clone()), &domain.name)?;
                }
            }
            let simple = |typ: &Type| {
                matches!(
                    typ,
                    Type::Var(_) | Type::Int | Type::Bool | Type::Ref | Type::Perm
                )
            };
            if domain
                .functions
                .iter()
                .any(|f| !simple(&f.typ) || f.formal_args.iter().any(|a| !simple(a.typ())))
            {
                return Err(NativePreambleError::Unsupported(
                    "recursive or collection generic signature",
                ));
            }
        }
    }
    if factory.is_none() && program.domains.iter().any(|d| !d.axioms.is_empty()) {
        return Err(NativePreambleError::Unsupported("domain axiom translation"));
    }
    let ground = collect_ground_types(&Node::Program(program.clone()), program)
        .map_err(NativePreambleError::GroundTypes)?;
    for root in &ground {
        for typ in ferrum_silver::ast::utility::domain_instances::down_closure_ground(root)
            .map_err(NativePreambleError::GroundTypes)?
        {
            if (!allow_multisets && matches!(typ, Type::Multiset(_)))
                || (!allow_maps && matches!(typ, Type::Map(_)))
                || (!allow_sequences && matches!(typ, Type::Seq(_)))
                || (!allow_sets && matches!(typ, Type::Set(_)))
            {
                return Err(NativePreambleError::Unsupported(
                    "collection domain analysis",
                ));
            }
        }
    }
    let mut result = NativePreambleData::default();
    for domain in &program.domains {
        let instances = ground
            .iter()
            .filter_map(|t| match t {
                Type::Domain(d) if d.domain_name == domain.name => Some(d),
                _ => None,
            })
            .collect::<Vec<_>>();
        for instance in instances {
            let substitution = instance.type_vars_map();
            if substitution
                .values()
                .any(|t| !matches!(t, Type::Int | Type::Bool | Type::Ref | Type::Perm))
            {
                return Err(NativePreambleError::Unsupported(
                    "non-atomic generic domain instance",
                ));
            }
            let sort = converter
                .to_sort(&Type::Domain(instance.clone()))
                .map_err(NativePreambleError::Symbol)?;
            result.domains.sorts = result.domains.sorts.incl(sort);
            for function in &domain.functions {
                if function.interpretation.is_some() {
                    continue;
                }
                let instantiated = if substitution.is_empty() {
                    function.clone()
                } else {
                    function.copy_with(|data| {
                        data.typ = data.typ.substitute(&substitution);
                        data.formal_args = data
                            .formal_args
                            .iter()
                            .map(|arg| match arg {
                                ferrum_silver::ast::program::AnyLocalVarDecl::Named(v) => {
                                    ferrum_silver::ast::program::AnyLocalVarDecl::Named(
                                        ferrum_silver::ast::program::LocalVarDecl::new(
                                            v.name.clone(),
                                            v.typ.substitute(&substitution),
                                            v.meta.clone(),
                                        ),
                                    )
                                }
                                ferrum_silver::ast::program::AnyLocalVarDecl::Unnamed(v) => {
                                    ferrum_silver::ast::program::AnyLocalVarDecl::Unnamed(
                                        v.copy_with(|d| d.typ = d.typ.substitute(&substitution)),
                                    )
                                }
                            })
                            .collect();
                    })
                };
                let applicable = converter
                    .domain_function(&instantiated, program)
                    .map_err(NativePreambleError::Symbol)?;
                result
                    .domains
                    .collect_function(applicable, instantiated.unique)
                    .map_err(NativePreambleError::Domain)?;
            }
            if let Some(factory) = factory {
                let mut translator =
                    crate::supporters::expression_translator::ExpressionTranslator::new(
                        factory,
                        converter,
                        |sort: &crate::state::terms::Sort| {
                            Ok::<_, std::convert::Infallible>(sort.to_string())
                        },
                    );
                translator.type_substitution = Some(&substitution);
                for axiom in &domain.axioms {
                    let mut term = translator
                        .translate(axiom.exp())
                        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
                    if let crate::state::terms::TermKind::Quantification {
                        quantifier,
                        vars,
                        body,
                        triggers,
                        name,
                        weight,
                        ..
                    } = term.kind()
                    {
                        if name.is_empty() {
                            let qid = match axiom.kind() {
                                ferrum_silver::ast::program::DomainAxiomKind::Named {
                                    name,
                                    ..
                                } => format!("prog.{name}"),
                                _ => String::new(),
                            };
                            term = factory
                                .quantification(
                                    *quantifier,
                                    vars.clone(),
                                    body.clone(),
                                    triggers.clone(),
                                    qid,
                                    false,
                                    *weight,
                                )
                                .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
                        }
                    }
                    result
                        .domains
                        .collect_axiom(factory, term, &mut |_| {
                            Err::<crate::state::terms::Applicable, _>(
                                "heap-dependent function in domain axiom",
                            )
                        })
                        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
                }
            }
        }
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::terms::{Sort, TermOptions};
    use ferrum_silver::ast::{
        ast::Metadata,
        program::{
            Domain, DomainData, DomainFunc, DomainFuncData, LocalVarDecl, Method, MethodData,
        },
        r#type::DomainType,
    };
    #[test]
    fn generic_domain_axiom_is_instantiated_for_atomic_type() {
        let source = "domain D[T] { function id(x: T): T axiom identity { forall x: T :: { id(x) } id(x) == x } } method m(d: D[Int]) {}";
        let parsed =
            ferrum_silver::parser::fast_parser::parse_program(source, "generic.vpr").unwrap();
        ferrum_silver::parser::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(
            ferrum_silver::parser::resolver::NameAnalyser::default()
                .run(parsed.node())
                .unwrap()
        );
        ferrum_silver::parser::resolver::check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let program = ferrum_silver::parser::translator::translate_program_core(&parsed).unwrap();
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        assert!(matches!(
            analyze_simple_generics(&program, &converter, &factory),
            Err(NativePreambleError::Unsupported(_))
        ));
        let general = analyze_general(&program, &converter, &factory, false, 1).unwrap();
        assert_eq!(general.domains.domains.axioms.len(), 1);
        let result = analyze_generic_axioms(&program, &converter, &factory).unwrap();
        assert_eq!(result.domains.axioms.len(), 1);
        let mut smt =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in &result.domains.axioms {
            smt.convert_term(axiom).unwrap();
        }
    }
    #[test]
    fn simple_generic_domain_instantiates_function_signature() {
        use ferrum_silver::ast::{program::AnyLocalVarDecl, r#type::TypeVar};
        let meta = Metadata::default();
        let parameter = TypeVar::new("T");
        let argument = LocalVarDecl::new("x".into(), Type::Var(parameter.clone()), meta.clone());
        let function = DomainFunc::new(DomainFuncData {
            name: "id".into(),
            formal_args: vec![AnyLocalVarDecl::Named(argument)],
            typ: Type::Var(parameter.clone()),
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![function],
            axioms: vec![],
            type_vars: vec![parameter.clone()],
            interpretations: None,
            meta: meta.clone(),
        });
        let typ = Type::Domain(DomainType::new(
            "D",
            [(parameter.clone(), Type::Int)].into_iter().collect(),
            vec![parameter],
        ));
        let var = LocalVarDecl::new("d".into(), typ, meta.clone());
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![var],
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
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let analyzed = analyze_simple_generics(&program, &converter, &factory).unwrap();
        let function = analyzed.domains.functions.iter().next().unwrap();
        assert_eq!(function.data().arg_sorts, vec![Sort::Int]);
        assert_eq!(function.data().result_sort, Sort::Int);
    }
    #[test]
    fn translates_ground_domain_axiom_and_rejects_legacy_axiom_free_api() {
        use ferrum_silver::ast::{
            expression::{Exp, ExpExtra, ExpKind},
            program::{DomainAxiom, DomainAxiomKind},
        };
        let meta = Metadata::default();
        let function = DomainFunc::new(DomainFuncData {
            name: "zero".into(),
            formal_args: vec![],
            typ: Type::Int,
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let app = Exp::with_extra(
            ExpKind::DomainFuncApp("zero".into(), vec![], Default::default()),
            meta.clone(),
            ExpExtra {
                typ: Some(Type::Int),
                domain_name: Some("D".into()),
                ..Default::default()
            },
        );
        let expr = Exp::new(
            ExpKind::EqCmp(app, Exp::new(ExpKind::IntLit(0.into()), meta.clone())),
            meta.clone(),
        );
        let axiom = DomainAxiom::new(DomainAxiomKind::Named {
            name: "zero_is_zero".into(),
            exp: expr,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![function],
            axioms: vec![axiom],
            type_vars: vec![],
            interpretations: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![domain], vec![], vec![], vec![], vec![], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        assert!(matches!(
            analyze(&program, &converter),
            Err(NativePreambleError::Unsupported("domain axiom translation"))
        ));
        let analyzed = analyze_with_axioms(&program, &converter, &factory).unwrap();
        assert_eq!(analyzed.domains.sorts.len(), 1);
        assert_eq!(analyzed.domains.functions.len(), 1);
        assert_eq!(analyzed.domains.axioms.len(), 1);
    }
    #[test]
    fn nullary_domain_application_induces_domain_instance() {
        use ferrum_silver::ast::{
            expression::{Exp, ExpExtra, ExpKind},
            statement::{Stmt, StmtKind},
        };
        let meta = Metadata::default();
        let function = DomainFunc::new(DomainFuncData {
            name: "zero".into(),
            formal_args: vec![],
            typ: Type::Int,
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![function],
            axioms: vec![],
            type_vars: vec![],
            interpretations: None,
            meta: meta.clone(),
        });
        let app = Exp::with_extra(
            ExpKind::DomainFuncApp("zero".into(), vec![], Default::default()),
            meta.clone(),
            ExpExtra {
                typ: Some(Type::Int),
                domain_name: Some("D".into()),
                ..Default::default()
            },
        );
        let assertion = Exp::new(
            ExpKind::EqCmp(app, Exp::new(ExpKind::IntLit(0.into()), meta.clone())),
            meta.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: Some(Stmt::new(StmtKind::Assert(assertion), meta.clone())),
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
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory, false);
        let analyzed = analyze(&program, &converter).unwrap();
        assert_eq!(analyzed.domains.sorts.len(), 1);
        assert_eq!(analyzed.domains.functions.len(), 1);
    }
    #[test]
    fn collects_ground_domain_symbols_and_unique_axioms() {
        let meta = Metadata::default();
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![DomainFunc::new(DomainFuncData {
                name: "zero".into(),
                formal_args: vec![],
                typ: Type::Int,
                unique: true,
                interpretation: None,
                domain_name: "D".into(),
                meta: meta.clone(),
            })],
            axioms: vec![],
            type_vars: vec![],
            interpretations: None,
            meta: meta.clone(),
        });
        let typ = Type::Domain(DomainType::new("D", Default::default(), vec![]));
        let parameter = LocalVarDecl::new("x".into(), typ, meta.clone());
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![parameter],
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
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let analyzed = analyze(&program, &converter).unwrap();
        assert_eq!(analyzed.domains.sorts.len(), 1);
        assert_eq!(analyzed.domains.functions.len(), 1);
        assert_eq!(
            analyzed
                .domains
                .functions
                .iter()
                .next()
                .unwrap()
                .data()
                .result_sort,
            Sort::Int
        );
        assert_eq!(analyzed.domains.uniqueness_assumptions(&factory).len(), 1);
    }
}

/// Parsed builtin sequence source, instantiated and translated before solver emission.
/// Collection analysis is intentionally separate from the checked user-domain profile.
pub struct NativeSequencePreamble {
    contributor: crate::supporters::builtin_domains_contributor::BuiltinDomainsContributor,
}
impl NativeSequencePreamble {
    pub fn sorts(&self) -> impl Iterator<Item = &crate::state::terms::Sort> {
        self.contributor.sorts.iter()
    }
    pub fn declare_sorts<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn declare_symbols<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit_axioms<P: ProverLike>(
        &self,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.contributor
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.contributor
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)
    }
}
/// Build actual sequence axioms for direct ground sequence instances. Programs
/// with user-defined generic domains are rejected until the full ground-instance
/// fixed point is available. The source is parsed only when an instance exists.
pub fn analyze_sequences(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
) -> Result<NativeSequencePreamble, NativePreambleError<std::convert::Infallible>> {
    analyze_sequences_inner(program, converter, factory, old_axiomatization, false, None)
}
fn analyze_sequences_inner(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    mixed: bool,
    closed_ground: Option<&std::collections::HashSet<Type>>,
) -> Result<NativeSequencePreamble, NativePreambleError<std::convert::Infallible>> {
    use crate::state::symbol_converter::BuiltinDomainSort;
    use crate::supporters::{
        builtin_domains_contributor::BuiltinDomainsContributor,
        default_sequences_contributor as sequences,
    };
    use ferrum_silver::ast::{
        program::{AnyLocalVarDecl, DomainAxiomKind, LocalVarDecl},
        utility::domain_instances::down_closure_ground,
    };
    if closed_ground.is_none()
        && program
            .domains
            .iter()
            .any(|domain| !domain.type_vars.is_empty())
    {
        return Err(NativePreambleError::Unsupported(
            "sequence ground instances with generic user domains",
        ));
    }
    let ground = match closed_ground {
        Some(ground) => ground.clone(),
        None => collect_ground_types(&Node::Program(program.clone()), program)
            .map_err(NativePreambleError::GroundTypes)?,
    };
    fn supported_element(typ: &Type) -> bool {
        match typ {
            Type::Int | Type::Bool | Type::Ref | Type::Perm => true,
            Type::Seq(inner) => supported_element(inner),
            _ => false,
        }
    }
    let mut instances = std::collections::HashSet::new();
    for root in &ground {
        for typ in down_closure_ground(root).map_err(NativePreambleError::GroundTypes)? {
            if let Type::Seq(element) = typ {
                if !(supported_element(&element)
                    || mixed && mixed_collection_type(&element, closed_ground.is_some()))
                {
                    return Err(NativePreambleError::Unsupported(
                        "sequence element requires another contributor",
                    ));
                }
                instances.insert((*element).clone());
            }
        }
    }
    let mut contributor = BuiltinDomainsContributor::default();
    if instances.is_empty() {
        return Ok(NativeSequencePreamble { contributor });
    }
    let path = sequences::source_resource(old_axiomatization);
    let source = crate::resources::bundled::get(path)
        .ok_or(NativePreambleError::Unsupported("missing sequence source"))?;
    let parsed = ferrum_silver::parser::fast_parser::parse_program(source, path)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    ferrum_silver::parser::parse_ast::init_properties(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    if !ferrum_silver::parser::resolver::NameAnalyser::default()
        .run(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
    {
        return Err(NativePreambleError::Unsupported(
            "sequence source name resolution",
        ));
    }
    ferrum_silver::parser::resolver::check_program_core(&parsed, &mut |_, _| {})
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    let builtin_program = ferrum_silver::parser::translator::translate_program_core(&parsed)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    let source_domain = builtin_program
        .find_domain_optionally(sequences::SOURCE_DOMAIN_NAME)
        .ok_or(NativePreambleError::Unsupported("sequence source domain"))?;
    if source_domain.type_vars.len() != 1 {
        return Err(NativePreambleError::Unsupported(
            "sequence source domain arity",
        ));
    }
    let builtin_converter = converter
        .clone()
        .with_builtin_domain(sequences::SOURCE_DOMAIN_NAME, BuiltinDomainSort::Sequence);
    let mut instances = instances.into_iter().collect::<Vec<_>>();
    fn nesting(typ: &Type) -> usize {
        match typ {
            Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => 1 + nesting(t),
            _ => 0,
        }
    }
    instances.sort_by_key(nesting);
    for element in instances {
        let substitution = [(source_domain.type_vars[0].clone(), element.clone())]
            .into_iter()
            .collect();
        let instantiated = sequences::transform_source_domain_instance(source_domain, &element);
        let element_sort = builtin_converter
            .to_sort(&element)
            .map_err(NativePreambleError::Symbol)?;
        contributor.sorts = contributor
            .sorts
            .incl(crate::state::terms::Sort::Seq(Box::new(
                element_sort.clone(),
            )));
        for function in &instantiated.functions {
            if function.interpretation.is_some() {
                continue;
            }
            let function = function.copy_with(|data| {
                data.typ = data.typ.substitute(&substitution);
                data.formal_args = data
                    .formal_args
                    .iter()
                    .map(|arg| match arg {
                        AnyLocalVarDecl::Named(v) => AnyLocalVarDecl::Named(LocalVarDecl::new(
                            v.name.clone(),
                            v.typ.substitute(&substitution),
                            v.meta.clone(),
                        )),
                        AnyLocalVarDecl::Unnamed(v) => AnyLocalVarDecl::Unnamed(
                            v.copy_with(|d| d.typ = d.typ.substitute(&substitution)),
                        ),
                    })
                    .collect();
            });
            let applicable = builtin_converter
                .domain_function(&function, program)
                .map_err(NativePreambleError::Symbol)?;
            contributor.functions = contributor.functions.incl(applicable);
        }
        let mut translator = crate::supporters::expression_translator::ExpressionTranslator::new(
            factory,
            &builtin_converter,
            |s: &crate::state::terms::Sort| Ok::<_, std::convert::Infallible>(s.to_string()),
        );
        translator.builtin = true;
        translator.type_substitution = Some(&substitution);
        for axiom in &instantiated.axioms {
            let mut term = translator
                .translate(axiom.exp())
                .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
            if let crate::state::terms::TermKind::Quantification {
                quantifier,
                vars,
                body,
                triggers,
                name,
                weight,
                ..
            } = term.kind()
            {
                if name.is_empty() {
                    let name = match axiom.kind() {
                        DomainAxiomKind::Named { name, .. } => {
                            format!("$Seq[{element_sort}]_prog.{name}")
                        }
                        _ => String::new(),
                    };
                    term = factory
                        .quantification(
                            *quantifier,
                            vars.clone(),
                            body.clone(),
                            triggers.clone(),
                            name,
                            false,
                            *weight,
                        )
                        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
                }
            }
            contributor.axioms = contributor.axioms.incl(term);
        }
    }
    Ok(NativeSequencePreamble { contributor })
}

/// Parsed builtin set source, instantiated and translated before solver emission.
/// Collection analysis is intentionally separate from the checked user-domain profile.
pub struct NativeSetPreamble {
    contributor: crate::supporters::builtin_domains_contributor::BuiltinDomainsContributor,
}
impl NativeSetPreamble {
    pub fn sorts(&self) -> impl Iterator<Item = &crate::state::terms::Sort> {
        self.contributor.sorts.iter()
    }
    pub fn declare_sorts<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn declare_symbols<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit_axioms<P: ProverLike>(
        &self,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.contributor
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.contributor
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)
    }
}
/// Build actual set axioms for direct ground set instances. Programs
/// with user-defined generic domains are rejected until the full ground-instance
/// fixed point is available. The source is parsed only when an instance exists.
pub fn analyze_sets(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
) -> Result<NativeSetPreamble, NativePreambleError<std::convert::Infallible>> {
    analyze_sets_inner(
        program,
        converter,
        factory,
        old_axiomatization,
        false,
        false,
        None,
    )
}
/// Include set sorts induced by map domain/range when a map contributor is active.
pub fn analyze_sets_with_maps(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
) -> Result<NativeSetPreamble, NativePreambleError<std::convert::Infallible>> {
    analyze_sets_inner(
        program,
        converter,
        factory,
        old_axiomatization,
        true,
        false,
        None,
    )
}
fn analyze_sets_inner(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    allow_maps: bool,
    mixed: bool,
    closed_ground: Option<&std::collections::HashSet<Type>>,
) -> Result<NativeSetPreamble, NativePreambleError<std::convert::Infallible>> {
    use crate::state::symbol_converter::BuiltinDomainSort;
    use crate::supporters::{
        builtin_domains_contributor::BuiltinDomainsContributor, default_sets_contributor as sets,
    };
    use ferrum_silver::ast::{
        program::{AnyLocalVarDecl, DomainAxiomKind, LocalVarDecl},
        utility::domain_instances::down_closure_ground,
    };
    if closed_ground.is_none()
        && program
            .domains
            .iter()
            .any(|domain| !domain.type_vars.is_empty())
    {
        return Err(NativePreambleError::Unsupported(
            "set ground instances with generic user domains",
        ));
    }
    let ground = match closed_ground {
        Some(ground) => ground.clone(),
        None => collect_ground_types(&Node::Program(program.clone()), program)
            .map_err(NativePreambleError::GroundTypes)?,
    };
    fn supported_element(typ: &Type) -> bool {
        match typ {
            Type::Int | Type::Bool | Type::Ref | Type::Perm => true,
            Type::Set(inner) => supported_element(inner),
            _ => false,
        }
    }
    let mut instances = std::collections::HashSet::new();
    for root in &ground {
        for typ in down_closure_ground(root).map_err(NativePreambleError::GroundTypes)? {
            if let Type::Map(pair) = &typ {
                if !allow_maps
                    || !(supported_element(&pair.0)
                        || mixed && mixed_collection_type(&pair.0, closed_ground.is_some()))
                    || !(supported_element(&pair.1)
                        || mixed && mixed_collection_type(&pair.1, closed_ground.is_some()))
                {
                    return Err(NativePreambleError::Unsupported(
                        "set instances induced by map domains",
                    ));
                }
                instances.insert(pair.0.clone());
                instances.insert(pair.1.clone());
            }
            if let Type::Set(element) = typ {
                if !(supported_element(&element)
                    || mixed && mixed_collection_type(&element, closed_ground.is_some()))
                {
                    return Err(NativePreambleError::Unsupported(
                        "set element requires another contributor",
                    ));
                }
                instances.insert((*element).clone());
            }
        }
    }
    let mut contributor = BuiltinDomainsContributor::default();
    if instances.is_empty() {
        return Ok(NativeSetPreamble { contributor });
    }
    let path = sets::source_resource(old_axiomatization);
    let source = crate::resources::bundled::get(path)
        .ok_or(NativePreambleError::Unsupported("missing set source"))?;
    let parsed = ferrum_silver::parser::fast_parser::parse_program(source, path)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    ferrum_silver::parser::parse_ast::init_properties(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    if !ferrum_silver::parser::resolver::NameAnalyser::default()
        .run(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
    {
        return Err(NativePreambleError::Unsupported(
            "set source name resolution",
        ));
    }
    ferrum_silver::parser::resolver::check_program_core(&parsed, &mut |_, _| {})
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    let builtin_program = ferrum_silver::parser::translator::translate_program_core(&parsed)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    let source_domain = builtin_program
        .find_domain_optionally(sets::SOURCE_DOMAIN_NAME)
        .ok_or(NativePreambleError::Unsupported("set source domain"))?;
    if source_domain.type_vars.len() != 1 {
        return Err(NativePreambleError::Unsupported("set source domain arity"));
    }
    let builtin_converter = converter
        .clone()
        .with_builtin_domain(sets::SOURCE_DOMAIN_NAME, BuiltinDomainSort::Set);
    let mut instances = instances.into_iter().collect::<Vec<_>>();
    fn nesting(typ: &Type) -> usize {
        match typ {
            Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => 1 + nesting(t),
            _ => 0,
        }
    }
    instances.sort_by_key(nesting);
    for element in instances {
        let substitution = [(source_domain.type_vars[0].clone(), element.clone())]
            .into_iter()
            .collect();
        let instantiated = source_domain.clone();
        let element_sort = builtin_converter
            .to_sort(&element)
            .map_err(NativePreambleError::Symbol)?;
        contributor.sorts = contributor
            .sorts
            .incl(crate::state::terms::Sort::Set(Box::new(
                element_sort.clone(),
            )));
        for function in &instantiated.functions {
            if function.interpretation.is_some() {
                continue;
            }
            let function = function.copy_with(|data| {
                data.typ = data.typ.substitute(&substitution);
                data.formal_args = data
                    .formal_args
                    .iter()
                    .map(|arg| match arg {
                        AnyLocalVarDecl::Named(v) => AnyLocalVarDecl::Named(LocalVarDecl::new(
                            v.name.clone(),
                            v.typ.substitute(&substitution),
                            v.meta.clone(),
                        )),
                        AnyLocalVarDecl::Unnamed(v) => AnyLocalVarDecl::Unnamed(
                            v.copy_with(|d| d.typ = d.typ.substitute(&substitution)),
                        ),
                    })
                    .collect();
            });
            let applicable = builtin_converter
                .domain_function(&function, program)
                .map_err(NativePreambleError::Symbol)?;
            contributor.functions = contributor.functions.incl(applicable);
        }
        let mut translator = crate::supporters::expression_translator::ExpressionTranslator::new(
            factory,
            &builtin_converter,
            |s: &crate::state::terms::Sort| Ok::<_, std::convert::Infallible>(s.to_string()),
        );
        translator.builtin = true;
        translator.type_substitution = Some(&substitution);
        for axiom in &instantiated.axioms {
            let mut term = translator
                .translate(axiom.exp())
                .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
            if let crate::state::terms::TermKind::Quantification {
                quantifier,
                vars,
                body,
                triggers,
                name,
                weight,
                ..
            } = term.kind()
            {
                if name.is_empty() {
                    let name = match axiom.kind() {
                        DomainAxiomKind::Named { name, .. } => {
                            format!("$Set[{element_sort}]_prog.{name}")
                        }
                        _ => String::new(),
                    };
                    term = factory
                        .quantification(
                            *quantifier,
                            vars.clone(),
                            body.clone(),
                            triggers.clone(),
                            name,
                            false,
                            *weight,
                        )
                        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
                }
            }
            contributor.axioms = contributor.axioms.incl(term);
        }
    }
    Ok(NativeSetPreamble { contributor })
}

/// Parsed builtin map source, instantiated and translated before solver emission.
/// Collection analysis is intentionally separate from the checked user-domain profile.
pub struct NativeMapPreamble {
    contributor: crate::supporters::builtin_domains_contributor::BuiltinDomainsContributor,
}
impl NativeMapPreamble {
    pub fn sorts(&self) -> impl Iterator<Item = &crate::state::terms::Sort> {
        self.contributor.sorts.iter()
    }
    pub fn declare_sorts<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn declare_symbols<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit_axioms<P: ProverLike>(
        &self,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.contributor
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.contributor
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)
    }
}
/// Build actual map axioms for direct ground map instances. Programs
/// with user-defined generic domains are rejected until the full ground-instance
/// fixed point is available. The source is parsed only when an instance exists.
pub fn analyze_maps(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
) -> Result<NativeMapPreamble, NativePreambleError<std::convert::Infallible>> {
    analyze_maps_inner(program, converter, factory, old_axiomatization, false, None)
}
fn analyze_maps_inner(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    mixed: bool,
    closed_ground: Option<&std::collections::HashSet<Type>>,
) -> Result<NativeMapPreamble, NativePreambleError<std::convert::Infallible>> {
    use crate::state::symbol_converter::BuiltinDomainSort;
    use crate::supporters::{
        builtin_domains_contributor::BuiltinDomainsContributor, default_maps_contributor as maps,
    };
    use ferrum_silver::ast::{
        program::{AnyLocalVarDecl, DomainAxiomKind, LocalVarDecl},
        utility::domain_instances::down_closure_ground,
    };
    if closed_ground.is_none()
        && program
            .domains
            .iter()
            .any(|domain| !domain.type_vars.is_empty())
    {
        return Err(NativePreambleError::Unsupported(
            "map ground instances with generic user domains",
        ));
    }
    let ground = match closed_ground {
        Some(ground) => ground.clone(),
        None => collect_ground_types(&Node::Program(program.clone()), program)
            .map_err(NativePreambleError::GroundTypes)?,
    };
    fn supported_element(typ: &Type) -> bool {
        matches!(typ, Type::Int | Type::Bool | Type::Ref | Type::Perm)
    }
    let mut instances = std::collections::HashSet::new();
    for root in &ground {
        for typ in down_closure_ground(root).map_err(NativePreambleError::GroundTypes)? {
            if let Type::Map(pair) = typ {
                if !(supported_element(&pair.0)
                    || mixed && mixed_collection_type(&pair.0, closed_ground.is_some()))
                    || !(supported_element(&pair.1)
                        || mixed && mixed_collection_type(&pair.1, closed_ground.is_some()))
                {
                    return Err(NativePreambleError::Unsupported(
                        "map key/value requires another contributor",
                    ));
                }
                instances.insert((pair.0.clone(), pair.1.clone()));
            }
        }
    }
    let mut contributor = BuiltinDomainsContributor::default();
    if instances.is_empty() {
        return Ok(NativeMapPreamble { contributor });
    }
    let path = maps::source_resource(old_axiomatization);
    let source = crate::resources::bundled::get(path)
        .ok_or(NativePreambleError::Unsupported("missing map source"))?;
    let parsed = ferrum_silver::parser::fast_parser::parse_program(source, path)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    ferrum_silver::parser::parse_ast::init_properties(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    if !ferrum_silver::parser::resolver::NameAnalyser::default()
        .run(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
    {
        return Err(NativePreambleError::Unsupported(
            "map source name resolution",
        ));
    }
    ferrum_silver::parser::resolver::check_program_core(&parsed, &mut |_, _| {})
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    let builtin_program = ferrum_silver::parser::translator::translate_program_core(&parsed)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    let source_domain = builtin_program
        .find_domain_optionally(maps::SOURCE_DOMAIN_NAME)
        .ok_or(NativePreambleError::Unsupported("map source domain"))?;
    if source_domain.type_vars.len() != 2 {
        return Err(NativePreambleError::Unsupported("map source domain arity"));
    }
    let builtin_converter = converter
        .clone()
        .with_builtin_domain(maps::SOURCE_DOMAIN_NAME, BuiltinDomainSort::Map);
    for (key, value) in instances {
        let substitution = [
            (source_domain.type_vars[0].clone(), key.clone()),
            (source_domain.type_vars[1].clone(), value.clone()),
        ]
        .into_iter()
        .collect();
        let instantiated = source_domain.clone();
        let key_sort = builtin_converter
            .to_sort(&key)
            .map_err(NativePreambleError::Symbol)?;
        let value_sort = builtin_converter
            .to_sort(&value)
            .map_err(NativePreambleError::Symbol)?;
        contributor.sorts = contributor.sorts.incl(crate::state::terms::Sort::Map(
            Box::new(key_sort.clone()),
            Box::new(value_sort.clone()),
        ));
        for function in &instantiated.functions {
            if function.interpretation.is_some() {
                continue;
            }
            let function = function.copy_with(|data| {
                data.typ = data.typ.substitute(&substitution);
                data.formal_args = data
                    .formal_args
                    .iter()
                    .map(|arg| match arg {
                        AnyLocalVarDecl::Named(v) => AnyLocalVarDecl::Named(LocalVarDecl::new(
                            v.name.clone(),
                            v.typ.substitute(&substitution),
                            v.meta.clone(),
                        )),
                        AnyLocalVarDecl::Unnamed(v) => AnyLocalVarDecl::Unnamed(
                            v.copy_with(|d| d.typ = d.typ.substitute(&substitution)),
                        ),
                    })
                    .collect();
            });
            let applicable = builtin_converter
                .domain_function(&function, program)
                .map_err(NativePreambleError::Symbol)?;
            contributor.functions = contributor.functions.incl(applicable);
        }
        let mut translator = crate::supporters::expression_translator::ExpressionTranslator::new(
            factory,
            &builtin_converter,
            |s: &crate::state::terms::Sort| Ok::<_, std::convert::Infallible>(s.to_string()),
        );
        translator.builtin = true;
        translator.type_substitution = Some(&substitution);
        for axiom in &instantiated.axioms {
            let mut term = translator
                .translate(axiom.exp())
                .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
            if let crate::state::terms::TermKind::Quantification {
                quantifier,
                vars,
                body,
                triggers,
                name,
                weight,
                ..
            } = term.kind()
            {
                if name.is_empty() {
                    let name = match axiom.kind() {
                        DomainAxiomKind::Named { name, .. } => {
                            format!("$Map[{key_sort},{value_sort}]_prog.{name}")
                        }
                        _ => String::new(),
                    };
                    term = factory
                        .quantification(
                            *quantifier,
                            vars.clone(),
                            body.clone(),
                            triggers.clone(),
                            name,
                            false,
                            *weight,
                        )
                        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
                }
            }
            contributor.axioms = contributor.axioms.incl(term);
        }
    }
    Ok(NativeMapPreamble { contributor })
}

/// Parsed builtin multiset source, instantiated and translated before solver emission.
/// Collection analysis is intentionally separate from the checked user-domain profile.
pub struct NativeMultisetPreamble {
    contributor: crate::supporters::builtin_domains_contributor::BuiltinDomainsContributor,
}
impl NativeMultisetPreamble {
    pub fn sorts(&self) -> impl Iterator<Item = &crate::state::terms::Sort> {
        self.contributor.sorts.iter()
    }
    pub fn declare_sorts<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn declare_symbols<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit_axioms<P: ProverLike>(
        &self,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.contributor
            .declare_sorts(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.contributor
            .declare_symbols(factory, prover)
            .map_err(NativePreambleError::Sink)?;
        self.contributor
            .emit_axioms(prover)
            .map_err(NativePreambleError::Sink)
    }
}
// A mixed contributor is only safe when every nested sort is assembled together.
fn mixed_collection_type(typ: &Type, allow_domains: bool) -> bool {
    match typ {
        Type::Int | Type::Bool | Type::Ref | Type::Perm => true,
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => mixed_collection_type(t, allow_domains),
        Type::Map(pair) => {
            mixed_collection_type(&pair.0, allow_domains)
                && mixed_collection_type(&pair.1, allow_domains)
        }
        Type::Domain(domain) => {
            allow_domains
                && domain
                    .type_arguments()
                    .iter()
                    .all(|t| mixed_collection_type(t, allow_domains))
        }
        _ => false,
    }
}

/// All collection contributors required by a program with mixed collection nesting.
pub struct NativeCollectionsPreamble {
    pub sequences: NativeSequencePreamble,
    pub sets: NativeSetPreamble,
    pub multisets: NativeMultisetPreamble,
    pub maps: NativeMapPreamble,
}

impl NativeCollectionsPreamble {
    pub fn sorts(&self) -> impl Iterator<Item = &crate::state::terms::Sort> {
        use crate::state::terms::Sort;
        fn depth(sort: &Sort) -> usize {
            match sort {
                Sort::Seq(t) | Sort::Set(t) | Sort::Multiset(t) => 1 + depth(t),
                Sort::Map(k, v) => 1 + depth(k).max(depth(v)),
                _ => 0,
            }
        }
        let mut sorts = self
            .sequences
            .sorts()
            .chain(self.sets.sorts())
            .chain(self.multisets.sorts())
            .chain(self.maps.sorts())
            .collect::<Vec<_>>();
        sorts.sort_by_key(|s| depth(s));
        sorts.into_iter()
    }
    pub fn declare_sorts<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        for sort in self.sorts() {
            prover
                .declare(&factory.sort_decl(sort.clone()))
                .map_err(NativePreambleError::Sink)?;
        }
        Ok(())
    }
    pub fn declare_symbols<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.sequences.declare_symbols(factory, prover)?;
        self.sets.declare_symbols(factory, prover)?;
        self.multisets.declare_symbols(factory, prover)?;
        self.maps.declare_symbols(factory, prover)
    }
    pub fn emit_axioms<P: ProverLike>(
        &self,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.sequences.emit_axioms(prover)?;
        self.sets.emit_axioms(prover)?;
        self.multisets.emit_axioms(prover)?;
        self.maps.emit_axioms(prover)
    }
}

/// Analyze all collection dependencies together. User generic domains remain rejected.
pub fn analyze_collections(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
) -> Result<NativeCollectionsPreamble, NativePreambleError<std::convert::Infallible>> {
    Ok(NativeCollectionsPreamble {
        sequences: analyze_sequences_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            None,
        )?,
        sets: analyze_sets_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            true,
            None,
        )?,
        multisets: analyze_multisets_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            None,
        )?,
        maps: analyze_maps_inner(program, converter, factory, old_axiomatization, true, None)?,
    })
}

/// User domains and collection instances analyzed from one ground-type closure.
pub struct NativeGeneralPreamble {
    pub domains: NativePreambleData,
    pub collections: NativeCollectionsPreamble,
}
impl NativeGeneralPreamble {
    pub fn sorts(&self) -> impl Iterator<Item = &crate::state::terms::Sort> {
        self.domains.sorts().chain(self.collections.sorts())
    }
    pub fn declare_sorts<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains.declare_sorts(factory, prover)?;
        self.collections.declare_sorts(factory, prover)
    }
    pub fn declare_symbols<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains.declare_symbols(factory, prover)?;
        self.collections.declare_symbols(factory, prover)
    }
    pub fn emit_axioms<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains.emit_axioms(factory, prover)?;
        self.collections.emit_axioms(prover)
    }
}
/// Analyze the upstream ground closure and instantiate each domain's surviving members.
/// Unsupported expression translation and function-precondition transformations propagate errors.
pub fn analyze_general(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    threshold: i32,
) -> Result<NativeGeneralPreamble, NativePreambleError<std::convert::Infallible>> {
    use ferrum_silver::ast::utility::domain_instances::{
        find_necessary_type_instances, get_instance_members,
    };
    let ground = if threshold == 1 {
        program.ground_type_instances()
    } else {
        find_necessary_type_instances(program, threshold)
    }
    .map_err(NativePreambleError::GroundTypes)?;
    let collections = NativeCollectionsPreamble {
        sequences: analyze_sequences_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            Some(&ground),
        )?,
        sets: analyze_sets_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            true,
            Some(&ground),
        )?,
        multisets: analyze_multisets_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            Some(&ground),
        )?,
        maps: analyze_maps_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            Some(&ground),
        )?,
    };
    let mut domains = NativePreambleData::default();
    for instance in ground.iter().filter_map(|t| {
        if let Type::Domain(d) = t {
            Some(d)
        } else {
            None
        }
    }) {
        domains.domains.sorts = domains.domains.sorts.incl(
            converter
                .to_sort(&Type::Domain(instance.clone()))
                .map_err(NativePreambleError::Symbol)?,
        );
        let (functions, axioms) = get_instance_members(program, instance, &ground)
            .map_err(NativePreambleError::GroundTypes)?;
        for function in functions {
            if function.interpretation.is_some() {
                continue;
            }
            let applicable = converter
                .domain_function(&function, program)
                .map_err(NativePreambleError::Symbol)?;
            domains
                .domains
                .collect_function(applicable, function.unique)
                .map_err(NativePreambleError::Domain)?;
        }
        let translator = crate::supporters::expression_translator::ExpressionTranslator::new(
            factory,
            converter,
            |sort: &crate::state::terms::Sort| Ok::<_, std::convert::Infallible>(sort.to_string()),
        );
        for axiom in axioms {
            let mut term = translator
                .translate(axiom.exp())
                .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
            if let crate::state::terms::TermKind::Quantification {
                quantifier,
                vars,
                body,
                triggers,
                name,
                weight,
                ..
            } = term.kind()
            {
                if name.is_empty() {
                    let qid = match axiom.kind() {
                        ferrum_silver::ast::program::DomainAxiomKind::Named { name, .. } => {
                            format!("prog.{name}")
                        }
                        _ => String::new(),
                    };
                    term = factory
                        .quantification(
                            *quantifier,
                            vars.clone(),
                            body.clone(),
                            triggers.clone(),
                            qid,
                            false,
                            *weight,
                        )
                        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
                }
            }
            domains
                .domains
                .collect_axiom(factory, term, &mut |_| {
                    Err::<crate::state::terms::Applicable, _>(
                        "heap-dependent function in domain axiom",
                    )
                })
                .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
        }
    }
    Ok(NativeGeneralPreamble {
        domains,
        collections,
    })
}

/// Build actual multiset axioms for direct ground multiset instances. Programs
/// with user-defined generic domains are rejected until the full ground-instance
/// fixed point is available. The source is parsed only when an instance exists.
pub fn analyze_multisets(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
) -> Result<NativeMultisetPreamble, NativePreambleError<std::convert::Infallible>> {
    analyze_multisets_inner(program, converter, factory, old_axiomatization, false, None)
}
fn analyze_multisets_inner(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    mixed: bool,
    closed_ground: Option<&std::collections::HashSet<Type>>,
) -> Result<NativeMultisetPreamble, NativePreambleError<std::convert::Infallible>> {
    use crate::state::symbol_converter::BuiltinDomainSort;
    use crate::supporters::{
        builtin_domains_contributor::BuiltinDomainsContributor,
        default_multisets_contributor as multisets,
    };
    use ferrum_silver::ast::{
        program::{AnyLocalVarDecl, DomainAxiomKind, LocalVarDecl},
        utility::domain_instances::down_closure_ground,
    };
    if closed_ground.is_none()
        && program
            .domains
            .iter()
            .any(|domain| !domain.type_vars.is_empty())
    {
        return Err(NativePreambleError::Unsupported(
            "multiset ground instances with generic user domains",
        ));
    }
    let ground = match closed_ground {
        Some(ground) => ground.clone(),
        None => collect_ground_types(&Node::Program(program.clone()), program)
            .map_err(NativePreambleError::GroundTypes)?,
    };
    fn supported_element(typ: &Type) -> bool {
        match typ {
            Type::Int | Type::Bool | Type::Ref | Type::Perm => true,
            Type::Multiset(inner) => supported_element(inner),
            _ => false,
        }
    }
    let mut instances = std::collections::HashSet::new();
    for root in &ground {
        for typ in down_closure_ground(root).map_err(NativePreambleError::GroundTypes)? {
            if let Type::Multiset(element) = typ {
                if !(supported_element(&element)
                    || mixed && mixed_collection_type(&element, closed_ground.is_some()))
                {
                    return Err(NativePreambleError::Unsupported(
                        "multiset element requires another contributor",
                    ));
                }
                instances.insert((*element).clone());
            }
        }
    }
    let mut contributor = BuiltinDomainsContributor::default();
    if instances.is_empty() {
        return Ok(NativeMultisetPreamble { contributor });
    }
    let path = multisets::source_resource(old_axiomatization);
    let source = crate::resources::bundled::get(path)
        .ok_or(NativePreambleError::Unsupported("missing multiset source"))?;
    let parsed = ferrum_silver::parser::fast_parser::parse_program(source, path)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    ferrum_silver::parser::macro_expander::expand_global_expression_macros(&parsed)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    ferrum_silver::parser::parse_ast::init_properties(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    if !ferrum_silver::parser::resolver::NameAnalyser::default()
        .run(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
    {
        return Err(NativePreambleError::Unsupported(
            "multiset source name resolution",
        ));
    }
    ferrum_silver::parser::resolver::check_program_core(&parsed, &mut |_, _| {})
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    let builtin_program = ferrum_silver::parser::translator::translate_program_core(&parsed)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    let source_domain = builtin_program
        .find_domain_optionally(multisets::SOURCE_DOMAIN_NAME)
        .ok_or(NativePreambleError::Unsupported("multiset source domain"))?;
    if source_domain.type_vars.len() != 1 {
        return Err(NativePreambleError::Unsupported(
            "multiset source domain arity",
        ));
    }
    let builtin_converter = converter
        .clone()
        .with_builtin_domain(multisets::SOURCE_DOMAIN_NAME, BuiltinDomainSort::Multiset);
    let mut instances = instances.into_iter().collect::<Vec<_>>();
    fn nesting(typ: &Type) -> usize {
        match typ {
            Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => 1 + nesting(t),
            _ => 0,
        }
    }
    instances.sort_by_key(nesting);
    for element in instances {
        let substitution = [(source_domain.type_vars[0].clone(), element.clone())]
            .into_iter()
            .collect();
        let instantiated = source_domain.clone();
        let element_sort = builtin_converter
            .to_sort(&element)
            .map_err(NativePreambleError::Symbol)?;
        contributor.sorts = contributor
            .sorts
            .incl(crate::state::terms::Sort::Multiset(Box::new(
                element_sort.clone(),
            )));
        for function in &instantiated.functions {
            if function.interpretation.is_some() {
                continue;
            }
            let function = function.copy_with(|data| {
                data.typ = data.typ.substitute(&substitution);
                data.formal_args = data
                    .formal_args
                    .iter()
                    .map(|arg| match arg {
                        AnyLocalVarDecl::Named(v) => AnyLocalVarDecl::Named(LocalVarDecl::new(
                            v.name.clone(),
                            v.typ.substitute(&substitution),
                            v.meta.clone(),
                        )),
                        AnyLocalVarDecl::Unnamed(v) => AnyLocalVarDecl::Unnamed(
                            v.copy_with(|d| d.typ = d.typ.substitute(&substitution)),
                        ),
                    })
                    .collect();
            });
            let applicable = builtin_converter
                .domain_function(&function, program)
                .map_err(NativePreambleError::Symbol)?;
            contributor.functions = contributor.functions.incl(applicable);
        }
        let mut translator = crate::supporters::expression_translator::ExpressionTranslator::new(
            factory,
            &builtin_converter,
            |s: &crate::state::terms::Sort| Ok::<_, std::convert::Infallible>(s.to_string()),
        );
        translator.builtin = true;
        translator.type_substitution = Some(&substitution);
        for axiom in &instantiated.axioms {
            let mut term = translator
                .translate(axiom.exp())
                .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
            if let crate::state::terms::TermKind::Quantification {
                quantifier,
                vars,
                body,
                triggers,
                name,
                weight,
                ..
            } = term.kind()
            {
                if name.is_empty() {
                    let name = match axiom.kind() {
                        DomainAxiomKind::Named { name, .. } => {
                            format!("$Multiset[{element_sort}]_prog.{name}")
                        }
                        _ => String::new(),
                    };
                    term = factory
                        .quantification(
                            *quantifier,
                            vars.clone(),
                            body.clone(),
                            triggers.clone(),
                            name,
                            false,
                            *weight,
                        )
                        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
                }
            }
            contributor.axioms = contributor.axioms.incl(term);
        }
    }
    Ok(NativeMultisetPreamble { contributor })
}

#[cfg(test)]
mod sequence_tests {
    use super::*;
    use crate::state::terms::{Sort, TermOptions};
    use ferrum_silver::ast::{
        ast::Metadata,
        program::{LocalVarDecl, Method, MethodData},
    };
    use std::sync::Arc;
    #[test]
    fn non_integer_sequences_do_not_emit_range_symbols() {
        let meta = Metadata::default();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new(
                "s".into(),
                Type::Seq(Arc::new(Type::Bool)),
                meta.clone(),
            )],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let data = analyze_sequences(&program, &converter, &factory, false).unwrap();
        assert!(
            data.contributor
                .sorts
                .contains(&Sort::Seq(Box::new(Sort::Bool)))
        );
        assert!(
            data.contributor
                .functions
                .iter()
                .all(|function| function.data().id.name() != "Seq_range")
        );
        let mut converter =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in &data.contributor.axioms {
            converter.convert_term(axiom).unwrap();
        }
    }
    #[test]
    fn bundled_sequence_axioms_are_instantiated_for_int() {
        let meta = Metadata::default();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new(
                "s".into(),
                Type::Seq(Arc::new(Type::Int)),
                meta.clone(),
            )],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let data = analyze_sequences(&program, &converter, &factory, false).unwrap();
        assert!(
            data.contributor
                .sorts
                .contains(&Sort::Seq(Box::new(Sort::Int)))
        );
        assert!(!data.contributor.functions.is_empty());
        assert!(!data.contributor.axioms.is_empty());
        let mut converter =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in &data.contributor.axioms {
            converter.convert_term(axiom).unwrap();
        }
    }
}

#[cfg(test)]
mod set_tests {
    use super::*;
    use crate::state::terms::{Sort, TermOptions};
    use ferrum_silver::ast::{
        ast::Metadata,
        program::{LocalVarDecl, Method, MethodData},
    };
    use std::sync::Arc;
    #[test]
    fn bundled_set_axioms_are_instantiated_for_int() {
        let meta = Metadata::default();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new(
                "s".into(),
                Type::Set(Arc::new(Type::Int)),
                meta.clone(),
            )],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let data = analyze_sets(&program, &converter, &factory, false).unwrap();
        assert!(
            data.contributor
                .sorts
                .contains(&Sort::Set(Box::new(Sort::Int)))
        );
        assert!(!data.contributor.functions.is_empty());
        assert!(!data.contributor.axioms.is_empty());
        let mut converter =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in &data.contributor.axioms {
            converter.convert_term(axiom).unwrap();
        }
    }
}

#[cfg(test)]
mod map_tests {
    use super::*;
    use crate::state::terms::{Sort, TermOptions};
    use ferrum_silver::ast::{
        ast::Metadata,
        program::{LocalVarDecl, Method, MethodData},
    };
    #[test]
    fn bundled_map_axioms_and_induced_sets_are_instantiated() {
        let meta = Metadata::default();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new(
                "m".into(),
                Type::map(Type::Int, Type::Bool),
                meta.clone(),
            )],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let sets = analyze_sets_with_maps(&program, &converter, &factory, false).unwrap();
        assert!(
            sets.contributor
                .sorts
                .contains(&Sort::Set(Box::new(Sort::Int)))
        );
        assert!(
            sets.contributor
                .sorts
                .contains(&Sort::Set(Box::new(Sort::Bool)))
        );
        let data = analyze_maps(&program, &converter, &factory, false).unwrap();
        assert!(
            data.contributor
                .sorts
                .contains(&Sort::Map(Box::new(Sort::Int), Box::new(Sort::Bool)))
        );
        assert!(!data.contributor.functions.is_empty());
        assert!(!data.contributor.axioms.is_empty());
        let mut converter =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in &data.contributor.axioms {
            converter.convert_term(axiom).unwrap();
        }
    }
}

#[cfg(test)]
mod multiset_tests {
    use super::*;
    use crate::state::terms::{Sort, TermOptions};
    use ferrum_silver::ast::{
        ast::Metadata,
        program::{LocalVarDecl, Method, MethodData},
    };
    use std::sync::Arc;
    #[test]
    fn bundled_multiset_axioms_expand_macros_and_instantiate() {
        let meta = Metadata::default();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new(
                "s".into(),
                Type::Multiset(Arc::new(Type::Int)),
                meta.clone(),
            )],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        for old_axiomatization in [false, true] {
            let data =
                analyze_multisets(&program, &converter, &factory, old_axiomatization).unwrap();
            assert!(
                data.contributor
                    .sorts
                    .contains(&Sort::Multiset(Box::new(Sort::Int)))
            );
            assert!(!data.contributor.functions.is_empty());
            assert!(!data.contributor.axioms.is_empty());
            let mut converter =
                crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(
                    factory.clone(),
                );
            for axiom in &data.contributor.axioms {
                converter.convert_term(axiom).unwrap();
            }
        }
    }
    #[test]
    fn nested_multiset_sorts_are_inner_first() {
        let meta = Metadata::default();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new(
                "s".into(),
                Type::Multiset(Arc::new(Type::Multiset(Arc::new(Type::Int)))),
                meta.clone(),
            )],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let data = analyze_multisets(&program, &converter, &factory, false).unwrap();
        assert_eq!(
            data.sorts().cloned().collect::<Vec<_>>(),
            vec![
                Sort::Multiset(Box::new(Sort::Int)),
                Sort::Multiset(Box::new(Sort::Multiset(Box::new(Sort::Int)))),
            ]
        );
        assert!(!data.contributor.functions.is_empty());
        assert!(!data.contributor.axioms.is_empty());
        let mut converter =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in &data.contributor.axioms {
            converter.convert_term(axiom).unwrap();
        }
    }
    #[test]
    fn general_preamble_analyzes_lowered_generic_adt() {
        use ferrum_silver::frontend::{
            frontend::FrontendPhases,
            sil_front_end_config::SilFrontendConfig,
            sil_frontend::{SilFrontendPhases, standard_plugin_manager},
        };
        let config = SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            std::path::PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases.parse("adt Box[T] { Boxed(value: T) } method m() { var a: Box[Int] := Boxed(1); assert a.value == 1; assert a.isBoxed; }").unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let preamble = analyze_general(&program, &converter, &factory, false, 1).unwrap();
        assert!(!preamble.domains.domains.sorts.is_empty());
        assert!(!preamble.domains.domains.axioms.is_empty());
        let mut smt =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in &preamble.domains.domains.axioms {
            smt.convert_term(axiom).unwrap();
        }
    }
    #[test]
    fn general_preamble_analyzes_collection_of_generic_adt() {
        use ferrum_silver::frontend::{
            frontend::FrontendPhases,
            sil_front_end_config::SilFrontendConfig,
            sil_frontend::{SilFrontendPhases, standard_plugin_manager},
        };
        let config = SilFrontendConfig::new("test");
        let mut phases = SilFrontendPhases::new(
            std::path::PathBuf::from("test.vpr"),
            standard_plugin_manager(&config).unwrap(),
        );
        let parsed = phases
            .parse(
                "adt Box[T] { Boxed(value: T) } method m(xs: Seq[Box[Int]]) { assert |xs| >= 0; }",
            )
            .unwrap();
        let analyzed = phases.analyze(parsed).unwrap();
        let program = phases.translate(analyzed).unwrap();
        let program = phases.check_consistency(program).unwrap();
        let program = phases.prepare_verification(program).unwrap();
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let preamble = analyze_general(&program, &converter, &factory, false, 1).unwrap();
        assert!(preamble.collections.sorts().any(
            |s| matches!(s, Sort::Seq(element) if matches!(element.as_ref(), Sort::UserSort(_)))
        ));
        assert!(!preamble.domains.domains.axioms.is_empty());
        let mut smt =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in preamble
            .domains
            .domains
            .axioms
            .iter()
            .chain(preamble.collections.sequences.contributor.axioms.iter())
        {
            smt.convert_term(axiom).unwrap();
        }
    }
    #[test]
    fn general_closure_instantiates_collection_domain_signature() {
        use ferrum_silver::ast::program::{
            AnyLocalVarDecl, Domain, DomainData, DomainFunc, DomainFuncData,
        };
        use ferrum_silver::ast::r#type::TypeVar;
        let meta = Metadata::default();
        let variable = TypeVar::new("T");
        let function = DomainFunc::new(DomainFuncData {
            name: "f".into(),
            formal_args: vec![AnyLocalVarDecl::Named(LocalVarDecl::new(
                "x".into(),
                Type::Seq(Arc::new(Type::Var(variable.clone()))),
                meta.clone(),
            ))],
            typ: Type::Var(variable.clone()),
            unique: false,
            interpretation: None,
            domain_name: "D".into(),
            meta: meta.clone(),
        });
        let domain = Domain::new(DomainData {
            name: "D".into(),
            functions: vec![function],
            axioms: vec![],
            type_vars: vec![variable.clone()],
            interpretations: None,
            meta: meta.clone(),
        });
        let dtype = Type::Domain(domain.domain_type([(variable, Type::Int)].into_iter().collect()));
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new("d".into(), dtype, meta.clone())],
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
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let data = analyze_general(&program, &converter, &factory, false, 1).unwrap();
        assert!(
            data.collections
                .sorts()
                .any(|s| *s == Sort::Seq(Box::new(Sort::Int)))
        );
        assert_eq!(data.domains.domains.functions.len(), 1);
    }
    #[test]
    fn mixed_sequence_set_axioms_include_both_sorts() {
        let meta = Metadata::default();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new(
                "s".into(),
                Type::Seq(Arc::new(Type::Set(Arc::new(Type::Int)))),
                meta.clone(),
            )],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let data = analyze_collections(&program, &converter, &factory, false).unwrap();
        assert_eq!(
            data.sorts().cloned().collect::<Vec<_>>(),
            vec![
                Sort::Set(Box::new(Sort::Int)),
                Sort::Seq(Box::new(Sort::Set(Box::new(Sort::Int))))
            ]
        );
        assert!(
            data.sorts()
                .any(|s| *s == Sort::Seq(Box::new(Sort::Set(Box::new(Sort::Int)))))
        );
        let mut converter =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in data
            .sequences
            .contributor
            .axioms
            .iter()
            .chain(data.sets.contributor.axioms.iter())
        {
            converter.convert_term(axiom).unwrap();
        }
    }
    #[test]
    fn mixed_map_collection_arguments_include_induced_set_sorts() {
        let meta = Metadata::default();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new(
                "s".into(),
                Type::map(
                    Type::Seq(Arc::new(Type::Int)),
                    Type::Multiset(Arc::new(Type::Bool)),
                ),
                meta.clone(),
            )],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let data = analyze_collections(&program, &converter, &factory, false).unwrap();
        assert!(
            data.sorts()
                .any(|s| *s == Sort::Set(Box::new(Sort::Seq(Box::new(Sort::Int)))))
        );
        assert!(
            data.sorts()
                .any(|s| *s == Sort::Set(Box::new(Sort::Multiset(Box::new(Sort::Bool)))))
        );
        let mut converter =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in data
            .sequences
            .contributor
            .axioms
            .iter()
            .chain(data.sets.contributor.axioms.iter())
            .chain(data.multisets.contributor.axioms.iter())
            .chain(data.maps.contributor.axioms.iter())
        {
            converter.convert_term(axiom).unwrap();
        }
    }
}
