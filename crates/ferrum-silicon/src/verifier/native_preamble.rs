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
/// Optional user-provided source files; absent entries use the pinned bundled sources.
/// Files are read only when their collection has ground instances, as upstream does.
#[derive(Clone, Debug, Default)]
pub struct CollectionAxiomatizationSources {
    pub sequences: Option<std::path::PathBuf>,
    pub sets: Option<std::path::PathBuf>,
    pub multisets: Option<std::path::PathBuf>,
    pub maps: Option<std::path::PathBuf>,
}

// Ground-type closure uses hash sets for membership. Never let their iteration
// order choose the order of SMT declarations or axioms: that changes Z3's search.
// Keep this key structural (including sorted substitutions), rather than using
// Debug on types containing hash maps or a possibly ambiguous printed sort name.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum PreambleTypeKey {
    Atomic(&'static str),
    Variable(String),
    Collection(&'static str, Vec<PreambleTypeKey>),
    Domain(String, Vec<(String, PreambleTypeKey)>),
    Backend(String, Vec<(String, String)>),
    Snap,
}

fn preamble_type_key(typ: &Type) -> Result<PreambleTypeKey, SymbolConversionError> {
    use PreambleTypeKey::*;
    Ok(match typ {
        Type::Int => Atomic("Int"),
        Type::Bool => Atomic("Bool"),
        Type::Ref => Atomic("Ref"),
        Type::Perm => Atomic("Perm"),
        Type::InternalType => Atomic("InternalType"),
        Type::Wand => Atomic("Wand"),
        Type::Var(var) => Variable(var.name.clone()),
        Type::Seq(t) => Collection("Seq", vec![preamble_type_key(t)?]),
        Type::Set(t) => Collection("Set", vec![preamble_type_key(t)?]),
        Type::Multiset(t) => Collection("Multiset", vec![preamble_type_key(t)?]),
        Type::Map(pair) => Collection(
            "Map",
            vec![preamble_type_key(&pair.0)?, preamble_type_key(&pair.1)?],
        ),
        Type::Domain(domain) => {
            let mut arguments = domain
                .partial_type_vars
                .iter()
                .map(|(var, typ)| Ok((var.name.clone(), preamble_type_key(typ)?)))
                .collect::<Result<Vec<_>, SymbolConversionError>>()?;
            arguments.sort();
            Domain(domain.domain_name.clone(), arguments)
        }
        Type::Backend(backend) => {
            let mut interpretations = backend
                .interpretations
                .iter()
                .map(|(name, value)| (name.clone(), value.clone()))
                .collect::<Vec<_>>();
            interpretations.sort();
            Backend(backend.viper_name.clone(), interpretations)
        }
        Type::Extension(t) if t.as_any().is::<SnapEmbedding>() => Snap,
        _ => return Err(SymbolConversionError::UnexpectedType),
    })
}

fn collection_depth(typ: &Type) -> usize {
    match typ {
        Type::Seq(t) | Type::Set(t) | Type::Multiset(t) => 1 + collection_depth(t),
        Type::Map(pair) => 1 + collection_depth(&pair.0).max(collection_depth(&pair.1)),
        _ => 0,
    }
}

fn ordered_preamble_types(
    types: impl IntoIterator<Item = Type>,
) -> Result<Vec<Type>, NativePreambleError<std::convert::Infallible>> {
    let mut keyed = types
        .into_iter()
        .map(|typ| {
            let key = preamble_type_key(&typ).map_err(NativePreambleError::Symbol)?;
            Ok(((collection_depth(&typ), key), typ))
        })
        .collect::<Result<Vec<_>, NativePreambleError<std::convert::Infallible>>>()?;
    keyed.sort_by(|a, b| a.0.cmp(&b.0));
    Ok(keyed.into_iter().map(|(_, typ)| typ).collect())
}

fn ordered_domain_instances(
    program: &Program,
    ground: &std::collections::HashSet<Type>,
) -> Result<
    Vec<ferrum_silver::ast::r#type::DomainType>,
    NativePreambleError<std::convert::Infallible>,
> {
    let instances = ordered_preamble_types(
        ground
            .iter()
            .filter(|typ| matches!(typ, Type::Domain(_)))
            .cloned(),
    )?;
    let mut instances = instances
        .into_iter()
        .map(|typ| match typ {
            Type::Domain(domain) => domain,
            _ => unreachable!("filtered domain instances"),
        })
        .collect::<Vec<_>>();
    // Preserve declaration order across domains, with a structural tie-breaker
    // for the concrete instantiations of each generic domain.
    let declaration_order = program
        .domains
        .iter()
        .enumerate()
        .map(|(index, domain)| (domain.name.as_str(), index))
        .collect::<std::collections::HashMap<_, _>>();
    instances.sort_by_key(|instance| {
        declaration_order
            .get(instance.domain_name.as_str())
            .copied()
    });
    Ok(instances)
}

fn parse_collection_source(
    bundled: &'static str,
    custom: Option<&std::path::Path>,
    expand_bundled_macros: bool,
) -> Result<
    ferrum_silver::parser::parse_ast::PProgramHandle,
    NativePreambleError<std::convert::Infallible>,
> {
    use ferrum_silver::parser::{fast_parser, macro_expander};
    let parsed = if let Some(path) = custom {
        let source = std::fs::read_to_string(path).map_err(|e| {
            NativePreambleError::Translation(format!(
                "could not read collection axiomatization {}: {e}",
                path.display()
            ))
        })?;
        fast_parser::parse_program_with_imports(
            &source,
            path,
            &[],
            &mut |import, standard| {
                if standard {
                    let key = format!(
                        "import/{}",
                        import.to_string_lossy().trim_start_matches('/')
                    );
                    ferrum_silver::resources::bundled::get(&key)
                        .or_else(|| crate::resources::bundled::get(&key))
                        .map(str::to_owned)
                        .ok_or_else(|| format!("standard import not found: {}", import.display()))
                } else {
                    std::fs::read_to_string(import).map_err(|e| e.to_string())
                }
            },
            &mut Ok,
        )
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
    } else {
        let source = crate::resources::bundled::get(bundled).ok_or(
            NativePreambleError::Unsupported("missing collection source"),
        )?;
        fast_parser::parse_program(source, bundled)
            .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
    };
    if custom.is_some() || expand_bundled_macros {
        macro_expander::expand_global_expression_macros(&parsed)
            .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    }
    let reports = parsed.errors();
    if !reports.is_empty() {
        return Err(NativePreambleError::Translation(format!(
            "collection source reports: {reports:?}"
        )));
    }
    Ok(parsed)
}

// Source BuiltinDomainsContributor caches translated programs by URL and
// millisecond modification time. Only successful loads enter the cache; an
// imported file changing alone does not invalidate its root source entry.
fn load_collection_program(
    bundled: &'static str,
    custom: Option<&std::path::Path>,
    expand_bundled_macros: bool,
    resolution_error: &'static str,
) -> Result<Program, NativePreambleError<std::convert::Infallible>> {
    use std::sync::{Mutex, OnceLock};
    #[derive(Hash, PartialEq, Eq)]
    enum CacheKey {
        Bundled(&'static str),
        File(std::path::PathBuf),
    }
    type Cache = std::collections::HashMap<CacheKey, (u128, Program)>;
    static PROGRAM_CACHE: OnceLock<Mutex<Cache>> = OnceLock::new();
    let mut cache = PROGRAM_CACHE
        .get_or_init(|| Mutex::new(Cache::new()))
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    let key = match custom {
        Some(path) => CacheKey::File(std::path::absolute(path).map_err(|e| {
            NativePreambleError::Translation(format!("invalid collection source path: {e}"))
        })?),
        None => CacheKey::Bundled(bundled),
    };
    let modified = custom.map_or(0, |p| {
        std::fs::metadata(p)
            .and_then(|m| m.modified())
            .ok()
            .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
            .map_or(0, |t| t.as_millis())
    });
    if let Some((cached_time, program)) = cache.get(&key) {
        if *cached_time == modified {
            return Ok(program.clone());
        }
    }
    let parsed = parse_collection_source(bundled, custom, expand_bundled_macros)?;
    ferrum_silver::parser::parse_ast::init_properties(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    if !ferrum_silver::parser::resolver::NameAnalyser::default()
        .run(parsed.node())
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
    {
        return Err(NativePreambleError::Unsupported(resolution_error));
    }
    ferrum_silver::parser::resolver::check_program_core(&parsed, &mut |_, _| {})
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    let program = ferrum_silver::parser::translator::translate_program_core(&parsed)
        .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
    cache.insert(key, (modified, program.clone()));
    Ok(program)
}

/// Collected source-order declarations and uniqueness assumptions for later emission.
#[derive(Default)]
pub struct NativePreambleData {
    domains: DefaultDomainsContributor,
}
impl NativePreambleData {
    /// Source domain contributor axioms, excluding uniqueness and collection axioms.
    pub fn domain_axioms(&self) -> impl Iterator<Item = &crate::state::terms::Term> {
        self.domains.axioms.iter()
    }
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
    pub fn emit_uniqueness<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains
            .emit_uniqueness(factory, prover)
            .map_err(NativePreambleError::Sink)
    }
    pub fn emit_domain_axioms<P: ProverLike>(
        &self,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains
            .emit_axioms(prover)
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
    let instances = ordered_domain_instances(program, &ground)?;
    for domain in &program.domains {
        for instance in instances.iter().filter(|d| d.domain_name == domain.name) {
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
    fn fresh_analyses_emit_identical_domain_and_collection_preambles() {
        // Multiple instances at each nesting depth exercise hash-order ties in
        // every contributor; two parameters also exercise substitution maps.
        let source = r#"
domain Z[T, U] {
  function z(x: T, y: U): T
  axiom { forall x: T, y: U :: { z(x, y) } z(x, y) == x }
}
domain A {
  unique function a(): A
  unique function b(): A
}
method m(z1: Z[Int, Bool], z2: Z[Bool, Int], argA: A,
         sq1: Seq[Int], sq2: Seq[Bool], sq3: Seq[Seq[Int]],
         st1: Set[Int], st2: Set[Bool], st3: Set[Set[Int]],
         ms1: Multiset[Int], ms2: Multiset[Bool], ms3: Multiset[Multiset[Int]],
         mp1: Map[Int, Bool], mp2: Map[Bool, Int], mp3: Map[Int, Map[Bool, Int]],
         mixed: Seq[Map[Int, Set[Bool]]]) {}
"#;
        let mut expected = None;
        for _ in 0..16 {
            let parsed =
                ferrum_silver::parser::fast_parser::parse_program(source, "order.vpr").unwrap();
            ferrum_silver::parser::parse_ast::init_properties(parsed.node()).unwrap();
            assert!(
                ferrum_silver::parser::resolver::NameAnalyser::default()
                    .run(parsed.node())
                    .unwrap()
            );
            ferrum_silver::parser::resolver::check_program_core(&parsed, &mut |_, _| {}).unwrap();
            let program =
                ferrum_silver::parser::translator::translate_program_core(&parsed).unwrap();
            let factory = TermFactory::new(TermOptions {
                use_flyweight: false,
                use_old_axiomatization: false,
                mask_heap_mode: false,
            });
            let converter = DefaultSymbolConverter::new(factory.clone(), false);
            let preamble = analyze_general(&program, &converter, &factory, false, 1).unwrap();
            let domain_sorts = preamble
                .domains
                .sorts()
                .map(ToString::to_string)
                .collect::<Vec<_>>();
            assert_eq!(domain_sorts, ["Z[Bool, Int]", "Z[Int, Bool]", "A"]);

            let restricted = program.copy_with(|data| {
                data.domains.truncate(1);
                data.methods[0] =
                    data.methods[0].copy_with(|method| method.formal_args.truncate(2));
            });
            let restricted = analyze_generic_axioms(&restricted, &converter, &factory).unwrap();
            assert_eq!(
                restricted
                    .sorts()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>(),
                domain_sorts[..2]
            );

            let mut smt = crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(
                factory.clone(),
            );
            let mut commands = Vec::new();
            for sort in preamble.sorts() {
                commands.push(
                    smt.convert_declaration(&factory.sort_decl(sort.clone()))
                        .unwrap(),
                );
            }
            let collections = &preamble.collections;
            for functions in [
                &collections.sets.contributor.functions,
                &collections.multisets.contributor.functions,
                &collections.sequences.contributor.functions,
                &collections.maps.contributor.functions,
                &preamble.domains.domains.functions,
            ] {
                for function in functions {
                    commands.push(
                        smt.convert_declaration(&factory.function_decl(function.clone()))
                            .unwrap(),
                    );
                }
            }
            for axioms in [
                &preamble.domains.domains.uniqueness_assumptions(&factory),
                &collections.sequences.contributor.axioms,
                &collections.sets.contributor.axioms,
                &collections.multisets.contributor.axioms,
                &collections.maps.contributor.axioms,
                &preamble.domains.domains.axioms,
            ] {
                for axiom in axioms {
                    commands.push(smt.convert_term(axiom).unwrap());
                }
            }
            if let Some(expected) = &expected {
                assert_eq!(&commands, expected, "fresh hash seeds changed SMT emission");
            } else {
                expected = Some(commands);
            }
        }
    }

    #[test]
    fn domain_axiom_function_call_uses_precondition_symbol_and_rejects_preconditions() {
        use ferrum_silver::ast::expression::{Exp, ExpKind};
        let source = "function f(x: Int): Int { x + 1 } domain D { function g(x: Int): Int axiom { forall x: Int :: {g(x)} g(x) == f(x) } } method m() { assert g(1) == 2 }";
        let parsed = ferrum_silver::parser::fast_parser::parse_program(source, "test.vpr").unwrap();
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
        let data = analyze_general(&program, &converter, &factory, false, 1).unwrap();
        let mut smt = crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(
            factory.clone(),
        );
        let rendered = data
            .domains
            .domain_axioms()
            .map(|axiom| smt.convert_term(axiom).unwrap())
            .collect::<Vec<_>>()
            .join("\n");
        assert!(rendered.contains("f%precondition"));
        let invalid = program.copy_with(|contents| {
            contents.functions[0] = contents.functions[0]
                .copy_with(|f| f.pres.push(Exp::new(ExpKind::TrueLit, Metadata::default())));
        });
        assert!(matches!(
            analyze_general(&invalid, &converter, &factory, false, 1),
            Err(NativePreambleError::Unsupported(
                "function with preconditions in domain axiom"
            ))
        ));
    }
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
    analyze_sequences_inner(
        program,
        converter,
        factory,
        old_axiomatization,
        false,
        None,
        None,
    )
}
fn analyze_sequences_inner(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    mixed: bool,
    closed_ground: Option<&std::collections::HashSet<Type>>,
    custom_source: Option<&std::path::Path>,
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
    let builtin_program = load_collection_program(
        path,
        custom_source,
        false,
        "sequence source name resolution",
    )?;
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
    for element in ordered_preamble_types(instances)? {
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
/// Source ViperEmbedding(sorts.Snap), used only to instantiate Set[Snap] axioms.
#[derive(Clone, Debug)]
struct SnapEmbedding;
impl ferrum_silver::ast::r#type::ExtensionType for SnapEmbedding {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn equals(&self, other: &dyn ferrum_silver::ast::r#type::ExtensionType) -> bool {
        other.as_any().is::<Self>()
    }
    fn hash_value(&self) -> u64 {
        0x534e4150
    }
    fn substitute(
        &self,
        _: &ferrum_silver::ast::r#type::TypeSubstitution,
    ) -> std::sync::Arc<dyn ferrum_silver::ast::r#type::ExtensionType> {
        std::sync::Arc::new(Self)
    }
    fn is_concrete(&self) -> bool {
        true
    }
}

/// Source DefaultSetsContributor condition for quantified-resource set instances.
pub fn uses_quantified_resource(
    program: &Program,
) -> Result<bool, NativePreambleError<std::convert::Infallible>> {
    use ferrum_silver::ast::{expression::ExpKind, utility::nodes::subnodes};
    fn contains_resource(
        node: &Node,
    ) -> Result<bool, NativePreambleError<std::convert::Infallible>> {
        if matches!(node, Node::FieldAccess(_) | Node::PredicateAccess(_))
            || matches!(node, Node::Exp(e) if matches!(e.kind(), ExpKind::FieldAccess(_) | ExpKind::PredicateAccess(_) | ExpKind::MagicWand(..)))
        {
            return Ok(true);
        }
        for child in
            subnodes(node).map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
        {
            if contains_resource(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    fn walk(node: &Node) -> Result<bool, NativePreambleError<std::convert::Infallible>> {
        if let Node::Exp(exp) = node {
            match exp.kind() {
                ExpKind::Forall(_, triggers, _) | ExpKind::Exists(_, triggers, _) => {
                    for trigger in triggers {
                        for e in &trigger.exps {
                            if contains_resource(&Node::Exp(e.clone()))? {
                                return Ok(true);
                            }
                        }
                    }
                    if !exp.is_pure() {
                        return Ok(true);
                    }
                }
                ExpKind::ForPerm(..) if !exp.is_pure() => return Ok(true),
                _ => {}
            }
        }
        for child in
            subnodes(node).map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
        {
            if walk(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
    walk(&Node::Program(program.clone()))
}

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
    custom_source: Option<&std::path::Path>,
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
    let needs_quantified_sets = uses_quantified_resource(program)?;
    if needs_quantified_sets {
        for field in &program.fields {
            if !(supported_element(&field.typ)
                || mixed && mixed_collection_type(&field.typ, closed_ground.is_some()))
            {
                return Err(NativePreambleError::Unsupported(
                    "quantified field set element",
                ));
            }
            instances.insert(field.typ.clone());
        }
        instances.insert(Type::Ref);
        instances.insert(Type::Extension(std::sync::Arc::new(SnapEmbedding)));
    }
    let mut contributor = BuiltinDomainsContributor::default();
    if instances.is_empty() {
        return Ok(NativeSetPreamble { contributor });
    }
    let path = sets::source_resource(old_axiomatization);
    let builtin_program =
        load_collection_program(path, custom_source, false, "set source name resolution")?;
    let source_domain = builtin_program
        .find_domain_optionally(sets::SOURCE_DOMAIN_NAME)
        .ok_or(NativePreambleError::Unsupported("set source domain"))?;
    if source_domain.type_vars.len() != 1 {
        return Err(NativePreambleError::Unsupported("set source domain arity"));
    }
    let builtin_converter = converter
        .clone()
        .with_embedding_override(std::sync::Arc::new(|value| {
            value
                .as_any()
                .is::<SnapEmbedding>()
                .then_some(crate::state::terms::Sort::Snap)
        }))
        .with_builtin_domain(sets::SOURCE_DOMAIN_NAME, BuiltinDomainSort::Set);
    for element in ordered_preamble_types(instances)? {
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
    analyze_maps_inner(
        program,
        converter,
        factory,
        old_axiomatization,
        false,
        None,
        None,
    )
}
fn analyze_maps_inner(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    mixed: bool,
    closed_ground: Option<&std::collections::HashSet<Type>>,
    custom_source: Option<&std::path::Path>,
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
    let builtin_program =
        load_collection_program(path, custom_source, false, "map source name resolution")?;
    let source_domain = builtin_program
        .find_domain_optionally(maps::SOURCE_DOMAIN_NAME)
        .ok_or(NativePreambleError::Unsupported("map source domain"))?;
    if source_domain.type_vars.len() != 2 {
        return Err(NativePreambleError::Unsupported("map source domain arity"));
    }
    let builtin_converter = converter
        .clone()
        .with_builtin_domain(maps::SOURCE_DOMAIN_NAME, BuiltinDomainSort::Map);
    let instances = ordered_preamble_types(
        instances
            .into_iter()
            .map(|pair| Type::Map(std::sync::Arc::new(pair))),
    )?;
    for instance in instances {
        let Type::Map(pair) = instance else {
            unreachable!("map instances")
        };
        let (key, value) = (&pair.0, &pair.1);
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
        Type::Backend(_) => allow_domains,
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
        self.sets.declare_symbols(factory, prover)?;
        self.multisets.declare_symbols(factory, prover)?;
        self.sequences.declare_symbols(factory, prover)?;
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
    analyze_collections_with_sources(
        program,
        converter,
        factory,
        old_axiomatization,
        &CollectionAxiomatizationSources::default(),
    )
}

pub fn analyze_collections_with_sources(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    sources: &CollectionAxiomatizationSources,
) -> Result<NativeCollectionsPreamble, NativePreambleError<std::convert::Infallible>> {
    Ok(NativeCollectionsPreamble {
        sequences: analyze_sequences_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            None,
            sources.sequences.as_deref(),
        )?,
        sets: analyze_sets_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            true,
            None,
            sources.sets.as_deref(),
        )?,
        multisets: analyze_multisets_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            None,
            sources.multisets.as_deref(),
        )?,
        maps: analyze_maps_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            None,
            sources.maps.as_deref(),
        )?,
    })
}

/// User domains and collection instances analyzed from one ground-type closure.
pub struct NativeGeneralPreamble {
    pub domains: NativePreambleData,
    pub collections: NativeCollectionsPreamble,
    backend_sorts: Vec<crate::state::terms::Sort>,
}
impl NativeGeneralPreamble {
    pub fn sorts(&self) -> impl Iterator<Item = &crate::state::terms::Sort> {
        self.domains
            .sorts()
            .chain(self.collections.sorts())
            .chain(self.backend_sorts.iter())
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
        self.collections.declare_symbols(factory, prover)?;
        self.domains.declare_symbols(factory, prover)
    }
    pub fn emit_axioms<P: ProverLike>(
        &self,
        factory: &TermFactory,
        prover: &mut P,
    ) -> Result<(), NativePreambleError<P::Error>> {
        self.domains.emit_uniqueness(factory, prover)?;
        self.collections.emit_axioms(prover)?;
        self.domains.emit_domain_axioms(prover)
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
    analyze_general_with_sources(
        program,
        converter,
        factory,
        old_axiomatization,
        threshold,
        &CollectionAxiomatizationSources::default(),
    )
}

pub fn analyze_general_with_sources(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    threshold: i32,
    sources: &CollectionAxiomatizationSources,
) -> Result<NativeGeneralPreamble, NativePreambleError<std::convert::Infallible>> {
    use ferrum_silver::ast::utility::domain_instances::{
        find_necessary_type_instances, get_instance_members,
    };
    fn validate_axiom_functions(
        node: &Node,
        program: &Program,
        converter: &DefaultSymbolConverter,
    ) -> Result<(), NativePreambleError<std::convert::Infallible>> {
        if let Node::Exp(expression) = node {
            if let ferrum_silver::ast::expression::ExpKind::FuncApp(name, args) = expression.kind()
            {
                let function = program.find_function_optionally(name).ok_or(
                    NativePreambleError::Unsupported("unknown function in domain axiom"),
                )?;
                if !function.pres.is_empty() {
                    return Err(NativePreambleError::Unsupported(
                        "function with preconditions in domain axiom",
                    ));
                }
                if args.len() != function.formal_args.len()
                    || args.iter().zip(&function.formal_args).any(|(arg, formal)| {
                        let Ok(actual) = arg.typ() else { return true };
                        !actual.is_subtype(&formal.typ)
                            || !matches!(
                                (converter.to_sort(&actual), converter.to_sort(&formal.typ)),
                                (Ok(a), Ok(b)) if a == b
                            )
                    })
                    || expression.typ().ok().as_ref() != Some(&function.typ)
                {
                    return Err(NativePreambleError::Unsupported(
                        "invalid function signature in domain axiom",
                    ));
                }
            }
        }
        for child in ferrum_silver::ast::utility::nodes::subnodes(node)
            .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
        {
            validate_axiom_functions(&child, program, converter)?;
        }
        Ok(())
    }
    let ground = if threshold == 1 {
        program.ground_type_instances()
    } else {
        find_necessary_type_instances(program, threshold)
    }
    .map_err(NativePreambleError::GroundTypes)?;
    // The source linked set deduplicates BackendType values, not SMT sort names.
    fn gather_backend_sorts(
        node: &Node,
        converter: &DefaultSymbolConverter,
        seen: &mut std::collections::HashSet<Type>,
        out: &mut Vec<crate::state::terms::Sort>,
    ) -> Result<(), NativePreambleError<std::convert::Infallible>> {
        if let Node::Type(t @ Type::Backend(_)) = node {
            if seen.insert(t.clone()) {
                out.push(converter.to_sort(t).map_err(NativePreambleError::Symbol)?);
            }
        }
        for child in ferrum_silver::ast::utility::nodes::subnodes(node)
            .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?
        {
            gather_backend_sorts(&child, converter, seen, out)?;
        }
        Ok(())
    }
    let mut backend_sorts = Vec::new();
    gather_backend_sorts(
        &Node::Program(program.clone()),
        converter,
        &mut std::collections::HashSet::new(),
        &mut backend_sorts,
    )?;
    let collections = NativeCollectionsPreamble {
        sequences: analyze_sequences_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            Some(&ground),
            sources.sequences.as_deref(),
        )?,
        sets: analyze_sets_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            true,
            Some(&ground),
            sources.sets.as_deref(),
        )?,
        multisets: analyze_multisets_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            Some(&ground),
            sources.multisets.as_deref(),
        )?,
        maps: analyze_maps_inner(
            program,
            converter,
            factory,
            old_axiomatization,
            true,
            Some(&ground),
            sources.maps.as_deref(),
        )?,
    };
    let mut domains = NativePreambleData::default();
    for instance in ordered_domain_instances(program, &ground)? {
        domains.domains.sorts = domains.domains.sorts.incl(
            converter
                .to_sort(&Type::Domain(instance.clone()))
                .map_err(NativePreambleError::Symbol)?,
        );
        let (functions, axioms) = get_instance_members(program, &instance, &ground)
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
            validate_axiom_functions(&Node::Exp(axiom.exp().clone()), program, converter)?;
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
                .collect_axiom(factory, term, &mut |function| {
                    Ok::<_, std::convert::Infallible>(
                        crate::rules::function_supporter::precondition_version(factory, function),
                    )
                })
                .map_err(|e| NativePreambleError::Translation(format!("{e:?}")))?;
        }
    }
    Ok(NativeGeneralPreamble {
        domains,
        collections,
        backend_sorts,
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
    analyze_multisets_inner(
        program,
        converter,
        factory,
        old_axiomatization,
        false,
        None,
        None,
    )
}
fn analyze_multisets_inner(
    program: &Program,
    converter: &DefaultSymbolConverter,
    factory: &TermFactory,
    old_axiomatization: bool,
    mixed: bool,
    closed_ground: Option<&std::collections::HashSet<Type>>,
    custom_source: Option<&std::path::Path>,
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
    let builtin_program =
        load_collection_program(path, custom_source, true, "multiset source name resolution")?;
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
    for element in ordered_preamble_types(instances)? {
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
    fn custom_collection_source_resolves_relative_imports_and_reports_failures() {
        let dir = std::env::temp_dir().join(format!("ferrum-custom-import-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("root.vpr");
        std::fs::write(&root, "import \"nested.vpr\"\n").unwrap();
        assert!(parse_collection_source("/unused", Some(&root), false).is_err());
        std::fs::write(dir.join("nested.vpr"), "domain $Seq[E] {}\n").unwrap();
        let parsed = parse_collection_source("/unused", Some(&root), false).unwrap();
        assert!(parsed.errors().is_empty());
        ferrum_silver::parser::parse_ast::init_properties(parsed.node()).unwrap();
        assert!(
            ferrum_silver::parser::resolver::NameAnalyser::default()
                .run(parsed.node())
                .unwrap()
        );
        ferrum_silver::parser::resolver::check_program_core(&parsed, &mut |_, _| {}).unwrap();
        let translated =
            ferrum_silver::parser::translator::translate_program_core(&parsed).unwrap();
        assert!(translated.find_domain_optionally("$Seq").is_some());
        load_collection_program("/unused", Some(&root), false, "resolution").unwrap();
        std::fs::write(dir.join("nested.vpr"), "invalid source").unwrap();
        assert!(load_collection_program("/unused", Some(&root), false, "resolution").is_ok());
        let modified = std::fs::metadata(&root).unwrap().modified().unwrap();
        std::fs::OpenOptions::new()
            .write(true)
            .open(&root)
            .unwrap()
            .set_times(
                std::fs::FileTimes::new()
                    .set_modified(modified + std::time::Duration::from_secs(2)),
            )
            .unwrap();
        assert!(load_collection_program("/unused", Some(&root), false, "resolution").is_err());
        std::fs::write(&root, "import <decreases/declaration.vpr>\n").unwrap();
        let parsed = parse_collection_source("/unused", Some(&root), false).unwrap();
        assert!(parsed.errors().is_empty());
        assert!(!parsed.all_members().is_empty());
        std::fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn custom_sequence_source_is_lazy_and_replaces_bundled_source() {
        let meta = Metadata::default();
        let empty = Program::new(vec![], vec![], vec![], vec![], vec![], vec![], meta.clone());
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
        let with_seq = Program::new(vec![], vec![], vec![], vec![], vec![method], vec![], meta);
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: false,
        });
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let path =
            std::env::temp_dir().join(format!("ferrum-custom-seq-{}.vpr", std::process::id()));
        let sources = CollectionAxiomatizationSources {
            sequences: Some(path.clone()),
            ..Default::default()
        };
        let _ = std::fs::remove_file(&path);
        assert!(
            analyze_collections_with_sources(&empty, &converter, &factory, false, &sources).is_ok()
        );
        assert!(
            analyze_collections_with_sources(&with_seq, &converter, &factory, false, &sources)
                .is_err()
        );
        std::fs::write(&path, "domain $Seq[E] {}\n").unwrap();
        let custom =
            analyze_collections_with_sources(&with_seq, &converter, &factory, false, &sources)
                .unwrap();
        let bundled = analyze_collections(&with_seq, &converter, &factory, false).unwrap();
        assert!(custom.sequences.contributor.axioms.is_empty());
        assert!(!bundled.sequences.contributor.axioms.is_empty());
        let saved_time = std::fs::metadata(&path).unwrap().modified().unwrap();
        std::fs::write(&path, "invalid source").unwrap();
        let file = std::fs::OpenOptions::new().write(true).open(&path).unwrap();
        file.set_times(std::fs::FileTimes::new().set_modified(saved_time))
            .unwrap();
        assert!(
            analyze_collections_with_sources(&with_seq, &converter, &factory, false, &sources)
                .is_ok()
        );
        file.set_times(
            std::fs::FileTimes::new().set_modified(saved_time + std::time::Duration::from_secs(2)),
        )
        .unwrap();
        assert!(
            analyze_collections_with_sources(&with_seq, &converter, &factory, false, &sources)
                .is_err()
        );
        std::fs::remove_file(path).unwrap();
    }
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
    fn general_preamble_rejects_backend_type_without_smt_interpretation() {
        let meta = Metadata::default();
        let typ = Type::Backend(ferrum_silver::ast::r#type::BackendType::new(
            "B".into(),
            [("Boogie".into(), "bv32".into())].into_iter().collect(),
        ));
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![LocalVarDecl::new("b".into(), typ, meta.clone())],
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
        assert!(matches!(
            analyze_general(&program, &converter, &factory, false, 1),
            Err(NativePreambleError::Symbol(
                SymbolConversionError::MissingSmtlibName
            ))
        ));
    }
    #[test]
    fn quantified_resource_adds_source_set_instances() {
        use ferrum_silver::ast::{
            expression::{Exp, ExpKind, FieldAccess, LocalVar},
            program::{Field, FieldData},
        };
        let meta = Metadata::default();
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let decl = LocalVarDecl::new("r".into(), Type::Ref, meta.clone());
        let receiver = Exp::new(
            ExpKind::LocalVar(LocalVar::new("r".into(), Type::Ref, meta.clone())),
            meta.clone(),
        );
        let access = Exp::new(
            ExpKind::FieldAccessPredicate(
                FieldAccess::new(receiver, field.clone(), meta.clone()),
                None,
            ),
            meta.clone(),
        );
        let quantifier = Exp::new(ExpKind::Forall(vec![decl], vec![], access), meta.clone());
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![quantifier],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![],
            vec![field],
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
        assert!(uses_quantified_resource(&program).unwrap());
        let data = analyze_collections(&program, &converter, &factory, false).unwrap();
        for element in [Sort::Int, Sort::Ref, Sort::Snap] {
            assert!(
                data.sets
                    .sorts()
                    .any(|s| *s == Sort::Set(Box::new(element.clone())))
            );
        }
        let mut smt =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in &data.sets.contributor.axioms {
            smt.convert_term(axiom).unwrap();
        }
    }
    #[test]
    fn resource_in_pure_quantifier_trigger_enables_quantified_sets() {
        use ferrum_silver::ast::{
            expression::{Exp, ExpKind, FieldAccess, LocalVar, Trigger},
            program::{Field, FieldData},
        };
        let meta = Metadata::default();
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Bool,
            meta: meta.clone(),
        });
        let decl = LocalVarDecl::new("r".into(), Type::Ref, meta.clone());
        let receiver = Exp::new(
            ExpKind::LocalVar(LocalVar::new("r".into(), Type::Ref, meta.clone())),
            meta.clone(),
        );
        let access = Exp::new(
            ExpKind::FieldAccess(FieldAccess::new(receiver, field.clone(), meta.clone())),
            meta.clone(),
        );
        let quantified = Exp::new(
            ExpKind::Exists(
                vec![decl],
                vec![Trigger::new(vec![access], meta.clone())],
                Exp::new(ExpKind::TrueLit, meta.clone()),
            ),
            meta.clone(),
        );
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![],
            formal_returns: vec![],
            pres: vec![quantified],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![],
            vec![field],
            vec![],
            vec![],
            vec![method],
            vec![],
            meta,
        );
        assert!(uses_quantified_resource(&program).unwrap());
    }
    #[test]
    fn general_preamble_collects_interpreted_sorts_and_sequence_instances() {
        use ferrum_silver::ast::utility::backend_type_factories::BVFactory;
        let meta = Metadata::default();
        let bitvec = BVFactory { size: 32 };
        let backend = bitvec.typ();
        let method = Method::new(MethodData {
            name: "m".into(),
            formal_args: vec![
                LocalVarDecl::new("b".into(), backend.clone(), meta.clone()),
                LocalVarDecl::new("s".into(), Type::Seq(Arc::new(backend)), meta.clone()),
            ],
            formal_returns: vec![],
            pres: vec![],
            posts: vec![],
            body: None,
            meta: meta.clone(),
        });
        let program = Program::new(
            vec![bitvec.construct_domain(vec![bitvec.from_int("toBV32")])],
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
        let preamble = analyze_general(&program, &converter, &factory, false, 1).unwrap();
        let backend_sort =
            Sort::SmtSort(crate::state::identifiers::Identifier::new("(_ BitVec 32)"));
        assert!(preamble.sorts().any(|s| *s == backend_sort));
        assert!(
            preamble
                .collections
                .sorts()
                .any(|s| *s == Sort::Seq(Box::new(backend_sort.clone())))
        );
        assert!(preamble.domains.domains.sorts.is_empty());
        let mut smt =
            crate::decider::term_to_smt_lib2_converter::TermToSmtLib2Converter::new(factory);
        for axiom in &preamble.collections.sequences.contributor.axioms {
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
