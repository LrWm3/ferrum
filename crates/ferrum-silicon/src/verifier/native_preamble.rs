//! Ferrum native contributor assembly described in PLAN.md.
//! Source domain contributor integration for the native verifier.
//! Upstream: https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/Domains.scala
//! Status: non-generic, axiom-free user domains and their uninterpreted functions are
//! analyzed and emitted; generic instances, domain axioms and collection domains fail explicitly.
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
    Sink(E),
}
/// Collected source-order declarations and uniqueness assumptions for later emission.
#[derive(Default)]
pub struct NativePreambleData {
    domains: DefaultDomainsContributor,
}
impl NativePreambleData {
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
    if program.domains.iter().any(|d| !d.type_vars.is_empty()) {
        return Err(NativePreambleError::Unsupported(
            "generic domain instantiation",
        ));
    }
    if program.domains.iter().any(|d| !d.axioms.is_empty()) {
        return Err(NativePreambleError::Unsupported("domain axiom translation"));
    }
    let ground = collect_ground_types(&Node::Program(program.clone()), program)
        .map_err(NativePreambleError::GroundTypes)?;
    if ground.iter().any(|t| {
        matches!(
            t,
            Type::Seq(_) | Type::Set(_) | Type::Multiset(_) | Type::Map(_)
        )
    }) {
        return Err(NativePreambleError::Unsupported(
            "collection domain analysis",
        ));
    }
    let mut result = NativePreambleData::default();
    for domain in &program.domains {
        let Some(typ) = ground
            .iter()
            .find(|t| matches!(t, Type::Domain(d) if d.domain_name == domain.name))
        else {
            continue;
        };
        let sort = converter
            .to_sort(typ)
            .map_err(NativePreambleError::Symbol)?;
        result.domains.sorts = result.domains.sorts.incl(sort);
        for function in &domain.functions {
            if function.interpretation.is_some() {
                continue;
            }
            let applicable = converter
                .domain_function(function, program)
                .map_err(NativePreambleError::Symbol)?;
            result
                .domains
                .collect_function(applicable, function.unique)
                .map_err(NativePreambleError::Domain)?;
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
