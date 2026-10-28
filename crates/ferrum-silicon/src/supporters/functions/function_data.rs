//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/FunctionData.scala
//!
//! Purpose:
//! Accumulate function verification recordings and construct phase-specific axioms.
//!
//! Planned Rust structure:
//! Port FunctionRecorderHandler and FunctionData: formal/state/result variables,
//! function/limited/stateless/precondition symbols, phase transitions, nested definitions,
//! predicate triggers, post/definition/precondition-propagation axioms.
//!
//! Behavior to preserve:
//! Merge recorders and retain insertion-ordered fresh declarations across phases; filter nested
//! definitions with unknown free variables. Limited and trigger axioms precede post axiom; phase 1
//! post axiom binds result to limited application, phase 2 definition guards body equality by
//! precondition and suppresses predicate triggers for opaque functions. Derive predicate triggers
//! from outer recursive unfoldings whose arguments have no free variables outside the formals;
//! arguments may be expressions. Preserve propagation axioms and encoding adaptations.
//!
//! Integration:
//! functions::{function_recorder,function_encoding,heap_access_replacing_expression_translator,function_verification_unit},
//! supporters::predicate_verification_unit, rules quantified definitions and state::terms.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for term identity, ordering, source contexts and phase ownership.
//!
//! Open decisions:
//! Resolve free-variable filtering, recorder lifecycle and snapshot/heap encoding contracts with
//! function verification and rules.
//!
//! Status: partial; shared function-recorder aggregation and ordered symbol collection
//! implemented, plus function symbols, phase transition and default post/definition axioms.
//! Alternate encodings and verification integration remain pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet;
use crate::state::terms::{ApplicationTarget, Declaration, Term, TermFactory, TermKind};
use crate::supporters::functions::function_recorder::{FunctionRecorder, SnapshotKey};

#[derive(Debug)]
pub enum RecorderHandlerError {
    InvalidSnapshotMap,
    InvalidPermissionMap,
}
/// Source FunctionRecorderHandler's accumulated cross-phase symbol declarations.
/// Individual recordings are replaced on each phase, while declarations accumulate.
pub struct FunctionRecorderHandler<D> {
    pub recorder: FunctionRecorder<D>,
    pub location_snapshots: Vec<(SnapshotKey, Term)>,
    pub function_snapshots: Vec<(SnapshotKey, Term)>,
    pub fresh_symbols_across_phases: InsertionOrderedSet<Declaration>,
}
impl<D> Default for FunctionRecorderHandler<D> {
    fn default() -> Self {
        Self {
            recorder: FunctionRecorder::Noop,
            location_snapshots: vec![],
            function_snapshots: vec![],
            fresh_symbols_across_phases: InsertionOrderedSet::new(),
        }
    }
}
impl<D: Clone> FunctionRecorderHandler<D> {
    pub fn add_recorders(
        &mut self,
        factory: &TermFactory,
        recorders: &[FunctionRecorder<D>],
        additional: &[Declaration],
    ) -> Result<(), RecorderHandlerError> {
        let recorder = if let Some((first, rest)) = recorders.split_first() {
            rest.iter().fold(first.clone(), |acc, next| acc.merge(next))
        } else {
            FunctionRecorder::Noop
        };
        let mut symbols = self.fresh_symbols_across_phases.clone();
        if let FunctionRecorder::Actual(actual) = &recorder {
            for symbol in &actual.fresh_path_symbols {
                symbols = symbols.incl(factory.function_decl_target(symbol.clone()));
            }
            for (var, _) in &actual.fresh_constrained_vars {
                symbols = symbols
                    .incl(factory.function_decl_target(ApplicationTarget::Variable(var.clone())));
            }
            for symbol in &actual.fresh_snapshots {
                symbols = symbols.incl(factory.function_decl_target(symbol.clone()));
            }
            for inverse in &actual.fresh_field_invs {
                for function in inverse.inverses().chain(inverse.images()) {
                    symbols = symbols.incl(factory.function_decl_target(function.clone()));
                }
            }
            for decl in &actual.fresh_macros {
                symbols = symbols.incl(decl.clone());
            }
            let declaration = |term: &Term| match term.kind() {
                TermKind::Var(_) => {
                    Some(factory.function_decl_target(ApplicationTarget::Variable(term.clone())))
                }
                TermKind::App {
                    applicable: ApplicationTarget::Function(fun),
                    ..
                } => Some(factory.function_decl(fun.clone())),
                _ => None,
            };
            for map in &actual.fresh_fvfs_and_domains {
                symbols = symbols.incl(
                    declaration(&map.snapshot_map)
                        .ok_or(RecorderHandlerError::InvalidSnapshotMap)?,
                );
            }
            for map in &actual.fresh_perm_maps {
                symbols = symbols.incl(
                    declaration(&map.permission_map)
                        .ok_or(RecorderHandlerError::InvalidPermissionMap)?,
                );
            }
        }
        for declaration in additional {
            symbols = symbols.incl(declaration.clone());
        }
        self.location_snapshots = recorder.location_snapshots(factory);
        self.function_snapshots = recorder.function_snapshots(factory);
        self.recorder = recorder;
        self.fresh_symbols_across_phases = symbols;
        Ok(())
    }
}

#[derive(Debug)]
pub enum FunctionDataError {
    Sort(crate::state::symbol_converter::SymbolConversionError),
    Transform(crate::state::terms::UnsupportedTriggerTransform),
    Recorder(RecorderHandlerError),
    InvalidPhase,
    MissingDebugVersionSeparator,
}
/// Per-function symbols and axioms constructed at analysis; later phases append
/// recorded declarations and produce translated postcondition/body axioms.
pub struct FunctionData<D> {
    pub program_function: ferrum_silver::ast::program::Function,
    pub program: ferrum_silver::ast::program::Program,
    pub height: i32,
    pub quantified_fields: Vec<ferrum_silver::ast::program::Field>,
    pub function: crate::state::terms::Applicable,
    pub limited_function: crate::state::terms::Applicable,
    pub stateless_function: crate::state::terms::Applicable,
    pub precondition_function: crate::state::terms::Applicable,
    pub state_args: Vec<Term>,
    pub formal_args: Vec<(crate::state::store::AbstractLocalVar, Term)>,
    pub formal_result: Term,
    pub formal_result_exp: Option<ferrum_silver::ast::expression::Exp>,
    pub arguments: Vec<Term>,
    pub arguments_during_verification: Vec<Term>,
    pub argument_exps: Vec<Option<ferrum_silver::ast::expression::Exp>>,
    pub argument_exps_during_verification: Vec<Option<ferrum_silver::ast::expression::Exp>>,
    pub function_application: Term,
    pub limited_application: Term,
    pub trigger_application: Term,
    pub precondition_application: Term,
    pub limited_axiom: Term,
    pub trigger_axiom: Term,
    pub recorder_handler: FunctionRecorderHandler<D>,
    phase: u8,
}
impl<D: Clone> FunctionData<D> {
    pub fn new(
        factory: &TermFactory,
        converter: &crate::state::symbol_converter::DefaultSymbolConverter,
        identifiers: &mut impl crate::state::identifiers::IdentifierFactory,
        program_function: ferrum_silver::ast::program::Function,
        program: ferrum_silver::ast::program::Program,
        height: i32,
        quantified_fields: Vec<ferrum_silver::ast::program::Field>,
        state_args: Vec<Term>,
        resources: Option<&[crate::state::terms::ResourceKey]>,
        debugging: bool,
    ) -> Result<Self, FunctionDataError> {
        use crate::rules::function_supporter::{
            limited_version, precondition_version, stateless_version,
        };
        use crate::state::store::AbstractLocalVar;
        use crate::state::terms::{Quantifier, Trigger};
        use ferrum_silver::ast::expression::{Exp, ExpKind, LocalVar};
        use ferrum_silver::ast::r#type::Type;
        let function = converter
            .heap_dependent_function(&program_function, &program, resources)
            .map_err(FunctionDataError::Sort)?;
        let limited_function = limited_version(factory, &function);
        let stateless_function = stateless_version(factory, &function, state_args.len() as i32);
        let precondition_function = precondition_version(factory, &function);
        let mut formal_args = Vec::new();
        for formal in &program_function.formal_args {
            let variable = factory.var(
                identifiers.fresh(&formal.name),
                converter
                    .to_sort(&formal.typ)
                    .map_err(FunctionDataError::Sort)?,
                false,
            );
            let local = AbstractLocalVar::new(Exp::new(
                ExpKind::LocalVar(formal.local_var()),
                formal.meta.clone(),
            ));
            if let Some((_, old)) = formal_args
                .iter_mut()
                .find(|(existing, _)| *existing == local)
            {
                *old = variable;
            } else {
                formal_args.push((local, variable));
            }
        }
        let result_id = identifiers.fresh("result");
        let formal_result = factory.var(
            result_id.clone(),
            converter
                .to_sort(&program_function.typ)
                .map_err(FunctionDataError::Sort)?,
            false,
        );
        let formal_result_exp = if debugging {
            let name = result_id.name();
            let index = name
                .rfind('@')
                .ok_or(FunctionDataError::MissingDebugVersionSeparator)?;
            Some(Exp::new(
                ExpKind::LocalVarWithVersion(
                    name[..index].to_string(),
                    program_function.typ.clone(),
                ),
                Default::default(),
            ))
        } else {
            None
        };
        let locals: Vec<_> = formal_args.iter().map(|(_, var)| var.clone()).collect();
        let arguments: Vec<_> = state_args.iter().chain(&locals).cloned().collect();
        let arguments_during_verification: Vec<_> = std::iter::once(factory.predef_snapshot_var())
            .chain(locals.iter().cloned())
            .collect();
        let debug_snapshot = || {
            Exp::new(
                ExpKind::LocalVar(LocalVar::new(
                    "?s".into(),
                    Type::InternalType,
                    Default::default(),
                )),
                Default::default(),
            )
        };
        let local_exps: Vec<_> = formal_args
            .iter()
            .map(|(var, _)| var.expression().clone())
            .collect();
        let argument_exps_during_verification = if debugging {
            std::iter::once(Some(debug_snapshot()))
                .chain(local_exps.iter().cloned().map(Some))
                .collect()
        } else {
            vec![None; 1 + locals.len()]
        };
        let argument_exps = if debugging {
            std::iter::once(Some(debug_snapshot()))
                .chain(local_exps.into_iter().map(Some))
                .collect()
        } else {
            vec![None; state_args.len() + locals.len()]
        };
        let function_application = factory.app(function.clone(), arguments.clone());
        let limited_application = factory.app(limited_function.clone(), arguments.clone());
        let trigger_application = factory.app(stateless_function.clone(), locals);
        let precondition_application =
            factory.app(precondition_function.clone(), arguments.clone());
        let limited_axiom = factory
            .quantification(
                Quantifier::Forall,
                arguments.clone(),
                factory.builtin_equals(limited_application.clone(), function_application.clone()),
                vec![Trigger {
                    terms: vec![function_application.clone()],
                }],
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(FunctionDataError::Transform)?;
        let trigger_axiom = factory
            .quantification(
                Quantifier::Forall,
                arguments.clone(),
                trigger_application.clone(),
                vec![Trigger {
                    terms: vec![limited_application.clone()],
                }],
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(FunctionDataError::Transform)?;
        Ok(Self {
            program_function,
            program,
            height,
            quantified_fields,
            function,
            limited_function,
            stateless_function,
            precondition_function,
            state_args,
            formal_args,
            formal_result,
            formal_result_exp,
            arguments,
            arguments_during_verification,
            argument_exps,
            argument_exps_during_verification,
            function_application,
            limited_application,
            trigger_application,
            precondition_application,
            limited_axiom,
            trigger_axiom,
            recorder_handler: FunctionRecorderHandler::default(),
            phase: 0,
        })
    }
    pub fn phase(&self) -> u8 {
        self.phase
    }
    pub fn advance_phase(
        &mut self,
        factory: &TermFactory,
        recorders: &[FunctionRecorder<D>],
        additional_first_phase: &[Declaration],
    ) -> Result<(), FunctionDataError> {
        if self.phase > 1 {
            return Err(FunctionDataError::InvalidPhase);
        }
        self.recorder_handler
            .add_recorders(
                factory,
                recorders,
                if self.phase == 0 {
                    additional_first_phase
                } else {
                    &[]
                },
            )
            .map_err(FunctionDataError::Recorder)?;
        self.phase += 1;
        Ok(())
    }
}

impl<D: Clone> FunctionData<D> {
    /// Build the phase-one postcondition axiom using the limited application for `result`.
    pub fn post_axiom<E>(
        &self,
        factory: &TermFactory,
        translated_posts: &[Term],
        nested: &[Term],
        adapt: impl FnOnce(Term) -> Result<Term, E>,
    ) -> Result<Option<Term>, FunctionAxiomError<E>> {
        use crate::state::terms::{Quantifier, Trigger};
        if self.phase != 1 {
            return Err(FunctionAxiomError::InvalidPhase);
        }
        if self.program_function.posts.is_empty() {
            return Ok(None);
        }
        let implication = factory.implies(
            self.precondition_application.clone(),
            factory.and(translated_posts.to_vec()),
        );
        let body = factory.and(nested.iter().cloned().chain(std::iter::once(implication)));
        let body = factory.let_term(
            [(self.formal_result.clone(), self.limited_application.clone())],
            body,
        );
        let axiom = factory
            .quantification(
                Quantifier::Forall,
                self.arguments.clone(),
                body,
                vec![Trigger {
                    terms: vec![self.limited_application.clone()],
                }],
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(FunctionAxiomError::Transform)?;
        adapt(axiom).map(Some).map_err(FunctionAxiomError::Adapt)
    }
    /// Build the phase-two definition; opaque annotations remove predicate triggers.
    pub fn definitional_axiom<E>(
        &self,
        factory: &TermFactory,
        translated_body: Option<Term>,
        nested: &[Term],
        predicate_triggers: &[Term],
        adapt: impl FnOnce(Term) -> Result<Term, E>,
    ) -> Result<Option<Term>, FunctionAxiomError<E>> {
        self.definitional_axiom_with_encoding(factory,translated_body,nested,predicate_triggers,
            |body,triggers| crate::supporters::functions::function_encoding::DefaultFunctionEncoding::definitional_axiom(
                factory,self.arguments.clone(),body,self.function_application.clone(),self.trigger_application.clone(),triggers)
                .map_err(FunctionAxiomError::Transform),adapt)
    }
    /// Select the source function encoding before applying its axiom adaptation.
    pub fn definitional_axiom_with_encoding<E>(
        &self,
        factory: &TermFactory,
        translated_body: Option<Term>,
        nested: &[Term],
        predicate_triggers: &[Term],
        encode: impl FnOnce(Term, &[Term]) -> Result<Term, FunctionAxiomError<E>>,
        adapt: impl FnOnce(Term) -> Result<Term, E>,
    ) -> Result<Option<Term>, FunctionAxiomError<E>> {
        use ferrum_silver::ast::ast::Info;
        if self.phase != 2 {
            return Err(FunctionAxiomError::InvalidPhase);
        }
        let Some(translated_body) = translated_body else {
            return Ok(None);
        };
        let equality = factory.builtin_equals(self.function_application.clone(), translated_body);
        let body = factory.and(
            nested
                .iter()
                .cloned()
                .chain(std::iter::once(factory.implies(
                    self.precondition_application.clone(),
                    factory.and([equality]),
                ))),
        );
        let opaque = matches!(self.program_function.meta.info.find(&|info|matches!(info,Info::Annotation(_))),
            Some(Info::Annotation(values)) if values.contains_key("opaque"));
        let triggers = if opaque { &[][..] } else { predicate_triggers };
        let axiom = encode(body, triggers)?;
        adapt(axiom).map(Some).map_err(FunctionAxiomError::Adapt)
    }
}
#[derive(Debug)]
pub enum FunctionAxiomError<E> {
    InvalidPhase,
    Transform(crate::state::terms::UnsupportedTriggerTransform),
    Adapt(E),
}

impl<D: Clone> FunctionData<D> {
    /// Retain recorded definitions whose free variables are formal arguments or
    /// identifiers of declared fresh symbols, in source insertion order.
    pub fn nested_definitional_axioms(
        &self,
    ) -> Result<InsertionOrderedSet<Term>, crate::state::terms::UnsupportedSubterms> {
        let mut terms = InsertionOrderedSet::new();
        if let FunctionRecorder::Actual(actual) = &self.recorder_handler.recorder {
            for inverse in &actual.fresh_field_invs {
                for term in inverse.definitional_axioms() {
                    terms = terms.incl(term.clone());
                }
            }
            for map in &actual.fresh_fvfs_and_domains {
                for term in map.domain_definitions.iter().chain(&map.value_definitions) {
                    terms = terms.incl(term.clone());
                }
            }
            for map in &actual.fresh_perm_maps {
                for term in &map.value_definitions {
                    terms = terms.incl(term.clone());
                }
            }
            for (_, term) in &actual.fresh_constrained_vars {
                terms = terms.incl(term.clone());
            }
            for term in &actual.fresh_constraints {
                terms = terms.incl(term.clone());
            }
        }
        let symbols: Vec<_> = self
            .recorder_handler
            .fresh_symbols_across_phases
            .iter()
            .map(|decl| decl.id())
            .collect();
        let mut result = InsertionOrderedSet::new();
        for term in terms {
            let free = term.free_variables()?;
            let valid = free.iter().all(|var| {
                if self.arguments.contains(var) {
                    return true;
                }
                match var.kind() {
                    TermKind::Var(v) => symbols.contains(&v.id),
                    _ => false,
                }
            });
            if valid {
                result = result.incl(term);
            }
        }
        Ok(result)
    }
}

impl<D: Clone> FunctionData<D> {
    pub fn body_precondition_axioms<E>(
        &self,
        factory: &TermFactory,
        body: Option<&Term>,
        mut transform: impl FnMut(&Term) -> Result<Term, E>,
        mut adapt: impl FnMut(Term) -> Result<Term, E>,
    ) -> Result<Vec<Term>, FunctionAxiomError<E>> {
        use crate::state::terms::{Quantifier, Trigger};
        if self.program_function.body.is_none() {
            return Ok(vec![]);
        }
        let Some(body) = body else {
            return Ok(vec![]);
        };
        let precondition = transform(body).map_err(FunctionAxiomError::Adapt)?;
        let body = factory.implies(self.precondition_application.clone(), precondition);
        let axiom = factory
            .quantification(
                Quantifier::Forall,
                self.arguments.clone(),
                body,
                vec![Trigger {
                    terms: vec![self.function_application.clone()],
                }],
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(FunctionAxiomError::Transform)?;
        Ok(vec![adapt(axiom).map_err(FunctionAxiomError::Adapt)?])
    }
    pub fn post_precondition_axioms<E>(
        &self,
        factory: &TermFactory,
        posts: &[Term],
        mut transform: impl FnMut(&Term) -> Result<Term, E>,
        mut adapt: impl FnMut(Term) -> Result<Term, E>,
    ) -> Result<Vec<Term>, FunctionAxiomError<E>> {
        use crate::state::terms::{Quantifier, Trigger};
        let mut axioms = Vec::new();
        if self.program_function.posts.is_empty() {
            return Ok(axioms);
        }
        for post in posts {
            let precondition = transform(post).map_err(FunctionAxiomError::Adapt)?;
            let body = factory.let_term(
                [(self.formal_result.clone(), self.limited_application.clone())],
                factory.implies(self.precondition_application.clone(), precondition),
            );
            let axiom = factory
                .quantification(
                    Quantifier::Forall,
                    self.arguments.clone(),
                    body,
                    vec![Trigger {
                        terms: vec![self.limited_application.clone()],
                    }],
                    TermFactory::forall_default_name(),
                    false,
                    None,
                )
                .map_err(FunctionAxiomError::Transform)?;
            axioms.push(adapt(axiom).map_err(FunctionAxiomError::Adapt)?);
        }
        Ok(axioms)
    }
}
