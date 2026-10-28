//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/supporters/functions/MaskHeapFunctionEncoding.scala
//!
//! Purpose:
//! Encode heap-dependent functions using resource heaps and footprint-based framing.
//!
//! Planned Rust structure:
//! Port MaskHeapFunctionEncoding stateArgs/adaptAxiom, predicate triggers and application
//! translation; FrameInfo cache, frame/precondition-frame functions and
//! computeFrame/qpFrameAxioms.
//!
//! Behavior to preserve:
//! Use one heap argument per ordered precondition resource; unpack snapshot trees or HeapMapTerm,
//! distribute applications over ITE. Definitional axiom retains direct function trigger and adds
//! predicate-trigger pattern, using stateless trigger only when all quantified arguments are
//! covered, otherwise limited application. Generate value frame axiom, precondition frame only
//! when predicate triggers exist, and QP frame axioms equating condition functions when two heaps
//! agree at permitted quantified locations. Frame expressions handle accesses, conjunction,
//! implication, conditional, let and quantified permissions; preserve wildcard-to-full permission,
//! resource order and recorded QP declarations.
//!
//! Integration:
//! functions::{function_encoding,function_data,heap_access_replacing_expression_translator},
//! rules::{mask_heap_supporter,function_supporter}, state::terms and verifier.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for heap isolation, exact permission checks, trigger coverage,
//! ordered resource maps and solver declarations.
//!
//! Open decisions:
//! Reconcile FrameInfo lifetime, resource indexing and heap/snapshot aliases with mask heap rules
//! and function verification.
//!
//! Status: resource arguments, application/trigger translation, footprint construction and QP
//! frame axioms connect to the native runtime. True frame-construction cycles fail explicitly;
//! debugging and broad source compatibility remain incomplete.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2026 ETH Zurich.
use crate::state::identifiers::IdentifierFactory;
use crate::state::symbol_converter::{DefaultSymbolConverter, SymbolConversionError};
use crate::state::terms::{
    Applicable, Quantifier, ResourceKey, Sort, Term, TermFactory, TermKind, Trigger,
    UnsupportedSubterms, UnsupportedTriggerTransform,
};
use crate::supporters::functions::function_data::FunctionData;
use std::collections::HashMap;

#[derive(Debug)]
pub enum MaskEncodingError {
    Sort(SymbolConversionError),
    Transform(UnsupportedTriggerTransform),
    Traversal(UnsupportedSubterms),
    MissingResource,
    InvalidTrigger,
}
/// Ordered resource heaps for mask-mode function encoding.
pub struct MaskHeapFunctionEncoding;

#[derive(Debug)]
pub enum MaskTriggerAdaptationError<E> {
    Frame(E),
    Transform(UnsupportedTriggerTransform),
}

/// Replace heap-dependent trigger applications by their frame versions, per occurrence.
/// The resolver returns `None` when the source program has no matching function data.
pub fn adapt_trigger_terms<E>(
    factory: &TermFactory,
    terms: &[Term],
    mut frame: impl FnMut(&Applicable, &[Term], &[Term]) -> Result<Option<Term>, E>,
) -> Result<Vec<Term>, MaskTriggerAdaptationError<E>> {
    use crate::state::terms::{ApplicableKind, ApplicationTarget};
    let frame = std::cell::RefCell::new(&mut frame);
    let error = std::cell::RefCell::new(None);
    let mut output = Vec::with_capacity(terms.len());
    for term in terms {
        let result = factory.transform_preorder_descending(term, &|candidate| {
            if error.borrow().is_some() {
                return None;
            }
            let TermKind::App {
                applicable: ApplicationTarget::Function(function),
                args,
            } = candidate.kind()
            else {
                return None;
            };
            if function.data().kind != ApplicableKind::HeapDepFun {
                return None;
            }
            let (heaps, other): (Vec<_>, Vec<_>) = args.iter().cloned().partition(|arg| {
                matches!(arg.sort(), Sort::Heap(_) | Sort::PredHeap | Sort::WandHeap)
            });
            if heaps.is_empty() {
                return None;
            }
            match frame.borrow_mut()(function, &other, &heaps) {
                Ok(Some(value)) => {
                    let frame_function = crate::rules::function_supporter::frame_version(
                        factory,
                        function,
                        heaps.len() as i32,
                    );
                    Some(factory.app(
                        frame_function,
                        std::iter::once(value).chain(other).collect(),
                    ))
                }
                Ok(None) => None,
                Err(err) => {
                    *error.borrow_mut() = Some(err);
                    None
                }
            }
        });
        if let Some(err) = error.borrow_mut().take() {
            return Err(MaskTriggerAdaptationError::Frame(err));
        }
        output.push(result.map_err(MaskTriggerAdaptationError::Transform)?);
    }
    Ok(output)
}
impl MaskHeapFunctionEncoding {
    fn heap_sort(
        converter: &DefaultSymbolConverter,
        resource: &ResourceKey,
    ) -> Result<Sort, MaskEncodingError> {
        Ok(match resource {
            ResourceKey::Field(field) => Sort::Heap(Box::new(
                converter
                    .to_sort(&field.typ)
                    .map_err(MaskEncodingError::Sort)?,
            )),
            ResourceKey::Predicate(_) => Sort::PredHeap,
            ResourceKey::Wand(_) => Sort::WandHeap,
        })
    }
    pub fn state_args(
        factory: &TermFactory,
        converter: &DefaultSymbolConverter,
        identifiers: &mut impl IdentifierFactory,
        resources: &[ResourceKey],
    ) -> Result<Vec<Term>, MaskEncodingError> {
        resources
            .iter()
            .map(|resource| {
                let name = match resource {
                    ResourceKey::Field(field) => field.name.clone(),
                    ResourceKey::Predicate(predicate) => predicate.name.clone(),
                    ResourceKey::Wand(wand) => wand.to_string(),
                };
                Ok(factory.var(
                    identifiers.fresh(&format!("heap_{name}")),
                    Self::heap_sort(converter, resource)?,
                    false,
                ))
            })
            .collect()
    }
    pub fn adapt_axiom(
        factory: &TermFactory,
        converter: &DefaultSymbolConverter,
        axiom: &Term,
        resources: &[ResourceKey],
        state_args: &[Term],
    ) -> Result<Term, MaskEncodingError> {
        let snapshots =
            factory.from_snap_tree(factory.predef_snapshot_var(), resources.len() as i32);
        let mut replacements = HashMap::new();
        for ((snapshot, resource), state_arg) in
            snapshots.into_iter().zip(resources).zip(state_args)
        {
            let heap = factory.snap_to_heap(
                snapshot,
                resource.clone(),
                Self::heap_sort(converter, resource)?,
            );
            replacements.insert(heap, state_arg.clone());
        }
        factory
            .replace(axiom, &replacements)
            .map_err(MaskEncodingError::Transform)
    }
    pub fn predicate_trigger_state_arg(
        predicate: &ferrum_silver::ast::program::Predicate,
        resources: &[ResourceKey],
        state_args: &[Term],
    ) -> Result<Term, MaskEncodingError> {
        let index = resources
            .iter()
            .position(
                |resource| matches!(resource,ResourceKey::Predicate(p) if p.as_ref() == predicate),
            )
            .ok_or(MaskEncodingError::MissingResource)?;
        state_args
            .get(index)
            .cloned()
            .ok_or(MaskEncodingError::MissingResource)
    }
    pub fn definitional_axiom<D>(
        factory: &TermFactory,
        data: &FunctionData<D>,
        body: Term,
        predicate_triggers: &[Term],
    ) -> Result<Term, MaskEncodingError> {
        let mut triggers = Vec::new();
        for predicate in predicate_triggers {
            if !matches!(predicate.kind(), TermKind::App { .. }) {
                return Err(MaskEncodingError::InvalidTrigger);
            }
            let mut covered = data
                .trigger_application
                .free_variables()
                .map_err(MaskEncodingError::Traversal)?;
            for var in predicate
                .free_variables()
                .map_err(MaskEncodingError::Traversal)?
            {
                covered = covered.incl(var);
            }
            let function_trigger = if data.arguments.iter().all(|arg| covered.contains(arg)) {
                data.trigger_application.clone()
            } else {
                data.limited_application.clone()
            };
            triggers.push(Trigger {
                terms: vec![function_trigger, predicate.clone()],
            });
        }
        // Source constructs the predicate axiom first even when no predicate
        // triggers exist; this consumes the default quantifier name in both cases.
        let predicate = factory
            .quantification(
                Quantifier::Forall,
                data.arguments.clone(),
                body.clone(),
                triggers.clone(),
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(MaskEncodingError::Transform)?;
        let direct = factory
            .quantification(
                Quantifier::Forall,
                data.arguments.clone(),
                body,
                vec![Trigger {
                    terms: vec![data.function_application.clone()],
                }],
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(MaskEncodingError::Transform)?;
        if triggers.is_empty() {
            Ok(direct)
        } else {
            Ok(factory.and([predicate, direct]))
        }
    }
    pub fn translate_application(
        factory: &TermFactory,
        converter: &DefaultSymbolConverter,
        function: &Applicable,
        snapshot: &Term,
        args: &[Term],
        resources: &[ResourceKey],
    ) -> Result<Term, MaskEncodingError> {
        match snapshot.kind() {
            TermKind::HeapMapTerm(map) => {
                let heaps = map
                    .iter()
                    .map(|(_, heap)| heap.clone())
                    .chain(args.iter().cloned())
                    .collect();
                Ok(factory.app(function.clone(), heaps))
            }
            TermKind::Ite(condition, yes, no) => Ok(factory.ite(
                condition.clone(),
                Self::translate_application(factory, converter, function, yes, args, resources)?,
                Self::translate_application(factory, converter, function, no, args, resources)?,
            )),
            _ => {
                let parts = factory.from_snap_tree(snapshot.clone(), resources.len() as i32);
                let mut heaps = Vec::new();
                for (part, resource) in parts.into_iter().zip(resources) {
                    let heap = match part.kind() {
                        TermKind::HeapToSnap(heap, ..) => heap.clone(),
                        _ => factory.snap_to_heap(
                            part,
                            resource.clone(),
                            Self::heap_sort(converter, resource)?,
                        ),
                    };
                    heaps.push(heap);
                }
                heaps.extend_from_slice(args);
                Ok(factory.app(function.clone(), heaps))
            }
        }
    }
    pub fn auxiliary_functions(
        factory: &TermFactory,
        function: &Applicable,
        resource_count: usize,
    ) -> Vec<Applicable> {
        vec![
            crate::rules::function_supporter::frame_version(
                factory,
                function,
                resource_count as i32,
            ),
            crate::rules::function_supporter::precondition_frame_version(
                factory,
                function,
                resource_count as i32,
            ),
        ]
    }
    /// Frame axiom, and optional precondition frame axiom when predicate triggers exist.
    pub fn frame_axioms<D>(
        factory: &TermFactory,
        data: &FunctionData<D>,
        frame: Term,
        resource_count: usize,
        has_predicate_triggers: bool,
    ) -> Result<Vec<Term>, MaskEncodingError> {
        let mut args = vec![frame];
        args.extend(data.formal_args.iter().map(|(_, term)| term.clone()));
        let [frame_fun, pre_fun] =
            Self::auxiliary_functions(factory, &data.function, resource_count)
                .try_into()
                .expect("two frame functions");
        // Source computes optional preFrame before frameAxiom, but emits frame first.
        let pre = if has_predicate_triggers {
            let pre_app = factory.app(pre_fun, args.clone());
            Some(
                factory
                    .quantification(
                        Quantifier::Forall,
                        data.arguments.clone(),
                        factory.builtin_equals(data.precondition_application.clone(), pre_app),
                        vec![Trigger {
                            terms: vec![data.precondition_application.clone()],
                        }],
                        TermFactory::forall_default_name(),
                        false,
                        None,
                    )
                    .map_err(MaskEncodingError::Transform)?,
            )
        } else {
            None
        };
        let frame_app = factory.app(frame_fun, args);
        let first = factory
            .quantification(
                Quantifier::Forall,
                data.arguments.clone(),
                factory.builtin_equals(data.limited_application.clone(), frame_app),
                vec![Trigger {
                    terms: vec![data.limited_application.clone()],
                }],
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(MaskEncodingError::Transform)?;
        let mut axioms = vec![first];
        axioms.extend(pre);
        Ok(axioms)
    }
}

pub trait FrameExpressionTranslator {
    type Error;
    /// Translate with heap access resolution and adapt the result to formal resource heaps.
    fn translate_frame_expression(
        &mut self,
        expression: &ferrum_silver::ast::expression::Exp,
    ) -> Result<Term, Self::Error>;
}
#[derive(Debug)]
pub enum FrameConstructionError<E> {
    MissingResource,
    UnsupportedAssertion,
    InvalidQuantifier,
    Transform(UnsupportedTriggerTransform),
    Traversal(UnsupportedSubterms),
    Projection(ferrum_silver::ast::utility::rewriter::strategy::ExpressionReplacementError),
    Instantiation(ferrum_silver::ast::utility::expressions::InstantiateError),
    Wand(ferrum_silver::ast::utility::expressions::MagicWandError),
    Service(E),
}
#[derive(Clone)]
pub struct QuantifiedFrameCondition {
    pub function: Applicable,
    pub assertion: ferrum_silver::ast::expression::Exp,
}
/// Cached per-function frame and quantified-permission condition symbols.
#[derive(Clone)]
pub struct FrameInfo {
    pub frame: Term,
    pub quantified_conditions: Vec<QuantifiedFrameCondition>,
}
impl MaskHeapFunctionEncoding {
    pub fn condition_frame_function(factory: &TermFactory) -> Applicable {
        use crate::state::identifiers::Identifier;
        use crate::state::terms::{ApplicableData, ApplicableKind};
        factory.applicable(ApplicableData {
            kind: ApplicableKind::Fun,
            id: Identifier::new("internalCondFrame"),
            arg_sorts: vec![Sort::Bool, Sort::Snap, Sort::Snap],
            result_sort: Sort::Snap,
        })
    }
    /// Build the footprint snapshot for all precondition conjuncts, retaining every
    /// quantified-permission placeholder for later declarations and frame axioms.
    pub fn compute_frame<D, T: FrameExpressionTranslator>(
        factory: &TermFactory,
        translator: &mut T,
        data: &FunctionData<D>,
        resources: &[ResourceKey],
    ) -> Result<FrameInfo, FrameConstructionError<T::Error>> {
        use crate::state::identifiers::Identifier;
        use crate::state::terms::{ApplicableData, ApplicableKind};
        use ferrum_silver::ast::expression::{Exp, ExpKind};
        use ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion;
        fn combine(factory: &TermFactory, a: Term, b: Term) -> Term {
            if matches!(a.kind(), TermKind::Unit) {
                b
            } else if matches!(b.kind(), TermKind::Unit) {
                a
            } else {
                factory.combine(a, b)
            }
        }
        fn conditional(factory: &TermFactory, condition: Term, yes: Term, no: Term) -> Term {
            if matches!(condition.kind(), TermKind::True) {
                yes
            } else if matches!(condition.kind(), TermKind::False) {
                no
            } else if yes == no {
                yes
            } else {
                factory.app(
                    MaskHeapFunctionEncoding::condition_frame_function(factory),
                    vec![condition, yes, no],
                )
            }
        }
        fn helper<D, T: FrameExpressionTranslator>(
            factory: &TermFactory,
            translator: &mut T,
            data: &FunctionData<D>,
            resources: &[ResourceKey],
            assertion: &Exp,
            conditions: &mut Vec<QuantifiedFrameCondition>,
        ) -> Result<Term, FrameConstructionError<T::Error>> {
            if let Some((forall, _, _)) = quantified_permission_assertion(assertion) {
                let function = factory.applicable(ApplicableData {
                    kind: ApplicableKind::Fun,
                    id: Identifier::new(format!(
                        "{}#condqp{}",
                        data.program_function.name,
                        conditions.len() + 1
                    )),
                    arg_sorts: data.arguments.iter().map(|a| a.sort().clone()).collect(),
                    result_sort: Sort::Snap,
                });
                conditions.push(QuantifiedFrameCondition {
                    function: function.clone(),
                    assertion: forall,
                });
                return Ok(
                    factory.sort_wrapper(factory.app(function, data.arguments.clone()), Sort::Snap)
                );
            }
            match assertion.kind() {
                ExpKind::FieldAccessPredicate(access, _) => {
                    let resource = ResourceKey::Field(std::sync::Arc::new(access.field.clone()));
                    let index = resources
                        .iter()
                        .position(|r| r == &resource)
                        .ok_or(FrameConstructionError::MissingResource)?;
                    let heap = data
                        .state_args
                        .get(index)
                        .ok_or(FrameConstructionError::MissingResource)?
                        .clone();
                    let receiver = translator
                        .translate_frame_expression(&access.receiver)
                        .map_err(FrameConstructionError::Service)?;
                    let value =
                        factory.sort_wrapper(factory.heap_lookup(heap, receiver), Sort::Snap);
                    let permission = assertion
                        .permission_or_full()
                        .expect("field access permission");
                    let wildcard = Exp::new(ExpKind::WildcardPerm, Default::default());
                    let full = Exp::new(ExpKind::FullPerm, Default::default());
                    let permission =
                        ferrum_silver::ast::utility::rewriter::strategy::replace_expressions(
                            &permission,
                            &[(wildcard, full)],
                        )
                        .map_err(FrameConstructionError::Projection)?;
                    let permission = translator
                        .translate_frame_expression(&permission)
                        .map_err(FrameConstructionError::Service)?;
                    Ok(conditional(
                        factory,
                        factory.greater(permission, factory.no_perm()),
                        value,
                        factory.unit(),
                    ))
                }
                ExpKind::PredicateAccessPredicate(access) => {
                    let predicate = data
                        .program
                        .find_predicate_optionally(&access.location.predicate_name)
                        .cloned()
                        .ok_or(FrameConstructionError::MissingResource)?;
                    let resource = ResourceKey::Predicate(std::sync::Arc::new(predicate));
                    let index = resources
                        .iter()
                        .position(|r| r == &resource)
                        .ok_or(FrameConstructionError::MissingResource)?;
                    let heap = data
                        .state_args
                        .get(index)
                        .ok_or(FrameConstructionError::MissingResource)?
                        .clone();
                    let args = access
                        .location
                        .args
                        .iter()
                        .map(|a| {
                            translator
                                .translate_frame_expression(a)
                                .map_err(FrameConstructionError::Service)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let value = factory.heap_lookup(heap, factory.to_snap_tree(args));
                    let permission = access.permission_or_full();
                    let wildcard = Exp::new(ExpKind::WildcardPerm, Default::default());
                    let full = Exp::new(ExpKind::FullPerm, Default::default());
                    let permission =
                        ferrum_silver::ast::utility::rewriter::strategy::replace_expressions(
                            &permission,
                            &[(wildcard, full)],
                        )
                        .map_err(FrameConstructionError::Projection)?;
                    let permission = translator
                        .translate_frame_expression(&permission)
                        .map_err(FrameConstructionError::Service)?;
                    Ok(conditional(
                        factory,
                        factory.greater(permission, factory.no_perm()),
                        value,
                        factory.unit(),
                    ))
                }
                ExpKind::MagicWand(..) => {
                    let wand = crate::state::chunks::MagicWandIdentifier::new(
                        assertion.clone(),
                        &data.program,
                    )
                    .map_err(FrameConstructionError::Wand)?;
                    let resource = ResourceKey::Wand(wand);
                    let index = resources
                        .iter()
                        .position(|r| r == &resource)
                        .ok_or(FrameConstructionError::MissingResource)?;
                    let heap = data
                        .state_args
                        .get(index)
                        .ok_or(FrameConstructionError::MissingResource)?
                        .clone();
                    let expressions = assertion
                        .magic_wand_subexpressions(&data.program)
                        .map_err(FrameConstructionError::Wand)?;
                    let args = expressions
                        .iter()
                        .map(|arg| {
                            translator
                                .translate_frame_expression(arg)
                                .map_err(FrameConstructionError::Service)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    let value = factory.heap_lookup(heap, factory.to_snap_tree(args));
                    Ok(conditional(
                        factory,
                        factory.greater(factory.full_perm(), factory.no_perm()),
                        value,
                        factory.unit(),
                    ))
                }
                ExpKind::Implies(condition, body) => {
                    let condition = translator
                        .translate_frame_expression(condition)
                        .map_err(FrameConstructionError::Service)?;
                    let body = helper(factory, translator, data, resources, body, conditions)?;
                    Ok(factory.sort_wrapper(
                        conditional(factory, condition, body, factory.unit()),
                        Sort::Snap,
                    ))
                }
                ExpKind::And(a, b) => {
                    let a = helper(factory, translator, data, resources, a, conditions)?;
                    let b = helper(factory, translator, data, resources, b, conditions)?;
                    Ok(combine(factory, a, b))
                }
                ExpKind::CondExp(condition, yes, no) => {
                    let condition = translator
                        .translate_frame_expression(condition)
                        .map_err(FrameConstructionError::Service)?;
                    let yes = helper(factory, translator, data, resources, yes, conditions)?;
                    let no = helper(factory, translator, data, resources, no, conditions)?;
                    Ok(factory.sort_wrapper(conditional(factory, condition, yes, no), Sort::Snap))
                }
                ExpKind::Let(decl, value, body) => {
                    let instantiated =
                        ferrum_silver::ast::utility::expressions::instantiate_variables(
                            body,
                            &[decl.clone()],
                            &[value.clone()],
                            &Default::default(),
                        )
                        .map_err(FrameConstructionError::Instantiation)?;
                    helper(
                        factory,
                        translator,
                        data,
                        resources,
                        &instantiated,
                        conditions,
                    )
                }
                _ if assertion.is_pure() => Ok(factory.unit()),
                _ => Err(FrameConstructionError::UnsupportedAssertion),
            }
        }
        let mut conditions = Vec::new();
        fn conjuncts<D, T: FrameExpressionTranslator>(
            factory: &TermFactory,
            translator: &mut T,
            data: &FunctionData<D>,
            resources: &[ResourceKey],
            assertions: &[Exp],
            conditions: &mut Vec<QuantifiedFrameCondition>,
        ) -> Result<Term, FrameConstructionError<T::Error>> {
            let Some((first, rest)) = assertions.split_first() else {
                return Ok(factory.unit());
            };
            let first = helper(factory, translator, data, resources, first, conditions)?;
            if rest.is_empty() {
                return Ok(first);
            }
            let rest = conjuncts(factory, translator, data, resources, rest, conditions)?;
            Ok(combine(factory, first, rest))
        }
        let frame = conjuncts(
            factory,
            translator,
            data,
            resources,
            &data.program_function.pres,
            &mut conditions,
        )?;
        Ok(FrameInfo {
            frame,
            quantified_conditions: conditions,
        })
    }
}

impl MaskHeapFunctionEncoding {
    /// Quantified footprint-frame axioms compare two fresh heap tuples whenever
    /// the quantified locations satisfy the condition and contain the same values.
    pub fn quantified_frame_axioms<D, T: FrameExpressionTranslator>(
        factory: &TermFactory,
        translator: &mut T,
        identifiers: &mut impl IdentifierFactory,
        data: &FunctionData<D>,
        resources: &[ResourceKey],
        info: &FrameInfo,
    ) -> Result<Vec<Term>, FrameConstructionError<T::Error>> {
        use crate::state::chunks::MagicWandIdentifier;
        use crate::state::identifiers::Identifier;
        use ferrum_silver::ast::expression::{Exp, ExpKind};
        use ferrum_silver::ast::utility::quantified_permissions::quantified_permission_assertion;
        let mut axioms = Vec::new();
        for frame in &info.quantified_conditions {
            let (forall, condition, access) = quantified_permission_assertion(&frame.assertion)
                .ok_or(FrameConstructionError::InvalidQuantifier)?;
            let heap_vars: Vec<_> = data
                .arguments
                .iter()
                .take(resources.len())
                .cloned()
                .collect();
            let mut fresh_heaps = || -> Result<Vec<Term>, FrameConstructionError<T::Error>> {
                heap_vars
                    .iter()
                    .map(|heap| {
                        let TermKind::Var(var) = heap.kind() else {
                            return Err(FrameConstructionError::InvalidQuantifier);
                        };
                        Ok(factory.var(identifiers.fresh(&var.id.name()), var.sort.clone(), false))
                    })
                    .collect()
            };
            // Source allocates the complete first tuple before the second tuple.
            let heaps1 = fresh_heaps()?;
            let heaps2 = fresh_heaps()?;
            let rest_args = &data.arguments[resources.len()..];
            let condition = translator
                .translate_frame_expression(&condition)
                .map_err(FrameConstructionError::Service)?;
            let permission = access
                .permission_or_full()
                .ok_or(FrameConstructionError::UnsupportedAssertion)?;
            let wildcard = Exp::new(ExpKind::WildcardPerm, Default::default());
            let full = Exp::new(ExpKind::FullPerm, Default::default());
            let permission = ferrum_silver::ast::utility::rewriter::strategy::replace_expressions(
                &permission,
                &[(wildcard, full)],
            )
            .map_err(FrameConstructionError::Projection)?;
            let permission = translator
                .translate_frame_expression(&permission)
                .map_err(FrameConstructionError::Service)?;
            let condition =
                factory.and([condition, factory.greater(permission, factory.no_perm())]);
            let (argument, resource) = match access.kind() {
                ExpKind::FieldAccessPredicate(access, _) => (
                    translator
                        .translate_frame_expression(&access.receiver)
                        .map_err(FrameConstructionError::Service)?,
                    ResourceKey::Field(std::sync::Arc::new(access.field.clone())),
                ),
                ExpKind::PredicateAccessPredicate(access) => {
                    let predicate = data
                        .program
                        .find_predicate_optionally(&access.location.predicate_name)
                        .cloned()
                        .ok_or(FrameConstructionError::MissingResource)?;
                    let args = access
                        .location
                        .args
                        .iter()
                        .map(|a| {
                            translator
                                .translate_frame_expression(a)
                                .map_err(FrameConstructionError::Service)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    (
                        factory.to_snap_tree(args),
                        ResourceKey::Predicate(std::sync::Arc::new(predicate)),
                    )
                }
                ExpKind::MagicWand(..) => {
                    let wand = MagicWandIdentifier::new(access.clone(), &data.program)
                        .map_err(FrameConstructionError::Wand)?;
                    let expressions = access
                        .magic_wand_subexpressions(&data.program)
                        .map_err(FrameConstructionError::Wand)?;
                    let args = expressions
                        .iter()
                        .map(|a| {
                            translator
                                .translate_frame_expression(a)
                                .map_err(FrameConstructionError::Service)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    (factory.to_snap_tree(args), ResourceKey::Wand(wand))
                }
                _ => return Err(FrameConstructionError::UnsupportedAssertion),
            };
            let resource_index = resources
                .iter()
                .position(|r| r == &resource)
                .ok_or(FrameConstructionError::MissingResource)?;
            let heap = data
                .state_args
                .get(resource_index)
                .ok_or(FrameConstructionError::MissingResource)?
                .clone();
            let ExpKind::Forall(variables, _, _) = forall.kind() else {
                return Err(FrameConstructionError::InvalidQuantifier);
            };
            let mut qvars = Vec::new();
            for variable in variables {
                let exp = Exp::new(
                    ExpKind::LocalVar(variable.local_var()),
                    variable.meta.clone(),
                );
                let term = translator
                    .translate_frame_expression(&exp)
                    .map_err(FrameConstructionError::Service)?;
                if !matches!(term.kind(), TermKind::Var(_)) {
                    return Err(FrameConstructionError::InvalidQuantifier);
                }
                qvars.push(term);
            }
            let names: Vec<_> = qvars
                .iter()
                .filter_map(|v| match v.kind() {
                    TermKind::Var(v) => Some(v.id.name()),
                    _ => None,
                })
                .collect();
            let found = argument
                .deep_collect(&mut |term| match term.kind() {
                    TermKind::Var(v) => match &v.id {
                        Identifier::Suffixed { prefix, .. } if names.contains(&prefix.name()) => {
                            Some((
                                term.clone(),
                                factory.var(
                                    Identifier::Simple(prefix.name()),
                                    v.sort.clone(),
                                    false,
                                ),
                            ))
                        }
                        _ => None,
                    },
                    _ => None,
                })
                .map_err(FrameConstructionError::Traversal)?;
            let replacements: HashMap<_, _> = found.into_iter().collect();
            let argument = factory
                .replace(&argument, &replacements)
                .map_err(FrameConstructionError::Transform)?;
            let first: HashMap<_, _> = heap_vars
                .iter()
                .cloned()
                .zip(heaps1.iter().cloned())
                .collect();
            let second: HashMap<_, _> = heap_vars
                .iter()
                .cloned()
                .zip(heaps2.iter().cloned())
                .collect();
            let cond1 = factory
                .replace(&condition, &first)
                .map_err(FrameConstructionError::Transform)?;
            let cond2 = factory
                .replace(&condition, &second)
                .map_err(FrameConstructionError::Transform)?;
            let arg1 = factory
                .replace(&argument, &first)
                .map_err(FrameConstructionError::Transform)?;
            let arg2 = factory
                .replace(&argument, &second)
                .map_err(FrameConstructionError::Transform)?;
            let heap1 = factory
                .replace(&heap, &first)
                .map_err(FrameConstructionError::Transform)?;
            let heap2 = factory
                .replace(&heap, &second)
                .map_err(FrameConstructionError::Transform)?;
            let lookup1 = factory.heap_lookup(heap1, arg1);
            let lookup2 = factory.heap_lookup(heap2, arg2);
            let same = factory
                .quantification(
                    Quantifier::Forall,
                    qvars,
                    factory.implies(
                        factory.and([cond1, cond2]),
                        factory.equals(lookup1.clone(), lookup2.clone()),
                    ),
                    vec![Trigger {
                        terms: vec![lookup1, lookup2],
                    }],
                    TermFactory::forall_default_name(),
                    false,
                    None,
                )
                .map_err(FrameConstructionError::Transform)?;
            let app1 = factory.app(
                frame.function.clone(),
                heaps1.iter().chain(rest_args).cloned().collect(),
            );
            let app2 = factory.app(
                frame.function.clone(),
                heaps2.iter().chain(rest_args).cloned().collect(),
            );
            let vars = heaps1
                .into_iter()
                .chain(heaps2)
                .chain(rest_args.iter().cloned())
                .collect();
            let axiom = factory
                .quantification(
                    Quantifier::Forall,
                    vars,
                    factory.implies(same, factory.builtin_equals(app1.clone(), app2.clone())),
                    vec![Trigger {
                        terms: vec![app1, app2],
                    }],
                    TermFactory::forall_default_name(),
                    false,
                    None,
                )
                .map_err(FrameConstructionError::Transform)?;
            axioms.push(axiom);
        }
        Ok(axioms)
    }
}

/// Worker-local identity-keyed frame cache, matching the source FunctionData keys.
pub struct FrameCache<D> {
    entries: Vec<(std::sync::Arc<FunctionData<D>>, FrameInfo)>,
}
impl<D> Default for FrameCache<D> {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
        }
    }
}
impl<D> FrameCache<D> {
    pub fn get_or_compute<T: FrameExpressionTranslator>(
        &mut self,
        factory: &TermFactory,
        translator: &mut T,
        data: &std::sync::Arc<FunctionData<D>>,
        resources: &[ResourceKey],
    ) -> Result<&FrameInfo, FrameConstructionError<T::Error>> {
        if let Some(index) = self
            .entries
            .iter()
            .position(|(key, _)| std::sync::Arc::ptr_eq(key, data))
        {
            return Ok(&self.entries[index].1);
        }
        let frame = MaskHeapFunctionEncoding::compute_frame(factory, translator, data, resources)?;
        self.entries.push((data.clone(), frame));
        Ok(&self.entries.last().expect("inserted frame").1)
    }
    pub fn clear(&mut self) {
        self.entries.clear();
    }
}

/// Identity cache for FunctionData, retaining a unique token even after an instance is dropped.
pub struct SharedFrameCache<D> {
    entries: Vec<(std::sync::Arc<()>, FrameInfo)>,
    marker: std::marker::PhantomData<fn() -> D>,
}
impl<D> Default for SharedFrameCache<D> {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
            marker: std::marker::PhantomData,
        }
    }
}
impl<D: Clone> SharedFrameCache<D> {
    pub fn get(&self, identity: &std::sync::Arc<()>) -> Option<FrameInfo> {
        self.entries
            .iter()
            .find(|(key, _)| std::sync::Arc::ptr_eq(key, identity))
            .map(|(_, info)| info.clone())
    }
    /// Retain the first successful frame for each source FunctionData identity.
    pub fn insert(&mut self, identity: std::sync::Arc<()>, info: FrameInfo) {
        if !self
            .entries
            .iter()
            .any(|(key, _)| std::sync::Arc::ptr_eq(key, &identity))
        {
            self.entries.push((identity, info));
        }
    }
    pub fn get_or_compute<T: FrameExpressionTranslator>(
        &mut self,
        factory: &TermFactory,
        translator: &mut T,
        data: &FunctionData<D>,
        resources: &[ResourceKey],
    ) -> Result<&FrameInfo, FrameConstructionError<T::Error>> {
        let identity = data.identity();
        if let Some(index) = self
            .entries
            .iter()
            .position(|(key, _)| std::sync::Arc::ptr_eq(key, &identity))
        {
            return Ok(&self.entries[index].1);
        }
        let info = MaskHeapFunctionEncoding::compute_frame(factory, translator, data, resources)?;
        self.entries.push((identity, info));
        Ok(&self.entries.last().expect("inserted frame").1)
    }
    pub fn clear(&mut self) {
        self.entries.clear();
    }
}
impl FrameInfo {
    pub fn declarations(&self, factory: &TermFactory) -> Vec<crate::state::terms::Declaration> {
        self.quantified_conditions
            .iter()
            .map(|item| factory.function_decl(item.function.clone()))
            .collect()
    }
    pub fn instantiated_frame<D>(
        &self,
        factory: &TermFactory,
        data: &FunctionData<D>,
        args: &[Term],
        heaps: &[Term],
    ) -> Result<Term, UnsupportedTriggerTransform> {
        let from = data
            .formal_args
            .iter()
            .map(|(_, term)| term.clone())
            .chain(data.state_args.iter().cloned());
        let to = args.iter().chain(heaps).cloned();
        let replacements: HashMap<_, _> = from.zip(to).collect();
        factory.replace(&self.frame, &replacements)
    }
}
