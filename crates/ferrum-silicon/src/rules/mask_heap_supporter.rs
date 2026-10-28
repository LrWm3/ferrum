//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/MaskHeapSupporter.scala
//!
//! Purpose:
//! Implement alternative mask-and-heap symbolic resource encoding.
//!
//! Planned Rust structure:
//! maskHeapSupporter implements HeapSupportRules and StatefulComponent: resource sequence
//! cache/lifecycle, ordered map merge, mask heap lookup/creation, wand heap merge and snapshot
//! conversions; mask subtraction/single-add simplification and bounds; single/quantified consume
//! and produce; field, current permission, havoc, forperm, function/predicate snapshots, resource
//! triggers and wand operations.
//!
//! Behavior to preserve:
//! Cache ordered resource sequences and clear on reset; resources sorted by name and first-map
//! ordering retained during map merge. Wand heap merge sums overlapping masks and merges heaps,
//! retaining resources appearing on just one side. Consume checks exact or constrainable permissions
//! and read-only access, uses reserve transfer during packaging and sums consumed masks; otherwise
//! subtract mask
//! and optionally freshen heap constrained to agree on known locations. simplifyOnConsume selects
//! solver-assisted cancellation. Quantified paths assume auxiliary and inverse definitions, assert
//! nonnegative permission and injectivity, build mask definitions and report appropriate failures;
//! inhale injectivity may be configured as assumed. Produce merges masks and heaps, assumes
//! good-mask and field bounds/non-nullness. Empty heaps use zero masks with fresh or dummy heaps.
//! Field reads/assignments assert permission, havoc frames untouched locations, trigger variants
//! offer heap and mask lookups, and function triggers use frame encoding. Preserve resource
//! snapshot conversion, predicate and wand-specific layouts and reserve merging.
//!
//! Integration:
//! rules::heap_supporter, quantified_chunk_support, magic_wand_supporter, evaluator, state::terms,
//! supporters::functions::mask_heap_function_encoding and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Mask/snapshot representation, ordered resource identity and solver/continuation ownership.
//!
//! Status: partial; resource discovery, snapshots, ordinary and quantified permission operations,
//! havoc and per-heap extended-exhale transfer steps are implemented. Full verifier integration,
//! trigger adaptation, transfer orchestration, debug expressions and source-level validation remain.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2025 ETH Zurich.
use crate::resources::resources::ResourceId;
use crate::state::chunks::{BasicMaskHeapChunk, Chunk, MagicWandIdentifier};
use crate::state::heap::{Heap, ListBackedHeap};
use crate::state::symbol_converter::{DefaultSymbolConverter, SymbolConversionError};
use crate::state::terms::{ResourceKey, Sort, Term, TermFactory, TermKind};
use ferrum_silver::ast::{
    expression::{Exp, ExpKind},
    program::Program,
    utility::{
        expressions::MagicWandError,
        nodes::{Node, TraversalError, subnodes},
        visitor::shallow_collect,
    },
};
use std::sync::Arc;

#[derive(Debug)]
pub enum ResourceDiscoveryError {
    Traversal(TraversalError),
    Wand(MagicWandError),
    MissingPredicate(String),
}
#[derive(Default)]
pub struct ResourceSequenceCache {
    entries: Vec<(Vec<Exp>, Vec<ResourceKey>)>,
}
impl ResourceSequenceCache {
    pub fn reset(&mut self) {
        self.entries.clear();
    }
    /// As upstream, the cache key is the ordered expression sequence, not the program identity.
    pub fn resources(
        &mut self,
        expressions: &[Exp],
        program: &Program,
    ) -> Result<Vec<ResourceKey>, ResourceDiscoveryError> {
        if let Some((_, resources)) = self.entries.iter().find(|(key, _)| key == expressions) {
            return Ok(resources.clone());
        }
        let mut resources = Vec::new();
        for expression in expressions {
            let nodes = shallow_collect(&[Node::Exp(expression.clone())], &subnodes, &mut |node| {
                if let Node::Exp(e) = node {
                    match e.kind() {
                        ExpKind::FieldAccessPredicate(..)
                        | ExpKind::PredicateAccessPredicate(..)
                        | ExpKind::MagicWand(..) => return Some(e.clone()),
                        _ => {}
                    }
                }
                None
            })
            .map_err(ResourceDiscoveryError::Traversal)?;
            for expression in nodes {
                let resource = match expression.kind() {
                    ExpKind::FieldAccessPredicate(access, _) => {
                        ResourceKey::Field(Arc::new(access.field.clone()))
                    }
                    ExpKind::PredicateAccessPredicate(access) => {
                        let name = &access.location.predicate_name;
                        let predicate = program
                            .predicates
                            .iter()
                            .find(|p| &p.name == name)
                            .ok_or_else(|| {
                                ResourceDiscoveryError::MissingPredicate(name.clone())
                            })?;
                        ResourceKey::Predicate(Arc::new(predicate.clone()))
                    }
                    ExpKind::MagicWand(..) => ResourceKey::Wand(
                        MagicWandIdentifier::new(expression.clone(), program)
                            .map_err(ResourceDiscoveryError::Wand)?,
                    ),
                    _ => unreachable!(),
                };
                if !resources.contains(&resource) {
                    resources.push(resource);
                }
            }
        }
        resources.sort_by_cached_key(|r| {
            match r {
                ResourceKey::Field(f) => f.name.clone(),
                ResourceKey::Predicate(p) => p.name.clone(),
                ResourceKey::Wand(w) => w.to_string(),
            }
            .encode_utf16()
            .collect::<Vec<_>>()
        });
        self.entries.push((expressions.to_vec(), resources.clone()));
        Ok(resources)
    }
}

/// Fail explicitly on mixed heaps or absent required resource/mask entries.
#[derive(Debug)]
pub enum MaskHeapError<E> {
    NonMaskChunk,
    MissingResource,
    MissingMask,
    MissingArgument,
    WrongResourceKind,
    InvalidQuantifier,
    Sort(SymbolConversionError),
    ExpressionType(ferrum_silver::ast::expression::ExpressionTypeError),
    Wand(MagicWandError),
    Trigger(crate::state::terms::UnsupportedTriggerTransform),
    Service(E),
}

/// Evaluated source QP components. Explicit triggers distinguish `Some(empty)` from none.
pub struct MaskQuantifiedInputs {
    pub resource: ResourceKey,
    pub qvars: Vec<Term>,
    pub qvar_expressions: Option<Vec<ferrum_silver::ast::program::LocalVarDecl>>,
    pub formal_qvars: Vec<Term>,
    pub formal_qvar_expressions: Option<Vec<ferrum_silver::ast::program::LocalVarDecl>>,
    pub condition: Term,
    pub condition_expression: Option<Exp>,
    pub arguments: Vec<Term>,
    pub argument_expressions: Option<Vec<Exp>>,
    pub permission: Term,
    pub permission_expression: Option<Exp>,
    pub scaling: Term,
    /// Present for inhale/production; source quantified consumption has no input snapshot.
    pub snapshot: Option<Term>,
    pub explicit_triggers: Option<Vec<crate::state::terms::Trigger>>,
    pub translated_triggers: Vec<crate::state::terms::Trigger>,
    pub auxiliary_globals: Vec<Term>,
    pub auxiliary_non_globals: Vec<Term>,
    pub auxiliary_debug: Option<(
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::debugger::debug_exp::DebugExp,
        >,
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::debugger::debug_exp::DebugExp,
        >,
    )>,
    pub qid: String,
    pub quantifier: Exp,
}

pub trait MaskQuantifiedProductionService: MaskHeapProductionService {
    fn fresh_inverse(
        &mut self,
        input: &MaskQuantifiedInputs,
    ) -> Result<
        (
            crate::rules::quantified_chunk_support::InverseFunctions,
            Vec<Term>,
        ),
        Self::Error,
    >;
    fn injectivity(&mut self, input: &MaskQuantifiedInputs) -> Result<Term, Self::Error>;
    fn transform_precondition(&mut self, term: Term) -> Result<Term, Self::Error>;
    fn assert_goal(&mut self, term: Term) -> Result<bool, Self::Error>;
    fn assume_definition(&mut self, term: Term) -> Result<(), Self::Error>;
    fn no_triggers(&mut self, quantifier: &Exp) -> Result<(), Self::Error>;
    fn record_inverse_and_mask(
        &mut self,
        inverse: crate::rules::quantified_chunk_support::InverseFunctions,
        mask: Term,
        definition: Term,
    ) -> Result<(), Self::Error>;
}

pub enum MaskQuantifiedProduction {
    Complete { heap: ListBackedHeap },
    NegativePermission { condition: Term },
    NonInjective { condition: Term },
}

pub trait MaskQuantifiedConsumptionService: MaskHeapConsumptionService {
    fn fresh_inverse(
        &mut self,
        input: &MaskQuantifiedInputs,
    ) -> Result<
        (
            crate::rules::quantified_chunk_support::InverseFunctions,
            Vec<Term>,
        ),
        Self::Error,
    >;
    fn injectivity(&mut self, input: &MaskQuantifiedInputs) -> Result<Term, Self::Error>;
    fn record_inverse_and_mask(
        &mut self,
        inverse: crate::rules::quantified_chunk_support::InverseFunctions,
        mask: Term,
        definition: Term,
    ) -> Result<(), Self::Error>;
}

pub enum MaskQuantifiedConsumption {
    Complete {
        heap: ListBackedHeap,
        snapshot: Option<Term>,
    },
    NegativePermission {
        condition: Term,
    },
    NonInjective {
        condition: Term,
    },
    Insufficient {
        condition: Term,
    },
}

/// Shared source prelude for ordinary and extended quantified consumption.
pub struct PreparedMaskQuantifiedConsumption {
    pub inverse: crate::rules::quantified_chunk_support::InverseFunctions,
    pub images_condition: Term,
    pub condition_at: Term,
    pub loss: Term,
    pub loss_at: Term,
}
pub enum MaskQuantifiedPreparation {
    Ready(PreparedMaskQuantifiedConsumption),
    NegativePermission { condition: Term },
    NonInjective { condition: Term },
}
pub fn prepare_quantified_consumption<S: MaskQuantifiedConsumptionService>(
    factory: &TermFactory,
    input: &MaskQuantifiedInputs,
    service: &mut S,
) -> Result<MaskQuantifiedPreparation, MaskHeapError<S::Error>> {
    use crate::state::terms::Quantifier;
    let (inverse, images) = service
        .fresh_inverse(input)
        .map_err(MaskHeapError::Service)?;
    let (effective_triggers, effective_vars) = if input.explicit_triggers.is_some() {
        (input.translated_triggers.clone(), input.qvars.clone())
    } else {
        match inverse.axiom_inverses_of_invertibles.kind() {
            TermKind::Quantification { vars, triggers, .. } => (triggers.clone(), vars.clone()),
            _ => return Err(MaskHeapError::InvalidQuantifier),
        }
    };
    for term in &input.auxiliary_globals {
        service
            .assume(term.clone())
            .map_err(MaskHeapError::Service)?;
    }
    for term in &input.auxiliary_non_globals {
        let changed = if input.explicit_triggers.is_some() {
            term.clone()
        } else {
            let TermKind::Quantification {
                quantifier,
                body,
                name,
                is_global,
                weight,
                ..
            } = term.kind()
            else {
                return Err(MaskHeapError::InvalidQuantifier);
            };
            factory
                .quantification(
                    *quantifier,
                    effective_vars.clone(),
                    body.clone(),
                    effective_triggers.clone(),
                    name.clone(),
                    *is_global,
                    *weight,
                )
                .map_err(MaskHeapError::Trigger)?
        };
        service.assume(changed).map_err(MaskHeapError::Service)?;
    }
    let nonnegative = factory.implies(
        input.condition.clone(),
        factory.is_nonnegative_perm(input.permission.clone()),
    );
    let transformed = service
        .transform_precondition(nonnegative.clone())
        .map_err(MaskHeapError::Service)?;
    let nonnegative = factory
        .quantification(
            Quantifier::Forall,
            input.qvars.clone(),
            factory.implies(transformed, nonnegative),
            vec![],
            TermFactory::forall_default_name(),
            false,
            None,
        )
        .map_err(MaskHeapError::Trigger)?;
    if !service
        .assert_goal(nonnegative.clone())
        .map_err(MaskHeapError::Service)?
    {
        return Ok(MaskQuantifiedPreparation::NegativePermission {
            condition: nonnegative,
        });
    }
    let loss = factory.perm_times(input.permission.clone(), input.scaling.clone());
    let injectivity = service.injectivity(input).map_err(MaskHeapError::Service)?;
    let transformed = service
        .transform_precondition(injectivity.clone())
        .map_err(MaskHeapError::Service)?;
    let injectivity = factory.implies(transformed, injectivity);
    if !service
        .assert_goal(injectivity.clone())
        .map_err(MaskHeapError::Service)?
    {
        return Ok(MaskQuantifiedPreparation::NonInjective {
            condition: injectivity,
        });
    }
    let replacements = inverse
        .qvars_to_inverses_of(factory, &input.formal_qvars)
        .into_iter()
        .collect();
    let images_condition = factory.and([factory.and(images), input.condition.clone()]);
    let condition_at = factory
        .replace(&images_condition, &replacements)
        .map_err(MaskHeapError::Trigger)?;
    let loss_at = factory
        .replace(&loss, &replacements)
        .map_err(MaskHeapError::Trigger)?;
    for axiom in inverse.definitional_axioms() {
        let transformed = service
            .transform_precondition(axiom.clone())
            .map_err(MaskHeapError::Service)?;
        service
            .assume_definition(transformed)
            .map_err(MaskHeapError::Service)?;
    }
    for axiom in inverse.definitional_axioms() {
        service
            .assume_definition(axiom.clone())
            .map_err(MaskHeapError::Service)?;
    }
    Ok(MaskQuantifiedPreparation::Ready(
        PreparedMaskQuantifiedConsumption {
            inverse,
            images_condition,
            condition_at,
            loss,
            loss_at,
        },
    ))
}

/// Source non-extended quantified consume. Extended transfer is a separate path.
pub fn consume_quantified<S: MaskQuantifiedConsumptionService>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    input: &MaskQuantifiedInputs,
    program: &Program,
    converter: &DefaultSymbolConverter,
    constrain_permissions: bool,
    read_only: bool,
    recording_function: bool,
    may_assume_upper_bounds: bool,
    return_snapshot: bool,
    simplify: bool,
    service: &mut S,
) -> Result<MaskQuantifiedConsumption, MaskHeapError<S::Error>> {
    use crate::state::terms::{Quantifier, Trigger};
    let PreparedMaskQuantifiedConsumption {
        inverse,
        images_condition,
        condition_at,
        loss,
        loss_at,
    } = match prepare_quantified_consumption(factory, input, service)? {
        MaskQuantifiedPreparation::Ready(prepared) => prepared,
        MaskQuantifiedPreparation::NegativePermission { condition } => {
            return Ok(MaskQuantifiedConsumption::NegativePermission { condition });
        }
        MaskQuantifiedPreparation::NonInjective { condition } => {
            return Ok(MaskQuantifiedConsumption::NonInjective { condition });
        }
    };
    let (heap, current) = match find_chunk(heap, &input.resource)? {
        Some(chunk) => (heap.clone(), chunk.clone()),
        None => match &input.resource {
            ResourceKey::Wand(_) => {
                let chunk = BasicMaskHeapChunk {
                    resource_id: ResourceId::MagicWand,
                    resource: input.resource.clone(),
                    mask: factory.pred_zero_mask(),
                    heap: service
                        .fresh("mwHeap", Sort::WandHeap)
                        .map_err(MaskHeapError::Service)?,
                };
                (heap.with_chunk(Chunk::MaskHeap(chunk.clone())), chunk)
            }
            _ => return Err(MaskHeapError::MissingResource),
        },
    };
    let at = if matches!(input.resource, ResourceKey::Field(_)) {
        input
            .formal_qvars
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?
    } else {
        factory.to_snap_tree(input.formal_qvars.iter().cloned())
    };
    let current_perm = factory.heap_lookup(current.mask.clone(), at.clone());
    if input.formal_qvars.len() != input.arguments.len() {
        return Err(MaskHeapError::MissingArgument);
    }
    let formal_to_args = input
        .formal_qvars
        .iter()
        .cloned()
        .zip(input.arguments.iter().cloned())
        .collect();
    let condition_q = factory
        .replace(&images_condition, &formal_to_args)
        .map_err(MaskHeapError::Trigger)?;
    let arg_q = if matches!(input.resource, ResourceKey::Field(_)) {
        input
            .arguments
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?
    } else {
        factory.to_snap_tree(input.arguments.iter().cloned())
    };
    let current_q = factory.heap_lookup(current.mask.clone(), arg_q);
    let enough = if read_only {
        factory.implies(
            factory.perm_less(factory.no_perm(), loss.clone()),
            factory.perm_less(factory.no_perm(), current_q),
        )
    } else if constrain_permissions {
        factory.perm_less(factory.no_perm(), current_q)
    } else {
        factory.perm_at_most(loss.clone(), current_q)
    };
    let sufficient = factory
        .quantification(
            Quantifier::Forall,
            input.qvars.clone(),
            factory.implies(condition_q, enough),
            input.translated_triggers.clone(),
            "sufficientPerms".into(),
            false,
            None,
        )
        .map_err(MaskHeapError::Trigger)?;
    let transformed = service
        .transform_precondition(sufficient.clone())
        .map_err(MaskHeapError::Service)?;
    let sufficient = factory.implies(transformed, sufficient);
    if !service
        .assert_goal(sufficient.clone())
        .map_err(MaskHeapError::Service)?
    {
        return Ok(MaskQuantifiedConsumption::Insufficient {
            condition: sufficient,
        });
    }
    if constrain_permissions {
        let constraint = factory
            .quantification(
                Quantifier::Forall,
                input.formal_qvars.clone(),
                factory.implies(
                    condition_at.clone(),
                    factory.perm_less(loss_at.clone(), current_perm),
                ),
                vec![],
                "qpConstrainWildcard".into(),
                false,
                None,
            )
            .map_err(MaskHeapError::Trigger)?;
        service.assume(constraint).map_err(MaskHeapError::Service)?;
    }
    let mask_sort = if matches!(input.resource, ResourceKey::Field(_)) {
        Sort::mask()
    } else {
        Sort::PredMask
    };
    let qp_mask = service
        .fresh("qpMask", mask_sort)
        .map_err(MaskHeapError::Service)?;
    let lookup = factory.heap_lookup(qp_mask.clone(), at);
    let conditional = factory.ite(condition_at, loss_at, factory.no_perm());
    let definition = factory
        .quantification(
            Quantifier::Forall,
            input.formal_qvars.clone(),
            factory.equals(lookup.clone(), conditional),
            vec![Trigger {
                terms: vec![lookup],
            }],
            "qpMaskdef".into(),
            false,
            None,
        )
        .map_err(MaskHeapError::Trigger)?;
    service
        .assume_definition(definition.clone())
        .map_err(MaskHeapError::Service)?;
    service
        .record_inverse_and_mask(inverse, qp_mask.clone(), definition)
        .map_err(MaskHeapError::Service)?;
    struct Adapter<'a, S>(&'a mut S);
    impl<S: MaskQuantifiedConsumptionService> MaskSimplificationService for Adapter<'_, S> {
        type Error = S::Error;
        fn alias(&mut self, term: Term) -> Result<Term, Self::Error> {
            self.0.alias(term)
        }
        fn check(&mut self, term: Term, timeout: i32) -> Result<bool, Self::Error> {
            self.0.check(term, timeout)
        }
    }
    let mask = if read_only {
        current.mask.clone()
    } else {
        subtract_mask(
            factory,
            current.mask.clone(),
            qp_mask.clone(),
            &input.resource,
            program,
            converter,
            simplify,
            &mut Adapter(service),
        )?
    };
    let good = if matches!(input.resource, ResourceKey::Field(_)) {
        factory.good_field_mask(mask.clone(), may_assume_upper_bounds)
    } else {
        factory.good_mask(mask.clone())
    };
    service.assume(good).map_err(MaskHeapError::Service)?;
    let updated = if recording_function || read_only {
        current.with_mask(mask)
    } else {
        let fresh = service
            .fresh("heap", current.heap.sort().clone())
            .map_err(MaskHeapError::Service)?;
        service
            .assume_definition(factory.identical_on_known_locations(
                current.heap.clone(),
                fresh.clone(),
                mask.clone(),
            ))
            .map_err(MaskHeapError::Service)?;
        current.with_mask_and_heap(mask, fresh)
    };
    let snapshot =
        return_snapshot.then(|| factory.mask_map_term([(input.resource.clone(), qp_mask)]));
    Ok(MaskQuantifiedConsumption::Complete {
        heap: heap
            .without_chunk(&Chunk::MaskHeap(current))
            .with_chunk(Chunk::MaskHeap(updated)),
        snapshot,
    })
}

/// Produce a quantified mask in the same order as source MaskHeapSupporter.produce.
pub fn produce_quantified<S: MaskQuantifiedProductionService>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    input: &MaskQuantifiedInputs,
    may_assume_upper_bounds: bool,
    assume_injectivity: bool,
    service: &mut S,
) -> Result<MaskQuantifiedProduction, MaskHeapError<S::Error>> {
    use crate::state::terms::{Quantifier, Trigger};
    let gain = factory.perm_times(input.permission.clone(), input.scaling.clone());
    let (mut inverse, images) = service
        .fresh_inverse(input)
        .map_err(MaskHeapError::Service)?;
    let substitutions = inverse
        .qvars_to_inverses_of(factory, &input.formal_qvars)
        .into_iter()
        .collect();
    let condition_at = factory
        .replace(&input.condition, &substitutions)
        .map_err(MaskHeapError::Trigger)?;
    let gain_at = factory
        .replace(&gain, &substitutions)
        .map_err(MaskHeapError::Trigger)?;
    let in_image = factory.and(images.clone());
    let conditional = factory.ite(
        factory.and([in_image.clone(), condition_at.clone()]),
        gain_at.clone(),
        factory.no_perm(),
    );
    let snapshot = input
        .snapshot
        .as_ref()
        .ok_or(MaskHeapError::MissingResource)?;
    let snapshot_heap = match snapshot.kind() {
        TermKind::HeapMapTerm(heaps) => heaps
            .iter()
            .find(|(key, _)| key == &input.resource)
            .map(|(_, heap)| heap.clone())
            .ok_or(MaskHeapError::MissingResource)?,
        _ => return Err(MaskHeapError::WrongResourceKind),
    };
    let mask_sort = if matches!(input.resource, ResourceKey::Field(_)) {
        Sort::mask()
    } else {
        Sort::PredMask
    };
    let qp_mask = service
        .fresh("qpMask", mask_sort)
        .map_err(MaskHeapError::Service)?;
    let at = if matches!(input.resource, ResourceKey::Field(_)) {
        input
            .formal_qvars
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?
    } else {
        factory.to_snap_tree(input.formal_qvars.iter().cloned())
    };
    let qp_lookup = factory.heap_lookup(qp_mask.clone(), at.clone());
    let qp_constraint = factory
        .quantification(
            Quantifier::Forall,
            input.formal_qvars.clone(),
            factory.equals(qp_lookup.clone(), conditional),
            vec![Trigger {
                terms: vec![qp_lookup],
            }],
            "qpMaskdef".into(),
            false,
            None,
        )
        .map_err(MaskHeapError::Trigger)?;
    let (heap, current) = match find_chunk(heap, &input.resource)? {
        Some(chunk) => (heap.clone(), chunk.clone()),
        None => match &input.resource {
            ResourceKey::Wand(_) => {
                let chunk = BasicMaskHeapChunk {
                    resource_id: ResourceId::MagicWand,
                    resource: input.resource.clone(),
                    mask: factory.pred_zero_mask(),
                    heap: service
                        .fresh("mwHeap", Sort::WandHeap)
                        .map_err(MaskHeapError::Service)?,
                };
                (heap.with_chunk(Chunk::MaskHeap(chunk.clone())), chunk)
            }
            _ => return Err(MaskHeapError::MissingResource),
        },
    };
    let new_mask = factory.mask_sum(current.mask.clone(), qp_mask.clone());
    let new_heap = factory.merge_heaps(
        current.heap.clone(),
        current.mask.clone(),
        snapshot_heap,
        qp_mask.clone(),
    );
    let new_lookup = factory.heap_lookup(new_mask.clone(), at.clone());
    let bound = if matches!(input.resource, ResourceKey::Field(_)) {
        let upper = factory
            .quantification(
                Quantifier::Forall,
                input.formal_qvars.clone(),
                factory.perm_at_most(new_lookup.clone(), factory.full_perm()),
                vec![Trigger {
                    terms: vec![new_lookup],
                }],
                "qp_produce_upper_bound".into(),
                false,
                None,
            )
            .map_err(MaskHeapError::Trigger)?;
        let positive = factory.perm_less(factory.no_perm(), gain_at);
        let receiver = input
            .formal_qvars
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?;
        let nonnull = factory
            .quantification(
                Quantifier::Forall,
                input.formal_qvars.clone(),
                factory.implies(
                    factory.and([in_image, condition_at, positive]),
                    factory.not(factory.equals(receiver, factory.null())),
                ),
                vec![],
                "qp_recvr_non_null".into(),
                false,
                None,
            )
            .map_err(MaskHeapError::Trigger)?;
        factory.and([upper, nonnull])
    } else {
        factory.boolean(true)
    };
    let (effective_triggers, effective_vars) = if input.explicit_triggers.is_some() {
        let rewritten = input
            .translated_triggers
            .iter()
            .map(|trigger| Trigger {
                terms: trigger
                    .terms
                    .iter()
                    .map(|term| match term.kind() {
                        TermKind::HeapLookup(heap, at) if heap == &current.heap => {
                            factory.heap_lookup(new_heap.clone(), at.clone())
                        }
                        TermKind::HeapLookup(mask, at) if mask == &current.mask => {
                            factory.heap_lookup(qp_mask.clone(), at.clone())
                        }
                        _ => term.clone(),
                    })
                    .collect(),
            })
            .collect();
        (rewritten, input.qvars.clone())
    } else {
        match inverse.axiom_inverses_of_invertibles.kind() {
            TermKind::Quantification { vars, triggers, .. } => (triggers.clone(), vars.clone()),
            _ => return Err(MaskHeapError::InvalidQuantifier),
        }
    };
    if effective_triggers.is_empty() {
        service
            .no_triggers(&input.quantifier)
            .map_err(MaskHeapError::Service)?;
    }
    for term in &input.auxiliary_globals {
        service
            .assume(term.clone())
            .map_err(MaskHeapError::Service)?;
    }
    for term in &input.auxiliary_non_globals {
        let TermKind::Quantification {
            quantifier,
            body,
            name,
            is_global,
            weight,
            ..
        } = term.kind()
        else {
            return Err(MaskHeapError::InvalidQuantifier);
        };
        let changed = factory
            .quantification(
                *quantifier,
                effective_vars.clone(),
                body.clone(),
                effective_triggers.clone(),
                name.clone(),
                *is_global,
                *weight,
            )
            .map_err(MaskHeapError::Trigger)?;
        service.assume(changed).map_err(MaskHeapError::Service)?;
    }
    let nonnegative = factory.implies(
        input.condition.clone(),
        factory.is_nonnegative_perm(input.permission.clone()),
    );
    let transformed = service
        .transform_precondition(nonnegative.clone())
        .map_err(MaskHeapError::Service)?;
    let nonnegative = factory
        .quantification(
            Quantifier::Forall,
            input.qvars.clone(),
            factory.implies(transformed, nonnegative),
            vec![],
            TermFactory::forall_default_name(),
            false,
            None,
        )
        .map_err(MaskHeapError::Trigger)?;
    if !service
        .assert_goal(nonnegative.clone())
        .map_err(MaskHeapError::Service)?
    {
        return Ok(MaskQuantifiedProduction::NegativePermission {
            condition: nonnegative,
        });
    }
    let injectivity = if assume_injectivity {
        factory.boolean(true)
    } else {
        service.injectivity(input).map_err(MaskHeapError::Service)?
    };
    let transformed = service
        .transform_precondition(injectivity.clone())
        .map_err(MaskHeapError::Service)?;
    let injectivity = factory.implies(transformed, injectivity);
    if !service
        .assert_goal(injectivity.clone())
        .map_err(MaskHeapError::Service)?
    {
        return Ok(MaskQuantifiedProduction::NonInjective {
            condition: injectivity,
        });
    }
    service
        .assume_definition(qp_constraint.clone())
        .map_err(MaskHeapError::Service)?;
    let good = if matches!(input.resource, ResourceKey::Field(_)) {
        factory.good_field_mask(new_mask.clone(), may_assume_upper_bounds)
    } else {
        factory.good_mask(new_mask.clone())
    };
    service.assume(good).map_err(MaskHeapError::Service)?;
    let ax = inverse.axiom_inverses_of_invertibles.clone();
    let TermKind::Quantification { vars, body, .. } = ax.kind() else {
        return Err(MaskHeapError::InvalidQuantifier);
    };
    inverse.axiom_inverses_of_invertibles = factory
        .quantification(
            Quantifier::Forall,
            vars.clone(),
            body.clone(),
            effective_triggers,
            TermFactory::forall_default_name(),
            false,
            None,
        )
        .map_err(MaskHeapError::Trigger)?;
    for axiom in inverse.definitional_axioms() {
        let transformed = service
            .transform_precondition(axiom.clone())
            .map_err(MaskHeapError::Service)?;
        service
            .assume_definition(transformed)
            .map_err(MaskHeapError::Service)?;
    }
    for axiom in inverse.definitional_axioms() {
        service
            .assume_definition(axiom.clone())
            .map_err(MaskHeapError::Service)?;
    }
    let updated = current.with_mask_and_heap(new_mask, new_heap);
    let heap = heap
        .without_chunk(&Chunk::MaskHeap(current))
        .with_chunk(Chunk::MaskHeap(updated));
    service.assume(bound).map_err(MaskHeapError::Service)?;
    service
        .record_inverse_and_mask(inverse, qp_mask, qp_constraint)
        .map_err(MaskHeapError::Service)?;
    Ok(MaskQuantifiedProduction::Complete { heap })
}

pub trait MaskHeapProductionService {
    type Error;
    fn fresh(&mut self, name: &str, sort: Sort) -> Result<Term, Self::Error>;
    fn alias(&mut self, term: Term) -> Result<Term, Self::Error>;
    fn assume(&mut self, term: Term) -> Result<(), Self::Error>;
}

/// Replace the values of one location or an injective family, retaining its permissions.
pub fn havoc_resource<S: MaskHeapProductionService>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    condition: Term,
    info: &crate::rules::havoc_supporter::HavocHelperData,
    service: &mut S,
) -> Result<ListBackedHeap, MaskHeapError<S::Error>> {
    use crate::rules::havoc_supporter::HavocHelperData;
    use crate::state::terms::{Quantifier, Trigger};

    let chunk = find_chunk(heap, resource)?.ok_or(MaskHeapError::MissingResource)?;
    let new_heap = match info {
        HavocHelperData::One(args) => {
            let (at, value_sort) = match chunk.heap.sort() {
                Sort::Heap(value) => (
                    args.first()
                        .cloned()
                        .ok_or(MaskHeapError::MissingArgument)?,
                    (**value).clone(),
                ),
                Sort::WandHeap => (
                    factory.to_snap_tree(args.iter().cloned()),
                    Sort::MagicWandSnapFunction,
                ),
                Sort::PredHeap => (factory.to_snap_tree(args.iter().cloned()), Sort::Snap),
                _ => return Err(MaskHeapError::WrongResourceKind),
            };
            let fresh = service
                .fresh("$t", value_sort)
                .map_err(MaskHeapError::Service)?;
            let old = factory.heap_lookup(chunk.heap.clone(), at.clone());
            factory.heap_update(chunk.heap.clone(), at, factory.ite(condition, fresh, old))
        }
        HavocHelperData::All {
            inverse_functions,
            codomain_vars,
            images_of_codomain,
        } => {
            let fresh = service
                .fresh("$t", chunk.heap.sort().clone())
                .map_err(MaskHeapError::Service)?;
            let at = match chunk.heap.sort() {
                Sort::Heap(_) => codomain_vars
                    .first()
                    .cloned()
                    .ok_or(MaskHeapError::MissingArgument)?,
                Sort::WandHeap | Sort::PredHeap => {
                    factory.to_snap_tree(codomain_vars.iter().cloned())
                }
                _ => return Err(MaskHeapError::WrongResourceKind),
            };
            let replacements = inverse_functions
                .qvars_to_inverses_of(factory, codomain_vars)
                .into_iter()
                .collect();
            let condition = factory.and([
                factory
                    .replace(&condition, &replacements)
                    .map_err(MaskHeapError::Trigger)?,
                factory.and(images_of_codomain.iter().cloned()),
            ]);
            let new_value = factory.heap_lookup(fresh.clone(), at.clone());
            let old_value = factory.heap_lookup(chunk.heap.clone(), at);
            let framing = factory
                .quantification(
                    Quantifier::Forall,
                    codomain_vars.clone(),
                    factory.implies(
                        factory.not(condition),
                        factory.equals(new_value.clone(), old_value),
                    ),
                    vec![Trigger {
                        terms: vec![new_value],
                    }],
                    "havocall.framing".into(),
                    false,
                    None,
                )
                .map_err(MaskHeapError::Trigger)?;
            service.assume(framing).map_err(MaskHeapError::Service)?;
            fresh
        }
    };
    Ok(heap
        .without_chunk(&Chunk::MaskHeap(chunk.clone()))
        .with_chunk(Chunk::MaskHeap(
            chunk.with_mask_and_heap(chunk.mask.clone(), new_heap),
        )))
}

pub trait MaskHeapConsumptionService: MaskHeapProductionService {
    fn check(&mut self, term: Term, timeout_ms: i32) -> Result<bool, Self::Error>;
    fn assert_goal(&mut self, term: Term) -> Result<bool, Self::Error>;
    fn transform_precondition(&mut self, term: Term) -> Result<Term, Self::Error>;
    fn assume_definition(&mut self, term: Term) -> Result<(), Self::Error>;
    /// During extended transfer source simplification uses the outer state, not the heap step state.
    fn simplify_alias(&mut self, term: Term) -> Result<Term, Self::Error> {
        self.alias(term)
    }
    fn simplify_check(&mut self, term: Term, timeout_ms: i32) -> Result<bool, Self::Error> {
        self.check(term, timeout_ms)
    }
}

pub enum MaskConsumption {
    Complete {
        heap: ListBackedHeap,
        snapshot: Option<Term>,
    },
    Insufficient {
        condition: Term,
    },
}

/// One source extended-exhale transfer step; `remaining` is absent when complete.
pub struct MaskTransferStep {
    pub heap: ListBackedHeap,
    pub remaining: Option<Term>,
    pub consumed: Option<Chunk>,
}

/// One quantified extended-exhale step after the source inverse and injectivity checks.
pub fn transfer_quantified_step<S: MaskQuantifiedConsumptionService>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    formal_qvars: &[Term],
    condition_at: Term,
    remaining: Term,
    constrain_permissions: bool,
    inverse: &crate::rules::quantified_chunk_support::InverseFunctions,
    service: &mut S,
) -> Result<MaskTransferStep, MaskHeapError<S::Error>> {
    use crate::state::terms::{Quantifier, Trigger};
    let (heap, chunk) = match find_chunk(heap, resource)? {
        Some(chunk) => (heap.clone(), chunk.clone()),
        None if matches!(resource, ResourceKey::Wand(_)) => {
            let chunk = BasicMaskHeapChunk {
                resource_id: ResourceId::MagicWand,
                resource: resource.clone(),
                mask: factory.pred_zero_mask(),
                heap: service
                    .fresh("mwHeap", Sort::WandHeap)
                    .map_err(MaskHeapError::Service)?,
            };
            (heap.with_chunk(Chunk::MaskHeap(chunk.clone())), chunk)
        }
        None => return Err(MaskHeapError::MissingResource),
    };
    let at = match resource {
        ResourceKey::Field(_) => formal_qvars
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?,
        _ => factory.to_snap_tree(formal_qvars.iter().cloned()),
    };
    let current = factory.heap_lookup(chunk.mask.clone(), at.clone());
    if current == factory.no_perm() {
        return Ok(MaskTransferStep {
            heap,
            remaining: Some(remaining),
            consumed: None,
        });
    }
    let enough = if constrain_permissions {
        factory.perm_less(factory.no_perm(), current.clone())
    } else {
        factory.perm_at_most(remaining.clone(), current.clone())
    };
    let all = factory
        .quantification(
            Quantifier::Forall,
            formal_qvars.to_vec(),
            factory.implies(condition_at.clone(), enough),
            vec![],
            "sufficientPerms".into(),
            false,
            None,
        )
        .map_err(MaskHeapError::Trigger)?;
    let sort = if matches!(resource, ResourceKey::Field(_)) {
        Sort::mask()
    } else {
        Sort::PredMask
    };
    let qp_mask = service
        .fresh("qpMask", sort)
        .map_err(MaskHeapError::Service)?;
    let lookup = factory.heap_lookup(qp_mask.clone(), at);
    let amount = factory.ite(
        condition_at,
        factory.perm_min(remaining.clone(), current),
        factory.no_perm(),
    );
    let definition = factory
        .quantification(
            Quantifier::Forall,
            formal_qvars.to_vec(),
            factory.equals(lookup.clone(), amount),
            vec![Trigger {
                terms: vec![lookup.clone()],
            }],
            "qpMaskdef".into(),
            false,
            None,
        )
        .map_err(MaskHeapError::Trigger)?;
    service
        .assume_definition(definition.clone())
        .map_err(MaskHeapError::Service)?;
    service
        .record_inverse_and_mask(inverse.clone(), qp_mask.clone(), definition)
        .map_err(MaskHeapError::Service)?;
    let rest = factory.mask_diff(chunk.mask.clone(), qp_mask.clone());
    let consumed = Chunk::MaskHeap(chunk.with_mask_and_heap(qp_mask, chunk.heap.clone()));
    let replacement = chunk.with_mask_and_heap(rest, chunk.heap.clone());
    let heap = heap
        .without_chunk(&Chunk::MaskHeap(chunk))
        .with_chunk(Chunk::MaskHeap(replacement));
    let complete = service.check(all, 0).map_err(MaskHeapError::Service)?;
    Ok(MaskTransferStep {
        heap,
        remaining: (!complete).then(|| factory.perm_minus(remaining, lookup)),
        consumed: Some(consumed),
    })
}

pub fn transfer_single_location<S: MaskHeapConsumptionService>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    arguments: &[Term],
    permission: Term,
    consume_exact: bool,
    read_only: bool,
    simplify: bool,
    split_timeout_ms: i32,
    service: &mut S,
) -> Result<MaskTransferStep, MaskHeapError<S::Error>> {
    let (heap, chunk) = match find_chunk(heap, resource)? {
        Some(chunk) => (heap.clone(), chunk.clone()),
        None if matches!(resource, ResourceKey::Wand(_)) => {
            let chunk = BasicMaskHeapChunk {
                resource_id: ResourceId::MagicWand,
                resource: resource.clone(),
                mask: factory.pred_zero_mask(),
                heap: service
                    .fresh("mwHeap", Sort::WandHeap)
                    .map_err(MaskHeapError::Service)?,
            };
            (heap.with_chunk(Chunk::MaskHeap(chunk.clone())), chunk)
        }
        None => return Err(MaskHeapError::MissingResource),
    };
    let at = match resource {
        ResourceKey::Field(_) => arguments
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?,
        _ => factory.to_snap_tree(arguments.iter().cloned()),
    };
    let available = factory.heap_lookup(chunk.mask.clone(), at.clone());
    let has_all = if consume_exact {
        factory.at_least(available.clone(), permission.clone())
    } else {
        factory.greater(available.clone(), factory.no_perm())
    };
    let has_none = factory.at_most(available.clone(), factory.no_perm());
    if service
        .check(has_none, split_timeout_ms)
        .map_err(MaskHeapError::Service)?
    {
        return Ok(MaskTransferStep {
            heap,
            remaining: Some(permission),
            consumed: None,
        });
    }
    if !consume_exact {
        service
            .assume(factory.perm_less(permission.clone(), available.clone()))
            .map_err(MaskHeapError::Service)?;
    }
    let taken = factory.perm_min(available, permission.clone());
    let mask = if read_only {
        chunk.mask.clone()
    } else {
        let added = service
            .alias(factory.mask_add(
                chunk.mask.clone(),
                at.clone(),
                factory.perm_negation(taken.clone()),
            ))
            .map_err(MaskHeapError::Service)?;
        let raw = matches!(added.kind(), TermKind::MaskAdd(base, receiver, negated) if base == &chunk.mask && receiver == &at && matches!(negated.kind(), TermKind::PermNegation(value) if value == &taken));
        if raw {
            struct Adapter<'a, S>(&'a mut S);
            impl<S: MaskHeapConsumptionService> MaskSimplificationService for Adapter<'_, S> {
                type Error = S::Error;
                fn alias(&mut self, term: Term) -> Result<Term, Self::Error> {
                    self.0.simplify_alias(term)
                }
                fn check(&mut self, term: Term, timeout: i32) -> Result<bool, Self::Error> {
                    self.0.simplify_check(term, timeout)
                }
            }
            remove_single_add(
                factory,
                chunk.mask.clone(),
                at.clone(),
                taken.clone(),
                simplify,
                split_timeout_ms,
                &mut Adapter(service),
            )
            .map_err(MaskHeapError::Service)?
        } else {
            added
        }
    };
    let empty = if matches!(resource, ResourceKey::Field(_)) {
        factory.zero_mask()
    } else {
        factory.pred_zero_mask()
    };
    let consumed_mask = service
        .alias(factory.mask_add(empty, at, taken.clone()))
        .map_err(MaskHeapError::Service)?;
    let consumed = Chunk::MaskHeap(chunk.with_mask_and_heap(consumed_mask, chunk.heap.clone()));
    let remaining_chunk = chunk.with_mask_and_heap(mask, chunk.heap.clone());
    let updated = heap
        .without_chunk(&Chunk::MaskHeap(chunk))
        .with_chunk(Chunk::MaskHeap(remaining_chunk));
    let complete = service.check(has_all, 0).map_err(MaskHeapError::Service)?;
    Ok(MaskTransferStep {
        heap: updated,
        remaining: (!complete).then(|| factory.perm_minus(permission, taken)),
        consumed: Some(consumed),
    })
}

pub enum MaskFieldRead {
    Value { value: Term, snapshot: Term },
    Insufficient { condition: Term },
}
pub enum MaskFieldWrite {
    Updated(ListBackedHeap),
    Insufficient { condition: Term },
}

/// Source current-permission lookup returns NoPerm when the resource chunk is absent.
pub fn current_permission<E>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    arguments: &[Term],
) -> Result<Term, MaskHeapError<E>> {
    let at = match resource {
        ResourceKey::Field(_) => arguments
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?,
        _ => factory.to_snap_tree(arguments.iter().cloned()),
    };
    Ok(match find_chunk(heap, resource)? {
        Some(chunk) => factory.heap_lookup(chunk.mask.clone(), at),
        None => factory.no_perm(),
    })
}

/// On success the caller records the returned snapshot under its current branch conditions.
pub fn read_field<E>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    receiver: Term,
    mut assert_goal: impl FnMut(Term) -> Result<bool, E>,
) -> Result<MaskFieldRead, MaskHeapError<E>> {
    if !matches!(resource, ResourceKey::Field(_)) {
        return Err(MaskHeapError::WrongResourceKind);
    }
    let chunk = find_chunk(heap, resource)?.ok_or(MaskHeapError::MissingResource)?;
    let condition =
        factory.is_positive_perm(factory.heap_lookup(chunk.mask.clone(), receiver.clone()));
    if !assert_goal(condition.clone()).map_err(MaskHeapError::Service)? {
        return Ok(MaskFieldRead::Insufficient { condition });
    }
    let value = factory.heap_lookup(chunk.heap.clone(), receiver);
    let snapshot = factory.sort_wrapper(value.clone(), Sort::Snap);
    Ok(MaskFieldRead::Value { value, snapshot })
}

pub fn write_field<E>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    receiver: Term,
    value: Term,
    mut assert_goal: impl FnMut(Term) -> Result<bool, E>,
) -> Result<MaskFieldWrite, MaskHeapError<E>> {
    if !matches!(resource, ResourceKey::Field(_)) {
        return Err(MaskHeapError::WrongResourceKind);
    }
    let chunk = find_chunk(heap, resource)?.ok_or(MaskHeapError::MissingResource)?;
    let condition = factory.at_least(
        factory.heap_lookup(chunk.mask.clone(), receiver.clone()),
        factory.full_perm(),
    );
    if !assert_goal(condition.clone()).map_err(MaskHeapError::Service)? {
        return Ok(MaskFieldWrite::Insufficient { condition });
    }
    let updated = chunk.with_heap(factory.heap_update(chunk.heap.clone(), receiver, value));
    Ok(MaskFieldWrite::Updated(
        heap.without_chunk(&Chunk::MaskHeap(chunk.clone()))
            .with_chunk(Chunk::MaskHeap(updated)),
    ))
}

/// Source fold packages the body snapshot as a singleton predicate heap map.
pub fn folded_predicate_snapshot<E>(
    factory: &TermFactory,
    resource: &ResourceKey,
    arguments: &[Term],
    snapshot: Term,
) -> Result<Term, MaskHeapError<E>> {
    if !matches!(resource, ResourceKey::Predicate(_)) {
        return Err(MaskHeapError::WrongResourceKind);
    }
    let at = factory.to_snap_tree(arguments.iter().cloned());
    let singleton = factory.heap_singleton(at.clone(), snapshot, Sort::PredHeap);
    let mask = factory.heap_update(factory.pred_zero_mask(), at, factory.full_perm());
    let restricted = factory.heap_to_snap(singleton, mask, resource.clone());
    let heap = factory.snap_to_heap(restricted, resource.clone(), Sort::PredHeap);
    Ok(factory.heap_map_term([(resource.clone(), heap)]))
}

/// Mask-mode wand chunk stores a full-permission singleton and its snapshot function.
pub fn create_wand_chunk<E>(
    factory: &TermFactory,
    id: MagicWandIdentifier,
    arguments: &[Term],
    snapshot: &Term,
) -> Result<Chunk, MaskHeapError<E>> {
    let TermKind::MagicWandSnapshot(mwsf) = snapshot.kind() else {
        return Err(MaskHeapError::WrongResourceKind);
    };
    let at = factory.to_snap_tree(arguments.iter().cloned());
    let mask = factory.mask_add(factory.pred_zero_mask(), at.clone(), factory.full_perm());
    let heap = factory.heap_singleton(at, mwsf.clone(), Sort::WandHeap);
    Ok(Chunk::MaskHeap(BasicMaskHeapChunk {
        resource_id: ResourceId::MagicWand,
        resource: ResourceKey::Wand(id),
        mask,
        heap,
    }))
}

/// Add a wand chunk, merging an existing resource's mask and heap in source order.
pub fn add_wand_chunk<E>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    chunk: &Chunk,
) -> Result<ListBackedHeap, MaskHeapError<E>> {
    let Chunk::MaskHeap(incoming) = chunk else {
        return Err(MaskHeapError::NonMaskChunk);
    };
    if !matches!(incoming.resource, ResourceKey::Wand(_)) {
        return Err(MaskHeapError::WrongResourceKind);
    }
    let Some(current) = find_chunk(heap, &incoming.resource)? else {
        return Ok(heap.with_chunk(chunk.clone()));
    };
    let mask = factory.mask_sum(current.mask.clone(), incoming.mask.clone());
    let values = factory.merge_heaps(
        current.heap.clone(),
        current.mask.clone(),
        incoming.heap.clone(),
        incoming.mask.clone(),
    );
    Ok(heap
        .without_chunk(&Chunk::MaskHeap(current.clone()))
        .with_chunk(Chunk::MaskHeap(current.with_mask_and_heap(mask, values))))
}

/// Unpack a consumed wand heap snapshot before applying its snapshot function.
pub fn applied_wand_snapshot(factory: &TermFactory, wand: &Term, lhs: Term) -> Term {
    if let TermKind::HeapToSnap(heap, mask, _) = wand.kind() {
        if let TermKind::MaskAdd(_, args, _) = mask.kind() {
            let function = factory.heap_lookup(heap.clone(), args.clone());
            return factory.apply_wand_snapshot(&factory.magic_wand_snapshot(function), lhs);
        }
    }
    crate::rules::heap_supporter::applied_wand_snapshot(factory, wand, lhs)
}

/// Source forperm contributes one guarded branch and a mask-lookup trigger.
pub fn forperm_mask_condition<E>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    arguments: &[Term],
) -> Result<Option<(Term, crate::state::terms::Trigger)>, MaskHeapError<E>> {
    let Some(chunk) = find_chunk(heap, resource)? else {
        return Ok(None);
    };
    let at = if matches!(resource, ResourceKey::Field(_)) {
        arguments
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?
    } else {
        factory.to_snap_tree(arguments.iter().cloned())
    };
    let lookup = factory.heap_lookup(chunk.mask.clone(), at);
    Ok(Some((
        factory.perm_less(factory.no_perm(), lookup.clone()),
        crate::state::terms::Trigger {
            terms: vec![lookup],
        },
    )))
}

/// Source explicitly constructs unsimplified heap/mask lookups for trigger candidates.
/// An absent wand chunk yields one empty variant; absent field/predicate is an error.
pub fn resource_trigger_variants<E>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    arguments: &[Term],
) -> Result<Vec<Vec<Term>>, MaskHeapError<E>> {
    let chunk = match find_chunk(heap, resource)? {
        Some(chunk) => chunk,
        None if matches!(resource, ResourceKey::Wand(_)) => return Ok(vec![vec![]]),
        None => return Err(MaskHeapError::MissingResource),
    };
    let at = if matches!(resource, ResourceKey::Field(_)) {
        arguments
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?
    } else {
        factory.to_snap_tree(arguments.iter().cloned())
    };
    Ok(vec![
        vec![factory.raw_heap_lookup(chunk.heap.clone(), at.clone())],
        vec![factory.raw_heap_lookup(chunk.mask.clone(), at)],
    ])
}

/// Return the heap arguments and the ordered heap map used as function-call snapshot.
pub fn function_app_snapshot<E>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resources: &[ResourceKey],
) -> Result<(Vec<Term>, Term), MaskHeapError<E>> {
    let mut heaps = Vec::with_capacity(resources.len());
    for resource in resources {
        let chunk = find_chunk(heap, resource)?.ok_or(MaskHeapError::MissingResource)?;
        heaps.push((resource.clone(), chunk.heap.clone()));
    }
    Ok((
        heaps.iter().map(|(_, heap)| heap.clone()).collect(),
        factory.heap_map_term(heaps),
    ))
}

/// Source predicate unfolding uses the evaluation heap selected by the caller.
pub fn unfolded_predicate_snapshot<E>(
    factory: &TermFactory,
    resource: &ResourceKey,
    arguments: &[Term],
    snapshot: Term,
    eval_heap: &ListBackedHeap,
    mut alias: impl FnMut(Term) -> Result<Term, E>,
) -> Result<Term, MaskHeapError<E>> {
    if !matches!(resource, ResourceKey::Predicate(_)) {
        return Err(MaskHeapError::WrongResourceKind);
    }
    let snapshot = if let TermKind::MaskMapTerm(masks) = snapshot.kind() {
        let entries: Vec<_> = masks.iter().cloned().collect();
        snapshot_from_masks(
            factory,
            &entries,
            std::slice::from_ref(resource),
            eval_heap,
            &mut alias,
        )?
    } else {
        snapshot
    };
    let heap = match snapshot.kind() {
        TermKind::HeapMapTerm(map) => map
            .iter()
            .find(|(key, _)| key == resource)
            .map(|(_, heap)| heap.clone())
            .ok_or(MaskHeapError::MissingResource)?,
        TermKind::HeapToSnap(heap, _, _) => heap.clone(),
        _ => alias(factory.snap_to_heap(snapshot, resource.clone(), Sort::PredHeap))
            .map_err(MaskHeapError::Service)?,
    };
    Ok(factory.heap_lookup(heap, factory.to_snap_tree(arguments.iter().cloned())))
}

/// Source ordinary consumeSingleLocation. Extended-exhale transfers use a separate path.
pub fn consume_single_location<S: MaskHeapConsumptionService>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    arguments: &[Term],
    permission: Term,
    consume_exact: bool,
    read_only: bool,
    recording_function: bool,
    may_assume_upper_bounds: bool,
    return_snapshot: bool,
    simplify: bool,
    check_timeout_ms: i32,
    service: &mut S,
) -> Result<MaskConsumption, MaskHeapError<S::Error>> {
    let (heap, chunk) = match find_chunk(heap, resource)? {
        Some(chunk) => (heap.clone(), chunk.clone()),
        None => match resource {
            ResourceKey::Wand(_) => {
                let chunk = BasicMaskHeapChunk {
                    resource_id: ResourceId::MagicWand,
                    resource: resource.clone(),
                    mask: factory.pred_zero_mask(),
                    heap: service
                        .fresh("mwHeap", Sort::WandHeap)
                        .map_err(MaskHeapError::Service)?,
                };
                (heap.with_chunk(Chunk::MaskHeap(chunk.clone())), chunk)
            }
            _ => return Err(MaskHeapError::MissingResource),
        },
    };
    let at = match resource {
        ResourceKey::Field(_) => arguments
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?,
        _ => factory.to_snap_tree(arguments.iter().cloned()),
    };
    let available = factory.heap_lookup(chunk.mask.clone(), at.clone());
    let sufficient = if read_only {
        factory.implies(
            factory.greater(permission.clone(), factory.no_perm()),
            factory.greater(available.clone(), factory.no_perm()),
        )
    } else if consume_exact {
        factory.at_least(available.clone(), permission.clone())
    } else {
        factory.greater(available.clone(), factory.no_perm())
    };
    let precondition = service
        .transform_precondition(sufficient.clone())
        .map_err(MaskHeapError::Service)?;
    let condition = factory.implies(precondition, sufficient);
    if !service
        .assert_goal(condition.clone())
        .map_err(MaskHeapError::Service)?
    {
        return Ok(MaskConsumption::Insufficient { condition });
    }
    if !consume_exact {
        service
            .assume(factory.perm_less(permission.clone(), available))
            .map_err(MaskHeapError::Service)?;
    }
    let mask = if read_only {
        chunk.mask.clone()
    } else {
        let added = service
            .alias(factory.mask_add(
                chunk.mask.clone(),
                at.clone(),
                factory.perm_negation(permission.clone()),
            ))
            .map_err(MaskHeapError::Service)?;
        let matches_raw = matches!(added.kind(), TermKind::MaskAdd(base, receiver, negated) if base == &chunk.mask && receiver == &at && matches!(negated.kind(), TermKind::PermNegation(value) if value == &permission));
        if matches_raw {
            struct Adapter<'a, S>(&'a mut S);
            impl<S: MaskHeapConsumptionService> MaskSimplificationService for Adapter<'_, S> {
                type Error = S::Error;
                fn alias(&mut self, term: Term) -> Result<Term, Self::Error> {
                    self.0.alias(term)
                }
                fn check(&mut self, term: Term, timeout: i32) -> Result<bool, Self::Error> {
                    self.0.check(term, timeout)
                }
            }
            remove_single_add(
                factory,
                chunk.mask.clone(),
                at.clone(),
                permission.clone(),
                simplify,
                check_timeout_ms,
                &mut Adapter(service),
            )
            .map_err(MaskHeapError::Service)?
        } else {
            added
        }
    };
    let good = if matches!(resource, ResourceKey::Field(_)) {
        factory.good_field_mask(mask.clone(), may_assume_upper_bounds)
    } else {
        factory.good_mask(mask.clone())
    };
    service.assume(good).map_err(MaskHeapError::Service)?;
    let updated = if recording_function || read_only {
        chunk.with_mask(mask)
    } else {
        let fresh = service
            .fresh("heap", chunk.heap.sort().clone())
            .map_err(MaskHeapError::Service)?;
        service
            .assume_definition(factory.identical_on_known_locations(
                chunk.heap.clone(),
                fresh.clone(),
                mask.clone(),
            ))
            .map_err(MaskHeapError::Service)?;
        chunk.with_mask_and_heap(mask, fresh)
    };
    let snap_perm = if !consume_exact && read_only {
        factory.full_perm()
    } else {
        permission
    };
    let zero = if matches!(resource, ResourceKey::Field(_)) {
        factory.zero_mask()
    } else {
        factory.pred_zero_mask()
    };
    let snap_mask = service
        .alias(factory.mask_add(zero, at, snap_perm))
        .map_err(MaskHeapError::Service)?;
    let snapshot = return_snapshot.then(|| factory.mask_map_term([(resource.clone(), snap_mask)]));
    Ok(MaskConsumption::Complete {
        heap: heap
            .without_chunk(&Chunk::MaskHeap(chunk))
            .with_chunk(Chunk::MaskHeap(updated)),
        snapshot,
    })
}

/// Source produceSingleLocation, operating on one immutable heap branch.
pub fn produce_single_location<S: MaskHeapProductionService>(
    factory: &TermFactory,
    heap: &ListBackedHeap,
    resource: &ResourceKey,
    arguments: &[Term],
    permission: Term,
    snapshot: Term,
    may_assume_upper_bounds: bool,
    service: &mut S,
) -> Result<ListBackedHeap, MaskHeapError<S::Error>> {
    let (heap, chunk) = match find_chunk(heap, resource)? {
        Some(chunk) => (heap.clone(), chunk.clone()),
        None => match resource {
            ResourceKey::Wand(_) => {
                let chunk = BasicMaskHeapChunk {
                    resource_id: ResourceId::MagicWand,
                    resource: resource.clone(),
                    mask: factory.pred_zero_mask(),
                    heap: service
                        .fresh("mwHeap", Sort::WandHeap)
                        .map_err(MaskHeapError::Service)?,
                };
                (heap.with_chunk(Chunk::MaskHeap(chunk.clone())), chunk)
            }
            _ => return Err(MaskHeapError::MissingResource),
        },
    };
    let at = match resource {
        ResourceKey::Field(_) => arguments
            .first()
            .cloned()
            .ok_or(MaskHeapError::MissingArgument)?,
        _ => factory.to_snap_tree(arguments.iter().cloned()),
    };
    let mask = service
        .alias(factory.mask_add(chunk.mask.clone(), at.clone(), permission.clone()))
        .map_err(MaskHeapError::Service)?;
    let good = if matches!(resource, ResourceKey::Field(_)) {
        factory.good_field_mask(mask.clone(), may_assume_upper_bounds)
    } else {
        factory.good_mask(mask.clone())
    };
    service.assume(good).map_err(MaskHeapError::Service)?;
    let value = match snapshot.kind() {
        TermKind::HeapMapTerm(heaps) => {
            let source = heaps
                .iter()
                .find(|(key, _)| key == resource)
                .map(|(_, value)| value.clone())
                .ok_or(MaskHeapError::MissingResource)?;
            factory.heap_lookup(source, at.clone())
        }
        _ => snapshot,
    };
    let new_heap = service
        .alias(factory.merge_single(chunk.heap.clone(), chunk.mask.clone(), at.clone(), value))
        .map_err(MaskHeapError::Service)?;
    let updated = chunk.with_mask_and_heap(mask.clone(), new_heap);
    let result = heap
        .without_chunk(&Chunk::MaskHeap(chunk))
        .with_chunk(Chunk::MaskHeap(updated));
    let constraint = if matches!(resource, ResourceKey::Field(_)) && may_assume_upper_bounds {
        factory.and([
            factory.implies(
                factory.is_positive_perm(permission),
                factory.not(factory.equals(at.clone(), factory.null())),
            ),
            factory.perm_at_most(factory.heap_lookup(mask, at), factory.full_perm()),
        ])
    } else {
        factory.boolean(true)
    };
    service.assume(constraint).map_err(MaskHeapError::Service)?;
    Ok(result)
}

/// Field-mask bound with source receiver and mask-trigger discovery order.
pub fn upper_bound_assertion<E>(
    factory: &TermFactory,
    mask: Term,
    mut fresh: impl FnMut(Sort) -> Result<Term, E>,
) -> Result<Term, MaskHeapError<E>> {
    fn collect(mask: &Term, receivers: &mut Vec<Term>, masks: &mut Vec<Term>) {
        match mask.kind() {
            TermKind::MaskAdd(base, receiver, _) => {
                if !receivers.contains(receiver) {
                    receivers.push(receiver.clone());
                }
                collect(base, receivers, masks);
            }
            TermKind::MaskSum(a, b) => {
                collect(a, receivers, masks);
                collect(b, receivers, masks);
            }
            TermKind::MaskDiff(a, b) => {
                if !masks.contains(b) {
                    masks.push(b.clone());
                }
                collect(a, receivers, masks);
            }
            TermKind::ZeroMask | TermKind::PredZeroMask => (),
            _ => {
                if !masks.contains(mask) {
                    masks.push(mask.clone());
                }
            }
        }
    }
    let mut receivers = Vec::new();
    let mut masks = Vec::new();
    collect(&mask, &mut receivers, &mut masks);
    let individual =
        factory.and(receivers.into_iter().map(|r| {
            factory.perm_at_most(factory.heap_lookup(mask.clone(), r), factory.full_perm())
        }));
    let q = fresh(Sort::Ref).map_err(MaskHeapError::Service)?;
    if !masks.contains(&mask) {
        masks.push(mask.clone());
    }
    let triggers = masks
        .into_iter()
        .map(|m| crate::state::terms::Trigger {
            terms: vec![factory.heap_lookup(m, q.clone())],
        })
        .collect();
    let body = factory.perm_at_most(factory.heap_lookup(mask, q.clone()), factory.full_perm());
    let bound = factory
        .quantification(
            crate::state::terms::Quantifier::Forall,
            vec![q],
            body,
            triggers,
            TermFactory::forall_default_name(),
            false,
            None,
        )
        .map_err(MaskHeapError::Trigger)?;
    Ok(factory.and([individual, bound]))
}

/// Alias creation and validity checks retain their original execution order.
pub trait MaskSimplificationService {
    type Error;
    fn alias(&mut self, term: Term) -> Result<Term, Self::Error>;
    fn check(&mut self, condition: Term, timeout_ms: i32) -> Result<bool, Self::Error>;
}

/// Remove a single permission addition, including the source solver-assisted path.
pub fn remove_single_add<S: MaskSimplificationService>(
    factory: &TermFactory,
    original: Term,
    at: Term,
    amount: Term,
    simplify: bool,
    check_timeout_ms: i32,
    service: &mut S,
) -> Result<Term, S::Error> {
    if !simplify {
        return service.alias(factory.mask_add(original, at, factory.perm_negation(amount)));
    }
    // LinkedHashMap updates the value without moving an existing key.
    fn collect(mask: &Term, additions: &mut Vec<(Term, Term)>) {
        match mask.kind() {
            TermKind::MaskAdd(base, _, value)
                if matches!(value.kind(), TermKind::PermNegation(_)) =>
            {
                collect(base, additions)
            }
            TermKind::MaskAdd(base, receiver, value) => {
                if let Some((_, old)) = additions.iter_mut().find(|(key, _)| key == receiver) {
                    *old = value.clone();
                } else {
                    additions.push((receiver.clone(), value.clone()));
                }
                collect(base, additions);
            }
            TermKind::MaskSum(first, second) => {
                collect(first, additions);
                collect(second, additions);
            }
            TermKind::MaskDiff(first, _) => collect(first, additions),
            _ => (),
        }
    }
    let mut additions = Vec::new();
    collect(&original, &mut additions);
    let direct = additions
        .iter()
        .find(|(receiver, value)| receiver == &at && value == &amount)
        .cloned();
    let mut remaining = amount.clone();
    let mut replacements = std::collections::HashMap::new();
    if let Some(pair) = direct {
        remaining = factory.no_perm();
        replacements.insert(pair, factory.no_perm());
    } else {
        // The upstream second filter compares the *value* with `at`; preserve it.
        let mut candidates = Vec::new();
        for pair in additions
            .iter()
            .filter(|(r, _)| r == &at)
            .chain(additions.iter().filter(|(_, v)| v != &at))
        {
            if !candidates.contains(pair) {
                candidates.push(pair.clone());
            }
        }
        for (receiver, value) in candidates {
            if service.check(
                factory.equals(at.clone(), receiver.clone()),
                check_timeout_ms,
            )? {
                let taken = factory.perm_min(value.clone(), remaining.clone());
                remaining = factory.perm_minus(remaining, taken.clone());
                let left = factory.perm_minus(value.clone(), taken);
                replacements.insert((receiver, value), left);
                if service.check(
                    factory.equals(remaining.clone(), factory.no_perm()),
                    check_timeout_ms,
                )? {
                    break;
                }
            }
        }
    }
    if replacements.is_empty() {
        return service.alias(factory.mask_add(original, at, factory.perm_negation(amount)));
    }
    fn replace<S: MaskSimplificationService>(
        factory: &TermFactory,
        mask: &Term,
        replacements: &mut std::collections::HashMap<(Term, Term), Term>,
        service: &mut S,
    ) -> Result<Term, S::Error> {
        if replacements.is_empty() {
            return Ok(mask.clone());
        }
        match mask.kind() {
            TermKind::MaskAdd(base, receiver, value) => {
                let replacement = replacements.remove(&(receiver.clone(), value.clone()));
                let base = replace(factory, base, replacements, service)?;
                let rewritten = factory.mask_add(
                    base,
                    receiver.clone(),
                    replacement.clone().unwrap_or_else(|| value.clone()),
                );
                if replacement.is_some() {
                    service.alias(rewritten)
                } else {
                    Ok(rewritten)
                }
            }
            TermKind::MaskSum(first, second) => {
                let first = replace(factory, first, replacements, service)?;
                let second = replace(factory, second, replacements, service)?;
                Ok(factory.mask_sum(first, second))
            }
            TermKind::MaskDiff(first, second) => {
                let first = replace(factory, first, replacements, service)?;
                Ok(factory.mask_diff(first, second.clone()))
            }
            _ => Ok(mask.clone()),
        }
    }
    let result = replace(factory, &original, &mut replacements, service)?;
    Ok(factory.mask_add(result, at, factory.perm_negation(remaining)))
}

/// Remove an entire mask, optionally proving equality of candidate mask lookups.
pub fn subtract_mask<S: MaskSimplificationService>(
    factory: &TermFactory,
    original: Term,
    removed: Term,
    resource: &ResourceKey,
    program: &Program,
    converter: &DefaultSymbolConverter,
    simplify: bool,
    service: &mut S,
) -> Result<Term, MaskHeapError<S::Error>> {
    if !simplify {
        return Ok(factory.mask_diff(original, removed));
    }
    fn collect(mask: &Term, additions: &mut Vec<Term>) {
        match mask.kind() {
            TermKind::MaskAdd(base, _, _) | TermKind::MaskDiff(base, _) => collect(base, additions),
            TermKind::MaskSum(a, b) => {
                collect(a, additions);
                collect(b, additions);
            }
            TermKind::ZeroMask | TermKind::PredZeroMask => (),
            _ => {
                if !additions.contains(mask) {
                    additions.push(mask.clone());
                }
            }
        }
    }
    let mut additions = Vec::new();
    collect(&original, &mut additions);
    let mut found = additions.iter().find(|a| **a == removed).cloned();
    if found.is_none() {
        let arg_sorts = match resource {
            ResourceKey::Field(_) => vec![Sort::Ref],
            ResourceKey::Predicate(predicate) => predicate
                .formal_args
                .iter()
                .map(|a| converter.to_sort(&a.typ).map_err(MaskHeapError::Sort))
                .collect::<Result<Vec<_>, _>>()?,
            ResourceKey::Wand(wand) => {
                ferrum_silver::ast::utility::expressions::magic_wand_subexpressions(
                    &wand.ghost_free_wand,
                    program,
                )
                .map_err(MaskHeapError::Wand)?
                .into_iter()
                .map(|exp| {
                    let typ = exp.typ().map_err(MaskHeapError::ExpressionType)?;
                    converter.to_sort(&typ).map_err(MaskHeapError::Sort)
                })
                .collect::<Result<Vec<_>, _>>()?
            }
        };
        let args: Vec<_> = arg_sorts
            .into_iter()
            .enumerate()
            .map(|(i, sort)| {
                factory.var(
                    crate::state::identifiers::Identifier::new(format!("arg_v{i}")),
                    sort,
                    false,
                )
            })
            .collect();
        let arg = if matches!(resource, ResourceKey::Field(_)) {
            args[0].clone()
        } else {
            factory.to_snap_tree(args.clone())
        };
        let removed_lookup = factory.heap_lookup(removed.clone(), arg.clone());
        for add in additions {
            let body = factory.equals(
                factory.heap_lookup(add.clone(), arg.clone()),
                removed_lookup.clone(),
            );
            let quant = factory
                .quantification(
                    crate::state::terms::Quantifier::Forall,
                    args.clone(),
                    body,
                    vec![crate::state::terms::Trigger {
                        terms: vec![removed_lookup.clone()],
                    }],
                    TermFactory::forall_default_name(),
                    false,
                    None,
                )
                .map_err(MaskHeapError::Trigger)?;
            if service.check(quant, 0).map_err(MaskHeapError::Service)? {
                found = Some(add);
                break;
            }
        }
    }
    let Some(found) = found else {
        return Ok(factory.mask_diff(original, removed));
    };
    fn replace(factory: &TermFactory, mask: &Term, found: &mut Option<Term>, zero: &Term) -> Term {
        let Some(target) = found.as_ref() else {
            return mask.clone();
        };
        match mask.kind() {
            TermKind::MaskAdd(base, at, value) => factory.mask_add(
                replace(factory, base, found, zero),
                at.clone(),
                value.clone(),
            ),
            TermKind::MaskSum(a, b) if a == target => {
                *found = None;
                b.clone()
            }
            TermKind::MaskSum(a, b) if b == target => {
                *found = None;
                a.clone()
            }
            TermKind::MaskSum(a, b) => {
                let a = replace(factory, a, found, zero);
                let b = replace(factory, b, found, zero);
                factory.mask_sum(a, b)
            }
            TermKind::MaskDiff(a, b) => {
                factory.mask_diff(replace(factory, a, found, zero), b.clone())
            }
            TermKind::ZeroMask | TermKind::PredZeroMask => mask.clone(),
            _ if mask == target => {
                *found = None;
                zero.clone()
            }
            _ => mask.clone(),
        }
    }
    let zero = if original.sort() == &Sort::mask() {
        factory.zero_mask()
    } else {
        factory.pred_zero_mask()
    };
    Ok(replace(factory, &original, &mut Some(found), &zero))
}

/// Source lookup walks heap order and expects every visited chunk to be mask-backed.
pub fn find_chunk<'a, E>(
    heap: &'a ListBackedHeap,
    resource: &ResourceKey,
) -> Result<Option<&'a BasicMaskHeapChunk>, MaskHeapError<E>> {
    for chunk in heap.values() {
        let Chunk::MaskHeap(chunk) = chunk else {
            return Err(MaskHeapError::NonMaskChunk);
        };
        if &chunk.resource == resource {
            return Ok(Some(chunk));
        }
    }
    Ok(None)
}

pub trait MaskHeapMergeService {
    type Error;
    fn alias(&mut self, term: Term) -> Result<Term, Self::Error>;
    fn assume_upper_bound(&mut self, mask: Term) -> Result<(), Self::Error>;
}

/// Merge in first-seen resource order, aliasing only overlapping heaps.
pub fn merge_wand_heaps<S: MaskHeapMergeService>(
    factory: &TermFactory,
    first: &ListBackedHeap,
    second: &ListBackedHeap,
    may_assume_upper_bounds: bool,
    service: &mut S,
) -> Result<ListBackedHeap, MaskHeapError<S::Error>> {
    let mut resources = Vec::new();
    for chunk in first.values().iter().chain(second.values()) {
        let Chunk::MaskHeap(chunk) = chunk else {
            return Err(MaskHeapError::NonMaskChunk);
        };
        if !resources.contains(&chunk.resource) {
            resources.push(chunk.resource.clone());
        }
    }
    let mut merged = Vec::with_capacity(resources.len());
    for resource in resources {
        let left = find_chunk(first, &resource)?;
        let right = find_chunk(second, &resource)?;
        let chunk = match (left, right) {
            (Some(left), Some(right)) => {
                let mask = factory.mask_sum(left.mask.clone(), right.mask.clone());
                let heap = service
                    .alias(factory.merge_heaps(
                        left.heap.clone(),
                        left.mask.clone(),
                        right.heap.clone(),
                        right.mask.clone(),
                    ))
                    .map_err(MaskHeapError::Service)?;
                if matches!(resource, ResourceKey::Field(_))
                    && may_assume_upper_bounds
                    && mask != left.mask
                    && mask != right.mask
                {
                    service
                        .assume_upper_bound(mask.clone())
                        .map_err(MaskHeapError::Service)?;
                }
                left.with_mask_and_heap(mask, heap)
            }
            (Some(chunk), None) | (None, Some(chunk)) => chunk.clone(),
            (None, None) => return Err(MaskHeapError::MissingResource),
        };
        merged.push(Chunk::MaskHeap(chunk));
    }
    Ok(ListBackedHeap::from_chunks(merged))
}

/// Build source field-first/predicate-second zero masks with fresh or dummy heaps.
pub fn empty_heap<E>(
    program: &Program,
    factory: &TermFactory,
    converter: &DefaultSymbolConverter,
    may_define_new_vars: bool,
    mut fresh: impl FnMut(&str, Sort) -> Result<Term, E>,
) -> Result<ListBackedHeap, MaskHeapError<E>> {
    let mut chunks = Vec::new();
    for field in &program.fields {
        let sort = Sort::Heap(Box::new(
            converter.to_sort(&field.typ).map_err(MaskHeapError::Sort)?,
        ));
        let heap = if may_define_new_vars {
            fresh("hInit", sort).map_err(MaskHeapError::Service)?
        } else {
            factory.dummy_heap(sort)
        };
        chunks.push(Chunk::MaskHeap(BasicMaskHeapChunk {
            resource_id: ResourceId::Field,
            resource: ResourceKey::Field(Arc::new(field.clone())),
            mask: factory.zero_mask(),
            heap,
        }));
    }
    for predicate in &program.predicates {
        let sort = Sort::PredHeap;
        let heap = if may_define_new_vars {
            fresh("hInit", sort).map_err(MaskHeapError::Service)?
        } else {
            factory.dummy_heap(sort)
        };
        chunks.push(Chunk::MaskHeap(BasicMaskHeapChunk {
            resource_id: ResourceId::Predicate,
            resource: ResourceKey::Predicate(Arc::new(predicate.clone())),
            mask: factory.pred_zero_mask(),
            heap,
        }));
    }
    Ok(ListBackedHeap::from_chunks(chunks))
}

/// Decode one mask per ordered resource; non-HeapToSnap projections use zero masks.
pub fn masks_from_snapshot(
    factory: &TermFactory,
    snapshot: Term,
    resources: &[ResourceKey],
) -> Vec<(ResourceKey, Term)> {
    let parts = factory.from_snap_tree(
        snapshot,
        i32::try_from(resources.len()).expect("too many resources"),
    );
    resources
        .iter()
        .cloned()
        .zip(parts)
        .map(|(resource, part)| {
            let mask = match part.kind() {
                TermKind::HeapToSnap(_, mask, _) => mask.clone(),
                _ if matches!(resource, ResourceKey::Field(_)) => factory.zero_mask(),
                _ => factory.pred_zero_mask(),
            };
            (resource, mask)
        })
        .collect()
}

/// Source preserves resource order and aliases each non-dummy HeapToSnap term.
pub fn snapshot_from_masks<E>(
    factory: &TermFactory,
    masks: &[(ResourceKey, Term)],
    resources: &[ResourceKey],
    heap: &ListBackedHeap,
    mut alias: impl FnMut(Term) -> Result<Term, E>,
) -> Result<Term, MaskHeapError<E>> {
    let mut parts = Vec::with_capacity(resources.len());
    for resource in resources {
        let Some(chunk) = find_chunk(heap, resource)? else {
            parts.push(factory.unit());
            continue;
        };
        if matches!(chunk.heap.kind(), TermKind::DummyHeap(_)) {
            parts.push(factory.unit());
            continue;
        }
        let mask = masks
            .iter()
            .find(|(key, _)| key == resource)
            .map(|(_, mask)| mask.clone())
            .ok_or(MaskHeapError::MissingMask)?;
        parts.push(
            alias(factory.heap_to_snap(chunk.heap.clone(), mask, resource.clone()))
                .map_err(MaskHeapError::Service)?,
        );
    }
    Ok(factory.to_snap_tree(parts))
}
/// Combine resource masks while preserving the first map's key order.
pub fn merge_preserving_first_order(
    factory: &TermFactory,
    first: &[(ResourceKey, Term)],
    second: &[(ResourceKey, Term)],
) -> Vec<(ResourceKey, Term)> {
    let mut result = first.to_vec();
    for (key, mask) in second {
        if let Some((_, value)) = result.iter_mut().find(|(old, _)| old == key) {
            *value = factory.mask_sum(value.clone(), mask.clone());
        } else {
            result.push((key.clone(), mask.clone()));
        }
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::state::{identifiers::Identifier, terms::TermOptions};
    #[derive(Default)]
    struct Service {
        aliases: usize,
        checks: usize,
    }
    impl MaskSimplificationService for Service {
        type Error = ();
        fn alias(&mut self, t: Term) -> Result<Term, ()> {
            self.aliases += 1;
            Ok(t)
        }
        fn check(&mut self, _: Term, _: i32) -> Result<bool, ()> {
            self.checks += 1;
            Ok(false)
        }
    }
    #[test]
    fn produce_single_field_uses_source_alias_and_assumption_order() {
        use ferrum_silver::ast::{
            ast::Metadata,
            program::{Field, FieldData},
            r#type::Type,
        };
        struct Production(Vec<&'static str>);
        impl MaskHeapProductionService for Production {
            type Error = ();
            fn fresh(&mut self, _: &str, _: Sort) -> Result<Term, ()> {
                panic!("existing field")
            }
            fn alias(&mut self, t: Term) -> Result<Term, ()> {
                self.0.push("alias");
                Ok(t)
            }
            fn assume(&mut self, _: Term) -> Result<(), ()> {
                self.0.push("assume");
                Ok(())
            }
        }
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let meta = Metadata::default();
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let resource = ResourceKey::Field(Arc::new(field.clone()));
        let program = Program::new(vec![], vec![field], vec![], vec![], vec![], vec![], meta);
        let converter = DefaultSymbolConverter::new(factory.clone(), false);
        let heap = empty_heap(
            &program,
            &factory,
            &converter,
            false,
            |_, _| -> Result<Term, ()> { unreachable!() },
        )
        .unwrap();
        let receiver = factory.var(Identifier::new("r"), Sort::Ref, false);
        let triggers =
            resource_trigger_variants::<()>(&factory, &heap, &resource, &[receiver.clone()])
                .unwrap();
        assert!(
            matches!(triggers[1][0].kind(), TermKind::HeapLookup(mask, _) if matches!(mask.kind(), TermKind::ZeroMask))
        );
        let mut service = Production(vec![]);
        let heap = produce_single_location(
            &factory,
            &heap,
            &resource,
            &[receiver.clone()],
            factory.full_perm(),
            factory.int_literal(7),
            true,
            &mut service,
        )
        .unwrap();
        assert_eq!(service.0, ["alias", "assume", "alias", "assume"]);
        let chunk = find_chunk::<()>(&heap, &resource).unwrap().unwrap();
        assert_eq!(
            factory.heap_lookup(chunk.heap.clone(), receiver.clone()),
            factory.int_literal(7)
        );
        let failed = write_field(
            &factory,
            &heap,
            &resource,
            receiver.clone(),
            factory.int_literal(8),
            |_| Ok::<_, ()>(false),
        )
        .unwrap();
        assert!(matches!(failed, MaskFieldWrite::Insufficient { .. }));
        let updated = write_field(
            &factory,
            &heap,
            &resource,
            receiver.clone(),
            factory.int_literal(8),
            |_| Ok::<_, ()>(true),
        )
        .unwrap();
        let MaskFieldWrite::Updated(updated) = updated else {
            panic!("expected updated heap")
        };
        let read = read_field(&factory, &updated, &resource, receiver, |_| {
            Ok::<_, ()>(true)
        })
        .unwrap();
        assert!(
            matches!(read, MaskFieldRead::Value { value, .. } if value == factory.int_literal(8))
        );
    }
    #[test]
    fn read_only_consume_reports_failure_without_mutation_and_retains_heap_on_success() {
        use ferrum_silver::ast::{
            ast::Metadata,
            program::{Field, FieldData},
            r#type::Type,
        };
        struct Consumer {
            succeeds: bool,
            events: Vec<&'static str>,
        }
        impl MaskHeapProductionService for Consumer {
            type Error = ();
            fn fresh(&mut self, _: &str, _: Sort) -> Result<Term, ()> {
                panic!("read-only consumption")
            }
            fn alias(&mut self, t: Term) -> Result<Term, ()> {
                self.events.push("alias");
                Ok(t)
            }
            fn assume(&mut self, _: Term) -> Result<(), ()> {
                self.events.push("assume");
                Ok(())
            }
        }
        impl MaskHeapConsumptionService for Consumer {
            fn check(&mut self, _: Term, _: i32) -> Result<bool, ()> {
                panic!("read-only consumption")
            }
            fn assert_goal(&mut self, _: Term) -> Result<bool, ()> {
                self.events.push("assert");
                Ok(self.succeeds)
            }
            fn transform_precondition(&mut self, t: Term) -> Result<Term, ()> {
                self.events.push("transform");
                Ok(t)
            }
            fn assume_definition(&mut self, _: Term) -> Result<(), ()> {
                panic!("read-only consumption")
            }
        }
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let meta = Metadata::default();
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let resource = ResourceKey::Field(Arc::new(field.clone()));
        let program = Program::new(vec![], vec![field], vec![], vec![], vec![], vec![], meta);
        let converter = DefaultSymbolConverter::new(f.clone(), false);
        let heap = empty_heap(
            &program,
            &f,
            &converter,
            false,
            |_, _| -> Result<Term, ()> { unreachable!() },
        )
        .unwrap();
        let receiver = f.var(Identifier::new("r"), Sort::Ref, false);
        let mut failed = Consumer {
            succeeds: false,
            events: vec![],
        };
        let result = consume_single_location(
            &f,
            &heap,
            &resource,
            &[receiver.clone()],
            f.full_perm(),
            true,
            true,
            false,
            true,
            true,
            false,
            10,
            &mut failed,
        )
        .unwrap();
        assert!(matches!(result, MaskConsumption::Insufficient { .. }));
        assert_eq!(failed.events, ["transform", "assert"]);
        let mut success = Consumer {
            succeeds: true,
            events: vec![],
        };
        let result = consume_single_location(
            &f,
            &heap,
            &resource,
            &[receiver],
            f.full_perm(),
            true,
            true,
            false,
            true,
            true,
            false,
            10,
            &mut success,
        )
        .unwrap();
        let MaskConsumption::Complete {
            heap: after,
            snapshot: Some(_),
        } = result
        else {
            panic!("expected successful snapshot")
        };
        assert_eq!(
            find_chunk::<()>(&after, &resource).unwrap(),
            find_chunk::<()>(&heap, &resource).unwrap()
        );
        assert_eq!(success.events, ["transform", "assert", "assume", "alias"]);
    }
    #[test]
    fn folded_predicate_heap_map_unfolds_to_original_snapshot() {
        use ferrum_silver::ast::{
            ast::Metadata,
            program::{Predicate, PredicateData},
        };
        let factory = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let predicate = Predicate::new(PredicateData {
            name: "p".into(),
            formal_args: vec![],
            body: None,
            meta: Metadata::default(),
        });
        let resource = ResourceKey::Predicate(Arc::new(predicate));
        let body_snap = factory.sort_wrapper(factory.int_literal(7), Sort::Snap);
        let folded =
            folded_predicate_snapshot::<()>(&factory, &resource, &[], body_snap.clone()).unwrap();
        let result = unfolded_predicate_snapshot(
            &factory,
            &resource,
            &[],
            folded,
            &ListBackedHeap::new(),
            |t| Ok::<_, ()>(t),
        )
        .unwrap();
        assert_eq!(result, body_snap);
    }
    #[test]
    fn quantified_producer_preserves_negative_and_injectivity_failures() {
        use crate::rules::quantified_chunk_support::{InverseFunctions, VariableFunctions};
        use ferrum_silver::ast::{
            ast::Metadata,
            expression::{Exp, ExpKind},
            program::{Field, FieldData},
            r#type::Type,
        };
        struct Qp {
            inverse: InverseFunctions,
            answers: std::collections::VecDeque<bool>,
            definitions: usize,
        }
        impl MaskHeapProductionService for Qp {
            type Error = ();
            fn fresh(&mut self, name: &str, sort: Sort) -> Result<Term, ()> {
                Ok(TermFactory::new(TermOptions {
                    use_flyweight: false,
                    use_old_axiomatization: false,
                    mask_heap_mode: true,
                })
                .var(Identifier::new(name), sort, false))
            }
            fn alias(&mut self, t: Term) -> Result<Term, ()> {
                Ok(t)
            }
            fn assume(&mut self, _: Term) -> Result<(), ()> {
                Ok(())
            }
        }
        impl MaskQuantifiedProductionService for Qp {
            fn fresh_inverse(
                &mut self,
                _: &MaskQuantifiedInputs,
            ) -> Result<(InverseFunctions, Vec<Term>), ()> {
                Ok((self.inverse.clone(), vec![]))
            }
            fn injectivity(&mut self, _: &MaskQuantifiedInputs) -> Result<Term, ()> {
                Ok(self.inverse.condition_ref().clone())
            }
            fn transform_precondition(&mut self, t: Term) -> Result<Term, ()> {
                Ok(t)
            }
            fn assert_goal(&mut self, _: Term) -> Result<bool, ()> {
                Ok(self.answers.pop_front().unwrap())
            }
            fn assume_definition(&mut self, _: Term) -> Result<(), ()> {
                self.definitions += 1;
                Ok(())
            }
            fn no_triggers(&mut self, _: &Exp) -> Result<(), ()> {
                Ok(())
            }
            fn record_inverse_and_mask(
                &mut self,
                _: InverseFunctions,
                _: Term,
                _: Term,
            ) -> Result<(), ()> {
                panic!("failed proof must not record")
            }
        }
        impl MaskHeapConsumptionService for Qp {
            fn check(&mut self, _: Term, _: i32) -> Result<bool, ()> {
                Ok(false)
            }
            fn assert_goal(&mut self, _: Term) -> Result<bool, ()> {
                Ok(self.answers.pop_front().unwrap())
            }
            fn transform_precondition(&mut self, t: Term) -> Result<Term, ()> {
                Ok(t)
            }
            fn assume_definition(&mut self, _: Term) -> Result<(), ()> {
                self.definitions += 1;
                Ok(())
            }
        }
        impl MaskQuantifiedConsumptionService for Qp {
            fn fresh_inverse(
                &mut self,
                _: &MaskQuantifiedInputs,
            ) -> Result<(InverseFunctions, Vec<Term>), ()> {
                Ok((self.inverse.clone(), vec![]))
            }
            fn injectivity(&mut self, _: &MaskQuantifiedInputs) -> Result<Term, ()> {
                Ok(self.inverse.condition_ref().clone())
            }
            fn record_inverse_and_mask(
                &mut self,
                _: InverseFunctions,
                _: Term,
                _: Term,
            ) -> Result<(), ()> {
                panic!("failed proof must not record")
            }
        }
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let meta = Metadata::default();
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let resource = ResourceKey::Field(Arc::new(field.clone()));
        let program = Program::new(
            vec![],
            vec![field],
            vec![],
            vec![],
            vec![],
            vec![],
            meta.clone(),
        );
        let converter = DefaultSymbolConverter::new(f.clone(), false);
        let heap = empty_heap(
            &program,
            &f,
            &converter,
            false,
            |_, _| -> Result<Term, ()> { unreachable!() },
        )
        .unwrap();
        let old_heap = find_chunk::<()>(&heap, &resource)
            .unwrap()
            .unwrap()
            .heap
            .clone();
        let q = f.var(Identifier::new("q"), Sort::Ref, false);
        let axiom = f
            .quantification(
                crate::state::terms::Quantifier::Forall,
                vec![q.clone()],
                f.boolean(true),
                vec![],
                "inverse".into(),
                false,
                None,
            )
            .unwrap();
        let inverse = InverseFunctions::new(
            f.boolean(true),
            vec![],
            None,
            vec![],
            axiom.clone(),
            axiom,
            None,
            VariableFunctions::default(),
            VariableFunctions::default(),
        );
        let input = MaskQuantifiedInputs {
            resource: resource.clone(),
            qvars: vec![q.clone()],
            qvar_expressions: None,
            formal_qvars: vec![q.clone()],
            formal_qvar_expressions: None,
            condition: f.boolean(true),
            condition_expression: None,
            arguments: vec![q],
            argument_expressions: None,
            permission: f.full_perm(),
            permission_expression: None,
            scaling: f.full_perm(),
            snapshot: Some(f.heap_map_term([(resource, old_heap)])),
            explicit_triggers: Some(vec![]),
            translated_triggers: vec![],
            auxiliary_globals: vec![],
            auxiliary_non_globals: vec![],
            auxiliary_debug: None,
            qid: "test".into(),
            quantifier: Exp::new(ExpKind::TrueLit, meta),
        };
        let mut negative = Qp {
            inverse: inverse.clone(),
            answers: [false].into(),
            definitions: 0,
        };
        assert!(matches!(
            produce_quantified(&f, &heap, &input, true, false, &mut negative).unwrap(),
            MaskQuantifiedProduction::NegativePermission { .. }
        ));
        assert_eq!(negative.definitions, 0);
        let mut noninjective = Qp {
            inverse: inverse.clone(),
            answers: [true, false].into(),
            definitions: 0,
        };
        assert!(matches!(
            produce_quantified(&f, &heap, &input, true, false, &mut noninjective).unwrap(),
            MaskQuantifiedProduction::NonInjective { .. }
        ));
        assert_eq!(noninjective.definitions, 0);
        let mut insufficient = Qp {
            inverse,
            answers: [true, true, false].into(),
            definitions: 0,
        };
        assert!(matches!(
            consume_quantified(
                &f,
                &heap,
                &input,
                &program,
                &converter,
                false,
                false,
                false,
                true,
                true,
                false,
                &mut insufficient
            )
            .unwrap(),
            MaskQuantifiedConsumption::Insufficient { .. }
        ));
        assert_eq!(insufficient.definitions, 4);
    }
    #[test]
    fn single_mask_direct_match_and_unmatched_paths_keep_alias_order() {
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let x = f.var(Identifier::new("x"), Sort::Ref, false);
        let y = f.var(Identifier::new("y"), Sort::Ref, false);
        let mask = f.mask_add(f.zero_mask(), x.clone(), f.full_perm());
        let mut service = Service::default();
        let result =
            remove_single_add(&f, mask.clone(), x, f.full_perm(), true, 10, &mut service).unwrap();
        assert!(matches!(result.kind(), TermKind::ZeroMask));
        assert_eq!((service.aliases, service.checks), (1, 0));
        let mut service = Service::default();
        let _ = remove_single_add(&f, mask, y, f.full_perm(), true, 10, &mut service).unwrap();
        assert_eq!((service.aliases, service.checks), (1, 1));
    }
    #[test]
    fn subtract_mask_direct_and_failed_solver_match_preserve_source_order() {
        use ferrum_silver::ast::{
            ast::Metadata,
            program::{Field, FieldData},
            r#type::Type,
        };
        let f = TermFactory::new(TermOptions {
            use_flyweight: false,
            use_old_axiomatization: false,
            mask_heap_mode: true,
        });
        let meta = Metadata::default();
        let field = Field::new(FieldData {
            name: "f".into(),
            typ: Type::Int,
            meta: meta.clone(),
        });
        let resource = ResourceKey::Field(Arc::new(field.clone()));
        let program = Program::new(vec![], vec![field], vec![], vec![], vec![], vec![], meta);
        let converter = DefaultSymbolConverter::new(f.clone(), false);
        let a = f.var(Identifier::new("a"), Sort::mask(), false);
        let b = f.var(Identifier::new("b"), Sort::mask(), false);
        let c = f.var(Identifier::new("c"), Sort::mask(), false);
        let mask = f.mask_sum(a.clone(), b.clone());
        let mut service = Service::default();
        assert_eq!(
            subtract_mask(
                &f,
                mask.clone(),
                a,
                &resource,
                &program,
                &converter,
                true,
                &mut service
            )
            .unwrap(),
            b
        );
        assert_eq!(service.checks, 0);
        let mut service = Service::default();
        let result = subtract_mask(
            &f,
            mask,
            c,
            &resource,
            &program,
            &converter,
            true,
            &mut service,
        )
        .unwrap();
        assert!(matches!(result.kind(), TermKind::MaskDiff(_, _)));
        assert_eq!(service.checks, 2);
    }
}
