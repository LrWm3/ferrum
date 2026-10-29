//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/rules/QuantifiedChunkSupport.scala
//!
//! Purpose:
//! Implement quantified permissions, snapshot/permission summaries and chunk matching.
//!
//! Planned Rust structure:
//! InverseFunctions carries condition, invertibles, additional arguments, inverse/image functions
//! and paired axioms; SnapshotMapDefinition and PermMapDefinition carry emitted definitions.
//! QuantifiedChunkSupport and quantifiedChunkSupporter implement singleton/general chunk
//! construction, heap partition, snapshot/permission map creation and caching,
//! quantified/single-location produce and consume, assertReadPermission/removePermissions, inverse
//! and injectivity axioms, alias matching, snapshot-map combination and chunk-order heuristics.
//!
//! Behavior to preserve:
//! Construct field, predicate and wand chunks with proper sorts, singleton args, inverse
//! substitutions and tags; splitHeap rejects matching nonquantified chunks. Summary definitions
//! condition value equality on positive permission, use snapshot-tuple codomains for
//! predicates/wands, preserve optional domains and configured triggers. Snapshot-map cache keys
//! use resource and ordered chunks; a hit also requires compatible stored domain condition
//! (equal, or cached True with no requested condition). Bypass snapshot cache in extended exhale
//! and re-emit value definitions on hits, plus domain definitions when requested. Permission-map
//! cache uses resource/chunks and likewise re-emits its value definitions.
//! Production scales permissions, selects explicit or inferred inverse triggers, checks nonnegative
//! and optionally injectivity, assumes inverse and resource properties then merges chunk; retain
//! function recorder and trigger summaries. Consumption checks nonnegative and injectivity, handles
//! wand reserve transfer, and otherwise removes from threaded partial heap. Greedy modes retry
//! after consolidation; complete mode avoids extra retry. Single-location paths distinguish missing
//! wand from insufficient permission and return wand snapshot-function lookup without Snap
//! conversion. Removal respects read-only mode, configurable ordering, greedy subset checks versus
//! complete matching, exact versus constrainable permissions, short intermediate checks and
//! mandatory final check; track untouched chunks for summaries and optional permission macros.
//! Inverse creation asserts arity/sorts and generates image functions for every quantified variable
//! despite older prose suggesting exceptions; axioms preserve trigger choices and global scope.
//! Greedy matching prioritizes original condition/tag then subset proof; complete matching proves
//! locations and conditions. Fresh snapshot maps when neither permission is provably positive avoid
//! unsound reuse.
//!
//! Integration:
//! rules::heap_supporter, mask_heap_supporter, consumer, producer, havoc_supporter,
//! magic_wand_supporter, state_consolidator, state::snapshot_map_cache, resources and
//! state::triggers.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for representation, branch state, continuation and solver context
//! ownership; preserve ordering and failures.
//!
//! Open decisions:
//! Inverse/trigger identity, caches, snapshot map and continuation/solver ownership with all heap
//! encodings.
//!
//! Status: partial; inverse/map data, hint extraction and resource-specific generic/singleton
//! chunks, inverse generation, summaries, matching, removal and single-location rules implemented.
//! General and single-location consumption use ordinary heaps or wand reserve transfer through
//! native solver services. Debug expression reconstruction and other heap encodings remain partial.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.

use crate::state::terms::{
    ApplicableKind, ApplicationTarget, Term, TermFactory, TermKind, UnsupportedTriggerTransform,
};
use ferrum_silver::ast::expression::Exp;
use ferrum_silver::ast::program::LocalVarDecl;
use std::collections::HashMap;

fn apply_function(factory: &TermFactory, function: &ApplicationTarget, args: Vec<Term>) -> Term {
    match function {
        ApplicationTarget::Function(f) => factory.app(f.clone(), args),
        ApplicationTarget::Variable(v) => factory.app_var(v.clone(), args),
    }
}

/// Ordered source map with map equality, independent of insertion order.
#[derive(Clone, Debug, Default)]
pub struct VariableFunctions(Vec<(Term, ApplicationTarget)>);
impl VariableFunctions {
    pub fn new(entries: impl IntoIterator<Item = (Term, ApplicationTarget)>) -> Self {
        let mut out: Vec<(Term, ApplicationTarget)> = Vec::new();
        for (var, function) in entries {
            assert!(
                matches!(var.kind(), TermKind::Var(_)),
                "expected quantified variable"
            );
            match &function {
                ApplicationTarget::Function(f) => {
                    assert_ne!(f.data().kind, ApplicableKind::Macro, "expected a function")
                }
                ApplicationTarget::Variable(v) => assert!(
                    matches!(v.kind(), TermKind::Var(_)),
                    "expected variable function"
                ),
            }
            if let Some((old_key, old)) = out.iter_mut().find(|(key, _)| key == &var) {
                *old_key = var;
                *old = function;
            } else {
                out.push((var, function));
            }
        }
        Self(out)
    }
    pub fn iter(&self) -> impl Iterator<Item = &(Term, ApplicationTarget)> {
        self.0.iter()
    }
}
impl PartialEq for VariableFunctions {
    fn eq(&self, other: &Self) -> bool {
        self.0.len() == other.0.len()
            && self
                .0
                .iter()
                .all(|(k, v)| other.0.iter().any(|(k2, v2)| k == k2 && v == v2))
    }
}
impl Eq for VariableFunctions {}

/// Data contract retained across quantified-chunk merges; rules are not implemented here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InverseFunctions {
    pub(crate) condition: Term,
    pub(crate) invertibles: Vec<Term>,
    pub(crate) invertible_exps: Option<Vec<Exp>>,
    pub(crate) additional_arguments: Vec<Term>,
    pub(crate) axiom_inverses_of_invertibles: Term,
    pub(crate) axiom_invertibles_of_inverses: Term,
    pub(crate) qvar_exps: Option<Vec<LocalVarDecl>>,
    pub(crate) qvars_to_inverses: VariableFunctions,
    pub(crate) qvars_to_images: VariableFunctions,
}
impl InverseFunctions {
    pub fn validate(&self) {
        assert!(matches!(
            self.axiom_inverses_of_invertibles.kind(),
            TermKind::Quantification { .. }
        ));
        assert!(matches!(
            self.axiom_invertibles_of_inverses.kind(),
            TermKind::Quantification { .. }
        ));
    }
    pub fn inverses(&self) -> impl Iterator<Item = &ApplicationTarget> {
        self.qvars_to_inverses.iter().map(|(_, f)| f)
    }
    pub fn images(&self) -> impl Iterator<Item = &ApplicationTarget> {
        self.qvars_to_images.iter().map(|(_, f)| f)
    }
    pub fn definitional_axioms(&self) -> [&Term; 2] {
        [
            &self.axiom_inverses_of_invertibles,
            &self.axiom_invertibles_of_inverses,
        ]
    }
    pub fn inverses_of(&self, factory: &TermFactory, arguments: &[Term]) -> Vec<Term> {
        self.inverses()
            .map(|fun| {
                apply_function(
                    factory,
                    fun,
                    self.additional_arguments
                        .iter()
                        .chain(arguments)
                        .cloned()
                        .collect(),
                )
            })
            .collect()
    }
    pub fn qvars_to_inverses_of(
        &self,
        factory: &TermFactory,
        arguments: &[Term],
    ) -> Vec<(Term, Term)> {
        self.qvars_to_inverses
            .iter()
            .map(|(var, fun)| {
                (
                    var.clone(),
                    apply_function(
                        factory,
                        fun,
                        self.additional_arguments
                            .iter()
                            .chain(arguments)
                            .cloned()
                            .collect(),
                    ),
                )
            })
            .collect()
    }
    pub fn substitute(
        &self,
        factory: &TermFactory,
        replacements: &HashMap<Term, Term>,
    ) -> Result<Self, UnsupportedTriggerTransform> {
        let mut result = self.clone();
        result.condition = factory.replace(&self.condition, replacements)?;
        result.invertibles = self
            .invertibles
            .iter()
            .map(|x| factory.replace(x, replacements))
            .collect::<Result<_, _>>()?;
        result.additional_arguments = self
            .additional_arguments
            .iter()
            .map(|x| factory.replace(x, replacements))
            .collect::<Result<_, _>>()?;
        result.axiom_inverses_of_invertibles =
            factory.replace(&self.axiom_inverses_of_invertibles, replacements)?;
        result.axiom_invertibles_of_inverses =
            factory.replace(&self.axiom_invertibles_of_inverses, replacements)?;
        result.validate();
        Ok(result)
    }
}

impl InverseFunctions {
    pub fn new(
        condition: Term,
        invertibles: Vec<Term>,
        invertible_exps: Option<Vec<Exp>>,
        additional_arguments: Vec<Term>,
        axiom_inverses_of_invertibles: Term,
        axiom_invertibles_of_inverses: Term,
        qvar_exps: Option<Vec<LocalVarDecl>>,
        qvars_to_inverses: VariableFunctions,
        qvars_to_images: VariableFunctions,
    ) -> Self {
        let result = Self {
            condition,
            invertibles,
            invertible_exps,
            additional_arguments,
            axiom_inverses_of_invertibles,
            axiom_invertibles_of_inverses,
            qvar_exps,
            qvars_to_inverses,
            qvars_to_images,
        };
        result.validate();
        result
    }
    pub fn condition_ref(&self) -> &Term {
        &self.condition
    }
    pub fn invertibles_ref(&self) -> &Vec<Term> {
        &self.invertibles
    }
    pub fn invertible_exps_ref(&self) -> &Option<Vec<Exp>> {
        &self.invertible_exps
    }
    pub fn additional_arguments_ref(&self) -> &Vec<Term> {
        &self.additional_arguments
    }
    pub fn axiom_inverses_of_invertibles_ref(&self) -> &Term {
        &self.axiom_inverses_of_invertibles
    }
    pub fn axiom_invertibles_of_inverses_ref(&self) -> &Term {
        &self.axiom_invertibles_of_inverses
    }
    pub fn qvar_exps_ref(&self) -> &Option<Vec<LocalVarDecl>> {
        &self.qvar_exps
    }
    pub fn qvars_to_inverses_ref(&self) -> &VariableFunctions {
        &self.qvars_to_inverses
    }
    pub fn qvars_to_images_ref(&self) -> &VariableFunctions {
        &self.qvars_to_images
    }
}

/// Source AST resource for snapshot/permission definitions. Wand equality here is
/// structural AST equality, not the structure-index equality of a chunk identifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SnapshotResource {
    Field(std::sync::Arc<ferrum_silver::ast::program::Field>),
    Predicate(std::sync::Arc<ferrum_silver::ast::program::Predicate>),
    Wand(Exp),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SnapshotMapDefinition {
    pub resource: SnapshotResource,
    pub snapshot_map: Term,
    pub value_definitions: Vec<Term>,
    pub domain_definitions: Vec<Term>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PermMapDefinition {
    pub resource: SnapshotResource,
    pub permission_map: Term,
    pub value_definitions: Vec<Term>,
}

/// Prefer direct sequence/map/function argument hints; only when none exist, use the
/// first sequence or set membership found in the condition's source traversal order.
pub fn extract_hints(
    factory: &TermFactory,
    condition: Option<&Term>,
    arguments: &[Term],
) -> Result<Vec<Term>, crate::state::terms::UnsupportedSubterms> {
    let hints: Vec<_> = arguments
        .iter()
        .filter_map(|argument| match argument.kind() {
            TermKind::SeqAt(sequence, _) | TermKind::MapLookup(sequence, _) => {
                Some(sequence.clone())
            }
            TermKind::App { applicable, .. } => Some(match applicable {
                ApplicationTarget::Function(function) => factory.app_hint(function.clone()),
                ApplicationTarget::Variable(variable) => factory.app_hint_var(variable.clone()),
            }),
            _ => None,
        })
        .collect();
    if !hints.is_empty() {
        return Ok(hints);
    }
    let Some(condition) = condition else {
        return Ok(Vec::new());
    };
    Ok(condition
        .find(&mut |term| match term.kind() {
            TermKind::SeqIn(sequence, _) | TermKind::SeqInTrigger(sequence, _) => {
                Some(sequence.clone())
            }
            TermKind::SetIn(_, set) => Some(set.clone()),
            _ => None,
        })?
        .into_iter()
        .collect())
}

/// Inputs shared by singleton and general quantified chunk construction.
pub struct QuantifiedChunkData {
    pub codomain_vars: Vec<Term>,
    pub codomain_var_exps: Option<Vec<LocalVarDecl>>,
    pub arguments: Vec<Term>,
    pub snapshot_map: Term,
    pub condition: Term,
    pub condition_exp: Option<Exp>,
    pub permission: Term,
    pub permission_exp: Option<Exp>,
    pub inverses: Vec<InverseFunctions>,
    pub singleton_args: Option<Vec<Term>>,
    pub singleton_arg_exps: Option<Vec<Exp>>,
    pub tag: Option<i32>,
    pub hints: Vec<Term>,
    pub debugging: bool,
}

#[derive(Debug)]
pub enum QuantifiedChunkConstructionError {
    MissingDebugPermission,
}

/// Construct the resource-specific quantified chunk. Wand permission is conditionalised
/// explicitly; field and predicate chunks perform the same conditioning in their constructors.
pub fn generic_quantified_chunk(
    factory: &TermFactory,
    resource: &crate::state::terms::ResourceKey,
    data: QuantifiedChunkData,
) -> Result<crate::state::chunks::Chunk, QuantifiedChunkConstructionError> {
    use crate::state::chunks::{
        BasicChunkIdentifier, Chunk, QuantifiedFieldChunk, QuantifiedMagicWandChunk,
        QuantifiedPredicateChunk,
    };
    use crate::state::terms::ResourceKey;
    use ferrum_silver::ast::expression::ExpKind;
    Ok(match resource {
        ResourceKey::Field(field) => {
            assert_eq!(data.arguments.len(), 1);
            assert!(
                data.singleton_args
                    .as_ref()
                    .is_none_or(|args| args.len() == 1)
            );
            assert!(
                data.singleton_arg_exps
                    .as_ref()
                    .is_none_or(|args| args.len() == 1)
            );
            Chunk::QuantifiedField(QuantifiedFieldChunk::new(
                factory,
                BasicChunkIdentifier(field.name.clone()),
                data.snapshot_map,
                data.condition.clone(),
                data.condition,
                data.condition_exp,
                data.permission,
                data.permission_exp,
                data.inverses,
                data.singleton_args.map(|v| v[0].clone()),
                data.singleton_arg_exps.map(|v| v[0].clone()),
                data.tag,
                data.hints,
                data.debugging,
            ))
        }
        ResourceKey::Predicate(predicate) => {
            Chunk::QuantifiedPredicate(QuantifiedPredicateChunk::new(
                factory,
                BasicChunkIdentifier(predicate.name.clone()),
                data.codomain_vars,
                data.codomain_var_exps,
                data.snapshot_map,
                data.condition.clone(),
                data.condition,
                data.condition_exp,
                data.permission,
                data.permission_exp,
                data.inverses,
                data.singleton_args,
                data.singleton_arg_exps,
                data.tag,
                data.hints,
            ))
        }
        ResourceKey::Wand(wand) => {
            let debug_permission = match data.condition_exp {
                Some(condition) => {
                    let permission = data
                        .permission_exp
                        .ok_or(QuantifiedChunkConstructionError::MissingDebugPermission)?;
                    let metadata = condition.metadata().clone();
                    Some(Exp::new(
                        ExpKind::CondExp(
                            condition,
                            permission,
                            Exp::new(ExpKind::NoPerm, Default::default()),
                        ),
                        metadata,
                    ))
                }
                None => None,
            };
            let permission =
                factory.ite(data.condition.clone(), data.permission, factory.no_perm());
            Chunk::QuantifiedMagicWand(QuantifiedMagicWandChunk::new(
                wand.clone(),
                data.codomain_vars,
                data.codomain_var_exps,
                data.snapshot_map,
                data.condition,
                permission,
                debug_permission,
                data.inverses,
                data.singleton_args,
                data.singleton_arg_exps,
                data.tag,
                data.hints,
            ))
        }
    })
}

#[derive(Debug)]
pub enum SingletonChunkError {
    MissingDebugArguments,
    Hints(crate::state::terms::UnsupportedSubterms),
    Construction(QuantifiedChunkConstructionError),
}

/// Form the codomain equality condition and hints for a single quantified location.
pub fn singleton_quantified_chunk(
    factory: &TermFactory,
    resource: &crate::state::terms::ResourceKey,
    codomain_vars: Vec<Term>,
    codomain_var_exps: Option<Vec<LocalVarDecl>>,
    arguments: Vec<Term>,
    argument_exps: Option<Vec<Exp>>,
    permission: Term,
    permission_exp: Option<Exp>,
    snapshot_map: Term,
    tag: Option<i32>,
    debugging: bool,
) -> Result<crate::state::chunks::Chunk, SingletonChunkError> {
    use ferrum_silver::ast::expression::ExpKind;
    let condition = factory.and(
        codomain_vars
            .iter()
            .zip(&arguments)
            .map(|(var, argument)| factory.equals(var.clone(), argument.clone())),
    );
    let condition_exp = if let Some(vars) = &codomain_var_exps {
        let args = argument_exps
            .as_ref()
            .ok_or(SingletonChunkError::MissingDebugArguments)?;
        let mut comparisons = vars.iter().zip(args).map(|(var, arg)| {
            let local = Exp::new(ExpKind::LocalVar(var.local_var()), var.meta.clone());
            Exp::new(ExpKind::EqCmp(local, arg.clone()), Default::default())
        });
        Some(match comparisons.next() {
            Some(first) => comparisons.fold(first, |left, right| {
                Exp::new(ExpKind::And(left, right), Default::default())
            }),
            None => Exp::new(ExpKind::TrueLit, Default::default()),
        })
    } else {
        None
    };
    let hints = extract_hints(factory, None, &arguments).map_err(SingletonChunkError::Hints)?;
    generic_quantified_chunk(
        factory,
        resource,
        QuantifiedChunkData {
            codomain_vars,
            codomain_var_exps,
            singleton_args: Some(arguments.clone()),
            singleton_arg_exps: argument_exps,
            arguments,
            snapshot_map,
            condition,
            condition_exp,
            permission,
            permission_exp,
            inverses: Vec::new(),
            tag,
            hints,
            debugging,
        },
    )
    .map_err(SingletonChunkError::Construction)
}

pub trait SnapshotMapFreshener<P, D, J> {
    type Error;
    fn fresh_snapshot_map(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
        additional_arguments: &[Term],
    ) -> Result<Term, Self::Error>;
}
#[derive(Debug)]
pub enum SingletonMapError<E> {
    Fresh(E),
    Traversal(crate::state::terms::UnsupportedSubterms),
}
/// A singleton map is constrained at exactly the requested resource arguments.
pub fn singleton_snapshot_map<P, D, J: Clone + PartialEq, F: SnapshotMapFreshener<P, D, J>>(
    factory: &TermFactory,
    freshener: &mut F,
    state: &crate::state::state::State<P, D, J>,
    resource: &crate::state::terms::ResourceKey,
    arguments: &[Term],
    value: Term,
) -> Result<(Term, Term), SingletonMapError<F::Error>> {
    let mut additional: Vec<_> = state
        .packaging_wand_snapshots
        .iter()
        .map(|(term, _)| term.clone())
        .collect();
    additional.extend(
        state
            .relevant_quantified_variables_in(arguments)
            .map_err(SingletonMapError::Traversal)?
            .into_iter()
            .map(|(term, _)| term),
    );
    let map = freshener
        .fresh_snapshot_map(state, resource, &additional)
        .map_err(SingletonMapError::Fresh)?;
    let lookup = factory.resource_lookup(resource, map.clone(), arguments.to_vec());
    Ok((map, factory.builtin_equals(lookup, value)))
}

#[derive(Debug)]
pub enum GeneralQuantifiedChunkError {
    Hints(crate::state::terms::UnsupportedSubterms),
    Transform(UnsupportedTriggerTransform),
    Construction(QuantifiedChunkConstructionError),
}
/// Build a general quantified chunk from freshly generated inverse functions and their
/// codomain-image constraints. The generator must use `condition && permission > 0`,
/// as in the source; construction then substitutes inverses into the original condition
/// and permission, and retains the original condition for hint extraction.
pub fn quantified_chunk_from_inverses(
    factory: &TermFactory,
    resource: &crate::state::terms::ResourceKey,
    mut data: QuantifiedChunkData,
    inverse: InverseFunctions,
    images_of_codomain: Vec<Term>,
) -> Result<crate::state::chunks::Chunk, GeneralQuantifiedChunkError> {
    let substitutions: HashMap<_, _> = inverse
        .qvars_to_inverses_of(factory, &data.codomain_vars)
        .into_iter()
        .collect();
    data.hints = extract_hints(factory, Some(&data.condition), &data.arguments)
        .map_err(GeneralQuantifiedChunkError::Hints)?;
    let condition = factory
        .replace(&data.condition, &substitutions)
        .map_err(GeneralQuantifiedChunkError::Transform)?;
    data.condition = factory.and(
        images_of_codomain
            .into_iter()
            .chain(std::iter::once(condition)),
    );
    data.permission = factory
        .replace(&data.permission, &substitutions)
        .map_err(GeneralQuantifiedChunkError::Transform)?;
    data.inverses = vec![inverse];
    data.singleton_args = None;
    data.singleton_arg_exps = None;
    generic_quantified_chunk(factory, resource, data)
        .map_err(GeneralQuantifiedChunkError::Construction)
}

pub trait PermissionMapFreshener {
    type Error;
    fn fresh_permission_map(
        &mut self,
        resource: &crate::state::terms::ResourceKey,
    ) -> Result<Term, Self::Error>;
    fn next_summary_id(&mut self) -> u64;
}
#[derive(Debug)]
pub enum PermissionSummaryError<E> {
    Fresh(E),
    NonQuantifiedChunk,
    Transform(UnsupportedTriggerTransform),
}
/// A permission map is axiomatized as the sum of the permissions of all matching chunks.
/// If this resource is used as a trigger, emit its additional trigger propagation axiom.
pub fn summarise_permission_map<F: PermissionMapFreshener>(
    factory: &TermFactory,
    freshener: &mut F,
    resource: &crate::state::terms::ResourceKey,
    codomain_vars: &[Term],
    relevant_chunks: &[crate::state::chunks::Chunk],
    snapshot_map: &Term,
    used_as_trigger: bool,
) -> Result<(Term, Vec<Term>), PermissionSummaryError<F::Error>> {
    use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
    use crate::state::chunks::Chunk;
    use crate::state::terms::{Quantifier, Trigger};
    let map = freshener
        .fresh_permission_map(resource)
        .map_err(PermissionSummaryError::Fresh)?;
    let lookup = factory.resource_permission_lookup(resource, map.clone(), codomain_vars.to_vec());
    let mut sum = factory.no_perm();
    let mut maps = Vec::new();
    for chunk in relevant_chunks {
        let (permission, map) = match chunk {
            Chunk::QuantifiedField(c) => (c.permission(factory), c.snapshot_map()),
            Chunk::QuantifiedPredicate(c) => (c.permission(factory), c.snapshot_map()),
            Chunk::QuantifiedMagicWand(c) => (c.permission(factory), c.snapshot_map()),
            _ => return Err(PermissionSummaryError::NonQuantifiedChunk),
        };
        sum = factory.perm_plus(sum, permission);
        maps.push(map.clone());
    }
    let body = factory.equals(lookup.clone(), sum);
    let name = format!("qp.resPrmSumDef{}", freshener.next_summary_id());
    let definition = factory
        .quantification(
            Quantifier::Forall,
            codomain_vars.to_vec(),
            body,
            vec![Trigger {
                terms: vec![lookup.clone()],
            }],
            name,
            true,
            None,
        )
        .map_err(PermissionSummaryError::Transform)?;
    let mut definitions = vec![definition];
    if used_as_trigger {
        let triggers = std::iter::once(snapshot_map.clone())
            .chain(maps)
            .map(|sm| factory.resource_trigger(resource, sm, codomain_vars.to_vec()));
        let body = factory.and(triggers);
        let name = format!("qp.resTrgDef{}", freshener.next_summary_id());
        definitions.push(
            factory
                .quantification(
                    Quantifier::Forall,
                    codomain_vars.to_vec(),
                    body,
                    vec![Trigger {
                        terms: vec![lookup],
                    }],
                    name,
                    true,
                    None,
                )
                .map_err(PermissionSummaryError::Transform)?,
        );
    }
    Ok((map, definitions))
}

pub trait SnapshotSummaryFreshener<P, D, J>: SnapshotMapFreshener<P, D, J> {
    fn fresh_summary_binder(&mut self) -> Result<Term, Self::Error>;
    fn next_snapshot_summary_id(&mut self) -> u64;
}
#[derive(Debug)]
pub enum SnapshotSummaryError<E> {
    Fresh(E),
    Traversal(crate::state::terms::UnsupportedSubterms),
    Transform(UnsupportedTriggerTransform),
    NonQuantifiedChunk,
    MissingFieldCodomain,
}
/// Produce the value, optional resource-trigger, and optional domain definitions for a
/// fresh summarising snapshot map. Emission and cache lookup are handled by the caller.
pub fn summarise_snapshot_map<P, D, J: Clone + PartialEq, F: SnapshotSummaryFreshener<P, D, J>>(
    factory: &TermFactory,
    freshener: &mut F,
    state: &crate::state::state::State<P, D, J>,
    resource: &crate::state::terms::ResourceKey,
    codomain_vars: &[Term],
    relevant_chunks: &[crate::state::chunks::Chunk],
    domain_condition: Option<&Term>,
    used_as_trigger: bool,
    disable_isc_triggers: bool,
) -> Result<(Term, Vec<Term>, Vec<Term>), SnapshotSummaryError<F::Error>> {
    use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
    use crate::state::chunks::Chunk;
    use crate::state::terms::{Quantifier, ResourceKey, Trigger};
    let mut chunks = Vec::new();
    for chunk in relevant_chunks {
        chunks.push(match chunk {
            Chunk::QuantifiedField(c) => (c.snapshot_map().clone(), c.permission(factory)),
            Chunk::QuantifiedPredicate(c) => (c.snapshot_map().clone(), c.permission(factory)),
            Chunk::QuantifiedMagicWand(c) => (c.snapshot_map().clone(), c.permission(factory)),
            _ => return Err(SnapshotSummaryError::NonQuantifiedChunk),
        });
    }
    let mut relevant: Vec<Term> = state
        .packaging_wand_snapshots
        .iter()
        .map(|(v, _)| v.clone())
        .collect();
    for (variable, _) in &state.quantified_variables {
        let mut occurs = false;
        for (map, _) in &chunks {
            if map
                .contains(variable)
                .map_err(SnapshotSummaryError::Traversal)?
            {
                occurs = true;
                break;
            }
        }
        if !occurs && let Some(condition) = domain_condition {
            occurs = condition
                .contains(variable)
                .map_err(SnapshotSummaryError::Traversal)?;
        }
        if occurs {
            relevant.push(variable.clone());
        }
    }
    let mut additional: Vec<Term> = state
        .function_recorder
        .arguments()
        .unwrap_or_default()
        .into_iter()
        .map(|(v, _)| v)
        .collect();
    additional.extend(relevant.iter().cloned());
    let snapshot = freshener
        .fresh_snapshot_map(state, resource, &additional)
        .map_err(SnapshotSummaryError::Fresh)?;
    let field = matches!(resource, ResourceKey::Field(_));
    let qvar = if field {
        codomain_vars
            .first()
            .cloned()
            .ok_or(SnapshotSummaryError::MissingFieldCodomain)?
    } else {
        freshener
            .fresh_summary_binder()
            .map_err(SnapshotSummaryError::Fresh)?
    };
    let substitutions: HashMap<_, _> = if field {
        HashMap::new()
    } else {
        codomain_vars
            .iter()
            .cloned()
            .zip(factory.from_snap_tree_targets(qvar.clone(), codomain_vars))
            .collect()
    };
    let domain_condition = domain_condition
        .map(|c| factory.replace(c, &substitutions))
        .transpose()
        .map_err(SnapshotSummaryError::Transform)?;
    let global = relevant.is_empty();
    let (domain, has_domain) = match resource {
        ResourceKey::Field(f) => (
            factory.domain(f.name.clone(), snapshot.clone()),
            factory.has_domain(f.name.clone(), snapshot.clone(), global),
        ),
        ResourceKey::Predicate(p) => (
            factory.predicate_domain(p.name.clone(), snapshot.clone()),
            factory.has_predicate_domain(p.name.clone(), snapshot.clone(), global),
        ),
        ResourceKey::Wand(w) => (
            factory.predicate_domain(w.to_string(), snapshot.clone()),
            factory.has_predicate_domain(w.to_string(), snapshot.clone(), global),
        ),
    };
    let in_domain = factory.set_in(qvar.clone(), domain);
    let summary_lookup = factory.resource_lookup(resource, snapshot.clone(), vec![qvar.clone()]);
    let mut definitions = Vec::new();
    for (map, permission) in &chunks {
        let permission = factory
            .replace(permission, &substitutions)
            .map_err(SnapshotSummaryError::Transform)?;
        let positive = factory.is_positive_perm(permission);
        let effective = factory.and([
            domain_condition
                .clone()
                .unwrap_or_else(|| factory.boolean(true)),
            positive,
        ]);
        let old_lookup = factory.resource_lookup(resource, map.clone(), vec![qvar.clone()]);
        let not_unit = if field {
            factory.boolean(true)
        } else if codomain_vars.is_empty() {
            factory.equals(qvar.clone(), factory.unit())
        } else {
            factory.not(factory.equals(qvar.clone(), factory.unit()))
        };
        let body = factory.implies(
            effective,
            factory.and([
                not_unit,
                factory.builtin_equals(summary_lookup.clone(), old_lookup.clone()),
            ]),
        );
        let triggers = if disable_isc_triggers {
            vec![]
        } else {
            vec![
                Trigger {
                    terms: vec![summary_lookup.clone()],
                },
                Trigger {
                    terms: vec![old_lookup],
                },
            ]
        };
        let name = format!("qp.psmValDef{}", freshener.next_snapshot_summary_id());
        definitions.push(
            factory
                .quantification(
                    Quantifier::Forall,
                    vec![qvar.clone()],
                    body,
                    triggers,
                    name,
                    global,
                    None,
                )
                .map_err(SnapshotSummaryError::Transform)?,
        );
    }
    if used_as_trigger {
        let body =
            factory.and(chunks.iter().map(|(map, _)| {
                factory.resource_trigger(resource, map.clone(), vec![qvar.clone()])
            }));
        let name = format!("qp.psmResTrgDef{}", freshener.next_snapshot_summary_id());
        definitions.push(
            factory
                .quantification(
                    Quantifier::Forall,
                    vec![qvar.clone()],
                    body,
                    vec![Trigger {
                        terms: vec![summary_lookup],
                    }],
                    name,
                    global,
                    None,
                )
                .map_err(SnapshotSummaryError::Transform)?,
        );
    }
    let mut domains = Vec::new();
    if let Some(condition) = domain_condition {
        let triggers = if disable_isc_triggers {
            vec![]
        } else {
            vec![Trigger {
                terms: vec![in_domain.clone()],
            }]
        };
        let name = format!("qp.psmDomDef{}", freshener.next_snapshot_summary_id());
        domains.push(
            factory
                .quantification(
                    Quantifier::Forall,
                    vec![qvar],
                    factory.iff(in_domain, condition),
                    triggers,
                    name,
                    global,
                    None,
                )
                .map_err(SnapshotSummaryError::Transform)?,
        );
        domains.push(has_domain);
    }
    Ok((snapshot, definitions, domains))
}

#[derive(Debug)]
pub enum InjectivityError {
    EmptyQuantifiedVariables,
    NonVariableBinder,
    Transform(UnsupportedTriggerTransform),
}
/// Create the source two-renaming injectivity check, guarded by positive permission.
pub fn injectivity_axiom(
    factory: &TermFactory,
    quantified_vars: &[Term],
    condition: &Term,
    permission: &Term,
    arguments: &[Term],
    triggers: Vec<crate::state::terms::Trigger>,
    qid_prefix: &str,
) -> Result<Term, InjectivityError> {
    use crate::state::terms::Quantifier;
    if quantified_vars.is_empty() {
        return Err(InjectivityError::EmptyQuantifiedVariables);
    }
    let mut first = Vec::new();
    let mut second = Vec::new();
    for var in quantified_vars {
        let TermKind::Var(v) = var.kind() else {
            return Err(InjectivityError::NonVariableBinder);
        };
        first.push(factory.var(
            v.id.rename(&|id| format!("{id}1")),
            v.sort.clone(),
            v.is_wildcard,
        ));
        second.push(factory.var(
            v.id.rename(&|id| format!("{id}2")),
            v.sort.clone(),
            v.is_wildcard,
        ));
    }
    let subst1: HashMap<_, _> = quantified_vars
        .iter()
        .cloned()
        .zip(first.iter().cloned())
        .collect();
    let subst2: HashMap<_, _> = quantified_vars
        .iter()
        .cloned()
        .zip(second.iter().cloned())
        .collect();
    let effective = factory.and([
        condition.clone(),
        factory.is_positive_perm(permission.clone()),
    ]);
    let c1 = factory
        .replace(&effective, &subst1)
        .map_err(InjectivityError::Transform)?;
    let c2 = factory
        .replace(&effective, &subst2)
        .map_err(InjectivityError::Transform)?;
    let mut args_equal = Vec::new();
    for argument in arguments {
        let a = factory
            .replace(argument, &subst1)
            .map_err(InjectivityError::Transform)?;
        let b = factory
            .replace(argument, &subst2)
            .map_err(InjectivityError::Transform)?;
        args_equal.push(factory.equals(a, b));
    }
    let vars_equal = factory.and(
        first
            .iter()
            .zip(&second)
            .map(|(a, b)| factory.equals(a.clone(), b.clone())),
    );
    let body = factory.implies(factory.and([c1, c2, factory.and(args_equal)]), vars_equal);
    first.extend(second);
    factory
        .quantification(
            Quantifier::Forall,
            first,
            body,
            triggers,
            format!("{qid_prefix}-rcvrInj"),
            false,
            None,
        )
        .map_err(InjectivityError::Transform)
}

pub trait InverseFunctionServices {
    type Error;
    fn fresh_inverse_function(
        &mut self,
        name: &str,
        arguments: &[crate::state::terms::Sort],
        result: &crate::state::terms::Sort,
    ) -> Result<ApplicationTarget, Self::Error>;
    /// Source trigger inference and axiom rewriting for the inverse quantifiers.
    fn assemble_inverse_quantifier(
        &mut self,
        variables: &[Term],
        body: Term,
        candidate_terms: &[Term],
        explicit_triggers: Option<&[crate::state::terms::Trigger]>,
        name: &str,
        global: bool,
    ) -> Result<Term, Self::Error>;
}
#[derive(Debug)]
pub enum InverseGenerationError<E> {
    ArityOrSortMismatch,
    NonVariableBinder,
    Service(E),
    Transform(UnsupportedTriggerTransform),
}
/// Generate an inverse and an image function for every quantified variable, together
/// with both directional axioms and the image constraints at the codomain variables.
pub fn fresh_inverse_functions<S: InverseFunctionServices>(
    factory: &TermFactory,
    services: &mut S,
    qvars: &[Term],
    qvar_exps: Option<Vec<LocalVarDecl>>,
    condition: Term,
    invertibles: Vec<Term>,
    invertible_exps: Option<Vec<Exp>>,
    codomain_vars: &[Term],
    additional_args: Vec<Term>,
    state_qvars: &[Term],
    user_triggers: Option<&[crate::state::terms::Trigger]>,
    qid_prefix: &str,
    disable_isc_triggers: bool,
) -> Result<(InverseFunctions, Vec<Term>), InverseGenerationError<S::Error>> {
    use crate::state::terms::{Quantifier, Sort, Trigger};
    if invertibles.len() != codomain_vars.len()
        || invertibles
            .iter()
            .zip(codomain_vars)
            .any(|(a, b)| a.sort() != b.sort())
    {
        return Err(InverseGenerationError::ArityOrSortMismatch);
    }
    if qvars
        .iter()
        .any(|var| !matches!(var.kind(), TermKind::Var(_)))
    {
        return Err(InverseGenerationError::NonVariableBinder);
    }
    let argument_sorts: Vec<_> = additional_args
        .iter()
        .chain(&invertibles)
        .map(|v| v.sort().clone())
        .collect();
    let inv_args: Vec<_> = additional_args
        .iter()
        .chain(&invertibles)
        .cloned()
        .collect();
    let cod_args: Vec<_> = additional_args
        .iter()
        .chain(codomain_vars)
        .cloned()
        .collect();
    let mut inverses = Vec::new();
    let mut images = Vec::new();
    let mut inv_f = Vec::new();
    let mut inv_cod = Vec::new();
    let mut img_f = Vec::new();
    let mut img_cod = Vec::new();
    for var in qvars {
        let inverse = services
            .fresh_inverse_function("inv", &argument_sorts, var.sort())
            .map_err(InverseGenerationError::Service)?;
        let image = services
            .fresh_inverse_function("img", &argument_sorts, &Sort::Bool)
            .map_err(InverseGenerationError::Service)?;
        inv_f.push(apply_function(factory, &inverse, inv_args.clone()));
        inv_cod.push(apply_function(factory, &inverse, cod_args.clone()));
        img_f.push(apply_function(factory, &image, inv_args.clone()));
        img_cod.push(apply_function(factory, &image, cod_args.clone()));
        inverses.push((var.clone(), inverse));
        images.push((var.clone(), image));
    }
    let substitutions: HashMap<_, _> = qvars.iter().cloned().zip(inv_cod.iter().cloned()).collect();
    let condition_inverse = factory
        .replace(&condition, &substitutions)
        .map_err(InverseGenerationError::Transform)?;
    let mut invertibles_inverse = Vec::new();
    for term in &invertibles {
        invertibles_inverse.push(
            factory
                .replace(term, &substitutions)
                .map_err(InverseGenerationError::Transform)?,
        );
    }
    let inverse_equalities = factory.and(
        inv_f
            .iter()
            .zip(qvars)
            .map(|(i, v)| factory.equals(i.clone(), v.clone())),
    );
    let inverse_body = factory.implies(
        condition.clone(),
        factory.and([inverse_equalities, factory.and(img_f)]),
    );
    let inverse_name = format!("{qid_prefix}-invOfFct");
    let inverse_axiom = if let Some(triggers) = user_triggers {
        factory
            .quantification(
                Quantifier::Forall,
                qvars.to_vec(),
                inverse_body,
                if disable_isc_triggers {
                    vec![]
                } else {
                    triggers.to_vec()
                },
                inverse_name,
                false,
                None,
            )
            .map_err(InverseGenerationError::Transform)?
    } else {
        let candidates = if disable_isc_triggers {
            vec![]
        } else {
            vec![factory.and(invertibles.clone()), inverse_body.clone()]
        };
        services
            .assemble_inverse_quantifier(
                qvars,
                inverse_body,
                &candidates,
                None,
                &inverse_name,
                state_qvars.is_empty(),
            )
            .map_err(InverseGenerationError::Service)?
    };
    let round_trip = factory.and(
        invertibles_inverse
            .into_iter()
            .zip(codomain_vars)
            .map(|(value, var)| factory.equals(value, var.clone())),
    );
    let forward_body = factory.implies(
        factory.and([factory.and(img_cod.clone()), condition_inverse]),
        round_trip,
    );
    let triggers: Vec<_> = if disable_isc_triggers {
        vec![]
    } else {
        inv_cod
            .into_iter()
            .map(|term| Trigger { terms: vec![term] })
            .collect()
    };
    let forward_axiom = services
        .assemble_inverse_quantifier(
            codomain_vars,
            forward_body,
            &[],
            Some(&triggers),
            &format!("{qid_prefix}-fctOfInv"),
            state_qvars.is_empty(),
        )
        .map_err(InverseGenerationError::Service)?;
    let inverse = InverseFunctions::new(
        condition,
        invertibles,
        invertible_exps,
        additional_args,
        inverse_axiom,
        forward_axiom,
        qvar_exps,
        VariableFunctions::new(inverses),
        VariableFunctions::new(images),
    );
    Ok((inverse, img_cod))
}

pub trait SummaryEmission: PermissionMapFreshener {
    fn assume_summary_definitions(
        &mut self,
        definitions: &[Term],
        domain: bool,
        instantiated: bool,
        permission_map: bool,
    ) -> Result<(), Self::Error>;
}
#[derive(Debug)]
pub enum SummaryCacheError<E> {
    Snapshot(SnapshotSummaryError<E>),
    Permission(PermissionSummaryError<E>),
    Emit(E),
    InvalidChunk,
    InvalidInstantiation,
    Transform(UnsupportedTriggerTransform),
}
/// Re-emit snapshot definitions even on cache hits, and instantiate definitions when requested.
fn emit_snapshot_summary<S: SummaryEmission>(
    factory: &TermFactory,
    services: &mut S,
    resource: &crate::state::terms::ResourceKey,
    definition: &SnapshotMapDefinition,
    domain_needed: bool,
    instantiations: Option<&[Term]>,
) -> Result<(), SummaryCacheError<S::Error>> {
    let instantiate = |definitions: &[Term]| -> Result<Vec<Term>, SummaryCacheError<S::Error>> {
        let Some(args) = instantiations else {
            return Ok(definitions.to_vec());
        };
        let args = match resource {
            crate::state::terms::ResourceKey::Field(_) => args.to_vec(),
            _ => vec![factory.to_snap_tree(args.to_vec())],
        };
        definitions
            .iter()
            .map(|term| {
                let TermKind::Quantification { vars, .. } = term.kind() else {
                    return Err(SummaryCacheError::InvalidInstantiation);
                };
                if vars.len() != args.len() {
                    return Err(SummaryCacheError::InvalidInstantiation);
                }
                factory
                    .instantiate(term, &args)
                    .map_err(SummaryCacheError::Transform)
            })
            .collect()
    };
    if domain_needed {
        let definitions = instantiate(&definition.domain_definitions)?;
        services
            .assume_summary_definitions(&definitions, true, instantiations.is_some(), false)
            .map_err(SummaryCacheError::Emit)?;
    }
    let definitions = instantiate(&definition.value_definitions)?;
    services
        .assume_summary_definitions(&definitions, false, instantiations.is_some(), false)
        .map_err(SummaryCacheError::Emit)
}
/// Compute or reuse both maps, re-emitting their definitions and recording them in state.
pub fn heap_summarising_maps<P, D: Clone, J: Clone + PartialEq, S>(
    factory: &TermFactory,
    services: &mut S,
    mut state: crate::state::state::State<P, D, J>,
    resource: &crate::state::terms::ResourceKey,
    source_resource: SnapshotResource,
    codomain_vars: &[Term],
    relevant_chunks: &[crate::state::chunks::Chunk],
    domain_condition: Option<Term>,
    instantiations: Option<&[Term]>,
    used_as_trigger: bool,
    disable_isc_triggers: bool,
    disable_value_map_caching: bool,
    disable_caches: bool,
) -> Result<
    (
        crate::state::state::State<P, D, J>,
        SnapshotMapDefinition,
        PermMapDefinition,
    ),
    SummaryCacheError<<S as SnapshotMapFreshener<P, D, J>>::Error>,
>
where
    S: SnapshotSummaryFreshener<P, D, J>
        + SummaryEmission<Error = <S as SnapshotMapFreshener<P, D, J>>::Error>,
{
    use crate::interfaces::state::chunks::GeneralChunk;
    use crate::state::chunks::Chunk;
    use crate::state::snapshot_map_cache::{CacheKey, QuantifiedBasicChunk};
    let cache_chunks = relevant_chunks
        .iter()
        .map(|chunk| match chunk {
            Chunk::QuantifiedField(c) => Ok(QuantifiedBasicChunk::Field(c.clone())),
            Chunk::QuantifiedPredicate(c) => Ok(QuantifiedBasicChunk::Predicate(c.clone())),
            Chunk::QuantifiedMagicWand(c) => Ok(QuantifiedBasicChunk::Wand(c.clone())),
            _ => Err(SummaryCacheError::InvalidChunk),
        })
        .collect::<Result<Vec<_>, _>>()?;
    let key = CacheKey {
        resource: source_resource.clone(),
        relevant_chunks: cache_chunks,
    };
    let cached = if disable_caches || state.exhale_ext {
        None
    } else {
        state
            .sm_cache
            .get(&key, domain_condition.as_ref())
            .map(|(definition, _)| definition.clone())
    };
    let snapshot = if let Some(definition) = cached {
        definition
    } else {
        let (snapshot_map, value_definitions, domain_definitions) = summarise_snapshot_map(
            factory,
            services,
            &state,
            resource,
            codomain_vars,
            relevant_chunks,
            domain_condition.as_ref(),
            used_as_trigger,
            disable_isc_triggers,
        )
        .map_err(SummaryCacheError::Snapshot)?;
        let definition = SnapshotMapDefinition {
            resource: source_resource.clone(),
            snapshot_map,
            value_definitions,
            domain_definitions,
        };
        if !disable_value_map_caching {
            let total = relevant_chunks
                .iter()
                .fold(factory.no_perm(), |sum, chunk| {
                    let permission = match chunk {
                        Chunk::QuantifiedField(c) => c.permission(factory),
                        Chunk::QuantifiedPredicate(c) => c.permission(factory),
                        Chunk::QuantifiedMagicWand(c) => c.permission(factory),
                        _ => unreachable!(),
                    };
                    factory.perm_plus(sum, permission)
                });
            state.sm_cache =
                state
                    .sm_cache
                    .with_entry(key.clone(), definition.clone(), total, domain_condition);
        }
        definition
    };
    emit_snapshot_summary(
        factory,
        services,
        resource,
        &snapshot,
        state.sm_domain_needed,
        instantiations,
    )?;
    let cached_permission = if disable_caches {
        None
    } else {
        state.pm_cache.get(&key)
    };
    let permission = if let Some(definition) = cached_permission {
        definition.clone()
    } else {
        let (permission_map, value_definitions) = summarise_permission_map(
            factory,
            services,
            resource,
            codomain_vars,
            relevant_chunks,
            &snapshot.snapshot_map,
            used_as_trigger,
        )
        .map_err(SummaryCacheError::Permission)?;
        let definition = PermMapDefinition {
            resource: source_resource,
            permission_map,
            value_definitions,
        };
        state.pm_cache.insert(key, definition.clone());
        definition
    };
    services
        .assume_summary_definitions(&permission.value_definitions, false, false, true)
        .map_err(SummaryCacheError::Emit)?;
    state.function_recorder = state
        .function_recorder
        .record_fvf_and_domain(snapshot.clone())
        .record_perm_map(permission.clone());
    Ok((state, snapshot, permission))
}

#[derive(Debug)]
pub enum QuantifiedSplitError {
    UnexpectedNonQuantifiedChunk,
}
/// Source quantified heap partition prepends each chunk, rejecting an ordinary chunk of the same id.
pub fn split_quantified_heap(
    heap: &crate::state::heap::ListBackedHeap,
    id: &crate::state::chunks::ChunkIdentifier,
) -> Result<
    (
        Vec<crate::state::chunks::Chunk>,
        Vec<crate::state::chunks::Chunk>,
    ),
    QuantifiedSplitError,
> {
    use crate::interfaces::state::chunks::GeneralChunk;
    use crate::state::chunks::Chunk;
    use crate::state::heap::Heap;
    let mut relevant = Vec::new();
    let mut other = Vec::new();
    for chunk in heap.values() {
        let (chunk_id, quantified) = match chunk {
            Chunk::QuantifiedField(c) => (Some(c.identifier()), true),
            Chunk::QuantifiedPredicate(c) => (Some(c.identifier()), true),
            Chunk::QuantifiedMagicWand(c) => (Some(c.identifier()), true),
            Chunk::Basic(c) => (Some(c.identifier()), false),
            Chunk::MagicWand(c) => (Some(c.identifier()), false),
            Chunk::MaskHeap(_) => (None, false),
        };
        if chunk_id.as_ref() == Some(id) {
            if !quantified {
                return Err(QuantifiedSplitError::UnexpectedNonQuantifiedChunk);
            }
            relevant.insert(0, chunk.clone());
        } else {
            other.insert(0, chunk.clone());
        }
    }
    Ok((relevant, other))
}

pub trait QuantifiedChunkSolver {
    type Error;
    fn check_quantified_alias(
        &mut self,
        assertion: &Term,
        timeout_ms: i32,
    ) -> Result<bool, Self::Error>;
    fn quantified_check_timeout(&self) -> i32;
}
#[derive(Debug)]
pub enum QuantifiedMatchError<E> {
    NonQuantifiedChunk,
    Transform(UnsupportedTriggerTransform),
    Solver(E),
}
/// Greedy merge matching first compares original conditions, then tags, then checks
/// either direction of permission-footprint containment using the configured timeout.
pub fn find_quantified_chunk_greedy<S: QuantifiedChunkSolver>(
    factory: &TermFactory,
    solver: &mut S,
    chunks: &[crate::state::chunks::Chunk],
    target: &crate::state::chunks::Chunk,
) -> Result<Option<usize>, QuantifiedMatchError<S::Error>> {
    use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
    use crate::state::chunks::{Chunk, ChunkIdentifier};
    use crate::state::terms::Quantifier;
    fn info(
        factory: &TermFactory,
        chunk: &Chunk,
    ) -> Option<(ChunkIdentifier, Vec<Term>, Term, Term, Option<i32>)> {
        match chunk {
            Chunk::QuantifiedField(c) => Some((
                c.identifier(),
                c.quantified_vars(factory),
                c.original_condition().clone(),
                c.permission(factory),
                c.tag(),
            )),
            Chunk::QuantifiedPredicate(c) => Some((
                c.identifier(),
                c.quantified_vars(factory),
                c.original_condition().clone(),
                c.permission(factory),
                c.tag(),
            )),
            Chunk::QuantifiedMagicWand(c) => Some((
                c.identifier(),
                c.quantified_vars(factory),
                c.original_condition().clone(),
                c.permission(factory),
                c.tag(),
            )),
            _ => None,
        }
    }
    let (id, vars, original, permission, tag) =
        info(factory, target).ok_or(QuantifiedMatchError::NonQuantifiedChunk)?;
    let relevant: Vec<_> = chunks
        .iter()
        .enumerate()
        .filter_map(|(i, c)| {
            info(factory, c)
                .filter(|(candidate_id, ..)| *candidate_id == id)
                .map(|data| (i, data))
        })
        .collect();
    for (index, (_, candidate_vars, candidate_condition, _, _)) in &relevant {
        let subst: HashMap<_, _> = candidate_vars
            .iter()
            .cloned()
            .zip(vars.iter().cloned())
            .collect();
        if factory
            .replace(candidate_condition, &subst)
            .map_err(QuantifiedMatchError::Transform)?
            == original
        {
            return Ok(Some(*index));
        }
    }
    if tag.is_some()
        && let Some((index, _)) = relevant
            .iter()
            .find(|(_, (_, _, _, _, candidate_tag))| *candidate_tag == tag)
    {
        return Ok(Some(*index));
    }
    for (index, (_, candidate_vars, candidate_condition, candidate_permission, _)) in relevant {
        let subst: HashMap<_, _> = candidate_vars
            .into_iter()
            .zip(vars.iter().cloned())
            .collect();
        let condition = factory
            .replace(&candidate_condition, &subst)
            .map_err(QuantifiedMatchError::Transform)?;
        let candidate_permission = factory
            .replace(&candidate_permission, &subst)
            .map_err(QuantifiedMatchError::Transform)?;
        let superset = factory.implies(
            factory.is_positive_perm(candidate_permission),
            original.clone(),
        );
        let subset = factory.implies(factory.is_positive_perm(permission.clone()), condition);
        let make_quantifier = |body| {
            factory
                .quantification(
                    Quantifier::Forall,
                    vars.clone(),
                    body,
                    vec![],
                    TermFactory::forall_default_name(),
                    false,
                    None,
                )
                .map_err(QuantifiedMatchError::Transform)
        };
        let timeout = solver.quantified_check_timeout().wrapping_mul(10);
        if solver
            .check_quantified_alias(&make_quantifier(superset)?, timeout)
            .map_err(QuantifiedMatchError::Solver)?
            || solver
                .check_quantified_alias(&make_quantifier(subset)?, timeout)
                .map_err(QuantifiedMatchError::Solver)?
        {
            return Ok(Some(index));
        }
    }
    Ok(None)
}

pub trait SnapshotCombinationFreshener {
    type Error;
    fn fresh_combined_snapshot_map(
        &mut self,
        sort: &crate::state::terms::Sort,
        additional_variables: &[Term],
    ) -> Result<(Term, ApplicationTarget), Self::Error>;
}
#[derive(Debug)]
pub enum SnapshotCombinationError<E> {
    Fresh(E),
    Transform(UnsupportedTriggerTransform),
}
/// Combine two field/predicate snapshot maps while guarding each equality by the
/// corresponding positive permission. If neither permission is provably positive,
/// allocate a third map rather than unsoundly constraining either original map.
pub fn combine_snapshot_maps<D: Clone, F: SnapshotCombinationFreshener>(
    factory: &TermFactory,
    freshener: &mut F,
    recorder: crate::supporters::functions::function_recorder::FunctionRecorder<D>,
    resource: &crate::state::terms::ResourceKey,
    codomain_vars: &[Term],
    additional_vars: &[Term],
    first: Term,
    second: Term,
    first_permission: Term,
    second_permission: Term,
) -> Result<
    (
        crate::supporters::functions::function_recorder::FunctionRecorder<D>,
        Term,
        Term,
    ),
    SnapshotCombinationError<F::Error>,
> {
    use crate::state::terms::{Quantifier, Trigger};
    let positive1 = factory.is_positive_perm(first_permission);
    let positive2 = factory.is_positive_perm(second_permission);
    if matches!(positive1.kind(), TermKind::True) && matches!(positive2.kind(), TermKind::True) {
        let equality = factory.equals(first.clone(), second);
        return Ok((recorder, first, equality));
    }
    let lookup1 = factory.resource_lookup(resource, first.clone(), codomain_vars.to_vec());
    let lookup2 = factory.resource_lookup(resource, second.clone(), codomain_vars.to_vec());
    let mut recorder = recorder;
    let (snapshot, body, triggers) = if matches!(positive1.kind(), TermKind::True) {
        (
            first,
            factory.implies(positive2, factory.equals(lookup1.clone(), lookup2.clone())),
            vec![
                Trigger {
                    terms: vec![lookup1],
                },
                Trigger {
                    terms: vec![lookup2],
                },
            ],
        )
    } else if matches!(positive2.kind(), TermKind::True) {
        (
            second,
            factory.implies(positive1, factory.equals(lookup2.clone(), lookup1.clone())),
            vec![
                Trigger {
                    terms: vec![lookup2],
                },
                Trigger {
                    terms: vec![lookup1],
                },
            ],
        )
    } else {
        let (fresh, symbol) = freshener
            .fresh_combined_snapshot_map(first.sort(), additional_vars)
            .map_err(SnapshotCombinationError::Fresh)?;
        let lookup3 = factory.resource_lookup(resource, fresh.clone(), codomain_vars.to_vec());
        let body = factory.and([
            factory.implies(positive1, factory.equals(lookup3.clone(), lookup1.clone())),
            factory.implies(positive2, factory.equals(lookup3.clone(), lookup2.clone())),
        ]);
        let triggers = vec![
            Trigger {
                terms: vec![lookup1],
            },
            Trigger {
                terms: vec![lookup2],
            },
            Trigger {
                terms: vec![lookup3],
            },
        ];
        let constraint = factory
            .quantification(
                Quantifier::Forall,
                codomain_vars.to_vec(),
                body.clone(),
                triggers.clone(),
                TermFactory::forall_default_name(),
                false,
                None,
            )
            .map_err(SnapshotCombinationError::Transform)?;
        recorder = recorder
            .record_path_symbol(symbol)
            .record_constraint(constraint);
        (fresh, body, triggers)
    };
    let definition = factory
        .quantification(
            Quantifier::Forall,
            codomain_vars.to_vec(),
            body,
            triggers,
            TermFactory::forall_default_name(),
            false,
            None,
        )
        .map_err(SnapshotCombinationError::Transform)?;
    Ok((recorder, snapshot, definition))
}

pub trait CompleteQuantifiedChunkSolver: QuantifiedChunkSolver {
    fn assume_quantified_alias(&mut self, assertion: &Term) -> Result<(), Self::Error>;
}
/// Complete-mode matching supports field/predicate singleton chunks and inverse-based
/// chunks. Successful solver comparisons are assumed as learned equalities.
pub fn find_quantified_chunk_complete<S: CompleteQuantifiedChunkSolver>(
    factory: &TermFactory,
    solver: &mut S,
    chunks: &[crate::state::chunks::Chunk],
    target: &crate::state::chunks::Chunk,
) -> Result<Option<usize>, QuantifiedMatchError<S::Error>> {
    use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
    use crate::state::chunks::{Chunk, ChunkIdentifier};
    enum Shape {
        Inverses(Vec<InverseFunctions>),
        Singleton(Vec<Term>),
    }
    fn data(
        factory: &TermFactory,
        chunk: &Chunk,
        prefer_singleton: bool,
    ) -> Option<(ChunkIdentifier, Vec<Term>, Term, Shape)> {
        match chunk {
            Chunk::QuantifiedField(c) => {
                let shape = if prefer_singleton && c.singleton_rcvr_ref().is_some() {
                    Shape::Singleton(vec![c.singleton_rcvr_ref().clone()?])
                } else if !c.invs_ref().is_empty() {
                    Shape::Inverses(c.invs_ref().clone())
                } else {
                    Shape::Singleton(vec![c.singleton_rcvr_ref().clone()?])
                };
                Some((
                    c.identifier(),
                    c.quantified_vars(factory),
                    c.condition_ref().clone(),
                    shape,
                ))
            }
            Chunk::QuantifiedPredicate(c) => {
                let shape = if prefer_singleton && c.singleton_args_ref().is_some() {
                    Shape::Singleton(c.singleton_args_ref().clone()?)
                } else if !c.invs_ref().is_empty() {
                    Shape::Inverses(c.invs_ref().clone())
                } else {
                    Shape::Singleton(c.singleton_args_ref().clone()?)
                };
                Some((
                    c.identifier(),
                    c.quantified_vars(factory),
                    c.condition_ref().clone(),
                    shape,
                ))
            }
            _ => None,
        }
    }
    fn expanded<E>(
        factory: &TermFactory,
        inverses: &[InverseFunctions],
        vars: &[Term],
    ) -> Result<Vec<Term>, QuantifiedMatchError<E>> {
        let mut result = Vec::new();
        for inverse in inverses {
            let substitutions: HashMap<_, _> = inverse
                .qvars_to_inverses_of(factory, vars)
                .into_iter()
                .collect();
            for term in &inverse.invertibles {
                result.push(
                    factory
                        .replace(term, &substitutions)
                        .map_err(QuantifiedMatchError::Transform)?,
                );
            }
        }
        Ok(result)
    }
    let Some((id, vars, condition, shape)) = data(factory, target, false) else {
        return Ok(None);
    };
    let timeout = solver.quantified_check_timeout();
    for (index, candidate) in chunks.iter().enumerate() {
        let Some((other_id, other_vars, other_condition, other_shape)) =
            data(factory, candidate, matches!(shape, Shape::Singleton(_)))
        else {
            continue;
        };
        if id != other_id {
            continue;
        }
        match (&shape, other_shape) {
            (Shape::Singleton(args), Shape::Singleton(other_args)) => {
                let equality = factory.and(
                    args.iter()
                        .zip(&other_args)
                        .map(|(a, b)| factory.equals(a.clone(), b.clone())),
                );
                let first_subst: HashMap<_, _> =
                    vars.iter().cloned().zip(args.iter().cloned()).collect();
                let second_subst: HashMap<_, _> = other_vars
                    .iter()
                    .cloned()
                    .zip(other_args.iter().cloned())
                    .collect();
                let first_cond = factory
                    .replace(&condition, &first_subst)
                    .map_err(QuantifiedMatchError::Transform)?;
                let second_cond = factory
                    .replace(&other_condition, &second_subst)
                    .map_err(QuantifiedMatchError::Transform)?;
                let test = factory.and([first_cond, second_cond, equality.clone()]);
                if solver
                    .check_quantified_alias(&test, timeout)
                    .map_err(QuantifiedMatchError::Solver)?
                {
                    solver
                        .assume_quantified_alias(&equality)
                        .map_err(QuantifiedMatchError::Solver)?;
                    return Ok(Some(index));
                }
            }
            (Shape::Inverses(inverses), Shape::Inverses(other_inverses)) => {
                let receiver_terms = expanded(factory, inverses, &vars)?;
                let other_terms = expanded(factory, &other_inverses, &other_vars)?;
                let mut matches = true;
                for (receiver, other) in receiver_terms.iter().zip(other_terms) {
                    if vars.len() != other_vars.len()
                        || other_vars
                            .iter()
                            .zip(&vars)
                            .any(|(a, b)| a.sort() != b.sort())
                    {
                        matches = false;
                        break;
                    }
                    let subst: HashMap<_, _> = other_vars
                        .iter()
                        .cloned()
                        .zip(vars.iter().cloned())
                        .collect();
                    let other = factory
                        .replace(&other, &subst)
                        .map_err(QuantifiedMatchError::Transform)?;
                    let other_condition = factory
                        .replace(&other_condition, &subst)
                        .map_err(QuantifiedMatchError::Transform)?;
                    let body = factory.and([
                        factory.equals(receiver.clone(), other),
                        factory.equals(condition.clone(), other_condition),
                    ]);
                    let equality = factory
                        .simplifying_forall(vars.clone(), body, vec![])
                        .map_err(QuantifiedMatchError::Transform)?;
                    if !solver
                        .check_quantified_alias(&equality, timeout)
                        .map_err(QuantifiedMatchError::Solver)?
                    {
                        matches = false;
                        break;
                    }
                    solver
                        .assume_quantified_alias(&equality)
                        .map_err(QuantifiedMatchError::Solver)?;
                }
                if matches {
                    return Ok(Some(index));
                }
            }
            _ => {}
        }
    }
    Ok(None)
}

pub trait SingleLocationProduction<P, D, J>: SnapshotMapFreshener<P, D, J> {
    fn assume_singleton_value(&mut self, definition: &Term) -> Result<(), Self::Error>;
    fn next_quantified_tag(&mut self) -> i32;
    fn merge_quantified_chunk(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        chunk: &crate::state::chunks::Chunk,
    ) -> Result<
        (
            crate::supporters::functions::function_recorder::FunctionRecorder<D>,
            crate::state::heap::ListBackedHeap,
        ),
        Self::Error,
    >;
    fn assume_quantified_chunk_properties(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        heap: &crate::state::heap::ListBackedHeap,
        chunk: &crate::state::chunks::Chunk,
    ) -> Result<(), Self::Error>;
    /// Re-summarise the merged heap and assume its resource trigger when required.
    fn trigger_single_location(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        heap: &crate::state::heap::ListBackedHeap,
        resource: &crate::state::terms::ResourceKey,
        formal_vars: &[Term],
        args: &[Term],
    ) -> Result<crate::state::snapshot_map_cache::SnapshotMapCache, Self::Error>;
    fn is_resource_trigger(
        &self,
        state: &crate::state::state::State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
    ) -> bool;
}
#[derive(Debug)]
pub enum SingleLocationProductionError<E> {
    Map(SingletonMapError<E>),
    Chunk(SingletonChunkError),
    Service(E),
}
/// Produce a single quantified location, preserving the source's map definition,
/// merge/property/trigger ordering, tag selection and function-recorder updates.
pub fn produce_single_quantified_location<
    P,
    D: Clone,
    J: Clone + PartialEq,
    S: SingleLocationProduction<P, D, J>,
>(
    factory: &TermFactory,
    services: &mut S,
    mut state: crate::state::state::State<P, D, J>,
    resource: &crate::state::terms::ResourceKey,
    source_resource: SnapshotResource,
    formal_vars: Vec<Term>,
    formal_var_exps: Option<Vec<LocalVarDecl>>,
    args: Vec<Term>,
    arg_exps: Option<Vec<Exp>>,
    snapshot: Term,
    permission: Term,
    permission_exp: Option<Exp>,
    merge_and_trigger: bool,
    debugging: bool,
) -> Result<crate::state::state::State<P, D, J>, SingleLocationProductionError<S::Error>> {
    use std::sync::Arc;
    let (map, value_definition) =
        singleton_snapshot_map(factory, services, &state, resource, &args, snapshot)
            .map_err(SingleLocationProductionError::Map)?;
    let definition = SnapshotMapDefinition {
        resource: source_resource,
        snapshot_map: map.clone(),
        value_definitions: vec![value_definition.clone()],
        domain_definitions: vec![],
    };
    services
        .assume_singleton_value(&value_definition)
        .map_err(SingleLocationProductionError::Service)?;
    let tag = state
        .qp_tag
        .unwrap_or_else(|| services.next_quantified_tag());
    let chunk = singleton_quantified_chunk(
        factory,
        resource,
        formal_vars.clone(),
        formal_var_exps,
        args.clone(),
        arg_exps,
        permission,
        permission_exp,
        map,
        Some(tag),
        debugging,
    )
    .map_err(SingleLocationProductionError::Chunk)?;
    if merge_and_trigger {
        let (recorder, heap) = services
            .merge_quantified_chunk(&state, &chunk)
            .map_err(SingleLocationProductionError::Service)?;
        services
            .assume_quantified_chunk_properties(&state, &heap, &chunk)
            .map_err(SingleLocationProductionError::Service)?;
        if services.is_resource_trigger(&state, resource) {
            state.sm_cache = services
                .trigger_single_location(&state, &heap, resource, &formal_vars, &args)
                .map_err(SingleLocationProductionError::Service)?;
        }
        state.h = Arc::new(heap);
        state.function_recorder = recorder.record_fvf_and_domain(definition);
    } else {
        state.h = Arc::new(state.h.with_chunk(chunk));
        state.function_recorder = state.function_recorder.record_fvf_and_domain(definition);
    }
    Ok(state)
}

pub trait QuantifiedReadPermissionSolver {
    type Error;
    fn check_read_permission(&mut self, goal: &Term, timeout_ms: i32) -> Result<bool, Self::Error>;
    fn quantified_assert_timeout(&self) -> i32;
}
#[derive(Debug)]
pub enum QuantifiedReadPermissionError<E> {
    NonQuantifiedChunk,
    MissingDebugPermission,
    Transform(UnsupportedTriggerTransform),
    Solver(E),
}
/// The read-only path checks that a positive request has some positive available
/// permission, without consuming chunks. The incomplete amount follows the source order.
pub fn assert_quantified_read_permission<S: QuantifiedReadPermissionSolver>(
    factory: &TermFactory,
    solver: &mut S,
    candidates: &[crate::state::chunks::Chunk],
    codomain_vars: &[Term],
    condition: Term,
    permission: Term,
    permission_exp: Option<Exp>,
    debugging: bool,
) -> Result<
    crate::rules::consumption_result::ConsumptionResult,
    QuantifiedReadPermissionError<S::Error>,
> {
    use crate::interfaces::state::chunks::GeneralChunk;
    use crate::rules::consumption_result::ConsumptionResult;
    use crate::state::chunks::Chunk;
    use crate::state::terms::Quantifier;
    use ferrum_silver::ast::expression::ExpKind;
    let mut available = factory.no_perm();
    let mut available_exp = debugging.then(|| Exp::new(ExpKind::NoPerm, Default::default()));
    for chunk in candidates {
        let p = match chunk {
            Chunk::QuantifiedField(c) => c.permission(factory),
            Chunk::QuantifiedPredicate(c) => c.permission(factory),
            Chunk::QuantifiedMagicWand(c) => c.permission(factory),
            _ => return Err(QuantifiedReadPermissionError::NonQuantifiedChunk),
        };
        available = factory.perm_plus(available, p);
        if let Some(exp) = available_exp.take() {
            let requested = permission_exp
                .clone()
                .ok_or(QuantifiedReadPermissionError::MissingDebugPermission)?;
            available_exp = Some(Exp::new(
                ExpKind::PermAdd(exp, requested),
                Default::default(),
            ));
        }
    }
    let body = factory.implies(
        condition,
        factory.implies(
            factory.greater(permission.clone(), factory.no_perm()),
            factory.greater(available.clone(), factory.no_perm()),
        ),
    );
    let goal = factory
        .quantification(
            Quantifier::Forall,
            codomain_vars.to_vec(),
            body,
            vec![],
            TermFactory::forall_default_name(),
            false,
            None,
        )
        .map_err(QuantifiedReadPermissionError::Transform)?;
    if solver
        .check_read_permission(&goal, solver.quantified_assert_timeout())
        .map_err(QuantifiedReadPermissionError::Solver)?
    {
        Ok(ConsumptionResult::Complete)
    } else {
        let debug = match available_exp {
            Some(exp) => Some(Exp::new(
                ExpKind::PermSub(
                    exp,
                    permission_exp.ok_or(QuantifiedReadPermissionError::MissingDebugPermission)?,
                ),
                Default::default(),
            )),
            None => None,
        };
        Ok(ConsumptionResult::Incomplete {
            perms_needed: factory.perm_minus(available, permission),
            perms_needed_exp: debug,
        })
    }
}

pub trait QuantifiedRemovalServices<P, D, J>: QuantifiedReadPermissionSolver {
    fn open_removal_scope(
        &mut self,
        _state: &crate::state::state::State<P, D, J>,
    ) -> Result<Option<i32>, Self::Error> {
        Ok(None)
    }
    fn close_removal_scope(&mut self, _id: Option<i32>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn check_removal_goal(&mut self, goal: &Term, timeout_ms: i32) -> Result<bool, Self::Error>;
    fn removal_check_timeout(&self) -> i32;
    fn removal_split_timeout(&self) -> i32;
    fn saturate_before_removal(&mut self) -> Result<(), Self::Error>;
    fn removal_macros_enabled(&self) -> bool;
    fn fresh_permission_macro(
        &mut self,
        arguments: &[Term],
        body: &Term,
    ) -> Result<(Term, crate::state::terms::Declaration), Self::Error>;
    fn auto_trigger_permission_constraint(&mut self, quantifier: Term)
    -> Result<Term, Self::Error>;
    fn assume_permission_constraint(
        &mut self,
        term: &Term,
        debug: Option<&Exp>,
    ) -> Result<(), Self::Error>;
    fn next_permission_constraint_id(&mut self) -> i32;
    /// Reconstruct the upstream quantified debug constraint using the supplied source expressions.
    fn removal_constraint_debug(
        &mut self,
        variables: Option<&[LocalVarDecl]>,
        condition: Option<&Exp>,
        requested: Option<&Exp>,
        provided: Option<&Exp>,
    ) -> Result<Option<Exp>, Self::Error>;
}
#[derive(Debug)]
pub enum QuantifiedRemovalError<E> {
    InvalidChunk,
    MissingDebugExpression,
    Transform(UnsupportedTriggerTransform),
    Read(QuantifiedReadPermissionError<E>),
    Service(E),
}
/// Remove permissions from ordered candidates. The caller applies the source ordering heuristic
/// before invoking this function when enabled. Solver failure and incomplete consumption are
/// distinct; the last condition is always checked with the assertion timeout when necessary.
pub fn remove_quantified_permissions<
    P,
    D: Clone,
    J: Clone + PartialEq,
    S: QuantifiedRemovalServices<P, D, J>,
>(
    factory: &TermFactory,
    services: &mut S,
    mut state: crate::state::state::State<P, D, J>,
    candidates: &[crate::state::chunks::Chunk],
    original_chunks: &[crate::state::chunks::Chunk],
    resource_id: &crate::state::chunks::ChunkIdentifier,
    codomain_vars: &[Term],
    codomain_var_exps: Option<&[LocalVarDecl]>,
    condition: Term,
    condition_exp: Option<Exp>,
    known_values: Option<&[Term]>,
    permissions: Term,
    permissions_exp: Option<Exp>,
    disable_isc_triggers: bool,
    debugging: bool,
) -> Result<
    (
        crate::rules::consumption_result::ConsumptionResult,
        crate::state::state::State<P, D, J>,
        Vec<crate::state::chunks::Chunk>,
        Vec<crate::state::chunks::Chunk>,
    ),
    QuantifiedRemovalError<S::Error>,
> {
    use crate::interfaces::state::chunks::GeneralChunk;
    use crate::rules::consumption_result::ConsumptionResult;
    use crate::state::chunks::Chunk;
    use crate::state::terms::{Quantifier, consume_exact_read};
    use ferrum_silver::ast::expression::ExpKind;
    fn data(
        factory: &TermFactory,
        chunk: &Chunk,
    ) -> Option<(crate::state::chunks::ChunkIdentifier, Term, Option<Exp>)> {
        match chunk {
            Chunk::QuantifiedField(c) => {
                Some((c.identifier(), c.permission(factory), c.permission_exp()))
            }
            Chunk::QuantifiedPredicate(c) => {
                Some((c.identifier(), c.permission(factory), c.permission_exp()))
            }
            Chunk::QuantifiedMagicWand(c) => {
                Some((c.identifier(), c.permission(factory), c.permission_exp()))
            }
            _ => None,
        }
    }
    fn subtract(factory: &TermFactory, chunk: &Chunk, taken: Term, debug: Option<Exp>) -> Chunk {
        match chunk {
            Chunk::QuantifiedField(c) => {
                Chunk::QuantifiedField(c.perm_minus(factory, taken, debug))
            }
            Chunk::QuantifiedPredicate(c) => {
                Chunk::QuantifiedPredicate(c.perm_minus(factory, taken, debug))
            }
            Chunk::QuantifiedMagicWand(c) => {
                Chunk::QuantifiedMagicWand(c.perm_minus(factory, taken, debug))
            }
            _ => unreachable!(),
        }
    }
    let scope = services
        .open_removal_scope(&state)
        .map_err(QuantifiedRemovalError::Service)?;
    for chunk in original_chunks {
        if data(factory, chunk).is_none_or(|(id, _, _)| &id != resource_id) {
            return Err(QuantifiedRemovalError::InvalidChunk);
        }
    }
    let constrain = !consume_exact_read(&permissions, &state.constrainable_arps);
    if state.assert_read_access_only {
        let result = assert_quantified_read_permission(
            factory,
            services,
            candidates,
            codomain_vars,
            condition,
            permissions,
            permissions_exp,
            debugging,
        )
        .map_err(QuantifiedRemovalError::Read)?;
        return Ok((result, state, original_chunks.to_vec(), Vec::new()));
    }
    let quantify = |body: Term, name: String| {
        factory
            .quantification(
                Quantifier::Forall,
                codomain_vars.to_vec(),
                body,
                vec![],
                name,
                false,
                None,
            )
            .map_err(QuantifiedRemovalError::Transform)
    };
    let mut needed = permissions.clone();
    let mut needed_exp = permissions_exp.clone();
    let mut result = ConsumptionResult::Incomplete {
        perms_needed: needed.clone(),
        perms_needed_exp: debugging.then(|| Exp::new(ExpKind::TrueLit, Default::default())),
    };
    let mut remaining = Vec::new();
    let mut untouched = Vec::new();
    let additional: Vec<_> = state
        .packaging_wand_snapshots
        .iter()
        .map(|(t, _)| t.clone())
        .chain(
            state
                .function_recorder
                .arguments()
                .unwrap_or_default()
                .into_iter()
                .map(|(t, _)| t),
        )
        .chain(state.quantified_variables.iter().map(|(t, _)| t.clone()))
        .collect();
    services
        .saturate_before_removal()
        .map_err(QuantifiedRemovalError::Service)?;
    for chunk in candidates {
        if result.is_complete() {
            untouched.push(chunk.clone());
            continue;
        }
        let (_, provided, provided_exp) =
            data(factory, chunk).ok_or(QuantifiedRemovalError::InvalidChunk)?;
        let relevant = if state.more_complete_exhale_qp {
            true
        } else {
            let active = factory.and([condition.clone(), factory.is_positive_perm(needed.clone())]);
            let sub = quantify(
                factory.implies(factory.is_positive_perm(provided.clone()), active.clone()),
                TermFactory::forall_default_name(),
            )?;
            let sup = quantify(
                factory.implies(active, factory.is_positive_perm(provided.clone())),
                TermFactory::forall_default_name(),
            )?;
            let timeout = services.removal_check_timeout().wrapping_mul(10);
            services
                .check_removal_goal(&sub, timeout)
                .map_err(QuantifiedRemovalError::Service)?
                || services
                    .check_removal_goal(&sup, timeout)
                    .map_err(QuantifiedRemovalError::Service)?
        };
        if !relevant {
            untouched.push(chunk.clone());
            continue;
        }
        let body = factory.ite(
            condition.clone(),
            factory.perm_min(provided.clone(), needed.clone()),
            factory.no_perm(),
        );
        let taken = if matches!(
            state.function_recorder,
            crate::supporters::functions::function_recorder::FunctionRecorder::Noop
        ) && services.removal_macros_enabled()
        {
            let args: Vec<_> = codomain_vars.iter().chain(&additional).cloned().collect();
            let (taken, declaration) = services
                .fresh_permission_macro(&args, &body)
                .map_err(QuantifiedRemovalError::Service)?;
            state.function_recorder = state.function_recorder.record_fresh_macro(declaration);
            taken
        } else {
            body
        };
        let taken_exp = if let Some(cond) = &condition_exp {
            let provided = provided_exp
                .clone()
                .ok_or(QuantifiedRemovalError::MissingDebugExpression)?;
            let requested = needed_exp
                .clone()
                .ok_or(QuantifiedRemovalError::MissingDebugExpression)?;
            let meta = ferrum_silver::ast::ast::Metadata {
                position: provided.metadata().position.clone(),
                info: provided.metadata().info.clone(),
                error_trafo: Default::default(),
            };
            let min = Exp::new(ExpKind::DebugPermMin(provided, requested), meta);
            Some(Exp::new(
                ExpKind::CondExp(
                    cond.clone(),
                    min,
                    Exp::new(ExpKind::NoPerm, Default::default()),
                ),
                Default::default(),
            ))
        } else {
            None
        };
        needed = factory.perm_minus(needed, taken.clone());
        needed_exp = match needed_exp {
            Some(exp) => Some(Exp::new(
                ExpKind::PermSub(
                    exp,
                    taken_exp
                        .clone()
                        .ok_or(QuantifiedRemovalError::MissingDebugExpression)?,
                ),
                Default::default(),
            )),
            None => None,
        };
        if constrain {
            let conditional =
                factory.ite(condition.clone(), permissions.clone(), factory.no_perm());
            let constraint_body = factory.implies(
                factory.not(factory.equals(provided.clone(), factory.no_perm())),
                factory.perm_less(conditional, provided.clone()),
            );
            let id = services.next_permission_constraint_id();
            let mut constraint = quantify(constraint_body, format!("qp.srp{id}"))?;
            if !disable_isc_triggers {
                constraint = services
                    .auto_trigger_permission_constraint(constraint)
                    .map_err(QuantifiedRemovalError::Service)?;
            }
            if let Some(values) = known_values {
                constraint = factory
                    .instantiate(&constraint, values)
                    .map_err(QuantifiedRemovalError::Transform)?;
            }
            let debug = services
                .removal_constraint_debug(
                    codomain_var_exps,
                    condition_exp.as_ref(),
                    permissions_exp.as_ref(),
                    provided_exp.as_ref(),
                )
                .map_err(QuantifiedRemovalError::Service)?;
            services
                .assume_permission_constraint(&constraint, debug.as_ref())
                .map_err(QuantifiedRemovalError::Service)?;
            remaining.push(subtract(factory, chunk, taken.clone(), taken_exp.clone()));
        } else {
            let depleted = quantify(
                factory.equals(
                    factory.perm_minus(provided, taken.clone()),
                    factory.no_perm(),
                ),
                TermFactory::forall_default_name(),
            )?;
            if !services
                .check_removal_goal(&depleted, services.removal_split_timeout())
                .map_err(QuantifiedRemovalError::Service)?
            {
                let unused = quantify(
                    factory.equals(taken.clone(), factory.no_perm()),
                    TermFactory::forall_default_name(),
                )?;
                if services
                    .check_removal_goal(&unused, services.removal_check_timeout())
                    .map_err(QuantifiedRemovalError::Service)?
                {
                    untouched.push(chunk.clone());
                } else {
                    remaining.push(subtract(factory, chunk, taken, taken_exp));
                }
            }
        }
        let enough = quantify(
            factory.implies(
                condition.clone(),
                factory.equals(needed.clone(), factory.no_perm()),
            ),
            TermFactory::forall_default_name(),
        )?;
        result = if services
            .check_removal_goal(&enough, services.removal_split_timeout())
            .map_err(QuantifiedRemovalError::Service)?
        {
            ConsumptionResult::Complete
        } else {
            ConsumptionResult::Incomplete {
                perms_needed: needed.clone(),
                perms_needed_exp: needed_exp.clone(),
            }
        };
    }
    let enough = quantify(
        factory.implies(condition, factory.equals(needed, factory.no_perm())),
        TermFactory::forall_default_name(),
    )?;
    if !result.is_complete()
        && services
            .check_removal_goal(&enough, services.quantified_assert_timeout())
            .map_err(QuantifiedRemovalError::Service)?
    {
        result = ConsumptionResult::Complete;
    }
    services
        .close_removal_scope(scope)
        .map_err(QuantifiedRemovalError::Service)?;
    Ok((result, state, remaining, untouched))
}

/// Order singleton chunks by literal receiver first, then the first prover-matching
/// receiver, and finally non-singletons by hints followed by remaining singletons.
pub fn single_receiver_chunk_order<S: QuantifiedChunkSolver>(
    factory: &TermFactory,
    solver: &mut S,
    chunks: &[crate::state::chunks::Chunk],
    receiver: &[Term],
    hints: &[Term],
) -> Result<Vec<crate::state::chunks::Chunk>, QuantifiedMatchError<S::Error>> {
    use crate::state::chunks::Chunk;
    fn info(chunk: &Chunk) -> Option<(Option<Vec<Term>>, &[Term])> {
        match chunk {
            Chunk::QuantifiedField(c) => Some((
                c.singleton_rcvr_ref().clone().map(|v| vec![v]),
                c.hints_ref(),
            )),
            Chunk::QuantifiedPredicate(c) => Some((c.singleton_args_ref().clone(), c.hints_ref())),
            Chunk::QuantifiedMagicWand(c) => Some((c.singleton_args_ref().clone(), c.hints_ref())),
            _ => None,
        }
    }
    let mut literal = Vec::new();
    let mut other = Vec::new();
    for chunk in chunks {
        let (args, _) = info(chunk).ok_or(QuantifiedMatchError::NonQuantifiedChunk)?;
        if args.as_deref() == Some(receiver) {
            literal.push(chunk.clone());
        } else {
            other.push(chunk.clone());
        }
    }
    if !literal.is_empty() {
        literal.extend(other);
        return Ok(literal);
    }
    for (index, chunk) in chunks.iter().enumerate() {
        let (args, _) = info(chunk).expect("validated chunk");
        let Some(args) = args else {
            continue;
        };
        if args.len() != receiver.len() {
            continue;
        }
        let mut matches = true;
        for (arg, actual) in args.iter().zip(receiver) {
            let equality = factory.equals(arg.clone(), actual.clone());
            if !solver
                .check_quantified_alias(&equality, solver.quantified_check_timeout())
                .map_err(QuantifiedMatchError::Solver)?
            {
                matches = false;
                break;
            }
        }
        if matches {
            let mut result = vec![chunk.clone()];
            result.extend(
                chunks
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| *i != index)
                    .map(|(_, c)| c.clone()),
            );
            return Ok(result);
        }
    }
    let mut hinted = Vec::new();
    let mut unhinted = Vec::new();
    let mut singletons = Vec::new();
    for chunk in chunks {
        let (args, chunk_hints) = info(chunk).expect("validated chunk");
        if args.is_some() {
            singletons.push(chunk.clone());
        } else if chunk_hints == hints {
            hinted.push(chunk.clone());
        } else {
            unhinted.push(chunk.clone());
        }
    }
    hinted.extend(unhinted);
    hinted.extend(singletons);
    Ok(hinted)
}

/// General quantified-application ordering compares receiver expressions under a
/// binder renaming, falling back to stable source hint partitioning.
pub fn quantified_application_chunk_order<S: QuantifiedChunkSolver>(
    factory: &TermFactory,
    solver: &mut S,
    chunks: &[crate::state::chunks::Chunk],
    receiver_terms: &[Term],
    quant_vars: &[Term],
    hints: &[Term],
) -> Result<Vec<crate::state::chunks::Chunk>, QuantifiedMatchError<S::Error>> {
    use crate::state::chunks::Chunk;
    fn info(chunk: &Chunk) -> Option<(&[InverseFunctions], &[Term])> {
        match chunk {
            Chunk::QuantifiedField(c) => Some((c.invs_ref(), c.hints_ref())),
            Chunk::QuantifiedPredicate(c) => Some((c.invs_ref(), c.hints_ref())),
            Chunk::QuantifiedMagicWand(c) => Some((c.invs_ref(), c.hints_ref())),
            _ => None,
        }
    }
    let mut matching = Vec::new();
    let mut others = Vec::new();
    for chunk in chunks {
        let (inverses, _) = info(chunk).ok_or(QuantifiedMatchError::NonQuantifiedChunk)?;
        let mut matched = !inverses.is_empty();
        if matched {
            let terms: Vec<_> = inverses.iter().flat_map(|i| i.invertibles.iter()).collect();
            let vars: Vec<_> = inverses
                .iter()
                .flat_map(|i| i.qvars_to_inverses.iter().map(|(v, _)| v))
                .collect();
            for (receiver, term) in receiver_terms.iter().zip(terms) {
                if vars.len() != quant_vars.len()
                    || vars
                        .iter()
                        .zip(quant_vars)
                        .any(|(a, b)| a.sort() != b.sort())
                {
                    matched = false;
                    break;
                }
                let substitutions: HashMap<_, _> = vars
                    .iter()
                    .map(|v| (*v).clone())
                    .zip(quant_vars.iter().cloned())
                    .collect();
                let term = factory
                    .replace(term, &substitutions)
                    .map_err(QuantifiedMatchError::Transform)?;
                let goal = factory
                    .simplifying_forall(
                        quant_vars.to_vec(),
                        factory.equals(receiver.clone(), term),
                        vec![],
                    )
                    .map_err(QuantifiedMatchError::Transform)?;
                if !solver
                    .check_quantified_alias(&goal, solver.quantified_check_timeout())
                    .map_err(QuantifiedMatchError::Solver)?
                {
                    matched = false;
                    break;
                }
            }
        }
        if matched {
            matching.push(chunk.clone());
        } else {
            others.push(chunk.clone());
        }
    }
    let mut preferred = Vec::new();
    let mut rest = Vec::new();
    for chunk in others {
        let (_, chunk_hints) = info(&chunk).expect("validated chunk");
        if chunk_hints == hints {
            preferred.push(chunk);
        } else {
            rest.push(chunk);
        }
    }
    matching.extend(preferred);
    matching.extend(rest);
    Ok(matching)
}

pub trait SingleLocationConsumption<P, D, J, V>:
    QuantifiedRemovalServices<P, D, J>
    + QuantifiedChunkSolver<Error = <Self as QuantifiedReadPermissionSolver>::Error>
{
    type VerificationError;
    fn retry_single_quantified(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        action: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                crate::state::state::State<P, D, J>,
                std::sync::Arc<crate::state::heap::ListBackedHeap>,
                Option<Term>,
            ) -> Result<
                crate::interfaces::verification::VerificationResult<V>,
                SingleConsumptionError<<Self as QuantifiedReadPermissionSolver>::Error>,
            >,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            SingleConsumptionError<<Self as QuantifiedReadPermissionSolver>::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
            std::sync::Arc<crate::state::heap::ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            SingleConsumptionError<<Self as QuantifiedReadPermissionSolver>::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        SingleConsumptionError<<Self as QuantifiedReadPermissionSolver>::Error>,
    >;
    fn single_consumption_failure(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        error: &Self::VerificationError,
        wand: bool,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        <Self as QuantifiedReadPermissionSolver>::Error,
    >;
    fn consume_single_in_package(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
        identifier: &crate::state::chunks::ChunkIdentifier,
        codomain_vars: &[Term],
        codomain_var_exps: Option<&[LocalVarDecl]>,
        args: &[Term],
        arg_exps: Option<&[Exp]>,
        permission: &Term,
        permission_exp: Option<&Exp>,
        return_snapshot: bool,
        error: &Self::VerificationError,
        continuation: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
            std::sync::Arc<crate::state::heap::ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            SingleConsumptionError<<Self as QuantifiedReadPermissionSolver>::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        SingleConsumptionError<<Self as QuantifiedReadPermissionSolver>::Error>,
    >;
    fn summarise_consumed_snapshot(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
        formal_vars: &[Term],
        consumed: &[crate::state::chunks::Chunk],
        args: &[Term],
    ) -> Result<
        (
            SnapshotMapDefinition,
            crate::state::snapshot_map_cache::SnapshotMapCache,
        ),
        <Self as QuantifiedReadPermissionSolver>::Error,
    >;
    fn next_consumption_tag(&mut self) -> i32;
    fn use_complete_quantified_exhale(&self) -> bool;
    fn disable_quantified_chunk_ordering(&self) -> bool;
    fn disable_quantified_triggers(&self) -> bool;
    fn debug_quantified_consumption(&self) -> bool;
}
#[derive(Debug)]
pub enum SingleConsumptionError<E> {
    Split(QuantifiedSplitError),
    Hints(crate::state::terms::UnsupportedSubterms),
    Order(QuantifiedMatchError<E>),
    Removal(QuantifiedRemovalError<E>),
    MissingDebugArguments,
    Service(E),
}
/// Single quantified consumption, with the original main heap restored within a
/// retry action and the partially consumed heap threaded separately to its continuation.
pub fn consume_single_quantified_location<
    P,
    D: Clone,
    J: Clone + PartialEq,
    V,
    C: SingleLocationConsumption<P, D, J, V>,
>(
    factory: &TermFactory,
    context: &mut C,
    state: crate::state::state::State<P, D, J>,
    heap: std::sync::Arc<crate::state::heap::ListBackedHeap>,
    resource: &crate::state::terms::ResourceKey,
    identifier: &crate::state::chunks::ChunkIdentifier,
    codomain_vars: &[Term],
    codomain_var_exps: Option<&[LocalVarDecl]>,
    args: &[Term],
    arg_exps: Option<&[Exp]>,
    permission: &Term,
    permission_exp: Option<&Exp>,
    return_snapshot: bool,
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        crate::state::state::State<P, D, J>,
        std::sync::Arc<crate::state::heap::ListBackedHeap>,
        Option<Term>,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        SingleConsumptionError<<C as QuantifiedReadPermissionSolver>::Error>,
    >,
) -> Result<
    crate::interfaces::verification::VerificationResult<V>,
    SingleConsumptionError<<C as QuantifiedReadPermissionSolver>::Error>,
> {
    use crate::interfaces::state::chunks::GeneralChunk;
    use crate::rules::consumption_result::ConsumptionResult;
    use crate::state::chunks::Chunk;
    use crate::state::terms::{ResourceKey, Sort};
    use ferrum_silver::ast::expression::ExpKind;
    use std::sync::Arc;
    let original_heap = state.h.clone();
    let original_state = state.clone();
    let action = |context: &mut C,
                  mut state: crate::state::state::State<P, D, J>,
                  heap: Arc<crate::state::heap::ListBackedHeap>,
                  done: &mut dyn FnMut(
        &mut C,
        crate::state::state::State<P, D, J>,
        Arc<crate::state::heap::ListBackedHeap>,
        Option<Term>,
    ) -> Result<_, _>| {
        if state.exhale_ext {
            return context.consume_single_in_package(
                state,
                resource,
                identifier,
                codomain_vars,
                codomain_var_exps,
                args,
                arg_exps,
                permission,
                permission_exp,
                return_snapshot,
                error,
                done,
            );
        }
        let (relevant, others) =
            split_quantified_heap(&heap, identifier).map_err(SingleConsumptionError::Split)?;
        let candidates = if context.disable_quantified_chunk_ordering() {
            relevant.clone()
        } else {
            let hints =
                extract_hints(factory, None, args).map_err(SingleConsumptionError::Hints)?;
            single_receiver_chunk_order(factory, context, &relevant, args, &hints)
                .map_err(SingleConsumptionError::Order)?
        };
        let condition = factory.and(
            codomain_vars
                .iter()
                .zip(args)
                .map(|(a, b)| factory.equals(a.clone(), b.clone())),
        );
        let condition_exp = if let Some(vars) = codomain_var_exps {
            let args = arg_exps.ok_or(SingleConsumptionError::MissingDebugArguments)?;
            let mut terms = vars.iter().zip(args).map(|(var, arg)| {
                Exp::new(
                    ExpKind::EqCmp(
                        Exp::new(ExpKind::LocalVar(var.local_var()), var.meta.clone()),
                        arg.clone(),
                    ),
                    Default::default(),
                )
            });
            Some(match terms.next() {
                Some(first) => terms.fold(first, |a, b| {
                    Exp::new(ExpKind::And(a, b), Default::default())
                }),
                None => Exp::new(ExpKind::TrueLit, Default::default()),
            })
        } else {
            None
        };
        let disabled = context.disable_quantified_triggers();
        let debugging = context.debug_quantified_consumption();
        let (result, next_state, mut remaining, untouched) = remove_quantified_permissions(
            factory,
            context,
            state,
            &candidates,
            &relevant,
            identifier,
            codomain_vars,
            codomain_var_exps,
            condition,
            condition_exp,
            Some(args),
            permission.clone(),
            permission_exp.cloned(),
            disabled,
            debugging,
        )
        .map_err(SingleConsumptionError::Removal)?;
        state = next_state;
        if !matches!(result, ConsumptionResult::Complete) {
            return context
                .single_consumption_failure(
                    &original_state,
                    error,
                    matches!(resource, ResourceKey::Wand(_)),
                )
                .map_err(SingleConsumptionError::Service);
        }
        remaining.extend(untouched.clone());
        remaining.extend(others);
        let new_heap = Arc::new(crate::state::heap::ListBackedHeap::from_chunks(remaining));
        let mut consumed = relevant;
        for chunk in &untouched {
            if let Some(index) = consumed.iter().position(|c| c == chunk) {
                consumed.remove(index);
            }
        }
        let mut counts: Vec<(i32, usize)> = Vec::new();
        for chunk in &consumed {
            let tag = match chunk {
                Chunk::QuantifiedField(c) => c.tag(),
                Chunk::QuantifiedPredicate(c) => c.tag(),
                Chunk::QuantifiedMagicWand(c) => c.tag(),
                _ => None,
            };
            if let Some(tag) = tag {
                if let Some((_, count)) = counts.iter_mut().find(|(t, _)| *t == tag) {
                    *count += 1;
                } else {
                    counts.push((tag, 1));
                }
            }
        }
        // Scala hash-map iteration leaves ties unspecified; Rust selects the last tied
        // first-occurrence group in the stable vector order.
        let tag = counts
            .into_iter()
            .max_by_key(|(_, n)| *n)
            .map(|(tag, _)| tag)
            .unwrap_or_else(|| context.next_consumption_tag());
        if return_snapshot {
            let (definition, cache) = context
                .summarise_consumed_snapshot(&state, resource, codomain_vars, &consumed, args)
                .map_err(SingleConsumptionError::Service)?;
            let lookup =
                factory.resource_lookup(resource, definition.snapshot_map.clone(), args.to_vec());
            let snapshot = if matches!(resource, ResourceKey::Wand(_)) {
                lookup
            } else {
                factory.sort_wrapper(lookup, Sort::Snap)
            };
            state.function_recorder = state.function_recorder.record_fvf_and_domain(definition);
            state.sm_cache = cache;
            state.qp_tag = Some(tag);
            done(context, state, new_heap, Some(snapshot))
        } else {
            done(context, state, new_heap, None)
        }
    };
    if context.use_complete_quantified_exhale() {
        action(context, state, heap, continuation)
    } else {
        let mut retry_state = state;
        retry_state.h = heap;
        context.retry_single_quantified(
            retry_state,
            &mut |context, mut state, done| {
                let consumed_heap = state.h.clone();
                state.h = original_heap.clone();
                action(context, state, consumed_heap, done)
            },
            continuation,
        )
    }
}

pub trait GeneralQuantifiedProduction<P, D, J, V>: InverseFunctionServices {
    type VerificationError;
    fn transform_precondition(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        term: &Term,
    ) -> Result<Term, Self::Error>;
    fn quantified_prover_comment(&mut self, comment: &str) -> Result<(), Self::Error>;
    fn assume_quantified_terms(
        &mut self,
        terms: &[Term],
        definitions: bool,
        debug: Option<&crate::debugger::debug_exp::DebugExp>,
    ) -> Result<(), Self::Error>;
    fn assert_quantified_goal(&mut self, goal: &Term) -> Result<bool, Self::Error>;
    fn quantified_production_failure(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        error: &Self::VerificationError,
        reason: QuantifiedProductionFailure,
        goal: &Term,
        assertion_exp: Option<&Exp>,
    ) -> Result<crate::interfaces::verification::VerificationResult<V>, Self::Error>;
    fn warn_missing_quantified_triggers(
        &mut self,
        position: &ferrum_silver::ast::position::Position,
    ) -> Result<(), Self::Error>;
    fn assume_quantified_properties(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        chunk: &crate::state::chunks::Chunk,
        args: &[Term],
        permission: &Term,
        condition: &Term,
        qvars: &[Term],
        triggers: &[crate::state::terms::Trigger],
        qid: &str,
        debug: Option<QuantifiedPropertyDebug<'_>>,
    ) -> Result<(), Self::Error>;
    fn merge_produced_quantified_chunk(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        chunk: &crate::state::chunks::Chunk,
    ) -> Result<
        (
            crate::supporters::functions::function_recorder::FunctionRecorder<D>,
            crate::state::heap::ListBackedHeap,
        ),
        Self::Error,
    >;
    fn production_resource_trigger(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
        heap: &crate::state::heap::ListBackedHeap,
        inverse: &InverseFunctions,
        condition: &Term,
    ) -> Result<
        Option<(
            SnapshotMapDefinition,
            crate::state::snapshot_map_cache::SnapshotMapCache,
        )>,
        Self::Error,
    >;
    fn next_production_tag(&mut self) -> i32;
    fn assume_injectivity_on_inhale(&self) -> bool;
    fn unsafe_wildcard_optimization(&self) -> bool;
    fn disable_isc_triggers(&self) -> bool;
}
#[derive(Clone, Copy, Debug)]
pub enum QuantifiedProductionFailure {
    NegativePermission,
    NotInjective,
}
fn quantified_negative_debug(input: &GeneralProductionInput, quantified: bool) -> Option<Exp> {
    use ferrum_silver::ast::expression::ExpKind;
    let condition = input.condition_exp.as_ref()?;
    let permission = input.permission_exp.as_ref()?;
    let comparison = Exp::new(
        ExpKind::PermGeCmp(
            permission.clone(),
            Exp::new(ExpKind::NoPerm, Default::default()),
        ),
        Default::default(),
    );
    let metadata = if quantified {
        permission.metadata().clone()
    } else {
        condition.metadata().clone()
    };
    let implication = Exp::new(ExpKind::Implies(condition.clone(), comparison), metadata);
    if quantified {
        Some(Exp::new(
            ExpKind::Forall(input.qvar_exps.clone()?, vec![], implication),
            Default::default(),
        ))
    } else {
        Some(implication)
    }
}

#[derive(Debug)]
pub enum GeneralProductionError<E> {
    Inverse(InverseGenerationError<E>),
    Chunk(GeneralQuantifiedChunkError),
    Injectivity(InjectivityError),
    Transform(UnsupportedTriggerTransform),
    Traversal(crate::state::terms::UnsupportedSubterms),
    MissingDebugScaling,
    InvalidQuantification,
    Service(E),
}
pub enum GeneralProductionOutcome<P, D, J, V> {
    Produced(crate::state::state::State<P, D, J>),
    Failed(crate::interfaces::verification::VerificationResult<V>),
}
pub struct QuantifiedPropertyDebug<'a> {
    pub qvar_exps: Option<&'a [LocalVarDecl]>,
    pub arg_exps: Option<&'a [Exp]>,
    pub permission_exp: Option<&'a Exp>,
    pub condition_exp: Option<&'a Exp>,
}
fn internal_inverse_debug(label: &str) -> crate::debugger::debug_exp::DebugExp {
    crate::debugger::debug_exp::DebugExp::create(
        Some(label.into()),
        None,
        None,
        None,
        true,
        Default::default(),
        false,
        &|e: &Exp| Ok::<_, std::convert::Infallible>(e.clone()),
    )
    .expect("infallible debug expression")
}
pub struct GeneralProductionInput {
    pub quantifier_position: ferrum_silver::ast::position::Position,
    pub qvars: Vec<Term>,
    pub qvar_exps: Option<Vec<LocalVarDecl>>,
    pub formal_vars: Vec<Term>,
    pub formal_var_exps: Option<Vec<LocalVarDecl>>,
    pub qid: String,
    pub has_explicit_triggers: bool,
    pub triggers: Vec<crate::state::terms::Trigger>,
    pub aux_globals: Vec<Term>,
    pub aux_non_globals: Vec<Term>,
    pub auxiliary_debug: Option<(
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::debugger::debug_exp::DebugExp,
        >,
        crate::common::collections::immutable::insertion_ordered_set::InsertionOrderedSet<
            crate::debugger::debug_exp::DebugExp,
        >,
    )>,
    pub condition: Term,
    pub condition_exp: Option<Exp>,
    pub args: Vec<Term>,
    pub arg_exps: Option<Vec<Exp>>,
    pub snapshot_map: Term,
    pub permission: Term,
    pub permission_exp: Option<Exp>,
    pub debugging: bool,
}
/// Produce a general quantified chunk with source trigger selection, permission and
/// injectivity proofs, inverse assumptions, resource properties and heap merge.
pub fn produce_general_quantified<
    P,
    D: Clone,
    J: Clone + PartialEq,
    V,
    C: GeneralQuantifiedProduction<P, D, J, V>,
>(
    factory: &TermFactory,
    context: &mut C,
    mut state: crate::state::state::State<P, D, J>,
    resource: &crate::state::terms::ResourceKey,
    input: GeneralProductionInput,
    error: &C::VerificationError,
) -> Result<GeneralProductionOutcome<P, D, J, V>, GeneralProductionError<C::Error>> {
    use crate::state::terms::{Quantifier, ResourceKey, Trigger};
    use ferrum_silver::ast::expression::ExpKind;
    let location = !matches!(resource, ResourceKey::Wand(_));
    let gain = if !context.unsafe_wildcard_optimization()
        || (location && state.perm_locations.contains(resource))
    {
        factory.perm_times(
            input.permission.clone(),
            state.permission_scaling_factor.clone(),
        )
    } else {
        factory.wildcard_simplifying_perm_times(
            input.permission.clone(),
            state.permission_scaling_factor.clone(),
        )
    };
    let gain_exp = match &input.permission_exp {
        Some(p) => Some(Exp::new(
            ExpKind::PermMul(
                p.clone(),
                state
                    .permission_scaling_factor_exp
                    .clone()
                    .ok_or(GeneralProductionError::MissingDebugScaling)?,
            ),
            p.metadata().clone(),
        )),
        None => None,
    };
    let additional = state
        .relevant_quantified_variables_in(&input.args)
        .map_err(GeneralProductionError::Traversal)?
        .into_iter()
        .map(|(term, _)| term)
        .collect();
    let mut state_qvars = Vec::new();
    for (var, _) in &state.quantified_variables {
        let mut occurs = input
            .condition
            .contains(var)
            .map_err(GeneralProductionError::Traversal)?;
        for arg in &input.args {
            if arg
                .contains(var)
                .map_err(GeneralProductionError::Traversal)?
            {
                occurs = true;
                break;
            }
        }
        if occurs {
            state_qvars.push(var.clone());
        }
    }
    let inv_condition = factory.and([
        input.condition.clone(),
        factory.is_positive_perm(gain.clone()),
    ]);
    let disabled = context.disable_isc_triggers();
    let (mut inverse, images) = fresh_inverse_functions(
        factory,
        context,
        &input.qvars,
        input.qvar_exps.clone(),
        inv_condition,
        input.args.clone(),
        input.arg_exps.clone(),
        &input.formal_vars,
        additional,
        &state_qvars,
        input
            .has_explicit_triggers
            .then_some(input.triggers.as_slice()),
        &input.qid,
        disabled,
    )
    .map_err(GeneralProductionError::Inverse)?;
    let tag = context.next_production_tag();
    let chunk = quantified_chunk_from_inverses(
        factory,
        resource,
        QuantifiedChunkData {
            codomain_vars: input.formal_vars.clone(),
            codomain_var_exps: input.formal_var_exps.clone(),
            arguments: input.args.clone(),
            snapshot_map: input.snapshot_map.clone(),
            condition: input.condition.clone(),
            condition_exp: input.condition_exp.clone(),
            permission: gain.clone(),
            permission_exp: gain_exp.clone(),
            inverses: vec![],
            singleton_args: None,
            singleton_arg_exps: None,
            tag: Some(tag),
            hints: vec![],
            debugging: input.debugging,
        },
        inverse.clone(),
        images,
    )
    .map_err(GeneralProductionError::Chunk)?;
    let (effective_vars, effective_triggers) = if input.has_explicit_triggers {
        let triggers = input
            .triggers
            .iter()
            .map(|trigger| Trigger {
                terms: trigger
                    .terms
                    .iter()
                    .map(|term| match (resource, term.kind()) {
                        (ResourceKey::Field(f), TermKind::FieldTrigger(name, _, at))
                            if f.name == *name =>
                        {
                            factory.field_trigger(
                                name.clone(),
                                input.snapshot_map.clone(),
                                at.clone(),
                            )
                        }
                        (ResourceKey::Predicate(p), TermKind::PredicateTrigger(name, _, args))
                            if p.name == *name =>
                        {
                            factory.predicate_trigger(
                                name.clone(),
                                input.snapshot_map.clone(),
                                args.clone(),
                            )
                        }
                        (ResourceKey::Wand(w), TermKind::PredicateTrigger(name, _, args))
                            if w.to_string() == *name =>
                        {
                            factory.predicate_trigger(
                                name.clone(),
                                input.snapshot_map.clone(),
                                args.clone(),
                            )
                        }
                        _ => term.clone(),
                    })
                    .collect(),
            })
            .collect();
        (input.qvars.clone(), triggers)
    } else {
        let TermKind::Quantification { vars, triggers, .. } =
            inverse.axiom_inverses_of_invertibles.kind()
        else {
            return Err(GeneralProductionError::InvalidQuantification);
        };
        (vars.clone(), triggers.clone())
    };
    if effective_triggers.is_empty() {
        context
            .warn_missing_quantified_triggers(&input.quantifier_position)
            .map_err(GeneralProductionError::Service)?;
    }
    context
        .quantified_prover_comment("Nested auxiliary terms: globals")
        .map_err(GeneralProductionError::Service)?;
    let global_debug = input.auxiliary_debug.as_ref().map(|(global, _)| {
        crate::debugger::debug_exp::DebugExp::group(
            "Nested auxiliary terms: globals".into(),
            global.clone(),
        )
    });
    context
        .assume_quantified_terms(&input.aux_globals, false, global_debug.as_ref())
        .map_err(GeneralProductionError::Service)?;
    let mut auxiliary = Vec::new();
    for term in &input.aux_non_globals {
        let TermKind::Quantification {
            quantifier,
            body,
            name,
            is_global,
            weight,
            ..
        } = term.kind()
        else {
            return Err(GeneralProductionError::InvalidQuantification);
        };
        auxiliary.push(
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
                .map_err(GeneralProductionError::Transform)?,
        );
    }
    context
        .quantified_prover_comment("Nested auxiliary terms: non-globals")
        .map_err(GeneralProductionError::Service)?;
    let local_debug = input.auxiliary_debug.as_ref().map(|(_, local)| {
        crate::debugger::debug_exp::DebugExp::group(
            "Nested auxiliary terms: non-globals".into(),
            local.clone(),
        )
    });
    context
        .assume_quantified_terms(&auxiliary, false, local_debug.as_ref())
        .map_err(GeneralProductionError::Service)?;
    let nonnegative = factory.implies(
        input.condition.clone(),
        factory.perm_at_most(factory.no_perm(), input.permission.clone()),
    );
    let precondition = context
        .transform_precondition(&state, &nonnegative)
        .map_err(GeneralProductionError::Service)?;
    let goal = factory
        .quantification(
            Quantifier::Forall,
            input.qvars.clone(),
            factory.implies(precondition, nonnegative.clone()),
            vec![],
            TermFactory::forall_default_name(),
            false,
            None,
        )
        .map_err(GeneralProductionError::Transform)?;
    if !context
        .assert_quantified_goal(&goal)
        .map_err(GeneralProductionError::Service)?
    {
        return Ok(GeneralProductionOutcome::Failed(
            context
                .quantified_production_failure(
                    &state,
                    error,
                    QuantifiedProductionFailure::NegativePermission,
                    &nonnegative,
                    quantified_negative_debug(&input, false).as_ref(),
                )
                .map_err(GeneralProductionError::Service)?,
        ));
    }
    let injectivity = if context.assume_injectivity_on_inhale() {
        factory.boolean(true)
    } else {
        injectivity_axiom(
            factory,
            &input.qvars,
            &input.condition,
            &input.permission,
            &input.args,
            vec![],
            &input.qid,
        )
        .map_err(GeneralProductionError::Injectivity)?
    };
    let precondition = context
        .transform_precondition(&state, &injectivity)
        .map_err(GeneralProductionError::Service)?;
    let complete = factory.implies(precondition, injectivity.clone());
    if !context
        .assert_quantified_goal(&complete)
        .map_err(GeneralProductionError::Service)?
    {
        return Ok(GeneralProductionOutcome::Failed(
            context
                .quantified_production_failure(
                    &state,
                    error,
                    QuantifiedProductionFailure::NotInjective,
                    &injectivity,
                    None,
                )
                .map_err(GeneralProductionError::Service)?,
        ));
    }
    let TermKind::Quantification { body, .. } = inverse.axiom_inverses_of_invertibles.kind() else {
        return Err(GeneralProductionError::InvalidQuantification);
    };
    inverse.axiom_inverses_of_invertibles = factory
        .quantification(
            Quantifier::Forall,
            effective_vars.clone(),
            body.clone(),
            effective_triggers.clone(),
            format!("{}-invOfFct", input.qid),
            false,
            None,
        )
        .map_err(GeneralProductionError::Transform)?;
    let axioms: Vec<_> = inverse.definitional_axioms().into_iter().cloned().collect();
    context
        .quantified_prover_comment("Definitional axioms for inverse functions")
        .map_err(GeneralProductionError::Service)?;
    let transformed = axioms
        .iter()
        .map(|a| context.transform_precondition(&state, a))
        .collect::<Result<Vec<_>, _>>()
        .map_err(GeneralProductionError::Service)?;
    context
        .assume_quantified_terms(&transformed, true, None)
        .map_err(GeneralProductionError::Service)?;
    context
        .assume_quantified_terms(&axioms, true, None)
        .map_err(GeneralProductionError::Service)?;
    context
        .assume_quantified_properties(
            &state,
            &chunk,
            &input.args,
            &gain,
            &input.condition,
            &effective_vars,
            &effective_triggers,
            &input.qid,
            input.debugging.then(|| QuantifiedPropertyDebug {
                qvar_exps: input.qvar_exps.as_deref(),
                arg_exps: input.arg_exps.as_deref(),
                permission_exp: gain_exp.as_ref(),
                condition_exp: input.condition_exp.as_ref(),
            }),
        )
        .map_err(GeneralProductionError::Service)?;
    let (mut recorder, heap) = context
        .merge_produced_quantified_chunk(&state, &chunk)
        .map_err(GeneralProductionError::Service)?;
    if let Some((definition, cache)) = context
        .production_resource_trigger(&state, resource, &heap, &inverse, &input.condition)
        .map_err(GeneralProductionError::Service)?
    {
        recorder = recorder.record_fvf_and_domain(definition);
        state.sm_cache = cache;
    }
    state.h = std::sync::Arc::new(heap);
    state.function_recorder = recorder.record_field_inv(inverse);
    Ok(GeneralProductionOutcome::Produced(state))
}

/// Outputs of the pre-retry phase of a general quantified consumption. The retry
/// action must recompute its heap partition and then remove `loss` under `condition`.
pub struct GeneralConsumptionPlan<P, D, J> {
    pub state: crate::state::state::State<P, D, J>,
    pub inverse: InverseFunctions,
    pub formal_vars: Vec<Term>,
    pub formal_var_exps: Option<Vec<LocalVarDecl>>,
    pub qvars: Vec<Term>,
    /// Source condition after the original inverse substitution, before image guards.
    pub inverse_condition: Term,
    pub original_args: Vec<Term>,
    pub original_condition: Term,
    pub qid: String,
    pub explicit_triggers: Option<Vec<crate::state::terms::Trigger>>,
    pub condition: Term,
    pub domain_condition: Term,
    pub trigger_cache: crate::state::snapshot_map_cache::SnapshotMapCache,
    pub condition_exp: Option<Exp>,
    pub loss: Term,
    pub loss_exp: Option<Exp>,
    pub relevant_snapshot: Option<SnapshotMapDefinition>,
    pub hints: Vec<Term>,
}
pub enum GeneralConsumptionPreparation<P, D, J, V> {
    Ready(GeneralConsumptionPlan<P, D, J>),
    Failed(crate::interfaces::verification::VerificationResult<V>),
}
pub trait GeneralQuantifiedConsumptionPreparation<P, D, J, V>: InverseFunctionServices {
    type VerificationError;
    fn consume_transform_precondition(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        term: &Term,
    ) -> Result<Term, Self::Error>;
    fn consume_prover_comment(&mut self, comment: &str) -> Result<(), Self::Error>;
    fn consume_assume_terms(
        &mut self,
        terms: &[Term],
        debug: Option<&crate::debugger::debug_exp::DebugExp>,
    ) -> Result<(), Self::Error>;
    fn consume_assert_goal(&mut self, term: &Term) -> Result<bool, Self::Error>;
    fn general_consumption_failure(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        error: &Self::VerificationError,
        reason: QuantifiedProductionFailure,
        goal: &Term,
        assertion_exp: Option<&Exp>,
    ) -> Result<crate::interfaces::verification::VerificationResult<V>, Self::Error>;
    fn consume_trigger_summary(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        heap: &crate::state::heap::ListBackedHeap,
        resource: &crate::state::terms::ResourceKey,
        formal_vars: &[Term],
        identifier: &crate::state::chunks::ChunkIdentifier,
    ) -> Result<
        Option<(
            SnapshotMapDefinition,
            crate::state::snapshot_map_cache::SnapshotMapCache,
        )>,
        Self::Error,
    >;
    fn consume_assume_inverse_trigger(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
        formal_vars: &[Term],
        condition: &Term,
        inverse: &InverseFunctions,
        snapshot: &SnapshotMapDefinition,
    ) -> Result<(), Self::Error>;
    fn consumption_unsafe_wildcard(&self) -> bool;
    fn consumption_disable_isc_triggers(&self) -> bool;
}
/// Evaluate the quantified proof/axiom phase before the source retryable heap action.
/// The caller must apply removal to the retry action's refreshed heap, not the heap
/// partition inspected here for trigger summaries.
pub fn prepare_general_quantified_consumption<
    P,
    D: Clone,
    J: Clone + PartialEq,
    V,
    C: GeneralQuantifiedConsumptionPreparation<P, D, J, V>,
>(
    factory: &TermFactory,
    context: &mut C,
    state: crate::state::state::State<P, D, J>,
    heap: &crate::state::heap::ListBackedHeap,
    resource: &crate::state::terms::ResourceKey,
    identifier: &crate::state::chunks::ChunkIdentifier,
    input: GeneralProductionInput,
    error: &C::VerificationError,
) -> Result<GeneralConsumptionPreparation<P, D, J, V>, GeneralProductionError<C::Error>> {
    use crate::state::terms::{Quantifier, ResourceKey};
    use ferrum_silver::ast::expression::ExpKind;
    let mut occurrence_terms = input.args.clone();
    occurrence_terms.push(input.condition.clone());
    let additional = state
        .relevant_quantified_variables_in(&occurrence_terms)
        .map_err(GeneralProductionError::Traversal)?
        .into_iter()
        .map(|(term, _)| term)
        .collect();
    let mut state_qvars = Vec::new();
    for (var, _) in &state.quantified_variables {
        let mut occurs = false;
        for term in &occurrence_terms {
            if term
                .contains(var)
                .map_err(GeneralProductionError::Traversal)?
            {
                occurs = true;
                break;
            }
        }
        if occurs {
            state_qvars.push(var.clone());
        }
    }
    let inverse_condition = factory.and([
        input.condition.clone(),
        factory.is_positive_perm(input.permission.clone()),
    ]);
    let disabled = context.consumption_disable_isc_triggers();
    let (inverse, images) = fresh_inverse_functions(
        factory,
        context,
        &input.qvars,
        input.qvar_exps.clone(),
        inverse_condition,
        input.args.clone(),
        input.arg_exps.clone(),
        &input.formal_vars,
        additional,
        &state_qvars,
        input
            .has_explicit_triggers
            .then_some(input.triggers.as_slice()),
        &input.qid,
        disabled,
    )
    .map_err(GeneralProductionError::Inverse)?;
    let (effective_vars, effective_triggers) = if input.has_explicit_triggers {
        (input.qvars.clone(), input.triggers.clone())
    } else {
        let TermKind::Quantification { vars, triggers, .. } =
            inverse.axiom_inverses_of_invertibles.kind()
        else {
            return Err(GeneralProductionError::InvalidQuantification);
        };
        (vars.clone(), triggers.clone())
    };
    context
        .consume_prover_comment("Nested auxiliary terms: globals")
        .map_err(GeneralProductionError::Service)?;
    let global_debug = input.auxiliary_debug.as_ref().map(|(global, _)| {
        crate::debugger::debug_exp::DebugExp::group(
            "Nested auxiliary terms: globals".into(),
            global.clone(),
        )
    });
    context
        .consume_assume_terms(&input.aux_globals, global_debug.as_ref())
        .map_err(GeneralProductionError::Service)?;
    let mut auxiliary = Vec::new();
    for term in &input.aux_non_globals {
        if input.has_explicit_triggers {
            auxiliary.push(term.clone());
            continue;
        }
        let TermKind::Quantification {
            quantifier,
            body,
            name,
            is_global,
            weight,
            ..
        } = term.kind()
        else {
            return Err(GeneralProductionError::InvalidQuantification);
        };
        auxiliary.push(
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
                .map_err(GeneralProductionError::Transform)?,
        );
    }
    context
        .consume_prover_comment("Nested auxiliary terms: non-globals")
        .map_err(GeneralProductionError::Service)?;
    let local_debug = input.auxiliary_debug.as_ref().map(|(_, local)| {
        crate::debugger::debug_exp::DebugExp::group(
            "Nested auxiliary terms: non-globals".into(),
            local.clone(),
        )
    });
    context
        .consume_assume_terms(&auxiliary, local_debug.as_ref())
        .map_err(GeneralProductionError::Service)?;
    let nonnegative = factory.implies(
        input.condition.clone(),
        factory.perm_at_most(factory.no_perm(), input.permission.clone()),
    );
    let precondition = context
        .consume_transform_precondition(&state, &nonnegative)
        .map_err(GeneralProductionError::Service)?;
    let goal = factory
        .quantification(
            Quantifier::Forall,
            input.qvars.clone(),
            factory.implies(precondition, nonnegative),
            vec![],
            TermFactory::forall_default_name(),
            false,
            None,
        )
        .map_err(GeneralProductionError::Transform)?;
    if !context
        .consume_assert_goal(&goal)
        .map_err(GeneralProductionError::Service)?
    {
        return Ok(GeneralConsumptionPreparation::Failed(
            context
                .general_consumption_failure(
                    &state,
                    error,
                    QuantifiedProductionFailure::NegativePermission,
                    &goal,
                    quantified_negative_debug(&input, true).as_ref(),
                )
                .map_err(GeneralProductionError::Service)?,
        ));
    }
    let hints = extract_hints(factory, Some(&input.condition), &input.args)
        .map_err(GeneralProductionError::Traversal)?;
    let location = !matches!(resource, ResourceKey::Wand(_));
    let loss = if !context.consumption_unsafe_wildcard()
        || (location && state.perm_locations.contains(resource))
    {
        factory.perm_times(
            input.permission.clone(),
            state.permission_scaling_factor.clone(),
        )
    } else {
        factory.wildcard_simplifying_perm_times(
            input.permission.clone(),
            state.permission_scaling_factor.clone(),
        )
    };
    let loss_exp = match &input.permission_exp {
        Some(p) => Some(Exp::new(
            ExpKind::PermMul(
                p.clone(),
                state
                    .permission_scaling_factor_exp
                    .clone()
                    .ok_or(GeneralProductionError::MissingDebugScaling)?,
            ),
            p.metadata().clone(),
        )),
        None => None,
    };
    let summary = context
        .consume_trigger_summary(&state, heap, resource, &input.formal_vars, identifier)
        .map_err(GeneralProductionError::Service)?;
    let injectivity_condition = match &summary {
        Some((definition, _)) => factory.and([
            input.condition.clone(),
            factory.resource_trigger(
                resource,
                definition.snapshot_map.clone(),
                input.args.clone(),
            ),
        ]),
        None => input.condition.clone(),
    };
    let injectivity = injectivity_axiom(
        factory,
        &input.qvars,
        &injectivity_condition,
        &input.permission,
        &input.args,
        vec![],
        &input.qid,
    )
    .map_err(GeneralProductionError::Injectivity)?;
    let precondition = context
        .consume_transform_precondition(&state, &injectivity)
        .map_err(GeneralProductionError::Service)?;
    if !context
        .consume_assert_goal(&factory.implies(precondition, injectivity.clone()))
        .map_err(GeneralProductionError::Service)?
    {
        return Ok(GeneralConsumptionPreparation::Failed(
            context
                .general_consumption_failure(
                    &state,
                    error,
                    QuantifiedProductionFailure::NotInjective,
                    &injectivity,
                    None,
                )
                .map_err(GeneralProductionError::Service)?,
        ));
    }
    let replacements: HashMap<_, _> = inverse
        .qvars_to_inverses_of(factory, &input.formal_vars)
        .into_iter()
        .collect();
    let condition = factory
        .replace(&input.condition, &replacements)
        .map_err(GeneralProductionError::Transform)?;
    let loss = factory
        .replace(&loss, &replacements)
        .map_err(GeneralProductionError::Transform)?;
    let mut args = Vec::new();
    for term in &input.args {
        args.push(
            factory
                .replace(term, &replacements)
                .map_err(GeneralProductionError::Transform)?,
        );
    }
    let arguments_match = factory.and(
        input
            .formal_vars
            .iter()
            .zip(args)
            .map(|(a, b)| factory.equals(a.clone(), b)),
    );
    let condition_exp = if let Some(condition) = &input.condition_exp {
        let vars = input
            .formal_var_exps
            .as_ref()
            .ok_or(GeneralProductionError::MissingDebugScaling)?;
        let args = input
            .arg_exps
            .as_ref()
            .ok_or(GeneralProductionError::MissingDebugScaling)?;
        let mut equalities = vars.iter().zip(args).map(|(var, arg)| {
            Exp::new(
                ExpKind::EqCmp(
                    Exp::new(ExpKind::LocalVar(var.local_var()), var.meta.clone()),
                    arg.clone(),
                ),
                var.meta.clone(),
            )
        });
        let matches = match equalities.next() {
            Some(first) => equalities.fold(first, |a, b| {
                Exp::new(ExpKind::And(a, b), Default::default())
            }),
            None => Exp::new(ExpKind::TrueLit, Default::default()),
        };
        Some(Exp::new(
            ExpKind::And(condition.clone(), matches),
            Default::default(),
        ))
    } else {
        None
    };
    let axioms: Vec<_> = inverse.definitional_axioms().into_iter().cloned().collect();
    context
        .consume_prover_comment("Definitional axioms for inverse functions")
        .map_err(GeneralProductionError::Service)?;
    let transformed = axioms
        .iter()
        .map(|a| context.consume_transform_precondition(&state, a))
        .collect::<Result<Vec<_>, _>>()
        .map_err(GeneralProductionError::Service)?;
    context
        .consume_assume_terms(
            &transformed,
            input
                .debugging
                .then(|| internal_inverse_debug("Inverse Function Axioms"))
                .as_ref(),
        )
        .map_err(GeneralProductionError::Service)?;
    context
        .consume_assume_terms(
            &axioms,
            input
                .debugging
                .then(|| internal_inverse_debug("Inverse function axiom"))
                .as_ref(),
        )
        .map_err(GeneralProductionError::Service)?;
    let (snapshot, trigger_cache) = if let Some((definition, cache)) = summary {
        context
            .consume_assume_inverse_trigger(
                &state,
                resource,
                &input.formal_vars,
                &condition,
                &inverse,
                &definition,
            )
            .map_err(GeneralProductionError::Service)?;
        (Some(definition), cache)
    } else {
        (None, state.sm_cache.clone())
    };
    let condition_of_inverse = condition.clone();
    let domain_condition = factory.and([
        condition.clone(),
        factory.is_positive_perm(loss.clone()),
        factory.and(images.clone()),
    ]);
    let condition = factory.and([condition, factory.and(images), arguments_match]);
    Ok(GeneralConsumptionPreparation::Ready(
        GeneralConsumptionPlan {
            state,
            inverse,
            formal_vars: input.formal_vars,
            formal_var_exps: input.formal_var_exps,
            qvars: input.qvars,
            inverse_condition: condition_of_inverse,
            original_args: input.args,
            original_condition: input.condition,
            qid: input.qid,
            explicit_triggers: input.has_explicit_triggers.then_some(input.triggers),
            condition,
            domain_condition,
            trigger_cache,
            condition_exp,
            loss,
            loss_exp,
            relevant_snapshot: snapshot,
            hints,
        },
    ))
}

pub trait GeneralConsumptionExecution<P, D, J, V>:
    QuantifiedRemovalServices<P, D, J>
    + QuantifiedChunkSolver<Error = <Self as QuantifiedReadPermissionSolver>::Error>
{
    type VerificationError;
    fn retry_general_quantified(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        action: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
            &mut dyn FnMut(
                &mut Self,
                crate::state::state::State<P, D, J>,
                std::sync::Arc<crate::state::heap::ListBackedHeap>,
                Option<Term>,
            ) -> Result<
                crate::interfaces::verification::VerificationResult<V>,
                GeneralConsumptionExecutionError<<Self as QuantifiedReadPermissionSolver>::Error>,
            >,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            GeneralConsumptionExecutionError<<Self as QuantifiedReadPermissionSolver>::Error>,
        >,
        continuation: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
            std::sync::Arc<crate::state::heap::ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            GeneralConsumptionExecutionError<<Self as QuantifiedReadPermissionSolver>::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        GeneralConsumptionExecutionError<<Self as QuantifiedReadPermissionSolver>::Error>,
    >;
    fn general_insufficient_permission(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        error: &Self::VerificationError,
        goal: Option<&Term>,
        description: &str,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        <Self as QuantifiedReadPermissionSolver>::Error,
    >;
    fn consume_general_in_package(
        &mut self,
        state: crate::state::state::State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
        identifier: &crate::state::chunks::ChunkIdentifier,
        plan: &GeneralConsumptionTerms,
        error: &Self::VerificationError,
        return_snapshot: bool,
        continuation: &mut dyn FnMut(
            &mut Self,
            crate::state::state::State<P, D, J>,
            std::sync::Arc<crate::state::heap::ListBackedHeap>,
            Option<Term>,
        ) -> Result<
            crate::interfaces::verification::VerificationResult<V>,
            GeneralConsumptionExecutionError<<Self as QuantifiedReadPermissionSolver>::Error>,
        >,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        GeneralConsumptionExecutionError<<Self as QuantifiedReadPermissionSolver>::Error>,
    >;
    fn summarise_general_consumed(
        &mut self,
        state: &crate::state::state::State<P, D, J>,
        resource: &crate::state::terms::ResourceKey,
        formal_vars: &[Term],
        consumed: &[crate::state::chunks::Chunk],
        domain_condition: Option<&Term>,
    ) -> Result<
        (
            SnapshotMapDefinition,
            crate::state::snapshot_map_cache::SnapshotMapCache,
        ),
        <Self as QuantifiedReadPermissionSolver>::Error,
    >;
    fn clear_general_consumption_model(
        &mut self,
    ) -> Result<(), <Self as QuantifiedReadPermissionSolver>::Error>;
    fn next_general_consumption_tag(&mut self) -> i32;
    fn complete_general_quantified_exhale(&self) -> bool;
    fn disable_general_chunk_ordering(&self) -> bool;
    fn disable_general_isc_triggers(&self) -> bool;
    fn debug_general_consumption(&self) -> bool;
}
/// Retry-independent quantified terms and source context used by ordinary and package paths.
pub struct GeneralConsumptionTerms {
    pub inverse: InverseFunctions,
    pub formal_vars: Vec<Term>,
    pub formal_var_exps: Option<Vec<LocalVarDecl>>,
    pub qvars: Vec<Term>,
    /// Source condition after the original inverse substitution, before image guards.
    pub inverse_condition: Term,
    pub original_args: Vec<Term>,
    pub original_condition: Term,
    pub qid: String,
    pub explicit_triggers: Option<Vec<crate::state::terms::Trigger>>,
    pub condition: Term,
    pub condition_exp: Option<Exp>,
    pub domain_condition: Term,
    pub loss: Term,
    pub loss_exp: Option<Exp>,
    pub trigger_cache: crate::state::snapshot_map_cache::SnapshotMapCache,
    pub relevant_snapshot: Option<SnapshotMapDefinition>,
    pub hints: Vec<Term>,
}
#[derive(Debug)]
pub enum GeneralConsumptionExecutionError<E> {
    Split(QuantifiedSplitError),
    Order(QuantifiedMatchError<E>),
    Removal(QuantifiedRemovalError<E>),
    Service(E),
}
/// Run the retryable quantified removal action, recomputing chunks after consolidation
/// and recording snapshot maps only when requested. Package transfer remains a service.
pub fn execute_general_quantified_consumption<
    P,
    D: Clone,
    J: Clone + PartialEq,
    V,
    C: GeneralConsumptionExecution<P, D, J, V>,
>(
    factory: &TermFactory,
    context: &mut C,
    plan: GeneralConsumptionPlan<P, D, J>,
    heap: std::sync::Arc<crate::state::heap::ListBackedHeap>,
    resource: &crate::state::terms::ResourceKey,
    identifier: &crate::state::chunks::ChunkIdentifier,
    return_snapshot: bool,
    error: &C::VerificationError,
    continuation: &mut dyn FnMut(
        &mut C,
        crate::state::state::State<P, D, J>,
        std::sync::Arc<crate::state::heap::ListBackedHeap>,
        Option<Term>,
    ) -> Result<
        crate::interfaces::verification::VerificationResult<V>,
        GeneralConsumptionExecutionError<<C as QuantifiedReadPermissionSolver>::Error>,
    >,
) -> Result<
    crate::interfaces::verification::VerificationResult<V>,
    GeneralConsumptionExecutionError<<C as QuantifiedReadPermissionSolver>::Error>,
> {
    use crate::interfaces::state::chunks::GeneralChunk;
    use crate::state::chunks::Chunk;
    use crate::state::terms::Sort;
    use std::sync::Arc;
    let GeneralConsumptionPlan {
        state,
        inverse,
        formal_vars,
        formal_var_exps,
        qvars,
        inverse_condition,
        original_args,
        original_condition,
        qid,
        explicit_triggers,
        condition,
        condition_exp,
        domain_condition,
        trigger_cache,
        loss,
        loss_exp,
        relevant_snapshot,
        hints,
    } = plan;
    let terms = GeneralConsumptionTerms {
        inverse,
        formal_vars,
        formal_var_exps,
        qvars,
        inverse_condition,
        original_args,
        original_condition,
        qid,
        explicit_triggers,
        condition,
        condition_exp,
        domain_condition,
        trigger_cache,
        loss,
        loss_exp,
        relevant_snapshot,
        hints,
    };
    let original_heap = state.h.clone();
    let action = |context: &mut C,
                  state: crate::state::state::State<P, D, J>,
                  heap: Arc<crate::state::heap::ListBackedHeap>,
                  done: &mut dyn FnMut(
        &mut C,
        crate::state::state::State<P, D, J>,
        Arc<crate::state::heap::ListBackedHeap>,
        Option<Term>,
    ) -> Result<_, _>| {
        if state.exhale_ext {
            return context.consume_general_in_package(
                state,
                resource,
                identifier,
                &terms,
                error,
                return_snapshot,
                done,
            );
        }
        context
            .clear_general_consumption_model()
            .map_err(GeneralConsumptionExecutionError::Service)?;
        let (relevant, others) = split_quantified_heap(&heap, identifier)
            .map_err(GeneralConsumptionExecutionError::Split)?;
        let candidates = if context.disable_general_chunk_ordering() {
            relevant.clone()
        } else {
            quantified_application_chunk_order(
                factory,
                context,
                &relevant,
                &terms.inverse.invertibles,
                &terms.qvars,
                &terms.hints,
            )
            .map_err(GeneralConsumptionExecutionError::Order)?
        };
        let original_arps = state.constrainable_arps.clone();
        let mut removal_state = state;
        removal_state.sm_cache = terms.trigger_cache.clone();
        let disabled = context.disable_general_isc_triggers();
        let debugging = context.debug_general_consumption();
        let (result, mut state, mut remaining, untouched) = remove_quantified_permissions(
            factory,
            context,
            removal_state,
            &candidates,
            &relevant,
            identifier,
            &terms.formal_vars,
            terms.formal_var_exps.as_deref(),
            terms.condition.clone(),
            terms.condition_exp.clone(),
            None,
            terms.loss.clone(),
            terms.loss_exp.clone(),
            disabled,
            debugging,
        )
        .map_err(GeneralConsumptionExecutionError::Removal)?;
        if !result.is_complete() {
            return context
                .general_insufficient_permission(&state, error, None, "QP consume")
                .map_err(GeneralConsumptionExecutionError::Service);
        }
        remaining.extend(untouched.clone());
        remaining.extend(others);
        let new_heap = Arc::new(crate::state::heap::ListBackedHeap::from_chunks(remaining));
        let mut consumed = relevant;
        for chunk in &untouched {
            if let Some(index) = consumed.iter().position(|c| c == chunk) {
                consumed.remove(index);
            }
        }
        let mut counts: Vec<(i32, usize)> = Vec::new();
        for chunk in &consumed {
            let tag = match chunk {
                Chunk::QuantifiedField(c) => c.tag(),
                Chunk::QuantifiedPredicate(c) => c.tag(),
                Chunk::QuantifiedMagicWand(c) => c.tag(),
                _ => None,
            };
            if let Some(tag) = tag {
                if let Some((_, count)) = counts.iter_mut().find(|(t, _)| *t == tag) {
                    *count += 1;
                } else {
                    counts.push((tag, 1));
                }
            }
        }
        // Scala hash-map iteration leaves ties unspecified; Rust selects the last tied
        // first-occurrence group in the stable vector order.
        let tag = counts
            .into_iter()
            .max_by_key(|(_, n)| *n)
            .map(|(tag, _)| tag)
            .unwrap_or_else(|| context.next_general_consumption_tag());
        if return_snapshot {
            let domain = state.sm_domain_needed.then_some(&terms.domain_condition);
            let (definition, cache) = context
                .summarise_general_consumed(&state, resource, &terms.formal_vars, &consumed, domain)
                .map_err(GeneralConsumptionExecutionError::Service)?;
            let snapshot = factory.sort_wrapper(definition.snapshot_map.clone(), Sort::Snap);
            let mut recorder = state
                .function_recorder
                .record_fvf_and_domain(definition)
                .record_field_inv(terms.inverse.clone());
            if let Some(summary) = &terms.relevant_snapshot {
                recorder = recorder.record_fvf_and_domain(summary.clone());
            }
            state.function_recorder = recorder;
            state.partially_consumed_heap = Some(new_heap.clone());
            state.constrainable_arps = original_arps;
            state.sm_cache = cache;
            state.qp_tag = Some(tag);
            done(context, state, new_heap, Some(snapshot))
        } else {
            done(context, state, new_heap, None)
        }
    };
    if context.complete_general_quantified_exhale() {
        action(context, state, heap, continuation)
    } else {
        let mut retry_state = state;
        retry_state.h = heap;
        context.retry_general_quantified(
            retry_state,
            &mut |context, mut state, done| {
                let consumed_heap = state.h.clone();
                state.h = original_heap.clone();
                action(context, state, consumed_heap, done)
            },
            continuation,
        )
    }
}
