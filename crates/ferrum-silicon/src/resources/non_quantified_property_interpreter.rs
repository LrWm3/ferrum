//! Upstream:
//! https://github.com/viperproject/silicon/blob/ff386aec4664231dc6f2cb56d8d35f1623088363/src/main/scala/resources/NonQuantifiedPropertyInterpreter.scala
//!
//! Purpose:
//! Instantiate resource properties over ordinary and singleton quantified heap chunks.
//!
//! Planned Rust structure:
//! Port NonQuantifiedPropertyInterpreter, placeholder Info map, chunk/resource entry points,
//! accessors, solver Check and recursive ForEach.
//!
//! Behavior to preserve:
//! Select nonquantified and singleton quantified chunks, substitute singleton arguments in
//! permissions/values. ForEach groups by resource and chunk ID, enumerates distinct chunk
//! identities, conjoins results; reject ForEach when This is bound. Check uses decider with
//! configured timeout and chooses one branch. Preserve debug expressions and traversal order.
//!
//! Integration:
//! resources::property_interpreter, state chunk interfaces, verifier::verifier and decider.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for identity, solver access and debug metadata.
//!
//! Open decisions:
//! Agree on heap iteration, reference identity and singleton chunk handling with state and
//! decider.
//!
//! Status: partial; nonquantified and singleton-quantified term interpretation implemented.
//! Debug-expression construction remains pending.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
// Copyright (c) 2011-2019 ETH Zurich.
use super::property::Property;
use super::property_expressions::{BooleanExpression, ChunkPlaceholder};
use super::property_interpreter::{PropertyContext, PropertyError, PropertyInterpreter};
use crate::interfaces::state::chunks::{GeneralChunk, QuantifiedChunk};
use crate::resources::resources::ResourceId;
use crate::state::chunks::{Chunk, ChunkIdentifier};
use crate::state::terms::{Term, TermFactory, UnsupportedTriggerTransform};
use std::collections::HashMap;

#[derive(Debug)]
pub enum NonQuantifiedError<E> {
    Solver(E),
    MissingChunk,
    ForEachWithThis,
    UnsupportedChunk,
    Transform(UnsupportedTriggerTransform),
    ZeroDenominator,
    InvalidQuantifier,
}
fn identity(c: &Chunk) -> Option<(ResourceId, ChunkIdentifier)> {
    match c {
        Chunk::Basic(c) => Some((c.resource_id(), c.identifier())),
        Chunk::MagicWand(c) => Some((c.resource_id(), c.identifier())),
        Chunk::QuantifiedField(c) if c.singleton_arguments().is_some() => {
            Some((c.resource_id(), c.identifier()))
        }
        Chunk::QuantifiedPredicate(c) if c.singleton_arguments().is_some() => {
            Some((c.resource_id(), c.identifier()))
        }
        _ => None,
    }
}
struct Context<'a, 'h, F> {
    factory: &'a TermFactory,
    heap: &'h [&'h Chunk],
    resource: ResourceId,
    bindings: HashMap<ChunkPlaceholder, &'h Chunk>,
    check: &'a mut F,
}
impl<'a, 'h, F, E> Context<'a, 'h, F>
where
    F: FnMut(&Term) -> Result<bool, E>,
{
    fn get(&self, c: &ChunkPlaceholder) -> Result<&'h Chunk, NonQuantifiedError<E>> {
        self.bindings
            .get(c)
            .copied()
            .ok_or(NonQuantifiedError::MissingChunk)
    }
    fn singleton<Q: QuantifiedChunk>(
        &self,
        c: &Q,
        args: Vec<Term>,
    ) -> Result<Term, NonQuantifiedError<E>> {
        let replacements = c
            .quantified_vars(self.factory)
            .into_iter()
            .zip(args)
            .collect();
        self.factory
            .replace(&c.permission(self.factory), &replacements)
            .map_err(NonQuantifiedError::Transform)
    }
    fn permutations(
        &mut self,
        chunks: &[&'h Chunk],
        vars: &[ChunkPlaceholder],
        body: &BooleanExpression,
    ) -> Result<Term, PropertyError<NonQuantifiedError<E>>> {
        let mut results = Vec::new();
        for chunk in chunks {
            if self
                .bindings
                .values()
                .any(|existing| std::ptr::eq(*existing, *chunk))
            {
                continue;
            }
            let old = self.bindings.insert(vars[0].clone(), *chunk);
            let result = if vars.len() == 1 {
                PropertyInterpreter {
                    factory: self.factory,
                    context: &mut *self,
                }
                .boolean(body)
            } else {
                self.permutations(chunks, &vars[1..], body)
            };
            if let Some(old) = old {
                self.bindings.insert(vars[0].clone(), old);
            } else {
                self.bindings.remove(&vars[0]);
            }
            results.push(result?);
        }
        Ok(self.factory.and(results))
    }
}
impl<F, E> PropertyContext for &mut Context<'_, '_, F>
where
    F: FnMut(&Term) -> Result<bool, E>,
{
    type Error = NonQuantifiedError<E>;
    fn permission(&mut self, key: &ChunkPlaceholder) -> Result<Term, Self::Error> {
        match self.get(key)? {
            Chunk::Basic(c) => Ok(c.permission(self.factory)),
            Chunk::MagicWand(c) => Ok(c.permission(self.factory)),
            Chunk::QuantifiedField(c) => self.singleton(
                c,
                c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?,
            ),
            Chunk::QuantifiedPredicate(c) => self.singleton(
                c,
                c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?
                    .to_vec(),
            ),
            _ => Err(NonQuantifiedError::UnsupportedChunk),
        }
    }
    fn value(&mut self, key: &ChunkPlaceholder) -> Result<Term, Self::Error> {
        match self.get(key)? {
            Chunk::Basic(c) => Ok(c.snap_ref().clone()),
            Chunk::MagicWand(c) => Ok(c.snap_ref().clone()),
            Chunk::QuantifiedField(c) => Ok(c.value_at(
                self.factory,
                &c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?,
            )),
            Chunk::QuantifiedPredicate(c) => Ok(c.value_at(
                self.factory,
                c.singleton_arguments()
                    .ok_or(NonQuantifiedError::UnsupportedChunk)?,
            )),
            _ => Err(NonQuantifiedError::UnsupportedChunk),
        }
    }
    fn arguments(&mut self, key: &ChunkPlaceholder) -> Result<Vec<Term>, Self::Error> {
        match self.get(key)? {
            Chunk::Basic(c) => Ok(c.args_ref().clone()),
            Chunk::MagicWand(c) => Ok(c.args_ref().clone()),
            Chunk::QuantifiedField(c) => c
                .singleton_arguments()
                .ok_or(NonQuantifiedError::UnsupportedChunk),
            Chunk::QuantifiedPredicate(c) => Ok(c
                .singleton_arguments()
                .ok_or(NonQuantifiedError::UnsupportedChunk)?
                .to_vec()),
            _ => Err(NonQuantifiedError::UnsupportedChunk),
        }
    }
    fn check(&mut self, term: &Term) -> Result<Option<bool>, Self::Error> {
        (self.check)(term)
            .map(Some)
            .map_err(NonQuantifiedError::Solver)
    }
    fn for_each(
        &mut self,
        factory: &TermFactory,
        vars: &[ChunkPlaceholder],
        body: &BooleanExpression,
    ) -> Result<Term, PropertyError<Self::Error>> {
        if self.bindings.contains_key(&ChunkPlaceholder::This) {
            return Err(PropertyError::Context(NonQuantifiedError::ForEachWithThis));
        }
        let mut groups: Vec<(ChunkIdentifier, Vec<&Chunk>)> = Vec::new();
        for chunk in self.heap {
            if let Some((resource, id)) = identity(chunk) {
                if resource == self.resource {
                    if let Some((_, group)) = groups.iter_mut().find(|(key, _)| *key == id) {
                        group.push(chunk);
                    } else {
                        groups.push((id, vec![chunk]));
                    }
                }
            }
        }
        let mut result = Vec::new();
        for (_, chunks) in groups {
            result.push(self.permutations(&chunks, vars, body)?);
        }
        Ok(factory.and(result))
    }
}
/// Evaluate a property against a resource group or a particular chunk. Debug expressions
/// are deliberately not fabricated: the debug-aware source counterpart is still pending.
pub fn build<E>(
    factory: &TermFactory,
    heap: &[&Chunk],
    resource: ResourceId,
    this: Option<&Chunk>,
    property: &Property,
    mut check: impl FnMut(&Term) -> Result<bool, E>,
) -> Result<Term, PropertyError<NonQuantifiedError<E>>> {
    let mut bindings = HashMap::new();
    if let Some(chunk) = this {
        bindings.insert(ChunkPlaceholder::This, chunk);
    }
    let mut context = Context {
        factory,
        heap,
        resource,
        bindings,
        check: &mut check,
    };
    PropertyInterpreter {
        factory,
        context: &mut context,
    }
    .boolean(&property.expression)
}
